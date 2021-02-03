/**
 * Compiler implementation of the
 * $(LINK2 http://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (C) 1999-2021 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 http://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/src/dmd/backend/dwarfdbginf.d, backend/dwarfdbginf.d)
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/src/dmd/backend/dwarfdbginf.d
 */

// Emit Dwarf symbolic debug info

/*
Some generic information for debug info on macOS:

The linker on macOS will remove any debug info, i.e. every section with the
`S_ATTR_DEBUG` flag, this includes everything in the `__DWARF` section. By using
the `S_REGULAR` flag the linker will not remove this section. This allows to get
the filenames and line numbers for backtraces from the executable.

Normally the linker removes all the debug info but adds a reference to the
object files. The debugger can then read the object files to get filename and
line number information. It's also possible to use an additional tool that
generates a separate `.dSYM` file. This file can then later be deployed with the
application if debug info is needed when the application is deployed.
*/

module dmd.backend.dwarfdbginf;

version (SCPP)
    version = COMPILE;
version (MARS)
    version = COMPILE;

version (COMPILE):

import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.string;
import core.stdc.errno;

import dmd.backend.cc;
import dmd.backend.cdef;

version(Windows)
{
    nothrow
    extern (C) char* getcwd(char* buffer, size_t maxlen);
    nothrow
    extern (C) int* _errno();   // not the multi-threaded version
}
else
{
    import core.sys.posix.unistd : getcwd;
}

static if (1)
{
    import dmd.backend.aarray;
    import dmd.backend.barray;
    import dmd.backend.code;
    import dmd.backend.code_x86;
    import dmd.backend.dwarf;
    import dmd.backend.dwarf2;
    import dmd.backend.dwarfeh : sLEB128size;
    import dmd.backend.mem;
    import dmd.backend.dlist;
    import dmd.backend.el;
    import dmd.backend.global;
    import dmd.backend.obj;
    import dmd.backend.oper;
    import dmd.backend.outbuf;
    import dmd.backend.symtab;
    import dmd.backend.ty;
    import dmd.backend.type;

    import dmd.backend.melf;
    import dmd.backend.mach;

    extern (C++):

    nothrow:

    int REGSIZE();

    __gshared
    {
        //static if (MACHOBJ)
            int except_table_seg = UNKNOWN; // __gcc_except_tab segment
            int except_table_num = 0;       // sequence number for GCC_except_table%d symbols
            int eh_frame_seg = UNKNOWN;     // __eh_frame segment
            Symbol *eh_frame_sym = null;    // past end of __eh_frame

        uint CIE_offset_unwind;     // CIE offset for unwind data
        uint CIE_offset_no_unwind;  // CIE offset for no unwind data

        static if (ELFOBJ)
        {
            IDXSYM elf_addsym(IDXSTR nam, targ_size_t val, uint sz,
                    uint typ, uint bind, IDXSEC sec,
                    ubyte visibility = STV_DEFAULT);
            void addSegmentToComdat(segidx_t seg, segidx_t comdatseg);
        }

        static if (MACHOBJ)
        {
            int getsegment2(ref int seg, const(char)* sectname, const(char)* segname,
                int align_, int flags);
        }

        Symbol* getRtlsymPersonality();

        private Barray!(Symbol*) resetSyms;        // Keep pointers to reset symbols
    }

    /***********************************
     * Determine if generating a eh_frame with full
     * unwinding information.
     * This decision is done on a per-function basis.
     * Returns:
     *      true if unwinding needs to be done
     */
    bool doUnwindEhFrame()
    {
        if (funcsym_p.Sfunc.Fflags3 & Feh_none)
        {
            return (config.exe & (EX_FREEBSD | EX_FREEBSD64 | EX_DRAGONFLYBSD64)) != 0;
        }

        /* FreeBSD fails when having some frames as having unwinding info and some not.
         * (It hangs in unittests for std.datetime.)
         * g++ on FreeBSD does not generate mixed frames, while g++ on OSX and Linux does.
         */
        assert(!(usednteh & ~(EHtry | EHcleanup)));
        return (usednteh & (EHtry | EHcleanup)) ||
               (config.exe & (EX_FREEBSD | EX_FREEBSD64 | EX_DRAGONFLYBSD64)) && config.useExceptions;
    }

    static if (ELFOBJ)
        SYMIDX MAP_SEG2SYMIDX(int seg) { return SegData[seg].SDsymidx; }
    else
        SYMIDX MAP_SEG2SYMIDX(int seg) { assert(0); }


    int OFFSET_FAC() { return REGSIZE(); }

    int dwarf_getsegment(const(char)* name, int align_, int flags)
    {
        static if (ELFOBJ)
            return Obj.getsegment(name, null, flags, 0, align_ * 4);
        else static if (MACHOBJ)
            return Obj.getsegment(name, "__DWARF", align_ * 2, flags);
        else
            assert(0);
    }

    static if (ELFOBJ)
    {
        int dwarf_getsegment_alloc(const(char)* name, const(char)* suffix, int align_)
        {
            return Obj.getsegment(name, suffix, SHT_PROGBITS, SHF_ALLOC, align_ * 4);
        }
    }

    int dwarf_except_table_alloc(Symbol *s)
    {
        //printf("dwarf_except_table_alloc('%s')\n", s.Sident.ptr);
        static if (ELFOBJ)
        {
            /* If `s` is in a COMDAT, then this table needs to go into
             * a unique section, which then gets added to the COMDAT group
             * associated with `s`.
             */
            seg_data *pseg = SegData[s.Sseg];
            if (pseg.SDassocseg)
            {
                const(char)* suffix = s.Sident.ptr; // cpp_mangle(s);
                segidx_t tableseg = Obj.getsegment(".gcc_except_table.", suffix, SHT_PROGBITS, SHF_ALLOC|SHF_GROUP, 1);
                addSegmentToComdat(tableseg, s.Sseg);
                return tableseg;
            }
            else
                return dwarf_getsegment_alloc(".gcc_except_table", null, 1);
        }
        else static if (MACHOBJ)
        {
            return getsegment2(except_table_seg, "__gcc_except_tab", "__TEXT", 2, S_REGULAR);
        }
        else
            assert(0);
    }

    int dwarf_eh_frame_alloc()
    {
        static if (ELFOBJ)
            return dwarf_getsegment_alloc(".eh_frame", null, I64 ? 2 : 1);
        else static if (MACHOBJ)
        {
            int seg = getsegment2(eh_frame_seg, "__eh_frame", "__TEXT", I64 ? 3 : 2,
                S_COALESCED | S_ATTR_NO_TOC | S_ATTR_STRIP_STATIC_SYMS | S_ATTR_LIVE_SUPPORT);
            /* Generate symbol for it to use for fixups
             */
            if (!eh_frame_sym)
            {
                type *t = tspvoid;
                t.Tcount++;
                type_setmangle(&t, mTYman_sys);         // no leading '_' for mangled name
                eh_frame_sym = symbol_name("EH_frame0", SCstatic, t);
                Obj.pubdef(seg, eh_frame_sym, 0);
                symbol_keep(eh_frame_sym);
            }
            return seg;
        }
        else
            assert(0);
    }

    // machobj.c
    enum RELaddr = 0;       // straight address
    enum RELrel  = 1;       // relative to location to be fixed up

    void dwarf_addrel(int seg, targ_size_t offset, int targseg, targ_size_t val = 0)
    {
        static if (ELFOBJ)
            Obj.addrel(seg, offset, I64 ? R_X86_64_32 : R_386_32, cast(int)MAP_SEG2SYMIDX(targseg), val);
        else static if (MACHOBJ)
            Obj.addrel(seg, offset, cast(Symbol*) null, targseg, RELaddr, cast(int)val);
        else
            assert(0);
    }

    void dwarf_addrel64(int seg, targ_size_t offset, int targseg, targ_size_t val)
    {
        static if (ELFOBJ)
            Obj.addrel(seg, offset, R_X86_64_64, cast(int)MAP_SEG2SYMIDX(targseg), val);
        else static if (MACHOBJ)
            Obj.addrel(seg, offset, null, targseg, RELaddr, cast(uint)val);
        else
            assert(0);
    }

    /**
     * Append a relocatable address (`targseg`) to `seg` at an offset.
     *
     * Params:
     *      seg     = where the address is going
     *      buf     = offset within seg (length is used)
     *      targseg = segment to relocate
     *      val     = addend or displacement from address
     */
    void dwarf_appreladdr(int seg, Outbuffer *buf, int targseg, targ_size_t val)
    {
        if (I64)
        {
            dwarf_addrel64(seg, buf.length(), targseg, val);
            buf.write64(0);
        }
        else
        {
            dwarf_addrel(seg, buf.length(), targseg, 0);
            buf.write32(cast(uint)val);
        }
    }

    void dwarf_apprel32(int seg, Outbuffer *buf, int targseg, targ_size_t val)
    {
        dwarf_addrel(seg, buf.length(), targseg, I64 ? val : 0);
        buf.write32(I64 ? 0 : cast(uint)val);
    }

    void append_addr(Outbuffer *buf, targ_size_t addr)
    {
        if (I64)
            buf.write64(addr);
        else
            buf.write32(cast(uint)addr);
    }


    /************************  DWARF DEBUG OUTPUT ********************************/

    // Dwarf Symbolic Debugging Information

    // CFA = value of the stack pointer at the call site in the previous frame

    struct CFA_reg
    {
        int offset;                 // offset from CFA
    }

    // Current CFA state for .debug_frame
    struct CFA_state
    {
        size_t location;
        int reg;                    // CFA register number
        int offset;                 // CFA register offset
        CFA_reg[17] regstates;      // register states
    }

    /***********************
     * Convert CPU register number to Dwarf register number.
     * Params:
     *      reg = CPU register
     * Returns:
     *      dwarf register
     */
    int dwarf_regno(int reg)
    {
        assert(reg < NUMGENREGS);
        if (I32)
        {
            static if (MACHOBJ)
            {
                    if (reg == BP || reg == SP)
                        reg ^= BP ^ SP;     // swap EBP and ESP register values for OSX (!)
            }
            return reg;
        }
        else
        {
            assert(I64);
            /* See https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf
             * Figure 3.3.8 pg. 62
             * R8..15    :  8..15
             * XMM0..15  : 17..32
             * ST0..7    : 33..40
             * MM0..7    : 41..48
             * XMM16..31 : 67..82
             */
            static immutable int[8] to_amd64_reg_map =
            // AX CX DX BX SP BP SI DI
            [   0, 2, 1, 3, 7, 6, 4, 5 ];
            return reg < 8 ? to_amd64_reg_map[reg] : reg;
        }
    }

    private __gshared
    {
        CFA_state CFA_state_init_32 =       // initial CFA state as defined by CIE
        {   0,                // location
            -1,               // register
            4,                // offset
            [   { 0 },        // 0: EAX
                { 0 },        // 1: ECX
                { 0 },        // 2: EDX
                { 0 },        // 3: EBX
                { 0 },        // 4: ESP
                { 0 },        // 5: EBP
                { 0 },        // 6: ESI
                { 0 },        // 7: EDI
                { -4 },       // 8: EIP
            ]
        };

        CFA_state CFA_state_init_64 =       // initial CFA state as defined by CIE
        {   0,                // location
            -1,               // register
            8,                // offset
            [   { 0 },        // 0: RAX
                { 0 },        // 1: RBX
                { 0 },        // 2: RCX
                { 0 },        // 3: RDX
                { 0 },        // 4: RSI
                { 0 },        // 5: RDI
                { 0 },        // 6: RBP
                { 0 },        // 7: RSP
                { 0 },        // 8: R8
                { 0 },        // 9: R9
                { 0 },        // 10: R10
                { 0 },        // 11: R11
                { 0 },        // 12: R12
                { 0 },        // 13: R13
                { 0 },        // 14: R14
                { 0 },        // 15: R15
                { -8 },       // 16: RIP
            ]
        };

        CFA_state CFA_state_current;     // current CFA state
        Outbuffer cfa_buf;               // CFA instructions
    }

    /***********************************
     * Set the location, i.e. the offset from the start
     * of the function. It must always be greater than
     * the current location.
     * Params:
     *      location = offset from the start of the function
     */
    void dwarf_CFA_set_loc(uint location)
    {
        assert(location >= CFA_state_current.location);
        uint inc = cast(uint)(location - CFA_state_current.location);
        if (inc <= 63)
            cfa_buf.writeByte(DW_CFA_advance_loc + inc);
        else if (inc <= 255)
        {   cfa_buf.writeByte(DW_CFA_advance_loc1);
            cfa_buf.writeByte(inc);
        }
        else if (inc <= 0xFFFF)
        {   cfa_buf.writeByte(DW_CFA_advance_loc2);
            cfa_buf.write16(inc);
        }
        else
        {   cfa_buf.writeByte(DW_CFA_advance_loc4);
            cfa_buf.write32(inc);
        }
        CFA_state_current.location = location;
    }

    /*******************************************
     * Set the frame register, and its offset.
     * Params:
     *      reg = machine register
     *      offset = offset from frame register
     */
    void dwarf_CFA_set_reg_offset(int reg, int offset)
    {
        int dw_reg = dwarf_regno(reg);
        if (dw_reg != CFA_state_current.reg)
        {
            if (offset == CFA_state_current.offset)
            {
                cfa_buf.writeByte(DW_CFA_def_cfa_register);
                cfa_buf.writeuLEB128(dw_reg);
            }
            else if (offset < 0)
            {
                cfa_buf.writeByte(DW_CFA_def_cfa_sf);
                cfa_buf.writeuLEB128(dw_reg);
                cfa_buf.writesLEB128(offset / -OFFSET_FAC);
            }
            else
            {
                cfa_buf.writeByte(DW_CFA_def_cfa);
                cfa_buf.writeuLEB128(dw_reg);
                cfa_buf.writeuLEB128(offset);
            }
        }
        else if (offset < 0)
        {
            cfa_buf.writeByte(DW_CFA_def_cfa_offset_sf);
            cfa_buf.writesLEB128(offset / -OFFSET_FAC);
        }
        else
        {
            cfa_buf.writeByte(DW_CFA_def_cfa_offset);
            cfa_buf.writeuLEB128(offset);
        }
        CFA_state_current.reg = dw_reg;
        CFA_state_current.offset = offset;
    }

    /***********************************************
     * Set reg to be at offset from frame register.
     * Params:
     *      reg = machine register
     *      offset = offset from frame register
     */
    void dwarf_CFA_offset(int reg, int offset)
    {
        int dw_reg = dwarf_regno(reg);
        if (CFA_state_current.regstates[dw_reg].offset != offset)
        {
            if (offset <= 0)
            {
                cfa_buf.writeByte(DW_CFA_offset + dw_reg);
                cfa_buf.writeuLEB128(offset / -OFFSET_FAC);
            }
            else
            {
                cfa_buf.writeByte(DW_CFA_offset_extended_sf);
                cfa_buf.writeuLEB128(dw_reg);
                cfa_buf.writesLEB128(offset / -OFFSET_FAC);
            }
        }
        CFA_state_current.regstates[dw_reg].offset = offset;
    }

    /**************************************
     * Set total size of arguments pushed on the stack.
     * Params:
     *      sz = total size
     */
    void dwarf_CFA_args_size(size_t sz)
    {
        cfa_buf.writeByte(DW_CFA_GNU_args_size);
        cfa_buf.writeuLEB128(cast(uint)sz);
    }

    struct Section
    {
        segidx_t seg = 0;
        IDXSEC secidx = 0;
        Outbuffer *buf = null;
        const(char)* name;

        static if (MACHOBJ)
            immutable flags = S_ATTR_DEBUG;
        else
            immutable flags = SHT_PROGBITS;

        /* Allocate and initialize Section
         */
        nothrow void initialize()
        {
            const segidx_t segi = dwarf_getsegment(name, 0, flags);
            seg = segi;
            secidx = SegData[segi].SDshtidx;
            buf = SegData[segi].SDbuf;
            buf.reserve(1000);
        }
    }


    private __gshared
    {

        static if (MACHOBJ)
        {
            Section debug_names         = { name: "__debug_names" };
            Section debug_aranges       = { name: "__debug_aranges" };
            Section debug_rnglists      = { name: "__debug_rnglists" };
            Section debug_loclists      = { name: "__debug_loclists" };
            Section debug_abbrev        = { name: "__debug_abbrev" };
            Section debug_info          = { name: "__debug_info" };
            Section debug_str           = { name: "__debug_str" };
            Section debug_macro         = { name: "__debug_macro" };
            Section debug_addr          = { name: "__debug_addr" };
            Section debug_str_offsets   = { name: "__debug_str_offsets" };
            Section debug_line_str      = { name: "__debug_line_str" };
            // We use S_REGULAR to make sure the linker doesn't remove this section. Needed
            // for filenames and line numbers in backtraces.
            Section debug_line          = { name: "__debug_line", flags: S_REGULAR };

            const char* debug_frame_name = "__debug_frame";
        }
        else static if (ELFOBJ)
        {
            Section debug_names         = { name: ".debug_names" };
            Section debug_aranges       = { name: ".debug_aranges" };
            Section debug_rnglists      = { name: ".debug_rnglists" };
            Section debug_loclists      = { name: ".debug_loclists" };
            Section debug_abbrev        = { name: ".debug_abbrev" };
            Section debug_info          = { name: ".debug_info" };
            Section debug_str           = { name: ".debug_str" };
            Section debug_macro         = { name: ".debug_macro" };
            Section debug_addr          = { name: ".debug_addr" };
            Section debug_str_offsets   = { name: ".debug_str_offsets" };
            Section debug_line_str      = { name: ".debug_line_str" };
            Section debug_line          = { name: ".debug_line" };
        }
        else
        {
            Section debug_pubnames;
            Section debug_aranges;
            Section debug_ranges;
            Section debug_loc;
            Section debug_abbrev;
            Section debug_info;
            Section debug_str;
            Section debug_line;
        }

        static if (MACHOBJ)
            const char* debug_frame_name = "__debug_frame";
        else static if (ELFOBJ)
            const char* debug_frame_name = ".debug_frame";
        else
            const char* debug_frame_name = null;

        /* DWARF 7.5.3: "Each declaration begins with an unsigned LEB128 number
         * representing the abbreviation code itself."
         */
        uint abbrevcode;
        AApair *abbrev_table;
        bool hasModname;    // if has DW_TAG_module

        // .debug_info
        AApair *type_table;
        AApair *functype_table;  // not sure why this cannot be combined with type_table
        Outbuffer *functypebuf;

        // debug_info's compilation unit offset
        size_t CUoffset;

        // .debug_line
        uint filenamesCount;
        AAchars* filenames_table;
        Barray!ubyte line_number_prog;
        const(char)[] primary_filename;

        immutable byte line_base = -5;
        immutable ubyte line_range = 14;
        immutable ubyte opcode_base = 13;

        public uint[TYMAX] typidx_tab;

        // .debug_names

        // We need to store offsets because the final count/size will be rewritten.
        size_t nCountOffset;
        size_t nAbbrevSizeOffset;

        size_t nCount;  // name_count


        // TODO:
        // 6.1.1.4.5 Hash Lookup Table
        Barray!uint nBuckets;
        Barray!uint nHashes;

        AApair* nAbbrevTable;
        uint nAbbrevCode;
        Outbuffer* nAbbrevBuffer;

        Barray!size_t nStringOffsets;
        Barray!size_t nEntryOffsets;
        Outbuffer* nIndexEntries;

        // .debug_loclists

        // List of Register Location Description
        Barray!RegLocDesc loc_regdesc;

        struct TargetAddress
        {
            IDXSEC seg;
            size_t func_offset;
        }

        struct RegLocDesc
        {
            TargetAddress[2] addresses;
            uint len;       // counted location description
            ubyte op;       // location descriptions
            int val;        // value of the OP code
        }
    }


    /*****************************************
     * Replace the bytes in `buf` from the `offset` by `data`.
     *
     * Params:
     *      buf = buffer where `data` will be written
     *      offset = offset of the bytes in `buf` to replace
     *      data = bytes to write
     */
    extern(D) void rewrite32(Outbuffer* buf, uint offset, uint data)
    {
        ulong end = offset + data.sizeof;
        for(uint i = 0; i < end - offset; ++i)
            buf.buf[offset + i] = (data >> (8 * i)) & 0xff;
    }

    /// Ditto
    extern(D) void rewrite64(Outbuffer* buf, uint offset, ulong data)
    {
        ulong end = offset + data.sizeof;
        for(uint i = 0; i < end - offset; ++i)
            buf.buf[offset + i] = (data >> (8 * i)) & 0xff;
    }

    void rewriteAddr(Outbuffer* buf, uint offset, size_t data)
    {
        if (I64)
            rewrite64(buf, offset, data); // minus unit_length's length
        else
            rewrite32(buf, offset, cast(uint)data); // Ditto
    }

    /*****************************************
     * Replace the `length` header in `buf`.
     * `writeUnitLength` must be called first.
     *
     * Params:
     *      buf = buffer where the `length` will be written
     *      length = length to write
     *
     * See_Also:
     *      writeUnitLength
     */
    void rewriteUnitLength(Outbuffer* buf, size_t length)
    {
        if (I64)
            rewrite64(buf, 4, length - 12); // minus unit_length's length
        else
            rewrite32(buf, 0, cast(uint)length - 4); // Ditto
    }

    /*****************************************
     * Append `length` to `buf` according to the DWARF v5 specification,
     * chapter 7.2.2 Initial Length Values
     *
     * Params:
     *      buf = buffer where the `length` will be written
     *      length = length to write
     * See_Also:
     *      rewriteUnitLength
     */
    void writeUnitLength(Outbuffer* buf, size_t length = 0)
    {
        if (I64)
            buf.write32(0xffffffff);    // initial length
        else
            assert(length < 0xfffffff0);
        append_addr(buf, length);       // actual length
    }

    /*****************************************
     * Append .debug_frame header to buf.
     * Params:
     *      buf = write raw data here
     */
    void writeDebugFrameHeader(Outbuffer *buf)
    {
        writeUnitLength(buf, I64 ? 20 : 16);                        // unit length
        append_addr(buf, I64 ? 0xffffffffffffffff : 0xffffffff);    // CIE id
        buf.writeByte(4);                                           // version
        buf.writeByte(0);                                           // augmentation
        buf.writeByte(I64 ? 8 : 4);                                 // address size
        buf.writeByte(0);                                           // segment selector size
        buf.writeByte(1);                                           // code alignement factor
        buf.writeByte(I64 ? 0x78 : 0x7c);                           // data alignement factor
        buf.writeByte(I64 ? 16 : 8);                                // return address register
        // TODO:
        buf.writeByte(0);                                           // initial instructions

        ubyte[11] padding =
        [
            DW_CFA_def_cfa,
            I64 ? 7 : 4, I64 ? 8 : 4,           // r4,4 [r7, 8]
            DW_CFA_offset + (I64 ? 16 : 8), 1,  // r8,1 [r16,1]
            DW_CFA_nop, DW_CFA_nop,
            DW_CFA_nop, DW_CFA_nop, // 64 padding
            DW_CFA_nop, DW_CFA_nop, // 64 padding
        ];

        buf.write(padding.ptr, padding.length);                      // padding
    }

    /*****************************************
     * Append .eh_frame header to buf.
     * Almost identical to .debug_frame
     * Params:
     *      dfseg = SegData[] index for .eh_frame
     *      buf = write raw data here
     *      personality = "__dmd_personality_v0"
     *      ehunwind = will have EH unwind table
     * Returns:
     *      offset of start of this header
     * See_Also:
     *      https://refspecs.linuxfoundation.org/LSB_3.0.0/LSB-PDA/LSB-PDA/ehframechpt.html
     */
    private uint writeEhFrameHeader(IDXSEC dfseg, Outbuffer *buf, Symbol *personality, bool ehunwind)
    {
        /* Augmentation string:
         *  z = first character, means Augmentation Data field is present
         *  eh = EH Data field is present
         *  P = Augmentation Data contains 2 args:
         *          1. encoding of 2nd arg
         *          2. address of personality routine
         *  L = Augmentation Data contains 1 arg:
         *          1. the encoding used for Augmentation Data in FDE
         *      Augmentation Data in FDE:
         *          1. address of LSDA (gcc_except_table)
         *  R = Augmentation Data contains 1 arg:
         *          1. encoding of addresses in FDE
         * Non-EH code: "zR"
         * EH code: "zPLR"
         */

        const uint startsize = cast(uint)buf.length();

        // Length of CIE, not including padding
        const uint cielen = 4 + 4 + 1 +
            (ehunwind ? 5 : 3) +
            1 + 1 + 1 +
            (ehunwind ? 8 : 2) +
            5;

        const uint pad = -cielen & (I64 ? 7 : 3);      // pad to addressing unit size boundary
        const uint length = cielen + pad - 4;

        buf.reserve(length + 4);
        buf.write32(length);       // length of CIE, not including length and extended length fields
        buf.write32(0);            // CIE ID
        buf.writeByten(1);         // version_
        if (ehunwind)
            buf.write("zPLR".ptr, 5);  // Augmentation String
        else
            buf.writen("zR".ptr, 3);
        // not present: EH Data: 4 bytes for I32, 8 bytes for I64
        buf.writeByten(1);                 // code alignment factor
        buf.writeByten(cast(ubyte)(0x80 - OFFSET_FAC)); // data alignment factor (I64 ? -8 : -4)
        buf.writeByten(I64 ? 16 : 8);      // return address register
        if (ehunwind)
        {
            static if (ELFOBJ)
            {
                    const ubyte personality_pointer_encoding = config.flags3 & CFG3pic
                            ? DW_EH_PE_indirect | DW_EH_PE_pcrel | DW_EH_PE_sdata4
                            : DW_EH_PE_absptr | DW_EH_PE_udata4;
                    const ubyte LSDA_pointer_encoding = config.flags3 & CFG3pic
                            ? DW_EH_PE_pcrel | DW_EH_PE_sdata4
                            : DW_EH_PE_absptr | DW_EH_PE_udata4;
                    const ubyte address_pointer_encoding =
                            DW_EH_PE_pcrel | DW_EH_PE_sdata4;
            }
            else static if (MACHOBJ)
            {
                    const ubyte personality_pointer_encoding =
                            DW_EH_PE_indirect | DW_EH_PE_pcrel | DW_EH_PE_sdata4;
                    const ubyte LSDA_pointer_encoding =
                            DW_EH_PE_pcrel | DW_EH_PE_ptr;
                    const ubyte address_pointer_encoding =
                            DW_EH_PE_pcrel | DW_EH_PE_ptr;
            }
            else
            {
                    const ubyte personality_pointer_encoding = 0;
                    const ubyte LSDA_pointer_encoding = 0;
                    const ubyte address_pointer_encoding = 0;
            }
            buf.writeByten(7);                                  // Augmentation Length
            buf.writeByten(personality_pointer_encoding);       // P: personality routine address encoding
            /* MACHOBJ 64: pcrel 1 length 2 extern 1 RELOC_GOT
             *         32: [4] address x0013 pcrel 0 length 2 value xfc type 4 RELOC_LOCAL_SECTDIFF
             *             [5] address x0000 pcrel 0 length 2 value xc7 type 1 RELOC_PAIR
             */
            if (config.objfmt == OBJ_ELF)
                elf_dwarf_reftoident(dfseg, buf.length(), personality, 0);
            else
                mach_dwarf_reftoident(dfseg, buf.length(), personality, 0);
            buf.writeByten(LSDA_pointer_encoding);              // L: address encoding for LSDA in FDE
            buf.writeByten(address_pointer_encoding);           // R: encoding of addresses in FDE
        }
        else
        {
            buf.writeByten(1);                                  // Augmentation Length

            static if (ELFOBJ)
                    buf.writeByten(DW_EH_PE_pcrel | DW_EH_PE_sdata4);   // R: encoding of addresses in FDE
            static if (MACHOBJ)
                    buf.writeByten(DW_EH_PE_pcrel | DW_EH_PE_ptr);      // R: encoding of addresses in FDE
        }

        // Set CFA beginning state at function entry point
        if (I64)
        {
            buf.writeByten(DW_CFA_def_cfa);        // DEF_CFA r7,8   RSP is at offset 8
            buf.writeByten(7);                     // r7 is RSP
            buf.writeByten(8);

            buf.writeByten(DW_CFA_offset + 16);    // OFFSET r16,1   RIP is at -8*1[RSP]
            buf.writeByten(1);
        }
        else
        {
            buf.writeByten(DW_CFA_def_cfa);        // DEF_CFA ESP,4
            buf.writeByten(cast(ubyte)dwarf_regno(SP));
            buf.writeByten(4);

            buf.writeByten(DW_CFA_offset + 8);     // OFFSET r8,1
            buf.writeByten(1);
        }

        for (uint i = 0; i < pad; ++i)
            buf.writeByten(DW_CFA_nop);

        assert(startsize + length + 4 == buf.length());
        return startsize;
    }

    /*********************************************
     * Generate function's Frame Description Entry into .debug_frame
     * Params:
     *      dfseg = SegData[] index for .debug_frame
     *      sfunc = the function
     */
    void writeDebugFrameFDE(IDXSEC dfseg, Symbol *sfunc)
    {
        if (I64)
        {
            static struct DebugFrameFDE64
            {
              align (1):
                uint length;
                uint CIE_pointer;
                ulong initial_location;
                ulong address_range;
            }
            static assert(DebugFrameFDE64.sizeof == 24);

            __gshared DebugFrameFDE64 debugFrameFDE64 =
            {
                20,             // length
                0,              // CIE_pointer
                0,              // initial_location
                0,              // address_range
            };

            // Pad to 8 byte boundary
            for (uint n = (-cfa_buf.length() & 7); n; n--)
                cfa_buf.writeByte(DW_CFA_nop);

            debugFrameFDE64.length = 20 + cast(uint)cfa_buf.length();
            debugFrameFDE64.address_range = sfunc.Ssize;
            // Do we need this?
            //debugFrameFDE64.initial_location = sfunc.Soffset;

            Outbuffer *debug_frame_buf = SegData[dfseg].SDbuf;
            uint debug_frame_buf_offset = cast(uint)debug_frame_buf.length();
            debug_frame_buf.reserve(1000);
            debug_frame_buf.writen(&debugFrameFDE64,debugFrameFDE64.sizeof);
            debug_frame_buf.write(cfa_buf[]);

            static if (ELFOBJ)
                // Absolute address for debug_frame, relative offset for eh_frame
                dwarf_addrel(dfseg,debug_frame_buf_offset + 4,dfseg,0);

            dwarf_addrel64(dfseg,debug_frame_buf_offset + 8,sfunc.Sseg,0);
        }
        else
        {
            static struct DebugFrameFDE32
            {
              align (1):
                uint length;
                uint CIE_pointer;
                uint initial_location;
                uint address_range;
            }
            static assert(DebugFrameFDE32.sizeof == 16);

            __gshared DebugFrameFDE32 debugFrameFDE32 =
            {
                12,             // length
                0,              // CIE_pointer
                0,              // initial_location
                0,              // address_range
            };

            // Pad to 4 byte boundary
            for (uint n = (-cfa_buf.length() & 3); n; n--)
                cfa_buf.writeByte(DW_CFA_nop);

            debugFrameFDE32.length = 12 + cast(uint)cfa_buf.length();
            debugFrameFDE32.address_range = cast(uint)sfunc.Ssize;
            // Do we need this?
            //debugFrameFDE32.initial_location = sfunc.Soffset;

            Outbuffer *debug_frame_buf = SegData[dfseg].SDbuf;
            uint debug_frame_buf_offset = cast(uint)debug_frame_buf.length();
            debug_frame_buf.reserve(1000);
            debug_frame_buf.writen(&debugFrameFDE32,debugFrameFDE32.sizeof);
            debug_frame_buf.write(cfa_buf[]);

            static if (ELFOBJ)
                // Absolute address for debug_frame, relative offset for eh_frame
                dwarf_addrel(dfseg,debug_frame_buf_offset + 4,dfseg,0);

            dwarf_addrel(dfseg,debug_frame_buf_offset + 8,sfunc.Sseg,0);
        }
    }

    /*********************************************
     * Append function's FDE (Frame Description Entry) to .eh_frame
     * Params:
     *      dfseg = SegData[] index for .eh_frame
     *      sfunc = the function
     *      ehunwind = will have EH unwind table
     *      CIE_offset = offset of enclosing CIE
     */
    void writeEhFrameFDE(IDXSEC dfseg, Symbol *sfunc, bool ehunwind, uint CIE_offset)
    {
        Outbuffer *buf = SegData[dfseg].SDbuf;
        const uint startsize = cast(uint)buf.length();

        static if (MACHOBJ)
        {
            /* Create symbol named "funcname.eh" for the start of the FDE
             */
            Symbol *fdesym;
            {
                const size_t len = strlen(getSymName(sfunc));
                char *name = cast(char *)malloc(len + 3 + 1);
                if (!name)
                    err_nomem();
                memcpy(name, getSymName(sfunc), len);
                memcpy(name + len, ".eh".ptr, 3 + 1);
                fdesym = symbol_name(name, SCglobal, tspvoid);
                Obj.pubdef(dfseg, fdesym, startsize);
                symbol_keep(fdesym);
                free(name);
            }
        }

        if (sfunc.ty() & mTYnaked)
        {
            /* Do not have info on naked functions. Assume they are set up as:
             *   push RBP
             *   mov  RSP,RSP
             */
            int off = 2 * REGSIZE;
            dwarf_CFA_set_loc(1);
            dwarf_CFA_set_reg_offset(SP, off);
            dwarf_CFA_offset(BP, -off);
            dwarf_CFA_set_loc(I64 ? 4 : 3);
            dwarf_CFA_set_reg_offset(BP, off);
        }

        // Length of FDE, not including padding
        static if (ELFOBJ)
            const uint fdelen = 4 + 4
                + 4 + 4
                + (ehunwind ? 5 : 1) + cast(uint)cfa_buf.length();
        else static if (MACHOBJ)
            const uint fdelen = 4 + 4
                + (I64 ? 8 + 8 : 4 + 4)                         // PC_Begin + PC_Range
                + (ehunwind ? (I64 ? 9 : 5) : 1) + cast(uint)cfa_buf.length();
        else
            const uint fdelen = 0;

            const uint pad = -fdelen & (I64 ? 7 : 3);      // pad to addressing unit size boundary
            const uint length = fdelen + pad - 4;

            buf.reserve(length + 4);
            buf.write32(length);                               // Length (no Extended Length)
            buf.write32((startsize + 4) - CIE_offset);         // CIE Pointer
        static if (ELFOBJ)
        {
            int fixup = I64 ? R_X86_64_PC32 : R_386_PC32;
            buf.write32(cast(uint)(I64 ? 0 : sfunc.Soffset));             // address of function
            Obj.addrel(dfseg, startsize + 8, fixup, cast(int)MAP_SEG2SYMIDX(sfunc.Sseg), sfunc.Soffset);
            //Obj.reftoident(dfseg, startsize + 8, sfunc, 0, CFpc32 | CFoff); // PC_begin
            buf.write32(cast(uint)sfunc.Ssize);                         // PC Range
        }
        else static if (MACHOBJ)
        {
            dwarf_eh_frame_fixup(dfseg, buf.length(), sfunc, 0, fdesym);

            if (I64)
                buf.write64(sfunc.Ssize);                     // PC Range
            else
                buf.write32(cast(uint)sfunc.Ssize);           // PC Range
        }

        if (ehunwind)
        {
            int etseg = dwarf_except_table_alloc(sfunc);
            static if (ELFOBJ)
            {
                buf.writeByten(4);                             // Augmentation Data Length
                buf.write32(I64 ? 0 : sfunc.Sfunc.LSDAoffset); // address of LSDA (".gcc_except_table")
                if (config.flags3 & CFG3pic)
                {
                    Obj.addrel(dfseg, buf.length() - 4, fixup, cast(int)MAP_SEG2SYMIDX(etseg), sfunc.Sfunc.LSDAoffset);
                }
                else
                    dwarf_addrel(dfseg, buf.length() - 4, etseg, sfunc.Sfunc.LSDAoffset);      // and the fixup
            }
            else static if (MACHOBJ)
            {
                buf.writeByten(I64 ? 8 : 4);                   // Augmentation Data Length
                dwarf_eh_frame_fixup(dfseg, buf.length(), sfunc.Sfunc.LSDAsym, 0, fdesym);
            }
        }
        else
            buf.writeByten(0);                             // Augmentation Data Length

        buf.write(cfa_buf[]);

        for (uint i = 0; i < pad; ++i)
            buf.writeByten(DW_CFA_nop);

        assert(startsize + length + 4 == buf.length());
    }

    void dwarf_initfile(const(char)* filename)
    {
        dwarf_initfile(filename ? filename[0 .. strlen(filename)] : null);
    }

    extern(D) void dwarf_initfile(const(char)[] filename)
    {
        if (config.ehmethod == EHmethod.EH_DWARF)
        {
            static if (MACHOBJ)
            {
                except_table_seg = UNKNOWN;
                except_table_num = 0;
                eh_frame_seg = UNKNOWN;
                eh_frame_sym = null;
            }
            CIE_offset_unwind = ~0;
            CIE_offset_no_unwind = ~0;
            //dwarf_except_table_alloc();
            dwarf_eh_frame_alloc();
        }
        if (!config.fulltypes)
            return;
        if (config.ehmethod == EHmethod.EH_DM)
        {
            static if (MACHOBJ)
                int flags = S_ATTR_DEBUG;
            else static if (ELFOBJ)
                int flags = SHT_PROGBITS;
            else
                int flags = 0;

            int seg = dwarf_getsegment(debug_frame_name, 1, flags);
            Outbuffer *buf = SegData[seg].SDbuf;
            buf.reserve(1000);
            writeDebugFrameHeader(buf);
        }

        /* ======================================== */

        foreach (s; resetSyms)
            symbol_reset(s);
        resetSyms.reset();


        /* *********************************************************************
         *                          String Table
         ******************************************************************** */
        {
            debug_str.initialize();
        }
        /* *********************************************************************
         *                     7.26 Strings Offset Table
         ******************************************************************** */
        {
            debug_str_offsets.initialize();

            writeUnitLength(debug_str_offsets.buf, 0);  // unit length
            debug_str_offsets.buf.write16(5);           // version
            debug_str_offsets.buf.write16(0);           // padding
        }
        /* *********************************************************************
         *                     7.27 Address Table
         ******************************************************************** */
        {
            debug_addr.initialize();

            writeUnitLength(debug_addr.buf, 0);     // unit length
            debug_addr.buf.write16(5);              // version
            debug_addr.buf.writeByte(I64 ? 8 : 4);  // address size
            debug_addr.buf.writeByte(0);            // segment selector size
        }
        /* *********************************************************************
         *                     7.28 Range List Tables
         ******************************************************************** */
        {
            debug_rnglists.initialize();

            writeUnitLength(debug_rnglists.buf, 0);     // unit length
            debug_rnglists.buf.write16(5);              // version
            debug_rnglists.buf.writeByte(I64 ? 8 : 4);  // address_size
            debug_rnglists.buf.writeByte(0);            // segment_selector_size
            debug_rnglists.buf.write32(0);              // offset_entry_count
        }
        /* *********************************************************************
         *                     7.29 Location List Table
         ******************************************************************** */
        {
            debug_loclists.initialize();

            writeUnitLength(debug_loclists.buf, 0);     // unit length
            debug_loclists.buf.write16(5);              // version
            debug_loclists.buf.writeByte(I64 ? 8 : 4);  // address_size
            debug_loclists.buf.writeByte(0);            // segment_selector_size
        }
        /* *********************************************************************
         *                     6.2.4 The Line Number Program Header
         ******************************************************************** */
        {
            if (filenames_table)
            {
                AAchars.destroy(filenames_table);
                filenames_table = null;
            }
            primary_filename = filename;

            debug_line.initialize();

            writeUnitLength(debug_line.buf, 0);     // unit length
            debug_line.buf.write16(5);              // version
            debug_line.buf.writeByte(I64 ? 8 : 4);  // address_size
            debug_line.buf.writeByte(0);            // segment_selector_size
            append_addr(debug_line.buf, 0);         // header_length
            debug_line.buf.writeByte(1);            // minimum_instruction_length
            debug_line.buf.writeByte(1);            // maximum_operations_per_instruction
            debug_line.buf.writeByte(true);         // default_is_stmt
            debug_line.buf.writeByte(line_base);    // line_base
            debug_line.buf.writeByte(line_range);   // line_range
            debug_line.buf.writeByte(opcode_base);  // opcode_base

            assert(opcode_base == 13);

            // 6.2.5.2 Standard Opcodes
            immutable ubyte[opcode_base - 1] sol =
            [
                0,      // DW_LNS_copy
                1,      // DW_LNS_advance_pc
                1,      // DW_LNS_advance_line
                1,      // DW_LNS_set_file
                1,      // DW_LNS_set_column
                0,      // DW_LNS_negate_stmt
                0,      // DW_LNS_set_basic_block
                0,      // DW_LNS_const_add_pc
                0,      // DW_LNS_fixed_advance_pc
                0,      // DW_LNS_set_prologue_end
                0,      // DW_LNS_set_epilogue_begin
                0,      // DW_LNS_set_isa
            ];
            debug_line.buf.write(sol);              // standard_opcode_lengths

            const ubyte[2] defmt =
            [
                DW_LNCT_path,   DW_FORM_string
            ];
            // number of pairs
            debug_line.buf.writeByte(1);            // directory_entry_format_count
            foreach(ubyte b; defmt)
                debug_line.buf.writeuLEB128(b);     // directory_entry_format


            version (SCPP)
            {
                debug_line.buf.writeuLEB128(pathlist.length());     // directories_count
                foreach(path; pathlist)
                {
                    debug_line.buf.writeString(path);   // directories
                    debug_line.buf.writeByte(0);
                }
            }
            else version (MARS)
            {
                debug_line.buf.writeuLEB128(1);         // directories_count
                debug_line.buf.writeString(cwd);        // directories
            }
            else version (none)
            {
                const len = global.params.imppath.dim;
                debug_line.buf.writeuLEB128(len);       // directories_count
                for (int i = 0; i < len; i++)
                {
                    debug_line.buf.writeString((*global.params.imppath)[i]);
                }
            }
            else
                assert(0);


            const ubyte[8] fefmt =
            [
                DW_LNCT_path,               DW_FORM_string,
                DW_LNCT_directory_index,    DW_FORM_udata,
                DW_LNCT_timestamp,          DW_FORM_udata,
                DW_LNCT_size,               DW_FORM_udata,
            ];
            // number of pairs
            debug_line.buf.writeByte(fefmt.length / 2); // file_name_entry_format_count

            foreach(ubyte b; fefmt)
                debug_line.buf.writeuLEB128(b);     // file_name_entry_format

            // file_names_count and file_names in dwarf_termfile
        }
        /* *********************************************************************
         *                     6.3 Macro Information
         ******************************************************************** */
        {
            debug_macro.initialize();

            debug_macro.buf.write16(5);                 // version
            ubyte flags = 0;

            if (I64)
                flags |= 1 << 0;                        // offset_size_flag

            //flags |= 1 << 1;                        // debug_line_offset_flag is present
            //flags |= 1 << 2;                        // opcode_operands_table_flag is present

            debug_macro.buf.writeByte(flags);           // flags
            //append_addr(debug_macro.buf, 0);        // debug_line_offset
            //append_addr(debug_macro.buf, 0);        // opcode_operands_table

            // DW_MACRO_define_strx
            // DW_MACRO_undef_strx
        }
        /* *********************************************************************
         *                     7.5.3 Abbreviations Tables
         ******************************************************************** */
        {
            debug_abbrev.initialize();

            // Free only if starting another file. Waste of time otherwise.
            if (abbrev_table)
            {
                AApair.destroy(abbrev_table);
                abbrev_table = null;
            }

            // Abbrev table of the compilation unit
            // Chapter 3.1.1 Full and Partial Compilation Unit Entries
            immutable ubyte[24] abbrevHeader =
            [
                DW_TAG_compile_unit,    DW_CHILDREN_yes,
                //DW_AT_ranges,           DW_FORM_sec_offset,
                DW_AT_low_pc,           DW_FORM_addr,
                DW_AT_name,             DW_FORM_string,
                DW_AT_language,         DW_FORM_data1,
                //DW_AT_stmt_list,        DW_FORM_sec_offset,
                //DW_AT_macros,           DW_FORM_sec_offset,
                DW_AT_comp_dir,         DW_FORM_string,
                DW_AT_producer,         DW_FORM_string,
                DW_AT_identifier_case,  DW_FORM_data1,
                //DW_AT_base_types,       DW_FORM_ref_sup8,   // TODO: sup4 or sup8 ? I64 ?
                DW_AT_use_UTF8,         DW_FORM_flag,
                DW_AT_main_subprogram,  DW_FORM_flag,
                DW_AT_entry_pc,         DW_FORM_addr,
                //DW_AT_str_offsets_base, DW_FORM_sec_offset, // TODO: DW_FORM_strx ?
                //DW_AT_addr_base,        DW_FORM_sec_offset, // TODO: DW_FORM_addrx ?
                //DW_AT_rnglists_base,    DW_FORM_sec_offset, // TODO: DW_FORM_rnglistx ?
                DW_AT_loclists_base,    DW_FORM_loclistx,
                0,                      0,
            ];

            abbrevcode = 0;
            dwarf_abbrev_code(abbrevHeader);
        }
        /* *********************************************************************
         *             7.5.1.1 Full and Partial Compilation Unit Headers
         ******************************************************************** */
        {
            debug_info.initialize();

            /* ================== Compilation Unit Header =================== */

            writeUnitLength(debug_info.buf, 0);         // unit length
            debug_info.buf.write16(5);                  // version
            debug_info.buf.writeByte(DW_UT_compile);    // Unit Type
            debug_info.buf.writeByte(I64 ? 8 : 4);      // Address size
            append_addr(debug_info.buf, 0);             // debug abbrev offset

            /* ================ END Compilation Unit Header ================= */

            CUoffset = debug_info.buf.length;

            /* ====================== Compilation Unit ====================== */

            //static if (ELFOBJ)
            //    dwarf_addrel(debug_info.seg, 6, debug_abbrev.seg); // TODO: Why 6 ?
            assert(abbrevcode == 1);
            debug_info.buf.writeuLEB128(abbrevcode);            // abbreviation code

            // TODO: set to the offset in rnglists
            /*
             * whose values encode the contiguous or non-contiguous address
             * ranges, respectively, of the machine instructions generated for
             * the compilation unit
             */
            // TODO: specify the default base address for use in loclists and rnglists
            // TODO: chap3.1.1
            //append_addr(debug_info.buf, 0);                     // DW_AT_ranges

            append_addr(debug_info.buf, 0);                     // DW_AT_low_pc
            debug_info.buf.writeString(filename);               // DW_AT_name

            // DW_AT_language
            version(MARS)
                debug_info.buf.writeByte((config.fulltypes == CVDWARF_D) ? DW_LANG_D : DW_LANG_C89);
            else version(SCPP)
                debug_info.buf.writeByte(DW_LANG_C89);
            else
                static assert(0);

            // TODO:
            //static if (ELFOBJ)
            //    dwarf_addrel(debug_info.seg, debug_info.buf.length(), debug_line.seg);

            // TODO: data4 -> offset (x2)
            //append_addr(debug_info.buf, 0);                   // DW_AT_stmt_list
            //append_addr(debug_info.buf, 0);                   // DW_AT_macros

            char* cwd = getcwd(null, 0);
            debug_info.buf.writeString(cwd);                    // DW_AT_comp_dir as DW_FORM_string
            free(cwd);

            // DW_AT_producer
            version (MARS)
            {
                debug_info.buf.write("Digital Mars D ");
                debug_info.buf.write(config._version);
            }
            else version (SCPP)
            {
                debug_info.buf.write("Digital Mars C ");
                debug_info.buf.writeString(global._version);
            }
            else
                static assert(0);

            debug_info.buf.writeByte(DW_ID_case_sensitive);     // DW_AT_identifier_case

            // TODO:
            // DW_AT_base_types

            debug_info.buf.writeByte(1);                        // DW_AT_use_UTF8
            // TODO: set to 1 if file contains the main function
            debug_info.buf.writeByte(0);                        // DW_AT_main_subprogram
            append_addr(debug_info.buf, 0);                     // DW_AT_entry_pc

            // TODO: data4 -> offset (x4)
            //append_addr(debug_info.buf, 0);                   // DW_AT_str_offsets_base
            //append_addr(debug_info.buf, 0);                   // DW_AT_addr_base
            //append_addr(debug_info.buf, 0);                   // DW_AT_rnglists_base

            static if (ELFOBJ)
                dwarf_addrel(debug_info.seg, debug_info.buf.length(), debug_loclists.seg);

            // The DW_AT_loclists_base attribute points to the first offset following the header.
            // + 4 because of offset_entry_count
            append_addr(debug_info.buf, debug_loclists.buf.length + 4);   // DW_AT_loclists_base

            memset(typidx_tab.ptr, 0, typidx_tab.sizeof);

            /* ==================== END Compilation Unit ==================== */
        }
        /* *********************************************************************
         *                     6.1.1 Lookup by Name
         ******************************************************************** */
        {
            debug_names.initialize();
            //int seg = debug_names.seg;

            writeUnitLength(debug_names.buf, 0);    // unit length
            debug_names.buf.write16(5);             // version
            debug_names.buf.write16(0);             // padding
            debug_names.buf.write32(1);             // comp_unit_count
            debug_names.buf.write32(0);             // local_type_unit_count
            debug_names.buf.write32(0);             // foreign_type_unit_count
            debug_names.buf.write32(0);             // bucket_count

            nCountOffset = debug_names.buf.length;
            debug_names.buf.write32(0);             // name_count

            nAbbrevSizeOffset = debug_names.buf.length;
            debug_names.buf.write32(0);             // abbrev_table_size
            debug_names.buf.write32(0);             // augmentation_string_size
            // no augmentation_string

            // TODO: check CUoffset is from debug info
            //static if (ELFOBJ)
            //    dwarf_addrel(debug_names.seg, CUoffset, debug_info.seg);
            append_addr(debug_names.buf, CUoffset); // CUs list (total: 1)
            // no TUs list

            alloc_buf(nAbbrevBuffer);
            alloc_buf(nIndexEntries);
            // TODO: delete_buf ?

        }
        /* *********************************************************************
         *                     7.21 Address Range Table
         *                     6.1.2 Lookup by Address
         ******************************************************************** */
        {
            debug_aranges.initialize();

            writeUnitLength(debug_aranges.buf, 0);      // unit length
            debug_aranges.buf.write16(2);               // version

            static if (ELFOBJ)
                dwarf_addrel(debug_aranges.seg, debug_aranges.buf.length(), debug_info.seg);

            debug_aranges.buf.write32(0);              // debug_info_offset
            debug_aranges.buf.writeByte(I64 ? 8 : 4);  // address_size
            debug_aranges.buf.writeByte(0);            // segment_size
            debug_aranges.buf.write32(0);              // pad to 16
        }
    }


    /*************************************
     * Add a file to the .debug_line header
     */
    int dwarf_line_addfile(const(char)* filename)
    {
        return dwarf_line_addfile(filename ? filename[0 .. strlen(filename)] : null);
    }

    /// Ditto
    extern(D) int dwarf_line_addfile(const(char)[] filename)
    {
        if (!filenames_table)
            filenames_table = AAchars.create();

        uint* pidx = filenames_table.get(filename);
        if (!*pidx)                 // if no idx assigned yet
            *pidx = filenames_table.length(); // assign newly computed idx

        return *pidx;
    }

    void dwarf_initmodule(const(char)* filename, const(char)* modname)
    {
        dwarf_initmodule(filename ? filename[0 .. strlen(filename)] : null,
                         modname ? modname[0 .. strlen(modname)] : null);
    }

    extern(D) void dwarf_initmodule(const(char)[] filename, const(char)[] modname)
    {
        if (modname)
        {
            static immutable ubyte[] abbrevModule =
            [
                DW_TAG_module, DW_CHILDREN_no,
                DW_AT_name,    DW_FORM_string, // module name
                0,             0,
            ];

            uint code = dwarf_abbrev_code(abbrevModule);

            debug_info.buf.writeuLEB128(code);      // abbreviation code
            debug_info.buf.writeString(modname);    // DW_AT_name
            //hasModname = 1;
        }
        else
            hasModname = 0;

        dwarf_line_addfile(filename);
    }

    void dwarf_termmodule()
    {
        if (hasModname)
            debug_info.buf.writeByte(0);  // end of DW_TAG_module's children
    }

    /*************************************
     * Finish writing Dwarf debug info to object file.
     */
    void dwarf_termfile()
    {
        //printf("dwarf_termfile()\n");

        /* ========================== debug_line ============================ */

        debug_line.buf.writeuLEB128(filenames_table.length());          // file_names_count

        /*
         * 6.2.4, The Line Number Program Header, "20. filenames", p157 :
         *
         * The first entry in the sequence is the primary source file whose file
         * name exactly matches that given in the DW_AT_name attribute in the
         * compilation unit debugging information entry.
         */
        debug_line.buf.writeString(primary_filename);   // DW_LNCT_path
        debug_line.buf.writeuLEB128(0);                 // DW_LNCT_directory_index
        debug_line.buf.writeuLEB128(0);                 // DW_LNCT_timestamp
        debug_line.buf.writeuLEB128(0);                 // DW_LNCT_size

        // TODO: set DW_LNCT_size to the size of the file in bytes
        foreach (const(char)[] f; filenames_table.aa.keys())    // file_names
        {
            if (f == primary_filename)
                continue;

            debug_line.buf.writeString(f);          // DW_LNCT_path
            debug_line.buf.writeuLEB128(0);         // DW_LNCT_directory_index
            debug_line.buf.writeuLEB128(0);         // DW_LNCT_timestamp
            debug_line.buf.writeuLEB128(0);         // DW_LNCT_size
        }


        // Put out line number info
/+
        // file_names
        uint last_filenumber = 0;
        const(char)* last_filename = null;
        for (uint seg = 1; seg < SegData.length; seg++)
        {
            for (uint i = 0; i < SegData[seg].SDlinnum_data.length; i++)
            {
                linnum_data *ld = &SegData[seg].SDlinnum_data[i];
                const(char)* filename;

                version (MARS)
                    filename = ld.filename;
                else
                {
                    Sfile *sf = ld.filptr;
                    if (sf)
                        filename = sf.SFname;
                    else
                        filename = .filename;
                }

                if (last_filename == filename)
                {
                    ld.filenumber = last_filenumber;
                }
                else
                {
                    ld.filenumber = dwarf_line_addfile(filename);

                    last_filenumber = ld.filenumber;
                    last_filename = filename;
                }
            }
        }
+/

        for (uint seg = 1; seg < SegData.length; seg++)
        {
            seg_data *sd = SegData[seg];
            uint addressmax = 0;
            uint linestart = ~0;

            if (!sd.SDlinnum_data.length)
                continue;

            // TODO: assert ?
            static if (ELFOBJ)
                if (!sd.SDsym) // gdb ignores line number data without a DW_AT_name
                    continue;

            //printf("sd = %p, SDlinnum_count = %lld\n", sd, sd.SDlinnum_data.length);
            for (int i = 0; i < sd.SDlinnum_data.length; i++)
            {
                linnum_data *ld = &sd.SDlinnum_data[i];

                // Set address to start of segment with DW_LNE_set_address
                debug_line.buf.writeByte(0);
                debug_line.buf.writeByte(_tysize[TYnptr] + 1);
                debug_line.buf.writeByte(DW_LNE_set_address);

                dwarf_appreladdr(debug_line.seg, debug_line.buf, seg, 0);

                /* *************************************************************
                 *             6.2 Line Number Information
                 ************************************************************ */

                /* ============= 6.2.2 State Machine Registers ============== */
                uint address = 0;           // instruction address
                uint opindex = 0;           // non-VLIW arch: always 0.
                uint file = ld.filenumber;
                uint line = 1;              // line numbers beginning with 1
                uint column = 1;
                bool is_stmt;               // = default_is_stmt                // TODO
                bool basic_block;           // Begining of a basic block        // TODO
                bool end_sequence;          // end of func                      // TODO
                bool prologue_end;          // breakpoint ?                     // TODO
                bool epilogue_begin;        // breakpoint prior exit ?          // TODO
                uint isa = 0;
                uint discriminator = 0;

                debug_line.buf.writeByte(DW_LNS_set_file);
                debug_line.buf.writeuLEB128(file);

                for (int j = 0; j < ld.linoff.length; j++)
                {
                    // desired line increment
                    int lininc = ld.linoff[j].lineNumber - line;
                    // operation advance
                    // address increment
                    int addinc = ld.linoff[j].offset - address;

                    //printf("\tld[%d] line = %d offset = x%x lininc = %d addinc = %d\n", j, ld.linoff[j].lineNumber, ld.linoff[j].offset, lininc, addinc);

                    //assert(addinc >= 0);
                    if (addinc < 0)
                        continue;

                    if (j && lininc == 0 && !(addinc && j + 1 == ld.linoff.length))
                        continue;

                    line += lininc;
                    if (line < linestart)
                        linestart = line;

                    address += addinc;
                    if (address >= addressmax)
                        addressmax = address + 1;

                    if (lininc >= line_base && lininc < line_base + line_range)
                    {
                        uint opcode = (lininc - line_base)
                            + (line_range * addinc)
                            + opcode_base;

                        if (opcode <= 255)
                        {
                            assert(opcode > opcode_base);
                            // special opcode
                            debug_line.buf.writeByte(opcode);
                            continue;
                        }
                    }


                    if (lininc)
                    {
                        debug_line.buf.writeByte(DW_LNS_advance_line);
                        debug_line.buf.writesLEB128(cast(int)lininc);
                    }
                    if (addinc)
                    {
                        debug_line.buf.writeByte(DW_LNS_advance_pc);
                        debug_line.buf.writeuLEB128(cast(uint)addinc);
                    }
                    if (lininc || addinc)
                        debug_line.buf.writeByte(DW_LNS_copy);
                }

                // Write DW_LNS_advance_pc to cover the function prologue
                debug_line.buf.writeByte(DW_LNS_advance_pc);
                debug_line.buf.writeuLEB128(cast(uint)(sd.SDbuf.length() - address));

                // Write DW_LNE_end_sequence
                debug_line.buf.writeByte(0);
                debug_line.buf.writeByte(1);
                debug_line.buf.writeByte(1);

                // reset linnum_data
                ld.linoff.reset();
            }
        }

        // TODO:
        // Bugzilla 3502, workaround OSX's ld64-77 bug.
        // Don't emit the the debug_line section if nothing has been written to the line table.

        rewriteUnitLength(debug_line.buf, debug_line.buf.length);

        /* ========================= debug_abbrev =========================== */

        debug_abbrev.buf.writeByte(0);  // ending abbreviation code

        /* ========================== debug_info ============================ */

        debug_info.buf.writeByte(0);    // ending abbreviation code

        rewriteUnitLength(debug_info.buf, debug_info.buf.length());

        /* *********************************************************************
         *                     6.1.1 Lookup by Name
         ******************************************************************** */
        {
            // TODO:
            // Write buckets
            // write hashes

            // 6.1.1.1
            // 2.17 Code Addresses, Ranges and Base
    /+


            ubyte[8] abbrev_variable =
            [
                DW_TAG_variable,
                DW_AT_name,     DW_FORM_string,
                DW_AT_location, DW_FORM_loclists_x, // offset in debug_loclists
                DW_IDX_parent,  DW_FORM_data8,
                0,
            ];
            dwarf_names_abbrev_code(abbrev_variable);
    +/
            debug_names.buf.write(nStringOffsets);
            //append_addr(debug_names.buf, 0);    // Last string offset

            debug_names.buf.write(nEntryOffsets);
            //append_addr(debug_names.buf, 0);    // Last entry offset

            nAbbrevBuffer.writeByte(0);         // Last abbrev code
            debug_names.buf.write(nAbbrevBuffer.buf, nAbbrevBuffer.length);
            //debug_names.buf.writeByte(0);
            nIndexEntries.writeByte(0); // Terminating entry whose abbreviation code is 0.
            debug_names.buf.write(nIndexEntries.buf, nIndexEntries.length);

            // Terminate by offset field containing 0
            debug_names.buf.write32(0);

            // Plug final sizes into header
            printf("abbrevtable: size: %lld, len: %lld, code: %d\n", nAbbrevBuffer.sizeof, nAbbrevBuffer.length, nAbbrevCode);
            printf("entry offsets: size:%lld, len: %lld, code: %lld\n", nEntryOffsets.sizeof, nEntryOffsets.length, nCount);

            assert(nEntryOffsets.length == nCount);
            assert(nStringOffsets.length == nCount);

            rewrite32(debug_names.buf, cast(uint) nAbbrevSizeOffset,
                cast(uint) nAbbrevBuffer.length);                                 // abbrev_table_size

            rewrite32(debug_names.buf, cast(uint) nCountOffset, cast(uint) nCount); // name_count

            rewriteUnitLength(debug_names.buf, debug_names.buf.length());



            //printf("names length: %lld\n", debug_names.buf.length);
            //printOutbuffer(debug_names.buf, "debug_names");
        }
        /* *********************************************************************
         *                     6.1.2 Lookup by Address
         ******************************************************************** */
        {
            // Terminate by address/length fields containing 0
            append_addr(debug_aranges.buf, 0);
            //append_addr(debug_aranges.buf, 0);

            // Plug final sizes into header
            rewriteUnitLength(debug_aranges.buf, debug_aranges.buf.length);
        }
        /* *********************************************************************
         *                     7.29 Location List Table
         ******************************************************************** */
        {
            // TODO:
            /*

    EXCEPTED ?:

0x0000023c:
            [0x000000000009693c, 0x000000000009693d): DW_OP_breg7 RSP+8
            [0x000000000009693d, 0x000000000009693f): DW_OP_breg7 RSP+16
            [0x000000000009693f, 0x0000000000096963): DW_OP_breg6 RBP+16
0x00000250:
            [0x0000000000096964, 0x0000000000096965): DW_OP_breg7 RSP+8
            [0x0000000000096965, 0x0000000000096967): DW_OP_breg7 RSP+16
            [0x0000000000096967, 0x0000000000096979): DW_OP_breg6 RBP+16
0xYYYYY...

    ACTUAL:


0x0000023c:
            [0x000000000009693c, 0x000000000009693d): DW_OP_breg7 RSP+8
            [0x000000000009693d, 0x000000000009693f): DW_OP_breg7 RSP+16
            [0x000000000009693f, 0x0000000000096963): DW_OP_breg6 RBP+16
            [0x0000000000096964, 0x0000000000096965): DW_OP_breg7 RSP+8
            [0x0000000000096965, 0x0000000000096967): DW_OP_breg7 RSP+16
            [0x0000000000096967, 0x0000000000096979): DW_OP_breg6 RBP+16

            */
            debug_loclists.buf.write32(cast(uint)loc_regdesc.length);  // offset_entry_count (header)

            // Offset of the begining of the offsets list
            uint off = cast(uint)debug_loclists.buf.length;

            // Write fake offsets
            foreach (RegLocDesc rld; loc_regdesc)
                 append_addr(debug_loclists.buf, 0);

            foreach (RegLocDesc rld; loc_regdesc)
            {
                /* The contents of the i th offset is the offset from the
                 * beginning of the offset array to the location of the i th
                 * location list.
                 */
                rewriteAddr(debug_loclists.buf, off, debug_loclists.buf.length);

                debug_loclists.buf.writeByte(DW_LLE_start_end);

                foreach (taddr; rld.addresses)
                    dwarf_appreladdr(debug_loclists.seg, debug_loclists.buf, taddr.seg, taddr.func_offset);

                debug_loclists.buf.writeuLEB128(rld.len);
                debug_loclists.buf.writeByte(rld.op);
                debug_loclists.buf.writesLEB128(rld.val);

                // Move to the next offset's offset
                off += I64 ? 8 : 4;
            }

            debug_loclists.buf.writeByte(DW_LLE_end_of_list);
            rewriteUnitLength(debug_loclists.buf, debug_loclists.buf.length);
        }
        /* *********************************************************************
         *                     7.28 Range List Table
         ******************************************************************** */
        {
            // TODO
            // Terminate by beg address/end address fields containing 0
            //append_addr(debug_rnglists.buf, 0);
            //append_addr(debug_rnglists.buf, 0);

            rewriteUnitLength(debug_rnglists.buf, debug_rnglists.buf.length);

        }

        /* *********************************************************************
         *                     7.27 Address Table
         ******************************************************************** */
        {
            rewriteUnitLength(debug_addr.buf, debug_addr.buf.length);
        }

        /* ================================================= */

        // Free only if starting another file. Waste of time otherwise.
        if (type_table)
        {
            AApair.destroy(type_table);
            type_table = null;
        }
        if (functype_table)
        {
            AApair.destroy(functype_table);
            functype_table = null;
        }
        if (functypebuf)
            functypebuf.reset();
    }

    /*****************************************
     * Start of code gen for function.
     */
    void dwarf_func_start(Symbol *sfunc)
    {
        //printf("dwarf_func_start(%s)\n", sfunc.Sident.ptr);
        if (I16 || I32)
            CFA_state_current = CFA_state_init_32;
        else if (I64)
            CFA_state_current = CFA_state_init_64;
        else
            assert(0);
        CFA_state_current.reg = dwarf_regno(SP);
        assert(CFA_state_current.offset == OFFSET_FAC);
        cfa_buf.reset();
    }

    /*****************************************
     * End of code gen for function.
     */
    void dwarf_func_term(Symbol *sfunc)
    {
        //printf("dwarf_func_term(sfunc = '%s')\n", sfunc.Sident.ptr);

        if (config.ehmethod == EHmethod.EH_DWARF)
        {
            bool ehunwind = doUnwindEhFrame();

            IDXSEC dfseg = dwarf_eh_frame_alloc();

            Outbuffer *buf = SegData[dfseg].SDbuf;
            buf.reserve(1000);

            uint *poffset = ehunwind ? &CIE_offset_unwind : &CIE_offset_no_unwind;
            if (*poffset == ~0)
                *poffset = writeEhFrameHeader(dfseg, buf, getRtlsymPersonality(), ehunwind);

            writeEhFrameFDE(dfseg, sfunc, ehunwind, *poffset);
        }
        if (!config.fulltypes)
            return;

        version (MARS)
        {
            if (sfunc.Sflags & SFLnodebug)
                return;
            const(char)* filename = sfunc.Sfunc.Fstartline.Sfilename;
            if (!filename)
                return;
        }

        uint funcabbrevcode;

        if (ehmethod(sfunc) == EHmethod.EH_DM)
        {
            static if (MACHOBJ)
                int flags = S_ATTR_DEBUG;
            else static if (ELFOBJ)
                int flags = SHT_PROGBITS;
            else
                int flags = 0;

            IDXSEC dfseg = dwarf_getsegment(debug_frame_name, 1, flags);
            writeDebugFrameFDE(dfseg, sfunc);
        }

        IDXSEC seg = sfunc.Sseg;
        seg_data *sd = SegData[seg];

        version (MARS)
            int filenum = dwarf_line_addfile(filename);
        else
            int filenum = 1;

        uint ret_type = dwarf_typidx(sfunc.Stype.Tnext);
        if (tybasic(sfunc.Stype.Tnext.Tty) == TYvoid)
            ret_type = 0;

        // See if there are any parameters
        int haveparameters = 0;
        uint formalcode = 0;
        uint autocode = 0;

        for (SYMIDX si = 0; si < globsym.length; si++)
        {
            Symbol *sa = globsym[si];

            version (MARS)
                if (sa.Sflags & SFLnodebug) continue;

            __gshared ubyte[12] formal =
            [
                DW_TAG_formal_parameter,
                0,
                DW_AT_name,       DW_FORM_string,
                DW_AT_type,       DW_FORM_ref4,
                DW_AT_artificial, DW_FORM_flag,
                DW_AT_location,   DW_FORM_block1,
                0,                0,
            ];

            switch (sa.Sclass)
            {
                case SCparameter:
                case SCregpar:
                case SCfastpar:
                    dwarf_typidx(sa.Stype);
                    formal[0] = DW_TAG_formal_parameter;
                    if (!formalcode)
                        formalcode = dwarf_abbrev_code(formal.ptr, formal.sizeof);
                    haveparameters = 1;
                    break;

                case SCauto:
                case SCbprel:
                case SCregister:
                case SCpseudo:
                    dwarf_typidx(sa.Stype);
                    formal[0] = DW_TAG_variable;
                    if (!autocode)
                        autocode = dwarf_abbrev_code(formal.ptr, formal.sizeof);
                    haveparameters = 1;
                    break;

                default:
                    break;
            }
        }

        Outbuffer abuf;
        abuf.writeByte(DW_TAG_subprogram);
        abuf.writeByte(haveparameters);          // have children?
        if (haveparameters)
        {
            abuf.writeByte(DW_AT_sibling);  abuf.writeByte(DW_FORM_ref4);
        }
        abuf.writeByte(DW_AT_name);      abuf.writeByte(DW_FORM_string);

        if (config.dwarf >= 4)
            abuf.writeuLEB128(DW_AT_linkage_name);
        else
            abuf.writeuLEB128(DW_AT_MIPS_linkage_name);
        abuf.writeByte(DW_FORM_string);

        abuf.writeByte(DW_AT_decl_file); abuf.writeByte(DW_FORM_data1);
        abuf.writeByte(DW_AT_decl_line); abuf.writeByte(DW_FORM_data2);
        if (ret_type)
        {
            abuf.writeByte(DW_AT_type);  abuf.writeByte(DW_FORM_ref4);
        }
        if (sfunc.Sclass == SCglobal)
        {
            abuf.writeByte(DW_AT_external);       abuf.writeByte(DW_FORM_flag);
        }
        if (sfunc.Sfunc.Fflags3 & Fpure)
        {
            abuf.writeByte(DW_AT_pure);
            if (config.dwarf >= 4)
                abuf.writeByte(DW_FORM_flag_present);
            else
                abuf.writeByte(DW_FORM_flag);
        }

        abuf.writeByte(DW_AT_low_pc);     abuf.writeByte(DW_FORM_addr);
        abuf.writeByte(DW_AT_high_pc);    abuf.writeByte(DW_FORM_addr);
        abuf.writeByte(DW_AT_frame_base); abuf.writeByte(DW_FORM_data4);
        abuf.writeByte(0);                abuf.writeByte(0);

        funcabbrevcode = dwarf_abbrev_code(abuf.buf, abuf.length());

        uint idxsibling = 0;
        uint siblingoffset;

        debug_info.buf.writeuLEB128(funcabbrevcode);  // abbreviation code
        if (haveparameters)
        {
            siblingoffset = cast(uint)debug_info.buf.length();
            debug_info.buf.write32(idxsibling);       // DW_AT_sibling
        }

        const(char)* name = getSymName(sfunc);

        debug_info.buf.writeString(name);             // DW_AT_name
        /*
         * TODO:
         *
         * 6.1.1.1:
         * If a subprogram or inlined subroutine is included, and has a
         * DW_AT_linkage_name attribute, there will be an additional index entry for
         * the linkage name.
         */
        debug_info.buf.writeString(sfunc.Sident.ptr);    // DW_AT_linkage_name
        debug_info.buf.writeByte(filenum);            // DW_AT_decl_file
        debug_info.buf.write16(sfunc.Sfunc.Fstartline.Slinnum);   // DW_AT_decl_line
        if (ret_type)
            debug_info.buf.write32(ret_type);         // DW_AT_type

        if (sfunc.Sclass == SCglobal)
            debug_info.buf.writeByte(1);              // DW_AT_external

        if (config.dwarf < 4 && sfunc.Sfunc.Fflags3 & Fpure)
            debug_info.buf.writeByte(true);           // DW_AT_pure

        // DW_AT_low_pc and DW_AT_high_pc
        dwarf_appreladdr(debug_info.seg, debug_info.buf, seg, funcoffset);
        dwarf_appreladdr(debug_info.seg, debug_info.buf, seg, funcoffset + sfunc.Ssize);

        // DW_AT_frame_base
        static if (ELFOBJ)
            dwarf_apprel32(debug_info.seg, debug_info.buf, debug_loclists.seg, debug_loclists.buf.length());
        else
            // 64-bit DWARF relocations don't work for OSX64 codegen
            debug_info.buf.write32(cast(uint)debug_loclists.buf.length());

        if (haveparameters)
        {
            for (SYMIDX si = 0; si < globsym.length; si++)
            {
                Symbol *sa = globsym[si];

                version (MARS)
                    if (sa.Sflags & SFLnodebug)
                        continue;

                uint vcode;

                switch (sa.Sclass)
                {
                    case SCparameter:
                    case SCregpar:
                    case SCfastpar:
                        vcode = formalcode;
                        goto L1;
                    case SCauto:
                    case SCregister:
                    case SCpseudo:
                    case SCbprel:
                        vcode = autocode;
                    L1:
                    {
                        uint soffset;
                        uint tidx = dwarf_typidx(sa.Stype);

                        debug_info.buf.writeuLEB128(vcode);           // abbreviation code
                        debug_info.buf.writeString(getSymName(sa));   // DW_AT_name
                        debug_info.buf.write32(tidx);                 // DW_AT_type
                        debug_info.buf.writeByte(sa.Sflags & SFLartifical ? 1 : 0); // DW_FORM_tag
                        soffset = cast(uint)debug_info.buf.length();
                        debug_info.buf.writeByte(2);                  // DW_FORM_block1
                        if (sa.Sfl == FLreg || sa.Sclass == SCpseudo)
                        {
                            // BUG: register pairs not supported in Dwarf?
                            debug_info.buf.writeByte(DW_OP_reg0 + sa.Sreglsw);
                        }
                        else if (sa.Sscope && vcode == autocode)
                        {
                            assert(sa.Sscope.Stype.Tnext && sa.Sscope.Stype.Tnext.Tty == TYstruct);

                            /* find member offset in closure */
                            targ_size_t memb_off = 0;
                            struct_t *st = sa.Sscope.Stype.Tnext.Ttag.Sstruct; // Sscope is __closptr
                            foreach (sl; ListRange(st.Sfldlst))
                            {
                                Symbol *sf = list_symbol(sl);
                                if (sf.Sclass == SCmember)
                                {
                                    if(strcmp(sa.Sident.ptr, sf.Sident.ptr) == 0)
                                    {
                                        memb_off = sf.Smemoff;
                                        goto L2;
                                    }
                                }
                            }
                        L2:
                            targ_size_t closptr_off = sa.Sscope.Soffset; // __closptr offset
                            printf("dwarf closure: sym: %s, closptr: %s, ptr_off: %lli, memb_off: %lli\n",
                                sa.Sident.ptr, sa.Sscope.Sident.ptr, closptr_off, memb_off);

                            debug_info.buf.writeByte(DW_OP_fbreg);
                            debug_info.buf.writesLEB128(cast(uint)(Auto.size + BPoff - Para.size + closptr_off)); // closure pointer offset from frame base
                            debug_info.buf.writeByte(DW_OP_deref);
                            debug_info.buf.writeByte(DW_OP_plus_uconst);
                            debug_info.buf.writeuLEB128(cast(uint)memb_off); // closure variable offset
                        }
                        else
                        {
                            debug_info.buf.writeByte(DW_OP_fbreg);
                            if (sa.Sclass == SCregpar ||
                                sa.Sclass == SCparameter)
                                debug_info.buf.writesLEB128(cast(int)sa.Soffset);
                            else if (sa.Sclass == SCfastpar)
                                debug_info.buf.writesLEB128(cast(int)(Fast.size + BPoff - Para.size + sa.Soffset));
                            else if (sa.Sclass == SCbprel)
                                debug_info.buf.writesLEB128(cast(int)(-Para.size + sa.Soffset));
                            else
                                debug_info.buf.writesLEB128(cast(int)(Auto.size + BPoff - Para.size + sa.Soffset));
                        }
                        debug_info.buf.buf[soffset] = cast(ubyte)(debug_info.buf.length() - soffset - 1);
                        break;
                    }
                    default:
                        break;
                }
            }
            debug_info.buf.writeByte(0);              // end of parameter children

            idxsibling = cast(uint)debug_info.buf.length();
            *cast(uint *)(debug_info.buf.buf + siblingoffset) = idxsibling;
        }

        /* ========================= debug_aranges ========================== */
        {
            if (sd.SDaranges_offset)
                // Extend existing entry size
                *cast(ulong *)(debug_aranges.buf.buf + sd.SDaranges_offset + _tysize[TYnptr]) = funcoffset + sfunc.Ssize;
            else
            {   // Add entry
                sd.SDaranges_offset = cast(uint)debug_aranges.buf.length();
                // address of start of .text segment
                dwarf_appreladdr(debug_aranges.seg, debug_aranges.buf, seg, 0);
                // size of .text segment
                append_addr(debug_aranges.buf, funcoffset + sfunc.Ssize);
            }
        }
        /* *********************************************************************
         *                     6.1.1 Lookup by Name
         ******************************************************************** */
        {
            // TODO
            ubyte[5] names_abbrev_subprogram =
            [
                DW_TAG_subprogram,
                DW_IDX_parent,  DW_FORM_data4,
                DW_AT_name,     DW_FORM_string,
                DW_AT_low_pc,   DW_FORM_addr,
                0,              0,
            ];
            uint name_code = dwarf_names_abbrev_code(names_abbrev_subprogram);
            uint offset = cast(uint) nIndexEntries.length;
            printf("code: %d", name_code);
            nIndexEntries.writeuLEB128(name_code);      // abbrev code
            //nIndexEntries.writeString(name);            // DW_AT_name
            //nIndexEntries.write64(cast(ulong) sfunc);   // DW_AT_low_pc
            nIndexEntries.write32(cast(uint) sfunc);                   // DW_IDX_parent
            nIndexEntries.write32(0);                 // end of entries for "a"


            nEntryOffsets.push(offset);
            // Should be the fully qualified name, not the simple DW_AT_name
            nStringOffsets.push(dwarf_str_add(name));

            nCount++;


            // TODO: buckets
            // 6.1.1.4.5 pseudo code:
            //uint hash = dwarf_hash();
            //bucket = hash % buket_count;
            // TODO: hashes

            //add_s
            // write entry offsets

            // The abbreviations table describes the formats of the entries in the entry pool.

            // index entries
        }
        /* ========================= debug_rnglists ========================= */

        /* Each function gets written into its own segment,
         * indicate this by adding to the debug_ranges
         */
        // start of function and end of function
        //dwarf_appreladdr(debug_ranges.seg, debug_ranges.buf, seg, funcoffset);
        //dwarf_appreladdr(debug_ranges.seg, debug_ranges.buf, seg, funcoffset + sfunc.Ssize);
        // TODO

        /* *********************************************************************
         *                     7.29 Location List Table
         *                     2.6.2 Location Lists
         ******************************************************************** */
        {
            assert(Para.size >= 2 * REGSIZE);
            //assert(Para.size < 63); // avoid sLEB128 encoding
            const ushort op_size = 0x0002;
            ubyte op;
            int val;
            uint len;

            void write_regdesc(ubyte op, int val, TargetAddress[2] addresses)
            {
                assert(op >= DW_OP_breg0 && op <= DW_OP_breg31);
                uint len = cast(uint)(op.sizeof + sLEB128size(val));

                RegLocDesc rld =
                {
                    addresses,  // Addresses to relocate
                    len,        // length of the location decription
                    op,         // location decription (DW_OP_breg0 .. 31)
                    val,        // offset from the contents of the specified register
                };

                loc_regdesc.push(rld);
            }

            // set the entry for this function in .debug_loclists segment
            // after call
            write_regdesc
            (
                cast(ubyte)(DW_OP_breg0 + dwarf_regno(SP)),
                cast(int)(Para.size - REGSIZE),
                [
                    TargetAddress(seg, funcoffset + 0),
                    TargetAddress(seg, funcoffset + 1),
                ]
            );

            // after push EBP
            write_regdesc
            (
                cast(ubyte)(DW_OP_breg0 + dwarf_regno(SP)),
                cast(int)Para.size,
                [
                    TargetAddress(seg, funcoffset + 1),
                    TargetAddress(seg, funcoffset + 3),
                ]
            );

            // after mov EBP, ESP
            write_regdesc
            (
                cast(ubyte)(DW_OP_breg0 + dwarf_regno(BP)),
                cast(int)Para.size,
                [
                    TargetAddress(seg, funcoffset + 3),
                    TargetAddress(seg, funcoffset + sfunc.Ssize),
                ]
            );
        }
    }


    /******************************************
     * Write out symbol table for current function.
     */

    void dwarf_outsym(Symbol *s)
    {
        //printf("dwarf_outsym('%s')\n",s.Sident.ptr);
        //symbol_print(s);

        symbol_debug(s);

        version (MARS)
        {
            if (s.Sflags & SFLnodebug)
                return;
        }

        type *t = s.Stype;
        type_debug(t);
        tym_t tym = tybasic(t.Tty);
        if (tyfunc(tym) && s.Sclass != SCtypedef)
            return;

        Outbuffer abuf;
        uint code;
        uint typidx;
        uint soffset;
        switch (s.Sclass)
        {
            case SCglobal:
                typidx = dwarf_typidx(t);

                abuf.writeByte(DW_TAG_variable);
                abuf.writeByte(DW_CHILDREN_no);
                abuf.writeByte(DW_AT_name);         abuf.writeByte(DW_FORM_string);
                abuf.writeByte(DW_AT_type);         abuf.writeByte(DW_FORM_ref4);
                abuf.writeByte(DW_AT_external);     abuf.writeByte(DW_FORM_flag);
                abuf.writeByte(DW_AT_location);     abuf.writeByte(DW_FORM_block1);
                abuf.writeByte(0);                  abuf.writeByte(0);
                code = dwarf_abbrev_code(abuf.buf, abuf.length());

                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.writeString(getSymName(s));// DW_AT_name
                debug_info.buf.write32(typidx);           // DW_AT_type
                debug_info.buf.writeByte(1);              // DW_AT_external

                soffset = cast(uint)debug_info.buf.length();
                debug_info.buf.writeByte(2);                      // DW_FORM_block1

                static if (ELFOBJ)
                {
                    // debug info for TLS variables
                    assert(s.Sxtrnnum);
                    if (s.Sfl == FLtlsdata)
                    {
                        if (I64)
                        {
                            debug_info.buf.writeByte(DW_OP_const8u);
                            Obj.addrel(debug_info.seg, debug_info.buf.length(), R_X86_64_DTPOFF32, s.Sxtrnnum, 0);
                            debug_info.buf.write64(0);
                        }
                        else
                        {
                            debug_info.buf.writeByte(DW_OP_const4u);
                            Obj.addrel(debug_info.seg, debug_info.buf.length(), R_386_TLS_LDO_32, s.Sxtrnnum, 0);
                            debug_info.buf.write32(0);
                        }
                        debug_info.buf.writeByte(DW_OP_GNU_push_tls_address);
                    }
                    else
                    {
                        debug_info.buf.writeByte(DW_OP_addr);
                        dwarf_appreladdr(debug_info.seg, debug_info.buf, s.Sseg, s.Soffset); // address of global
                    }
                }
                else
                {
                    debug_info.buf.writeByte(DW_OP_addr);
                    dwarf_appreladdr(debug_info.seg, debug_info.buf, s.Sseg, s.Soffset); // address of global
                }

                debug_info.buf.buf[soffset] = cast(ubyte)(debug_info.buf.length() - soffset - 1);
                break;

            default:
                break;
        }
    }


    /******************************************
     * Write out any deferred symbols.
     */
    static if (0)
    void cv_outlist()
    {
        // TODO
    }

    /******************************************
     * Write out symbol table for current function.
     */
    void cv_func(Funcsym *s)
    {
        // TODO
    }

    /*****************************************************
     * Add `name` in .debug_str table
     *
     * Params:
     *      name = string to add
     * Returns:
     *      Offset in .debug_str
     */
    uint dwarf_str_add(const(char)* name)
    {
        // TODO: check for duplicate entries, and return the corresponding offset
        uint offset = cast(uint) debug_str.buf.length;

        debug_str.buf.writeString(name);
        debug_str.buf.writeByte(0);

        return offset;
    }


    /*****************************************************
     * Name Table Hash Function
     *
     * Params:
     *      str = symbol name
     *
     * Return:
     *      A hash for the Hash Lookup Table
     */
    uint dwarf_hash(ubyte* str)
    {
        uint hash = 5381;
        int c = (*str)++;

        while (c)
        {
            c = (*str)++;
            hash = hash * 33 + c;
        }

        return hash;
    }

    /// Ditto
    extern(D) uint dwarf_hash(string str)
    {
        return dwarf_hash((cast(ubyte[]) str).ptr);
    }

    /*****************************************************
     * Allocates a `buffer`. If it is already allocated, reset it.
     *
     * Params:
     *      buffer = Buffer which will be allocated
     */
    extern(D) void alloc_buf(ref Outbuffer* buffer)
    {
        if (buffer)
            buffer.reset();
        else
            buffer = cast(Outbuffer*) calloc(1, Outbuffer.sizeof);
        assert(buffer);
    }

    /* =================== Cached Types in debug_info ================= */

    ubyte dwarf_classify_struct(uint sflags)
    {
        if (sflags & STRclass)
            return DW_TAG_class_type;

        if (sflags & STRunion)
            return DW_TAG_union_type;

        // TODO: DW_TAG_interface_type;

        return DW_TAG_structure_type;
    }

    /* ======================= Type Index ============================== */

    uint dwarf_typidx(type *t)
    {
        uint idx = 0;
        uint nextidx;
        uint keyidx;
        uint pvoididx;
        uint code;
        type *tnext;
        type *tbase;
        const(char)* p;

        static immutable ubyte[] abbrevTypeBasic =
        [
            DW_TAG_base_type,       DW_CHILDREN_no,
            DW_AT_name,             DW_FORM_string,
            DW_AT_byte_size,        DW_FORM_data1,
            DW_AT_encoding,         DW_FORM_data1,
            0,                      0,
        ];
        static immutable ubyte[] abbrevWchar =
        [
            DW_TAG_typedef,         DW_CHILDREN_no,
            DW_AT_name,             DW_FORM_string,
            DW_AT_type,             DW_FORM_ref4,
            DW_AT_decl_file,        DW_FORM_data1,
            DW_AT_decl_line,        DW_FORM_data2,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypePointer =
        [
            DW_TAG_pointer_type,    DW_CHILDREN_no,
            DW_AT_type,             DW_FORM_ref4,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypePointerVoid =
        [
            DW_TAG_pointer_type,    DW_CHILDREN_no,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeRef =
        [
            DW_TAG_reference_type,  DW_CHILDREN_no,
            DW_AT_type,             DW_FORM_ref4,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeConst =
        [
            DW_TAG_const_type,      DW_CHILDREN_no,
            DW_AT_type,             DW_FORM_ref4,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeConstVoid =
        [
            DW_TAG_const_type,      DW_CHILDREN_no,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeVolatile =
        [
            DW_TAG_volatile_type,   DW_CHILDREN_no,
            DW_AT_type,             DW_FORM_ref4,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeVolatileVoid =
        [
            DW_TAG_volatile_type,   DW_CHILDREN_no,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeShared =
        [
            DW_TAG_shared_type,     DW_CHILDREN_no,
            DW_AT_type,             DW_FORM_ref4,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeSharedVoid =
        [
            DW_TAG_shared_type,     DW_CHILDREN_no,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeImmutable =
        [
            DW_TAG_immutable_type,  DW_CHILDREN_no,
            DW_AT_type,             DW_FORM_ref4,
            0,                      0,
        ];
        static immutable ubyte[] abbrevTypeImmutableVoid =
        [
            DW_TAG_immutable_type,  DW_CHILDREN_no,
            0,                      0,
        ];

        if (!t)
            return 0;

        auto types = [mTYconst, mTYshared, mTYvolatile];
        if (config.dwarf >= 5)
            types ~= mTYimmutable;

        foreach(mty; types)
        {
            if (t.Tty & mty)
            {
                // We make a copy of the type to strip off the const qualifier and
                // recurse, and then add the const abbrev code. To avoid ending in a
                // loop if the type references the const version of itself somehow,
                // we need to set TFforward here, because setting TFforward during
                // member generation of dwarf_typidx(tnext) has no effect on t itself.
                const ushort old_flags = t.Tflags;
                t.Tflags |= TFforward;

                tnext = type_copy(t);
                tnext.Tcount++;
                tnext.Tty &= ~mty;
                nextidx = dwarf_typidx(tnext);

                t.Tflags = old_flags;

                if (mty == mTYconst)
                {
                    code = nextidx
                        ? dwarf_abbrev_code(abbrevTypeConst)
                        : dwarf_abbrev_code(abbrevTypeConstVoid);
                }
                else if (mty == mTYvolatile)
                {
                    code = nextidx
                        ? dwarf_abbrev_code(abbrevTypeVolatile)
                        : dwarf_abbrev_code(abbrevTypeVolatileVoid);
                }
                else if (mty == mTYshared)
                {
                    code = nextidx
                        ? dwarf_abbrev_code(abbrevTypeShared)
                        : dwarf_abbrev_code(abbrevTypeSharedVoid);
                }
                else if (mty == mTYimmutable)
                {
                    code = nextidx
                        ? dwarf_abbrev_code(abbrevTypeImmutable)
                        : dwarf_abbrev_code(abbrevTypeImmutableVoid);
                }
                else
                    assert(0);

                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);    // abbreviation code
                if (nextidx)
                    debug_info.buf.write32(nextidx);  // DW_AT_type
                goto Lret;
            }
        }

        tym_t ty;
        ty = tybasic(t.Tty);
        // use cached basic type if it's not TYdarray or TYdelegate
        if (!(t.Tnext && (ty == TYdarray || ty == TYdelegate)))
        {
            idx = typidx_tab[ty];
            if (idx)
                return idx;
        }

        ubyte ate;
        ate = tyuns(t.Tty) ? DW_ATE_unsigned : DW_ATE_signed;

        static immutable ubyte[8] abbrevTypeStruct =
        [
            DW_TAG_structure_type,  DW_CHILDREN_yes,
            DW_AT_name,             DW_FORM_string,
            DW_AT_byte_size,        DW_FORM_data1,
            0,                      0,
        ];

        static immutable ubyte[10] abbrevTypeMember =
        [
            DW_TAG_member,          DW_CHILDREN_no,
            DW_AT_name,             DW_FORM_string,
            DW_AT_type,             DW_FORM_ref4,
            DW_AT_data_member_location, DW_FORM_block1,
            0,                      0,
        ];

        // TODO: DW_AT_accessibility
        // TODO: DW_AT_alignment
        // TODO: DW_AT_default_value
        // TODO: DW_AT_deleted ?
        // TODO: DW_AT_macros -> version = x ?
        // TODO: DW_AT_main_subprogram (main)
        // TODO: DW_AT_pure (pure)
        // TODO: DW_AT_object_pointer (this)
        // TODO: DW_AT_mutable ?
        // TODO: DW_AT_visibility: DW_VIS_exported

        switch (tybasic(t.Tty))
        {
            Lnptr:
                nextidx = dwarf_typidx(t.Tnext);
                code = nextidx
                    ? dwarf_abbrev_code(abbrevTypePointer.ptr, (abbrevTypePointer).sizeof)
                    : dwarf_abbrev_code(abbrevTypePointerVoid.ptr, (abbrevTypePointerVoid).sizeof);
                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                if (nextidx)
                    debug_info.buf.write32(nextidx);      // DW_AT_type
                break;

            case TYullong:
            case TYucent:
                if (!t.Tnext)
                {   p = (tybasic(t.Tty) == TYullong) ? "uint long long" : "ucent";
                    goto Lsigned;
                }

                /* It's really TYdarray, and Tnext is the
                 * element type
                 */
                {
                    uint lenidx = I64 ? dwarf_typidx(tstypes[TYulong]) : dwarf_typidx(tstypes[TYuint]);

                    {
                        type *tdata = type_alloc(TYnptr);
                        tdata.Tnext = t.Tnext;
                        t.Tnext.Tcount++;
                        tdata.Tcount++;
                        nextidx = dwarf_typidx(tdata);
                        type_free(tdata);
                    }

                    code = dwarf_abbrev_code(abbrevTypeStruct.ptr, (abbrevTypeStruct).sizeof);
                    idx = cast(uint)debug_info.buf.length();
                    debug_info.buf.writeuLEB128(code);        // abbreviation code
                    debug_info.buf.write("_Array_".ptr, 7);       // DW_AT_name
                    // Handles multi-dimensional array
                    auto lastdim = t.Tnext;
                    while (lastdim.Tty == TYucent && lastdim.Tnext)
                    {
                        debug_info.buf.write("Array_".ptr, 6);
                        lastdim = lastdim.Tnext;
                    }

                    if (tybasic(lastdim.Tty))
                        debug_info.buf.writeString(tystring[tybasic(lastdim.Tty)]);
                    else
                        debug_info.buf.writeByte(0);
                    debug_info.buf.writeByte(tysize(t.Tty)); // DW_AT_byte_size

                    // length
                    code = dwarf_abbrev_code(abbrevTypeMember.ptr, (abbrevTypeMember).sizeof);
                    debug_info.buf.writeuLEB128(code);        // abbreviation code
                    debug_info.buf.writeString("length");     // DW_AT_name
                    debug_info.buf.write32(lenidx);           // DW_AT_type

                    debug_info.buf.writeByte(2);              // DW_AT_data_member_location
                    debug_info.buf.writeByte(DW_OP_plus_uconst);
                    debug_info.buf.writeByte(0);

                    // ptr
                    debug_info.buf.writeuLEB128(code);        // abbreviation code
                    debug_info.buf.writeString("ptr");        // DW_AT_name
                    debug_info.buf.write32(nextidx);          // DW_AT_type

                    debug_info.buf.writeByte(2);              // DW_AT_data_member_location
                    debug_info.buf.writeByte(DW_OP_plus_uconst);
                    debug_info.buf.writeByte(I64 ? 8 : 4);

                    debug_info.buf.writeByte(0);              // no more children
                }
                break;

            case TYllong:
            case TYcent:
                if (!t.Tnext)
                {   p = (tybasic(t.Tty) == TYllong) ? "long long" : "cent";
                    goto Lsigned;
                }
                /* It's really TYdelegate, and Tnext is the
                 * function type
                 */
                {
                    type *tp = type_fake(TYnptr);
                    tp.Tcount++;
                    pvoididx = dwarf_typidx(tp);    // void*

                    tp.Tnext = t.Tnext;           // fptr*
                    tp.Tnext.Tcount++;
                    nextidx = dwarf_typidx(tp);
                    type_free(tp);
                }

                code = dwarf_abbrev_code(abbrevTypeStruct.ptr, (abbrevTypeStruct).sizeof);
                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.writeString("_Delegate");  // DW_AT_name
                debug_info.buf.writeByte(tysize(t.Tty)); // DW_AT_byte_size

                // ctxptr
                code = dwarf_abbrev_code(abbrevTypeMember.ptr, (abbrevTypeMember).sizeof);
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.writeString("ctxptr");     // DW_AT_name
                debug_info.buf.write32(pvoididx);         // DW_AT_type

                debug_info.buf.writeByte(2);              // DW_AT_data_member_location
                debug_info.buf.writeByte(DW_OP_plus_uconst);
                debug_info.buf.writeByte(0);

                // funcptr
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.writeString("funcptr");    // DW_AT_name
                debug_info.buf.write32(nextidx);          // DW_AT_type

                debug_info.buf.writeByte(2);              // DW_AT_data_member_location
                debug_info.buf.writeByte(DW_OP_plus_uconst);
                debug_info.buf.writeByte(I64 ? 8 : 4);

                debug_info.buf.writeByte(0);              // no more children
                break;

            case TYnref:
            case TYref:
                nextidx = dwarf_typidx(t.Tnext);
                assert(nextidx);
                code = dwarf_abbrev_code(abbrevTypeRef.ptr, (abbrevTypeRef).sizeof);
                idx = cast(uint)cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.write32(nextidx);          // DW_AT_type
                break;

            case TYnptr:
                if (!t.Tkey)
                    goto Lnptr;

                /* It's really TYaarray, and Tnext is the
                 * element type, Tkey is the key type
                 */
                {
                    type *tp = type_fake(TYnptr);
                    tp.Tcount++;
                    pvoididx = dwarf_typidx(tp);    // void*
                }

                code = dwarf_abbrev_code(abbrevTypeStruct.ptr, (abbrevTypeStruct).sizeof);
                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.write("_AArray_".ptr, 8);      // DW_AT_name
                if (tybasic(t.Tkey.Tty))
                    p = tystring[tybasic(t.Tkey.Tty)];
                else
                    p = "key";
                debug_info.buf.write(p, cast(uint)strlen(p));

                debug_info.buf.writeByte('_');
                if (tybasic(t.Tnext.Tty))
                    p = tystring[tybasic(t.Tnext.Tty)];
                else
                    p = "value";
                debug_info.buf.writeString(p);

                debug_info.buf.writeByte(tysize(t.Tty)); // DW_AT_byte_size

                // ptr
                code = dwarf_abbrev_code(abbrevTypeMember.ptr, (abbrevTypeMember).sizeof);
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.writeString("ptr");        // DW_AT_name
                debug_info.buf.write32(pvoididx);         // DW_AT_type

                debug_info.buf.writeByte(2);              // DW_AT_data_member_location
                debug_info.buf.writeByte(DW_OP_plus_uconst);
                debug_info.buf.writeByte(0);

                debug_info.buf.writeByte(0);              // no more children
                break;

            case TYvoid:        return 0;
            case TYbool:        p = "_Bool";         ate = DW_ATE_boolean;       goto Lsigned;
            case TYchar:
                p = "char";
                ate = (config.flags & CFGuchar) ? DW_ATE_unsigned_char : DW_ATE_signed_char;
                goto Lsigned;
            case TYschar:       p = "signed char";   ate = DW_ATE_signed_char;   goto Lsigned;
            case TYuchar:       p = "ubyte";         ate = DW_ATE_unsigned_char; goto Lsigned;
            case TYshort:       p = "short";         goto Lsigned;
            case TYushort:      p = "ushort";        goto Lsigned;
            case TYint:         p = "int";           goto Lsigned;
            case TYuint:        p = "uint";          goto Lsigned;
            case TYlong:        p = "long";          goto Lsigned;
            case TYulong:       p = "ulong";         goto Lsigned;
            case TYdchar:       p = "dchar";                goto Lsigned;
            case TYfloat:       p = "float";        ate = DW_ATE_float;     goto Lsigned;
            case TYdouble_alias:
            case TYdouble:      p = "double";       ate = DW_ATE_float;     goto Lsigned;
            case TYldouble:     p = "long double";  ate = DW_ATE_float;     goto Lsigned;
            case TYifloat:      p = "imaginary float";       ate = DW_ATE_imaginary_float;  goto Lsigned;
            case TYidouble:     p = "imaginary double";      ate = DW_ATE_imaginary_float;  goto Lsigned;
            case TYildouble:    p = "imaginary long double"; ate = DW_ATE_imaginary_float;  goto Lsigned;
            case TYcfloat:      p = "complex float";         ate = DW_ATE_complex_float;    goto Lsigned;
            case TYcdouble:     p = "complex double";        ate = DW_ATE_complex_float;    goto Lsigned;
            case TYcldouble:    p = "complex long double";   ate = DW_ATE_complex_float;    goto Lsigned;
            Lsigned:
                code = dwarf_abbrev_code(abbrevTypeBasic.ptr, (abbrevTypeBasic).sizeof);
                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);        // abbreviation code
                debug_info.buf.writeString(p);            // DW_AT_name
                debug_info.buf.writeByte(tysize(t.Tty)); // DW_AT_byte_size
                debug_info.buf.writeByte(ate);            // DW_AT_encoding
                typidx_tab[ty] = idx;
                return idx;

            case TYnsfunc:
            case TYnpfunc:
            case TYjfunc:

            case TYnfunc:
            {
                /* The dwarf typidx for the function type is completely determined by
                 * the return type typidx and the parameter typidx's. Thus, by
                 * caching these, we can cache the function typidx.
                 * Cache them in functypebuf[]
                 */
                Outbuffer tmpbuf;
                nextidx = dwarf_typidx(t.Tnext);                   // function return type
                tmpbuf.write32(nextidx);
                uint params = 0;
                for (param_t *p2 = t.Tparamtypes; p2; p2 = p2.Pnext)
                {
                    params = 1;
                    uint paramidx = dwarf_typidx(p2.Ptype);
                    //printf("1: paramidx = %d\n", paramidx);

                    debug
                        if (!paramidx)
                            type_print(p2.Ptype);

                    assert(paramidx);
                    tmpbuf.write32(paramidx);
                }

                if (!functypebuf)
                {
                    functypebuf = cast(Outbuffer*) calloc(1, Outbuffer.sizeof);
                    assert(functypebuf);
                }
                uint functypebufidx = cast(uint)functypebuf.length();
                functypebuf.write(tmpbuf.buf, cast(uint)tmpbuf.length());
                /* If it's in the cache already, return the existing typidx
                 */
                if (!functype_table)
                    functype_table = AApair.create(&functypebuf.buf);
                uint *pidx = cast(uint *)functype_table.get(functypebufidx, cast(uint)functypebuf.length());
                if (*pidx)
                {
                    // Reuse existing typidx
                    functypebuf.setsize(functypebufidx);
                    return *pidx;
                }

                /* Not in the cache, create a new typidx
                 */
                Outbuffer abuf;             // for abbrev
                abuf.writeByte(DW_TAG_subroutine_type);
                abuf.writeByte(params ? DW_CHILDREN_yes : DW_CHILDREN_no);
                abuf.writeByte(DW_AT_prototyped);
                abuf.writeByte(DW_FORM_flag);
                if (nextidx != 0)           // Don't write DW_AT_type for void
                {
                    abuf.writeByte(DW_AT_type);
                    abuf.writeByte(DW_FORM_ref4);
                }

                abuf.writeByte(0);
                abuf.writeByte(0);
                code = dwarf_abbrev_code(abuf.buf, abuf.length());

                uint paramcode;
                if (params)
                {
                    abuf.reset();
                    abuf.writeByte(DW_TAG_formal_parameter);
                    abuf.writeByte(0);
                    abuf.writeByte(DW_AT_type);     abuf.writeByte(DW_FORM_ref4);
                    abuf.writeByte(0);              abuf.writeByte(0);
                    paramcode = dwarf_abbrev_code(abuf.buf, abuf.length());
                }

                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);
                debug_info.buf.writeByte(1);            // DW_AT_prototyped
                if (nextidx)                            // if return type is not void
                    debug_info.buf.write32(nextidx);    // DW_AT_type

                if (params)
                {
                    uint *pparamidx = cast(uint *)(functypebuf.buf + functypebufidx);
                    //printf("2: functypebufidx = %x, pparamidx = %p, size = %x\n", functypebufidx, pparamidx, functypebuf.length());
                    for (param_t *p2 = t.Tparamtypes; p2; p2 = p2.Pnext)
                    {
                        debug_info.buf.writeuLEB128(paramcode);
                        //uint x = dwarf_typidx(p2.Ptype);
                        uint paramidx = *++pparamidx;
                        //printf("paramidx = %d\n", paramidx);
                        assert(paramidx);
                        debug_info.buf.write32(paramidx);        // DW_AT_type
                    }
                    debug_info.buf.writeByte(0);          // end parameter list
                }

                *pidx = idx;                        // remember it in the functype_table[] cache
                break;
            }

            case TYarray:
            {
                static immutable ubyte[6] abbrevTypeArray =
                [
                    DW_TAG_array_type,      DW_CHILDREN_yes,    // child (the subrange type)
                    DW_AT_type,             DW_FORM_ref4,
                    0,                      0,
                ];
                static immutable ubyte[4] abbrevTypeArrayVoid =
                [
                    DW_TAG_array_type,      DW_CHILDREN_yes,    // child (the subrange type)
                    0,                      0,
                ];
                static immutable ubyte[8] abbrevTypeSubrange =
                [
                    DW_TAG_subrange_type,   DW_CHILDREN_no,
                    DW_AT_type,             DW_FORM_ref4,
                    DW_AT_upper_bound,      DW_FORM_data4,
                    0,                      0,
                ];
                static immutable ubyte[6] abbrevTypeSubrange2 =
                [
                    DW_TAG_subrange_type,   DW_CHILDREN_no,
                    DW_AT_type,             DW_FORM_ref4,
                    0,                      0,
                ];
                uint code2 = (t.Tflags & TFsizeunknown)
                    ? dwarf_abbrev_code(abbrevTypeSubrange2.ptr, (abbrevTypeSubrange2).sizeof)
                    : dwarf_abbrev_code(abbrevTypeSubrange.ptr, (abbrevTypeSubrange).sizeof);
                uint idxbase = dwarf_typidx(tssize);
                nextidx = dwarf_typidx(t.Tnext);
                uint code1 = nextidx ? dwarf_abbrev_code(abbrevTypeArray.ptr, (abbrevTypeArray).sizeof)
                                     : dwarf_abbrev_code(abbrevTypeArrayVoid.ptr, (abbrevTypeArrayVoid).sizeof);
                idx = cast(uint)debug_info.buf.length();

                debug_info.buf.writeuLEB128(code1);       // DW_TAG_array_type
                if (nextidx)
                    debug_info.buf.write32(nextidx);      // DW_AT_type

                debug_info.buf.writeuLEB128(code2);       // DW_TAG_subrange_type
                debug_info.buf.write32(idxbase);          // DW_AT_type
                if (!(t.Tflags & TFsizeunknown))
                    debug_info.buf.write32(t.Tdim ? cast(uint)t.Tdim - 1 : 0);    // DW_AT_upper_bound

                debug_info.buf.writeByte(0);              // no more children
                break;
            }

            // SIMD vector types
            case TYfloat16:
            case TYfloat8:
            case TYfloat4:   tbase = tstypes[TYfloat];  goto Lvector;
            case TYdouble8:
            case TYdouble4:
            case TYdouble2:  tbase = tstypes[TYdouble]; goto Lvector;
            case TYschar64:
            case TYschar32:
            case TYschar16:  tbase = tstypes[TYschar];  goto Lvector;
            case TYuchar64:
            case TYuchar32:
            case TYuchar16:  tbase = tstypes[TYuchar];  goto Lvector;
            case TYshort32:
            case TYshort16:
            case TYshort8:   tbase = tstypes[TYshort];  goto Lvector;
            case TYushort32:
            case TYushort16:
            case TYushort8:  tbase = tstypes[TYushort]; goto Lvector;
            case TYlong16:
            case TYlong8:
            case TYlong4:    tbase = tstypes[TYlong];   goto Lvector;
            case TYulong16:
            case TYulong8:
            case TYulong4:   tbase = tstypes[TYulong];  goto Lvector;
            case TYllong8:
            case TYllong4:
            case TYllong2:   tbase = tstypes[TYllong];  goto Lvector;
            case TYullong8:
            case TYullong4:
            case TYullong2:  tbase = tstypes[TYullong]; goto Lvector;
            Lvector:
            {
                static immutable ubyte[9] abbrevTypeArray2 =
                [
                    DW_TAG_array_type,      DW_CHILDREN_yes,    // child (the subrange type)
                    (DW_AT_GNU_vector & 0x7F) | 0x80, DW_AT_GNU_vector >> 7,
                    DW_FORM_flag,
                    DW_AT_type,             DW_FORM_ref4,
                    0,                      0,
                ];
                static immutable ubyte[6] abbrevSubRange =
                [
                    DW_TAG_subrange_type,   DW_CHILDREN_no,
                    DW_AT_upper_bound,      DW_FORM_data1,  // length of vector
                    0,                      0,
                ];

                uint code2 = dwarf_abbrev_code(abbrevTypeArray2.ptr, (abbrevTypeArray2).sizeof);
                uint idxbase = dwarf_typidx(tbase);

                idx = cast(uint)debug_info.buf.length();

                debug_info.buf.writeuLEB128(code2);       // DW_TAG_array_type
                debug_info.buf.writeByte(1);              // DW_AT_GNU_vector
                debug_info.buf.write32(idxbase);          // DW_AT_type

                // vector length stored as subrange type
                code2 = dwarf_abbrev_code(abbrevSubRange.ptr, (abbrevSubRange).sizeof);
                debug_info.buf.writeuLEB128(code2);       // DW_TAG_subrange_type
                ubyte dim = cast(ubyte)(tysize(t.Tty) / tysize(tbase.Tty));
                debug_info.buf.writeByte(dim - 1);        // DW_AT_upper_bound

                debug_info.buf.writeByte(0);              // no more children
                break;
            }

            case TYwchar_t:
            {
                uint code3 = dwarf_abbrev_code(abbrevWchar.ptr, (abbrevWchar).sizeof);
                uint typebase = dwarf_typidx(tstypes[TYint]);
                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code3);       // abbreviation code
                debug_info.buf.writeString("wchar_t");    // DW_AT_name
                debug_info.buf.write32(typebase);         // DW_AT_type
                debug_info.buf.writeByte(1);              // DW_AT_decl_file
                debug_info.buf.write16(1);                // DW_AT_decl_line
                typidx_tab[ty] = idx;
                break;
            }


            case TYstruct:
            {
                Classsym *s = t.Ttag;
                struct_t *st = s.Sstruct;

                if (s.Stypidx)
                    return s.Stypidx;

                __gshared ubyte[8] abbrevTypeStruct0 =
                [
                    DW_TAG_structure_type,  DW_CHILDREN_no,
                    DW_AT_name,             DW_FORM_string,
                    DW_AT_byte_size,        DW_FORM_data1,
                    0,                      0,
                ];
                __gshared ubyte[8] abbrevTypeStruct1 =
                [
                    DW_TAG_structure_type,  DW_CHILDREN_no,
                    DW_AT_name,             DW_FORM_string,
                    DW_AT_declaration,      DW_FORM_flag,
                    0,                      0,
                ];

                if (t.Tflags & (TFsizeunknown | TFforward))
                {
                    abbrevTypeStruct1[0] = dwarf_classify_struct(st.Sflags);
                    code = dwarf_abbrev_code(abbrevTypeStruct1.ptr, (abbrevTypeStruct1).sizeof);
                    idx = cast(uint)debug_info.buf.length();
                    debug_info.buf.writeuLEB128(code);
                    debug_info.buf.writeString(getSymName(s));    // DW_AT_name
                    debug_info.buf.writeByte(1);                  // DW_AT_declaration
                    break;                  // don't set Stypidx
                }

                Outbuffer fieldidx;

                // Count number of fields
                uint nfields = 0;
                t.Tflags |= TFforward;
                foreach (sl; ListRange(st.Sfldlst))
                {
                    Symbol *sf = list_symbol(sl);
                    switch (sf.Sclass)
                    {
                        case SCmember:
                            fieldidx.write32(dwarf_typidx(sf.Stype));
                            nfields++;
                            break;

                        default:
                            break;
                    }
                }
                t.Tflags &= ~TFforward;
                if (nfields == 0)
                {
                    abbrevTypeStruct0[0] = dwarf_classify_struct(st.Sflags);
                    abbrevTypeStruct0[1] = DW_CHILDREN_no;
                    abbrevTypeStruct0[5] = DW_FORM_data1;   // DW_AT_byte_size
                    code = dwarf_abbrev_code(abbrevTypeStruct0.ptr, (abbrevTypeStruct0).sizeof);
                    idx = cast(uint)debug_info.buf.length();
                    debug_info.buf.writeuLEB128(code);
                    debug_info.buf.writeString(getSymName(s));    // DW_AT_name
                    debug_info.buf.writeByte(0);                  // DW_AT_byte_size
                }
                else
                {
                    Outbuffer abuf;         // for abbrev
                    abuf.writeByte(dwarf_classify_struct(st.Sflags));
                    abuf.writeByte(DW_CHILDREN_yes);
                    abuf.writeByte(DW_AT_name);     abuf.writeByte(DW_FORM_string);
                    abuf.writeByte(DW_AT_byte_size);

                    size_t sz = cast(uint)st.Sstructsize;
                    if (sz <= 0xFF)
                        abuf.writeByte(DW_FORM_data1);      // DW_AT_byte_size
                    else if (sz <= 0xFFFF)
                        abuf.writeByte(DW_FORM_data2);      // DW_AT_byte_size
                    else
                        abuf.writeByte(DW_FORM_data4);      // DW_AT_byte_size
                    abuf.writeByte(0);              abuf.writeByte(0);

                    code = dwarf_abbrev_code(abuf.buf, abuf.length());

                    uint membercode;
                    abuf.reset();
                    abuf.writeByte(DW_TAG_member);
                    abuf.writeByte(DW_CHILDREN_no);
                    abuf.writeByte(DW_AT_name);
                    abuf.writeByte(DW_FORM_string);
                    abuf.writeByte(DW_AT_type);
                    abuf.writeByte(DW_FORM_ref4);
                    abuf.writeByte(DW_AT_data_member_location);
                    abuf.writeByte(DW_FORM_block1);
                    abuf.writeByte(0);
                    abuf.writeByte(0);
                    membercode = dwarf_abbrev_code(abuf.buf, abuf.length());

                    idx = cast(uint)debug_info.buf.length();
                    debug_info.buf.writeuLEB128(code);
                    debug_info.buf.writeString(getSymName(s));      // DW_AT_name
                    if (sz <= 0xFF)
                        debug_info.buf.writeByte(cast(uint)sz);     // DW_AT_byte_size
                    else if (sz <= 0xFFFF)
                        debug_info.buf.write16(cast(uint)sz);     // DW_AT_byte_size
                    else
                        debug_info.buf.write32(cast(uint)sz);       // DW_AT_byte_size

                    s.Stypidx = idx;
                    uint n = 0;
                    foreach (sl; ListRange(st.Sfldlst))
                    {
                        Symbol *sf = list_symbol(sl);
                        size_t soffset;

                        switch (sf.Sclass)
                        {
                            case SCmember:
                                debug_info.buf.writeuLEB128(membercode);
                                debug_info.buf.writeString(getSymName(sf));      // DW_AT_name
                                //debug_info.buf.write32(dwarf_typidx(sf.Stype));
                                uint fi = (cast(uint *)fieldidx.buf)[n];
                                debug_info.buf.write32(fi);
                                n++;
                                soffset = debug_info.buf.length();
                                debug_info.buf.writeByte(2);
                                debug_info.buf.writeByte(DW_OP_plus_uconst);
                                debug_info.buf.writeuLEB128(cast(uint)sf.Smemoff);
                                debug_info.buf.buf[soffset] = cast(ubyte)(debug_info.buf.length() - soffset - 1);
                                break;

                            default:
                                break;
                        }
                    }

                    debug_info.buf.writeByte(0);          // no more children
                }
                s.Stypidx = idx;
                resetSyms.push(s);
                return idx;                 // no need to cache it
            }

            case TYenum:
            {
                static immutable ubyte[8] abbrevTypeEnum =
                [
                    DW_TAG_enumeration_type,DW_CHILDREN_yes,    // child (the subrange type)
                    DW_AT_name,             DW_FORM_string,
                    DW_AT_byte_size,        DW_FORM_data1,
                    0,                      0,
                ];
                static immutable ubyte[8] abbrevTypeEnumMember =
                [
                    DW_TAG_enumerator,      DW_CHILDREN_no,
                    DW_AT_name,             DW_FORM_string,
                    DW_AT_const_value,      DW_FORM_data1,
                    0,                      0,
                ];

                Symbol *s = t.Ttag;
                enum_t *se = s.Senum;
                type *tbase2 = s.Stype.Tnext;
                uint sz = cast(uint)type_size(tbase2);
                symlist_t sl;

                if (s.Stypidx)
                    return s.Stypidx;

                if (se.SEflags & SENforward)
                {
                    static immutable ubyte[8] abbrevTypeEnumForward =
                    [
                        DW_TAG_enumeration_type,    DW_CHILDREN_no,
                        DW_AT_name,                 DW_FORM_string,
                        DW_AT_declaration,          DW_FORM_flag,
                        0,                          0,
                    ];
                    code = dwarf_abbrev_code(abbrevTypeEnumForward.ptr, abbrevTypeEnumForward.sizeof);
                    idx = cast(uint)debug_info.buf.length();
                    debug_info.buf.writeuLEB128(code);
                    debug_info.buf.writeString(getSymName(s));    // DW_AT_name
                    debug_info.buf.writeByte(1);                  // DW_AT_declaration
                    break;                  // don't set Stypidx
                }

                Outbuffer abuf;             // for abbrev
                abuf.write(abbrevTypeEnum.ptr, abbrevTypeEnum.sizeof);
                code = dwarf_abbrev_code(abuf.buf, abuf.length());

                uint membercode;
                abuf.reset();
                abuf.writeByte(DW_TAG_enumerator);
                abuf.writeByte(DW_CHILDREN_no);
                abuf.writeByte(DW_AT_name);
                abuf.writeByte(DW_FORM_string);
                abuf.writeByte(DW_AT_const_value);
                if (tyuns(tbase2.Tty))
                    abuf.writeByte(DW_FORM_udata);
                else
                    abuf.writeByte(DW_FORM_sdata);
                abuf.writeByte(0);
                abuf.writeByte(0);
                membercode = dwarf_abbrev_code(abuf.buf, abuf.length());

                idx = cast(uint)debug_info.buf.length();
                debug_info.buf.writeuLEB128(code);
                debug_info.buf.writeString(getSymName(s));// DW_AT_name
                debug_info.buf.writeByte(sz);             // DW_AT_byte_size

                foreach (sl2; ListRange(s.Senum.SEenumlist))
                {
                    Symbol *sf = cast(Symbol *)list_ptr(sl2);
                    const value = cast(uint)el_tolongt(sf.Svalue);

                    debug_info.buf.writeuLEB128(membercode);
                    debug_info.buf.writeString(getSymName(sf)); // DW_AT_name
                    if (tyuns(tbase2.Tty))
                        debug_info.buf.writeuLEB128(value);
                    else
                        debug_info.buf.writesLEB128(value);
                }

                debug_info.buf.writeByte(0);              // no more children

                s.Stypidx = idx;
                resetSyms.push(s);
                return idx;                 // no need to cache it
            }

            default:
                return 0;
        }
    Lret:
        /* If debug_info.buf.buf[idx .. length()] is already in debug_info.buf,
         * discard this one and use the previous one.
         */
        if (!type_table)
            /* uint[Adata] type_table;
             * where the table values are the type indices
             */
            type_table = AApair.create(&debug_info.buf.buf);

        uint *pidx = type_table.get(idx, cast(uint)debug_info.buf.length());
        if (!*pidx)                 // if no idx assigned yet
        {
            *pidx = idx;            // assign newly computed idx
        }
        else
        {   // Reuse existing code
            debug_info.buf.setsize(idx);  // discard current
            idx = *pidx;
        }
        return idx;
    }

    /**
     *  Returns a pretty identifier name from `sym`.
     *
     *  Params:
     *      sym = the symbol which the name comes from
     *  Returns:
     *      The identifier name
     */
    const(char)* getSymName(Symbol* sym)
    {
        version (MARS)
            return sym.prettyIdent ? sym.prettyIdent : sym.Sident.ptr;
        else
            return sym.Sident.ptr;
    }

    /* ======================= Abbreviation Codes ====================== */

    extern(D) uint dwarf_abbrev_code(const(ubyte)[] data)
    {
        return dwarf_abbrev_code_backend(data, abbrev_table,
            abbrevcoed, debug_abbrev.buf);
    }

    extern(D) uint dwarf_names_abbrev_code(const(ubyte)[] data)
    {
        return dwarf_abbrev_code_backend(data, nAbbrevTable,
            nAbbrevCode, nAbbrevBuffer);
    }

    extern(D) uint dwarf_abbrev_code_backend(const(ubyte)[] data,
        ref AApair* abbrev_table, ref uint abbrevcode, ref Outbuffer* buffer)
    {
        if (!abbrev_table)
            /* uint[Adata] abbrev_table;
             * where the table values are the abbreviation codes.
             */
            abbrev_table = AApair.create(&buffer.buf);



        // Write new entry into buffer

        uint idx = cast(uint) buffer.length();
        abbrevcode++;
        buffer.writeuLEB128(abbrevcode);
        size_t start = buffer.length();
        buffer.write(data);
        size_t end = buffer.length();

        /* If debug_abbrev.buf.buf[idx .. length()] is already in buffer,
         * discard this one and use the previous one.
         */

        uint* pcode = abbrev_table.get(cast(uint)start, cast(uint)end);
        if (!*pcode)                // if no code assigned yet
        {
            *pcode = abbrevcode;    // assign newly computed code
        }
        else
        {   // Reuse existing code
            buffer.setsize(idx);        // discard current
            abbrevcode--;
        }
        return *pcode;
    }

    /*****************************************************
     * Write Dwarf-style exception tables.
     * Params:
     *      sfunc = function to generate tables for
     *      startoffset = size of function prolog
     *      retoffset = offset from start of function to epilog
     */
    void dwarf_except_gentables(Funcsym *sfunc, uint startoffset, uint retoffset)
    {
        if (!doUnwindEhFrame())
            return;

        int seg = dwarf_except_table_alloc(sfunc);
        Outbuffer *buf = SegData[seg].SDbuf;
        buf.reserve(100);

        static if (ELFOBJ)
            sfunc.Sfunc.LSDAoffset = cast(uint)buf.length();

        static if (MACHOBJ)
        {
            char[16 + (except_table_num).sizeof * 3 + 1] name = void;
            sprintf(name.ptr, "GCC_except_table%d", ++except_table_num);
            type *t = tspvoid;
            t.Tcount++;
            type_setmangle(&t, mTYman_sys);         // no leading '_' for mangled name
            Symbol *s = symbol_name(name.ptr, SCstatic, t);
            Obj.pubdef(seg, s, cast(uint)buf.length());
            symbol_keep(s);

            sfunc.Sfunc.LSDAsym = s;
        }
        genDwarfEh(sfunc, seg, buf, (usednteh & EHcleanup) != 0, startoffset, retoffset);
    }

}
else
{
    extern (C++):

    void dwarf_CFA_set_loc(uint location) { }
    void dwarf_CFA_set_reg_offset(int reg, int offset) { }
    void dwarf_CFA_offset(int reg, int offset) { }
    void dwarf_except_gentables(Funcsym *sfunc, uint startoffset, uint retoffset) { }
}
