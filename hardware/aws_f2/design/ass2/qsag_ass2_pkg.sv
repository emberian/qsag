package qsag_ass2_pkg;
    typedef logic [63:0] word_t;
    typedef enum logic [3:0] {
        SYS, LUT4, ALU, ALUI, IMM20, CMP, BYTE_OP, LOAD, STORE, BR,
        JAL, JALR, SPG, GL64, GF128, PERM
    } opcode_t;
    typedef enum logic [7:0] {
        ARCH_ID=0, WORD_BITS=1, EVEC=2, POWER=3, INSTRET=4, CYCLES=5,
        FEATURES=6, EPC=8, ECAUSE=9, DBG_OUT=10, DBG_IN=11,
        EXC_EN=63, DIT=64, ZEROIZE=65
    } csr_t;
    typedef enum logic [2:0] {
        ILLEGAL=1, ENVCALL=2, MIS_PC=3, MIS_MEM=4, MEM_FAULT=5
    } cause_t;
    typedef enum logic [2:0] {
        LC_RESET         = 3'd0,
        LC_BLANK         = 3'd1,
        LC_PROVISIONED   = 3'd2,
        LC_LEASE_PENDING = 3'd3,
        LC_ORPHAN        = 3'd4,
        LC_READY         = 3'd5,
        LC_LOCKED_OUT    = 3'd6
    } lc_state_t;

    localparam word_t PRIME = 64'hffffffff00000001;
    localparam word_t ID    = 64'h4153533200000001;

    function automatic word_t gl_reduce64(input word_t x);
        return (&x[63:32] && |x[31:0]) ? {32'd0,x[31:0]-1'b1} : x;
    endfunction

    // Canonicalize both operands so at most one modulus correction is needed.
    function automatic word_t gl_add64(input word_t a,b);
        logic [64:0] t;
        t = {1'b0,gl_reduce64(a)} + {1'b0,gl_reduce64(b)};
        return t >= {1'b0,PRIME} ? t[63:0]-PRIME : t[63:0];
    endfunction
    function automatic word_t gl_sub64(input word_t a,b);
        logic [64:0] t;
        t = {1'b0,gl_reduce64(a)} - {1'b0,gl_reduce64(b)};
        return t[64] ? t[63:0]+PRIME : t[63:0];
    endfunction
    function automatic word_t gl_shl_small64(input word_t a, input logic [4:0] n);
        logic [86:0] t;
        logic [22:0] hi;
        t = 87'(gl_reduce64(a)) << n;
        hi = t[86:64];
        return gl_add64(t[63:0],{9'd0,hi,32'd0}-64'(hi));
    endfunction
endpackage
