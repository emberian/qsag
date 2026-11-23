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

    // 2-level zero-detect prefix decrementer for x[31:0] - 1 (`< 2.5 ns` SS, eliminates 32-bit ripple)
    function automatic logic [31:0] dec32_prefix(input logic [31:0] x);
        logic [7:0]  z4;
        logic [31:0] flip;
        for (int n = 0; n < 8; n++) z4[n] = ~(|x[4*n +: 4]);
        for (int n = 0; n < 8; n++) begin
            logic low_z;
            low_z = 1'b1;
            for (int j = 0; j < n; j++) low_z &= z4[j];
            flip[4*n + 0] = low_z;
            flip[4*n + 1] = low_z & ~x[4*n + 0];
            flip[4*n + 2] = low_z & ~(|x[4*n +: 2]);
            flip[4*n + 3] = low_z & ~(|x[4*n +: 3]);
        end
        return x ^ flip;
    endfunction

    function automatic word_t gl_reduce64(input word_t x);
        logic [31:0] xm1;
        xm1 = dec32_prefix(x[31:0]);
        return ((&x[63:32]) && (|x[31:0])) ? {32'd0, xm1} : x;
    endfunction

    function automatic word_t gl_mul_2p32m1(input logic [31:0] x);
        logic [31:0] y;
        y = dec32_prefix(x);
        return (|x) ? {y, ~y} : 64'd0;
    endfunction

    function automatic word_t gl_add64(input word_t a, b);
        logic [64:0] t;
        t = {1'b0, gl_reduce64(a)} + {1'b0, gl_reduce64(b)};
        return t >= {1'b0, PRIME} ? t[63:0] - PRIME : t[63:0];
    endfunction

    function automatic word_t gl_sub64(input word_t a, b);
        logic [64:0] t;
        t = {1'b0, gl_reduce64(a)} - {1'b0, gl_reduce64(b)};
        return t[64] ? t[63:0] + PRIME : t[63:0];
    endfunction

    // Fast 2-level carry-lookahead 64b + 8b unsigned adder (`< 3.5 ns` SS)
    function automatic word_t add64_u8(input word_t x, input logic [7:0] inc);
        logic [8:0]  lo9;
        logic [13:0] n4_all1;
        logic [2:0]  grp_all1;
        logic [3:0]  grp_cin;
        logic [63:0] res;
        lo9      = {1'b0, x[7:0]} + {1'b0, inc};
        res[7:0] = lo9[7:0];
        for (int n = 0; n < 14; n++) n4_all1[n] = &x[8 + 4*n +: 4];
        grp_all1[0] = &n4_all1[3:0];
        grp_all1[1] = &n4_all1[7:4];
        grp_all1[2] = &n4_all1[11:8];

        grp_cin[0] = lo9[8];
        grp_cin[1] = lo9[8] & grp_all1[0];
        grp_cin[2] = lo9[8] & grp_all1[0] & grp_all1[1];
        grp_cin[3] = lo9[8] & grp_all1[0] & grp_all1[1] & grp_all1[2];

        for (int n = 0; n < 14; n++) begin
            int g, r;
            logic cin_n;
            g = n / 4;
            r = n % 4;
            cin_n = (r == 0) ? grp_cin[g]
                  : (r == 1) ? (grp_cin[g] & n4_all1[4*g + 0])
                  : (r == 2) ? (grp_cin[g] & n4_all1[4*g + 0] & n4_all1[4*g + 1])
                  :            (grp_cin[g] & n4_all1[4*g + 0] & n4_all1[4*g + 1] & n4_all1[4*g + 2]);
            res[8 + 4*n + 0] = x[8 + 4*n + 0] ^ cin_n;
            res[8 + 4*n + 1] = x[8 + 4*n + 1] ^ (cin_n & x[8 + 4*n + 0]);
            res[8 + 4*n + 2] = x[8 + 4*n + 2] ^ (cin_n & (&x[8 + 4*n +: 2]));
            res[8 + 4*n + 3] = x[8 + 4*n + 3] ^ (cin_n & (&x[8 + 4*n +: 3]));
        end
        return res;
    endfunction
endpackage
