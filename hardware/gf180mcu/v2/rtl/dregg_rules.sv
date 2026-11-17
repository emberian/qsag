// Dregg-180 v2 decoder rules (ARCHITECTURE.md 5.3; v2/model/machine.py R1 to R12).
//
// Combinational. Given the micro-instruction at the program counter and the sequencer's flags, this
// module decides whether the instruction may execute (`fault` = control fault: every latch is cleared
// and nothing more is answered) and how the taint and session flags move. It uses only hardwired
// constants (dregg_defs.svh) and sequencer state, never a property of the ROM image. The sequencer
// (dregg_seq) executes; it takes every permission from here.
//
// Each fault term is named after the model's message. `why` is the index of the first raised term
// (test bench diagnostics only).
`default_nettype none

module dregg_rules (
    // the instruction
    input  wire  [4:0]  op,
    input  wire  [6:0]  fa,
    input  wire  [6:0]  fb,
    input  wire  [3:0]  fn,
    input  wire         ib,
    input  wire         ret,          // seq bit 0
    input  wire  [6:0]  ra,           // row A after indexing
    input  wire  [6:0]  rb,           // row B after indexing
    input  wire  [10:0] pc,
    input  wire  [10:0] target,
    input  wire         taken,        // the instruction transfers control to `target`
    // sequencer state
    input  wire         keyed,
    input  wire         dirty,
    input  wire         t_lanes,
    input  wire         t_h,
    input  wire         t_z,
    input  wire         t_cy,
    input  wire         hdr_done,
    input  wire         failed,
    input  wire         auth_ok,
    input  wire  [1:0]  sp,           // return-stack depth
    input  wire  [10:0] ret_addr,     // top of the return stack
    input  wire  [11:0] rom_len,      // words in the ROM image
    input  wire         din_none,     // no payload word left
    input  wire         din_lt2,      // fewer than two payload words left
    input  wire         push_room,    // the declared response length allows another word
    input  wire         h_gt_cap,     // H[23:0] > the immediate (HDR)
    input  wire         const_ok,     // the constant index exists
    input  wire         un_ok,        // the unary function code exists
    input  wire         fr_open,
    input  wire         fr_writing,
    input  wire         fr_left0,
    input  wire         runaway,      // more instructions executed in this command than MAX_STEPS
    input  wire         off_end,      // the previous instruction ran off the last address of the 11-bit space
    // dispatch (R12)
    input  wire         disp_magic_ok,
    input  wire         disp_hit,
    input  wire  [1:0]  disp_class,
    input  wire         dev_ok,
    input  wire         key_valid,
    output logic [15:0] disp_code,    // 0: dispatch; else the refusal code
    // verdict
    output wire         fault,
    output logic [5:0]  why,
    // what the instruction reads
    output logic        rd_need,      // it reads a register-file row through the word unit / PUSH / FRAM path
    output logic [6:0]  rd_row,
    // flag movement (applied by the sequencer when the instruction completes)
    output logic        clear_h,
    output logic        t_h_n,
    output logic        t_z_n,
    output logic        t_cy_n,
    output logic        set_t_lanes,
    output logic        clr_lanes_flags,   // dirty and t_lanes cleared (a wipe of all lanes)
    output logic        set_keyed,         // keyed, dirty, t_lanes set (KMOV)
    output logic        clr_dirty          // a permutation has run
);
`include "dregg_defs.svh"

    // ------------------------------------------------------------ row classes
    localparam logic [2:0] RC_NONE = 3'd0, RC_LANE = 3'd1, RC_KWORK = 3'd2, RC_SCRATCH = 3'd3, RC_KEY = 3'd4,
                           RC_PIN = 3'd5, RC_STATE = 3'd6, RC_OUT = 3'd7;
    function automatic logic [2:0] row_class(input logic [6:0] r);
        if      (r < 7'(KWORK0))   row_class = RC_LANE;
        else if (r < 7'(SCRATCH0)) row_class = RC_KWORK;
        else if (r < 7'(KEY0))     row_class = RC_SCRATCH;
        else if (r < 7'(PIN0))     row_class = RC_KEY;
        else if (r < 7'(STATE0))   row_class = RC_PIN;
        else if (r < 7'(OUT0))     row_class = RC_STATE;
        else if (r < 7'(NROWS))    row_class = RC_OUT;
        else                       row_class = RC_NONE;      // configuration S has no challenge rows
    endfunction
    function automatic logic unreadable(input logic [2:0] c);
        unreadable = (c == RC_NONE) || (c == RC_KEY) || (c == RC_OUT) || (c == RC_KWORK);
    endfunction

    wire [2:0] ca = row_class(ra);
    wire [2:0] cb = row_class(rb);
    wire [2:0] c_fb = row_class(fb);        // FRAM WWORD names its row directly
    wire       a_lane  = (ca == RC_LANE);
    wire       a_rate  = a_lane && (ra < 7'(RATE_LANES));
    wire       store   = fn[0];
    wire       imm     = fn[1];

    wire is_alu  = (op == OP_LD) || (op == OP_XOR) || (op == OP_AND) || (op == OP_OR) || (op == OP_ADD) || (op == OP_SUB);
    wire is_cmp  = (op == OP_CMP);
    wire is_cmpt = is_cmp && store && !imm;
    wire is_ctl  = (op == OP_CTL);
    wire is_fram = (op == OP_FRAM);
    wire is_push = (op == OP_PUSH);
    wire push_h  = is_push && imm;
    wire push_rel = is_push && !imm && store;
    wire push_row = is_push && !imm && !store;
    wire fr_wword = is_fram && (fa == FRF_WWORD);
    wire in_key   = (pc >= KEY_LO) && (pc <= KEY_HI);
    wire in_rec   = (pc >= REC_LO) && (pc <= REC_HI);

    // ------------------------------------------------------------ what is read
    always_comb begin
        rd_need = 1'b0;
        rd_row  = ra;
        if ((is_alu || is_cmp) && !imm) rd_need = 1'b1;
        if (is_push && !imm)            rd_need = 1'b1;
        if (fr_wword) begin
            rd_need = 1'b1;
            rd_row  = fb;
        end
    end
    wire [2:0] cr = fr_wword ? c_fb : ca;                 // class of the row read
    wire       r_lane = (cr == RC_LANE);
    // R3: while dirty a lane is read only by an XOR that stores back to the same lane
    wire       same_ok = (op == OP_XOR) && store && !imm && (ra == rb);
    wire       tx = r_lane && t_lanes;                  // the value read is key-derived

    // ------------------------------------------------------------ faults
    localparam int NF = 49;
    logic [NF-1:0] f;
    wire alu_store  = is_alu && !imm && store;
    wire dirty_read = rd_need && r_lane && dirty;       // a lane read while a key is in the lanes
    wire alu_clear  = is_alu && !imm && dirty && a_lane;
    wire t_h_alu    = (op == OP_LD) ? (imm ? 1'b0 : tx) : (t_h | (imm ? 1'b0 : tx));
    wire st_alu     = alu_store;
    wire st_un      = (op == OP_UN) && store;
    wire st_clean   = ((op == OP_DIN) || (op == OP_LDF) || (op == OP_LDC) || (is_fram && fa == FRF_RWORD)) && store;
    wire st_any     = st_alu | st_un | st_clean;
    wire st_taint   = (st_alu && (t_h_alu || alu_clear)) || (st_un && t_h);
    wire cond_z     = (fa == COND_Z)  || (fa == COND_NZ);
    wire cond_cy    = (fa == COND_CY) || (fa == COND_NC);
    wire cond_h     = (fa == COND_HZ) || (fa == COND_HNZ);
    wire goes       = taken;
    wire rets       = ret && !taken && (op != OP_FAIL) && (op != OP_END) && !(op == OP_DISP && disp_code != 16'd0);

    always_comb begin
        f = '0;
        // fetch
        f[0]  = ({1'b0, pc} >= rom_len) || off_end;                          // fell off the end of the ROM
        f[1]  = (op == OP_ILL) || (op == OP_FLD) || (op == OP_FADD);         // illegal instruction (no field unit in S)
        // _rd
        f[2]  = rd_need && unreadable(cr);                                   // read of a key, out, work or absent row
        f[3]  = dirty_read && !(same_ok && !fr_wword);                       // read of a lane while a key is in the lanes
        f[4]  = rd_need && r_lane && keyed && (rd_row >= 7'(RATE_LANES));    // read of a capacity lane in a keyed command
        // _wr
        f[5]  = st_any && unreadable(cb);                                    // write of a key, out, work or absent row
        f[6]  = st_taint && (cb != RC_LANE);                                 // store of key-derived data outside the lanes
        // CMPT
        f[7]  = is_cmpt && t_h;                                              // CMPT with key-derived data in H
        f[8]  = is_cmpt && !a_rate;                                          // CMPT operand is not a rate lane
        // UN / LDF / LDC with an undefined index
        f[9]  = (op == OP_UN) && !un_ok;
        f[10] = (op == OP_LDF) && (fa >= 7'(N_LDF));
        f[11] = (op == OP_LDC) && !const_ok;
        // DIN
        f[12] = (op == OP_DIN) && din_none;                                  // DIN past the end of the payload
        // PUSH
        f[13] = push_h && t_h;                                               // PUSH of key-derived data
        f[14] = push_rel && !a_rate;                                         // REL operand is not a rate lane
        f[15] = push_row && tx;                                              // PUSH of key-derived data
        f[16] = is_push && (!hdr_done || failed);                            // PUSH before the response header
        f[17] = is_push && !push_room;                                       // PUSH beyond the declared length
        // HDR / FAIL / END
        f[18] = (op == OP_HDR) && (hdr_done || failed);                      // second response header
        f[19] = (op == OP_HDR) && t_h;                                       // response length from key-derived data
        f[20] = (op == OP_HDR) && fn[0] && t_z;                              // response flag from a key-derived compare
        f[21] = (op == OP_HDR) && h_gt_cap;                                  // response longer than the routine's cap
        f[22] = (op == OP_FAIL) && (hdr_done || failed);                     // FAIL after the response header
        f[23] = (op == OP_END) && !(hdr_done || failed);                     // command ended without a header
        // KMOV / KEYWR
        f[24] = (op == OP_KMOV) && (ca != RC_KEY);                           // KMOV source is not a key row
        f[25] = (op == OP_KMOV) && !(rb < 7'(RATE_LANES));                   // KMOV destination is not a rate lane
        f[26] = (op == OP_KEYWR) && !in_key;                                 // KEYWR outside the key range
        f[27] = (op == OP_KEYWR) && !auth_ok;                                // KEYWR without authorisation
        f[28] = (op == OP_KEYWR) && (cb != RC_KEY);                          // KEYWR destination is not a key row
        // CTL
        f[29] = is_ctl && (fa >= 7'(N_CTL));
        f[30] = is_ctl && ((fa == CTL_SETKV) || (fa == CTL_AUTH) || (fa == CTL_NONCE)) && !in_key;   // outside the key range
        f[31] = is_ctl && (fa == CTL_SETKV) && !auth_ok;                     // SETKV without authorisation
        f[32] = is_ctl && (fa == CTL_SETKV) && t_h;                          // key attribute from key-derived data
        f[33] = is_ctl && (fa == CTL_VOK) && t_z;                            // verdict pin from a key-derived compare
        f[34] = is_ctl && (fa == CTL_AUTH) && din_lt2;                       // AUTH past the end of the payload
        // FRAM
        f[35] = is_fram && (!in_rec || fa >= 7'(N_FRAM));                    // FRAM instruction outside the record range
        f[36] = is_fram && ((fa == FRF_RSTART) || (fa == FRF_WSTART)) && t_h;   // FRAM slot from key-derived data
        f[37] = is_fram && ((fa == FRF_RSTART) || (fa == FRF_WSTART)) && fr_open;   // transaction already open
        f[38] = is_fram && (fa == FRF_RWORD) && !(fr_open && !fr_writing && !fr_left0);   // word outside a matching transaction
        f[39] = fr_wword && !(fr_open && fr_writing && !fr_left0);
        f[40] = fr_wword && (ib || !((fb == FRAM_SRC0) || (fb == FRAM_SRC1) || (fb == FRAM_SRC2)));   // FRAM WWORD of another row
        f[41] = is_fram && (fa == FRF_DONE) && !fr_open;                     // FRAM DONE without a transaction
        // SETX / SETC
        f[42] = (op == OP_SETX) && fn[0] && t_h;                             // index from key-derived data
        f[43] = (op == OP_SETC) && fa[1] && t_h;                             // loop count from key-derived data
        // branches
        f[44] = (op == OP_BR) && ((fa >= 7'(N_COND)) || (cond_z && t_z) || (cond_cy && t_cy) || (cond_h && t_h));
        f[45] = (op == OP_CALL) && (sp == 2'd2);                             // return stack overflow
        f[46] = (goes && ((target == IDLE_ADDR) || ({1'b0, target} >= rom_len)))   // transfer to idle or outside the ROM
              | (rets && ((sp == 2'd0) || (ret_addr == IDLE_ADDR) || ({1'b0, ret_addr} >= rom_len)));   // return with an empty stack
        f[47] = (op == OP_DISP) && (pc != IDLE_ADDR);                        // DISP away from address 0
        f[48] = runaway;                                                     // runaway microprogram
    end
    assign fault = |f;
    always_comb begin
        why = '0;
        for (int i = NF - 1; i >= 0; i--) if (f[i]) why = 6'(i);
    end

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, fn[3:2]};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------ dispatch gate (R12)
    always_comb begin
        disp_code = 16'd0;
        if (!disp_magic_ok)                                 disp_code = E_MAGIC;
        else if (!disp_hit)                                 disp_code = E_OPCODE;
        else if (disp_class == D_PROV && !dev_ok)           disp_code = E_NOKEY;
        else if (disp_class == D_PROV && key_valid)         disp_code = E_KEYSET;
        else if (disp_class == D_KEYED && !key_valid)       disp_code = E_NOKEY;
    end

    // ------------------------------------------------------------ flag movement (R2, R3, R5, R6)
    always_comb begin
        clear_h         = 1'b0;
        t_h_n           = t_h;
        t_z_n           = t_z;
        t_cy_n          = t_cy;
        set_t_lanes     = 1'b0;
        clr_lanes_flags = 1'b0;
        set_keyed       = 1'b0;
        clr_dirty       = 1'b0;
        if (is_cmp && !is_cmpt) t_z_n = t_z | t_h | (imm ? 1'b0 : tx);
        if (is_alu) begin
            t_h_n = t_h_alu;
            if ((op == OP_ADD) || (op == OP_SUB)) t_cy_n = t_h_alu;
            if (alu_clear) clear_h = 1'b1;
        end
        if ((op == OP_DIN) || (op == OP_LDF) || (op == OP_LDC) || (is_fram && fa == FRF_RWORD)) t_h_n = 1'b0;
        if (st_taint) set_t_lanes = 1'b1;
        if (op == OP_KMOV) begin
            set_keyed = 1'b1;
            clear_h   = 1'b1;
        end
        if (op == OP_KEYWR) clear_h = 1'b1;
        if (is_ctl && fa == CTL_CLRZ) t_z_n = 1'b0;
        if ((op == OP_WIPE) && fa[W_LANES_LO_B] && fa[W_LANES_HI_B]) clr_lanes_flags = 1'b1;
        if (op == OP_KEC) clr_dirty = 1'b1;
        if (clear_h) t_h_n = 1'b0;
    end
endmodule
`default_nettype wire
