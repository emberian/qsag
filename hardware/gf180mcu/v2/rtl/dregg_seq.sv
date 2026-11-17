// Dregg-180 v2 sequencer (ARCHITECTURE.md 5.5; v2/model/machine.py).
//
// One micro-instruction per clock: the ROM is read combinationally at the program counter, the
// instruction is decoded, checked by dregg_rules and executed in the same clock. Exceptions:
//   stall     an instruction that reads the row written by the previous one waits one clock (the row
//             is transparent in that clock, ARCHITECTURE.md 5.2)
//   KMOV      two clocks: key row into the hold register; hold register into the lane
//   KEC       one clock to start the Keccak unit, then the unit's 721 or 373
//   FRAM      the FRAM port's clocks (dregg_fram)
//   CTL NONCE / CTL AUTH   the stage 3 and 4 interfaces (entropy, owner authorisation)
//   END, FAIL, refused DISP   the hardware end action: wait for the response to leave and the unread
//             payload to drain, wipe every working row, clear the session, return to address 0
//   link waits  DIN with no word offered, PUSH with both out rows full; `link_wait` marks them
//
// The hold register H is the register file's write-hold register. Three micro-operations borrow it
// as a pure write buffer (PUSH of a row, REL, the Keccak unit's write-back) while the model keeps the
// accumulator value across them. H_SHADOW selects how that is built:
//   1  a 64-bit shadow register keeps the accumulator across the borrow (the model's behaviour)
//   0  the accumulator reads as zero after the borrow (proposal: 64 flops fewer; needs a model change)
// KEC_WAIT_AFTER_STORE = 1 makes KEC wait one clock when the previous instruction wrote a row, as the
// model charges it; the Keccak unit's first read is a clock later, so 0 is also safe.
//
// IR_STAGE = 1 puts an instruction register between the ROM and the decoder (physical-design finding:
// PC -> ROM -> row address -> read -> word unit -> hold register does not fit one 40 ns clock). The ROM
// is then read one clock ahead at pc + 1. An instruction whose successor is not pc + 1 (taken branch,
// call, return, dispatch) is followed by one empty clock in which the ROM is read at the new address.
// A row written by that instruction has closed by the time the next one runs, so the two-phase stall
// (and the KEC wait) that would have followed is absorbed by the empty clock. Nothing else changes; the
// model does not count that clock (IR_STAGE = 0 is the model's machine).
//
// Address 0 is the idle point: the instruction there executes only when the framer offers a header.
`default_nettype none

module dregg_seq #(
    parameter bit H_SHADOW = 1'b1,
    parameter bit KEC_WAIT_AFTER_STORE = 1'b1,
    parameter bit IR_STAGE = 1'b0
) (
    input  wire         clk,
    input  wire         srst_n,
    // microcode ROM
    output wire  [10:0] rom_addr,
    input  wire  [27:0] rom_word,
    output wire  [6:0]  const_idx,
    input  wire  [63:0] const_data,
    input  wire         const_ok,
    output wire  [7:0]  disp_op,
    input  wire         disp_hit,
    input  wire  [10:0] disp_addr,
    input  wire  [1:0]  disp_class,
    input  wire  [11:0] rom_len,
    input  wire  [11:0] rom_used,
    // register file
    output logic        h_en,
    output logic [63:0] h_d,
    input  wire  [63:0] h_q,
    output logic        rf_we,
    output logic [6:0]  rf_waddr,
    output logic [1:0]  rf_out_we,
    output logic [3:0]  rf_wipe,
    output logic [6:0]  rf_raddr,
    input  wire  [63:0] rf_rdata,
    // word unit
    output wire  [63:0] wu_h,
    output logic [63:0] wu_x,
    output logic [4:0]  wu_op,
    output wire  [6:0]  wu_un,
    input  wire  [63:0] wu_y,
    input  wire         wu_cy,
    input  wire         wu_ne,
    input  wire         wu_un_ok,
    // Keccak unit
    output wire         kec_start,
    output wire         kec_turbo,
    input  wire         kec_last,
    input  wire  [5:0]  kec_rd_addr,
    input  wire         kec_wr_en,
    input  wire  [5:0]  kec_wr_addr,
    input  wire  [63:0] kec_wr_data,
    // framer
    output wire         fr_idle,
    input  wire         fr_hdr_valid,
    output wire         fr_take_hdr,
    output wire         fr_take_din,
    output wire         fr_drain,
    input  wire         fr_din_valid,
    input  wire  [63:0] fr_din,
    input  wire         fr_drained,
    input  wire         fr_rem_lt2,
    input  wire         fr_in_magic_ok,
    input  wire  [7:0]  fr_in_op,
    input  wire  [63:0] fr_hdr,
    input  wire  [21:0] fr_remaining,
    // egress
    output wire         eg_hdr,
    output wire         eg_fail,
    output logic [15:0] eg_n,
    output wire         eg_ok,
    output wire         eg_push,
    input  wire         eg_can_push,
    input  wire         eg_wr_slot,
    input  wire         eg_push_room,
    output wire         eg_flush,
    input  wire         eg_flushed,
    input  wire         eg_idle,
    // FRAM port
    output wire         fm_start,
    output wire         fm_write,
    output wire         fm_slot,
    output wire         fm_rword,
    output wire         fm_wword,
    output wire         fm_done,
    output wire         fm_abort,
    input  wire  [63:0] fm_rx,
    input  wire         fm_fin,
    input  wire         fm_open,
    input  wire         fm_writing,
    input  wire  [1:0]  fm_left,
    // stage 3 interface: device secret at boot (PUF reconstruction)
    input  wire         puf_present,
    output wire         puf_req,
    output wire  [1:0]  puf_idx,
    input  wire         puf_valid,
    input  wire  [63:0] puf_data,
    // stage 3 interface: conditioned nonce
    input  wire         ent_present,
    output wire         ent_req,
    input  wire         ent_valid,
    input  wire  [127:0] ent_data,
    // stage 4 interface: owner authorisation of (authorisation words, statement digest, nonce)
    output wire         own_start,
    output wire         own_valid,
    output wire  [2:0]  own_idx,      // 0, 1 authorisation words; 2..5 lanes 0..3; 6, 7 nonce
    output logic [63:0] own_data,
    input  wire         own_done,
    input  wire         own_ok,
    // control fault and pins
    output wire         fault_now,    // a decoder rule refuses the instruction of this clock
    output wire  [5:0]  fault_why,
    output wire         verify_ok,
    output wire         fault_mac,
    output wire         fault_anchor,
    output wire         ready,        // booted
    output wire         busy,         // a command is executing
    // observation (test bench, assertions)
    output wire         cmd_active,   // high from the dispatch clock to the last clock of the end action
    output wire         link_wait,    // this clock is spent waiting for the link
    output wire         stall,        // this clock is a two-phase stall
    output wire  [10:0] pc_o,
    output wire  [27:0] ir_o,         // the instruction at pc_o
    output wire         rd_used,      // rf_rdata is consumed in this clock
    output wire         key_wr,       // a key row is opened in this clock ...
    output wire         key_wr_boot   // ... by the boot interface
);
`include "dregg_defs.svh"

    localparam logic [3:0] S_BOOTW = 4'd0, S_PUFA = 4'd1, S_PUFB = 4'd2, S_RUN = 4'd3, S_KMOV2 = 4'd4, S_KEC = 4'd5,
                           S_FRAM = 4'd6, S_ENT = 4'd7, S_AUTH = 4'd8, S_ENDF = 4'd9, S_ENDI = 4'd10;
    localparam logic [1:0] HA_NONE = 2'd0, HA_ZERO = 2'd1, HA_SHADOW = 2'd2;

    // ------------------------------------------------------------ state
    (* keep *) logic [3:0]  st;         // kept by name: timing reports select paths by these registers
    logic [3:0]  boot_cnt;
    logic [1:0]  pidx;
    logic        dev_ok;
    // session (cleared by the end action)
    (* keep *) logic [10:0] pc;
    logic [10:0] stk0, stk1;
    logic [1:0]  sp;
    logic [11:0] c0, c1;
    logic [6:0]  x;
    logic        z, cyf;
    logic        keyed, dirty, t_lanes, t_h, t_z, t_cy;
    logic        hdr_done, failed, auth_ok;
    logic        active_q;
    logic [1:0]  h_alt;
    wire  [63:0] shadow;
    logic        tr_valid;
    logic [6:0]  tr_row;
    logic [2:0]  tr_wipe;
    logic        lw_valid;
    logic [3:0]  astep;
    logic [24:0] steps;         // instructions completed in this command
    logic        off_end;       // the program counter wrapped past address 2047 (a 2048-word ROM that falls off its end)
    // chip state that outlives a command
    logic        key_valid;
    logic [3:0]  key_attr;
    logic        f_mac, f_anchor, v_ok;
    logic        nonce_valid;
    wire  [127:0] nonce;

    // ------------------------------------------------------------ decode
    (* keep *) logic [27:0] ir_q;          // instruction register (IR_STAGE)
    logic        ir_v;          // ir_q is the ROM word at pc
    wire         ir_ok = !IR_STAGE || ir_v;
    wire [10:0]  pc_p1 = pc + 11'd1;
    assign rom_addr = (IR_STAGE && ir_v) ? pc_p1 : pc;
    wire [27:0] iw   = IR_STAGE ? ir_q : rom_word;     // the instruction at pc
    assign ir_o = iw;
    wire [4:0]  op   = iw[27:23];
    wire [6:0]  fa   = iw[22:16];
    wire [6:0]  fb   = iw[15:9];
    wire [3:0]  fn   = iw[8:5];
    wire        ia   = iw[4];
    wire        ib   = iw[3];
    wire        xi   = iw[2];
    wire        ret  = iw[0];
    wire [6:0]  ra   = ia ? (fa + x) : fa;
    wire [6:0]  rb   = ib ? (fb + x) : fb;
    wire [15:0] imm16  = {fn[3:2], fa, fb};
    wire [10:0] target = {fb, fn};
    wire        store  = fn[0];
    wire        immf   = fn[1];

    wire is_alu  = (op == OP_LD) || (op == OP_XOR) || (op == OP_AND) || (op == OP_OR) || (op == OP_ADD) || (op == OP_SUB);
    wire is_cmp  = (op == OP_CMP);
    wire is_ctl  = (op == OP_CTL);
    wire is_fram = (op == OP_FRAM);
    wire is_push = (op == OP_PUSH);
    wire fr_start_op = is_fram && ((fa == FRF_RSTART) || (fa == FRF_WSTART));
    wire fr_rword_op = is_fram && (fa == FRF_RWORD);
    wire fr_wword_op = is_fram && (fa == FRF_WWORD);
    wire fr_done_op  = is_fram && (fa == FRF_DONE);
    wire ctl_nonce   = is_ctl && (fa == CTL_NONCE);
    wire ctl_auth    = is_ctl && (fa == CTL_AUTH);

    // the accumulator as instructions see it
    wire [63:0] h_vis = (h_alt == HA_ZERO) ? 64'd0 : (h_alt == HA_SHADOW) ? shadow : h_q;
    assign wu_h  = h_vis;
    assign wu_un = fa;
    assign const_idx = fa;

    // conditions and transfers
    wire [11:0] csel   = fa[0] ? c1 : c0;
    wire [11:0] cdec   = csel - 12'd1;
    logic cond;
    always_comb begin
        unique case (fa)
            COND_AL:     cond = 1'b1;
            COND_Z:      cond = z;
            COND_NZ:     cond = !z;
            COND_CY:     cond = cyf;
            COND_NC:     cond = !cyf;
            COND_HZ:     cond = (h_vis == 64'd0);
            COND_HNZ:    cond = (h_vis != 64'd0);
            COND_MORE:   cond = !fr_drained;
            COND_NOMORE: cond = fr_drained;
            COND_KV:     cond = key_valid;
            COND_NKV:    cond = !key_valid;
            COND_C1Z:    cond = (c1 == 12'd0);
            COND_C1NZ:   cond = (c1 != 12'd0);
            default:     cond = 1'b0;
        endcase
    end
    wire taken = ((op == OP_BR) && cond) || ((op == OP_BXNE) && (x != fa)) || ((op == OP_DBNZ) && (cdec != 12'd0))
               || (op == OP_CALL);

    // ------------------------------------------------------------ rules
    wire        r_fault, r_rd_need, r_clear_h, r_t_h_n, r_t_z_n, r_t_cy_n, r_set_t_lanes, r_clr_lanes, r_set_keyed, r_clr_dirty;
    wire [5:0]  r_why;
    wire [6:0]  r_rd_row;
    wire [15:0] r_disp_code;
    dregg_rules u_rules (
        .op(op), .fa(fa), .fb(fb), .fn(fn), .ib(ib), .ret(ret), .ra(ra), .rb(rb), .pc(pc), .target(target),
        .taken(taken),
        .keyed(keyed), .dirty(dirty), .t_lanes(t_lanes), .t_h(t_h), .t_z(t_z), .t_cy(t_cy),
        .hdr_done(hdr_done), .failed(failed), .auth_ok(auth_ok), .sp(sp), .ret_addr(stk0), .rom_len(rom_len),
        .din_none(fr_drained), .din_lt2(fr_rem_lt2), .push_room(eg_push_room),
        .h_gt_cap(h_vis[23:0] > {8'd0, imm16}), .const_ok(const_ok), .un_ok(wu_un_ok),
        .fr_open(fm_open), .fr_writing(fm_writing), .fr_left0(fm_left == 2'd0),
        .runaway(steps > 25'(MAX_STEPS)), .off_end(off_end),
        .disp_magic_ok(fr_in_magic_ok), .disp_hit(disp_hit), .disp_class(disp_class), .dev_ok(dev_ok),
        .key_valid(key_valid), .disp_code(r_disp_code),
        .fault(r_fault), .why(r_why), .rd_need(r_rd_need), .rd_row(r_rd_row),
        .clear_h(r_clear_h), .t_h_n(r_t_h_n), .t_z_n(r_t_z_n), .t_cy_n(r_t_cy_n), .set_t_lanes(r_set_t_lanes),
        .clr_lanes_flags(r_clr_lanes), .set_keyed(r_set_keyed), .clr_dirty(r_clr_dirty)
    );
    assign disp_op = fr_in_op;

    // ------------------------------------------------------------ the clock's verdict
    wire at_idle  = (st == S_RUN) && (pc == IDLE_ADDR) && !off_end && ir_ok;
    assign fr_idle = at_idle;
    wire present  = (st == S_RUN) && ir_ok && (!at_idle || fr_hdr_valid);     // an instruction is up for execution
    assign fault_now = present && r_fault;
    assign fault_why = r_why;

    // the row this instruction reads (KMOV reads its key row in its first clock)
    wire        phys_rd  = r_rd_need || (op == OP_KMOV);
    wire [6:0]  phys_row = r_rd_need ? r_rd_row : ra;
    wire        row_lo   = (phys_row <= 7'(WIPE_LO_LAST));
    wire        row_hi   = !row_lo && (phys_row <= 7'(WIPE_HI_LAST));
    wire        row_sc   = (phys_row >= 7'(SCRATCH0)) && (phys_row < 7'(SCRATCH0 + N_SCRATCH));
    wire        open_hit = (tr_valid && (tr_row == phys_row))
                         | (tr_wipe[0] && row_lo) | (tr_wipe[1] && row_hi) | (tr_wipe[2] && row_sc);
    wire        kec_hold = KEC_WAIT_AFTER_STORE && (op == OP_KEC) && lw_valid;
    wire        do_stall = present && !r_fault && ((phys_rd && open_hit) || kec_hold);
    assign stall = do_stall;

    wire        wipe_out  = (op == OP_WIPE) && fa[W_OUT_B];
    wire        wait_din  = (op == OP_DIN) && !fr_din_valid;
    wire        wait_push = is_push && !eg_can_push;
    wire        wait_wipe = wipe_out && !eg_idle;
    wire        run_wait  = present && !r_fault && !do_stall && (wait_din || wait_push || wait_wipe);
    // the instruction starts (and, if it is a one-clock instruction, completes) in this clock
    wire        go = present && !r_fault && !do_stall && !run_wait;

    wire        disp_refuse = (op == OP_DISP) && (r_disp_code != 16'd0);
    wire        to_end      = (op == OP_END) || (op == OP_FAIL) || disp_refuse;
    wire        ent_wait_op = ctl_nonce && ent_present;
    wire        multi       = (op == OP_KMOV) || (op == OP_KEC) || (is_fram && !fm_fin) || ent_wait_op || ctl_auth;

    wire        auth_fin = (st == S_AUTH) && (astep == 4'd8) && own_done;
    wire        fin = (go && !multi && !to_end)
                    | (st == S_KMOV2)
                    | ((st == S_KEC) && kec_last)
                    | ((st == S_FRAM) && fm_fin)
                    | ((st == S_ENT) && ent_valid)
                    | auth_fin;

    wire end_ready = eg_flushed && fr_drained;
    wire auth_din  = (st == S_AUTH) && (astep < 4'd2);
    assign link_wait = run_wait | ((st == S_ENDF) && !end_ready) | (auth_din && !fr_din_valid);
    assign cmd_active = active_q | (at_idle && fr_hdr_valid);
    assign busy  = cmd_active;
    assign ready = (st != S_BOOTW) && (st != S_PUFA) && (st != S_PUFB);
    assign pc_o  = pc;

    // ------------------------------------------------------------ unit strobes
    assign kec_start = go && (op == OP_KEC);
    assign kec_turbo = (fa != 7'd0);
    assign fm_start  = go && fr_start_op;
    assign fm_write  = (fa == FRF_WSTART);
    assign fm_slot   = h_vis[0];
    assign fm_rword  = go && fr_rword_op;
    assign fm_wword  = go && fr_wword_op;
    assign fm_done   = go && fr_done_op;
    assign fm_abort  = (st == S_ENDF) && end_ready;
    assign ent_req   = go && ent_wait_op;
    assign own_start = go && ctl_auth;
    assign own_valid = (st == S_AUTH) && (astep < 4'd8) && !(auth_din && !fr_din_valid);
    assign own_idx   = astep[2:0];
    always_comb begin
        if (astep < 4'd2)       own_data = fr_din;
        else if (astep < 4'd6)  own_data = rf_rdata;
        else if (astep == 4'd6) own_data = nonce[63:0];
        else                    own_data = nonce[127:64];
    end
    assign puf_req = (st == S_PUFA);
    assign puf_idx = pidx;

    assign fr_take_hdr = go && at_idle;
    assign fr_take_din = (go && (op == OP_DIN)) | (auth_din && fr_din_valid);
    assign fr_drain    = (st == S_ENDF);

    assign eg_hdr   = go && (op == OP_HDR);
    assign eg_fail  = go && ((op == OP_FAIL) || disp_refuse);
    assign eg_ok    = fn[0] ? !z : 1'b1;
    assign eg_push  = go && is_push;
    assign eg_flush = (st == S_ENDF);
    always_comb begin
        if (op == OP_HDR)       eg_n = h_vis[15:0];
        else if (op == OP_FAIL) eg_n = imm16;
        else                    eg_n = r_disp_code;
    end

    // ------------------------------------------------------------ word unit operand
    logic [63:0] ldf;
    wire  [63:0] status = {20'd0, rom_used, 23'd0, 1'b0, key_attr, dev_ok, f_anchor, f_mac, key_valid};
    always_comb begin
        unique case (fa)
            LDF_HDRW:   ldf = fr_hdr;
            LDF_FLAGS:  ldf = {56'd0, fr_hdr[23:16]};
            LDF_LEN:    ldf = {40'd0, fr_hdr[47:24]};
            LDF_NWORDS: ldf = {42'd0, fr_remaining};
            LDF_ARG:    ldf = {48'd0, fr_hdr[63:48]};
            LDF_ARGLO:  ldf = {56'd0, fr_hdr[55:48]};
            LDF_ARGHI:  ldf = {56'd0, fr_hdr[63:56]};
            LDF_X:      ldf = {57'd0, x};
            LDF_STATUS: ldf = status;
            LDF_NONCE0: ldf = nonce_valid ? nonce[63:0] : 64'd0;
            LDF_NONCE1: ldf = nonce_valid ? nonce[127:64] : 64'd0;
            LDF_KATTR:  ldf = {60'd0, key_attr};
            default:    ldf = 64'd0;
        endcase
    end
    always_comb begin
        wu_op = op;
        wu_x  = immf ? {48'd0, imm16} : rf_rdata;
        unique case (op)
            OP_DIN:  begin wu_op = OP_LD; wu_x = fr_din; end
            OP_LDF:  begin wu_op = OP_LD; wu_x = ldf; end
            OP_LDC:  begin wu_op = OP_LD; wu_x = const_data; end
            OP_FRAM: begin wu_op = OP_LD; wu_x = fm_rx; end
            default: ;
        endcase
    end
    wire loads_h = is_alu || (op == OP_UN) || (op == OP_DIN) || (op == OP_LDF) || (op == OP_LDC) || fr_rword_op;
    wire stores  = store && ((is_alu && !immf) || (op == OP_UN) || (op == OP_DIN) || (op == OP_LDF) || (op == OP_LDC)
                             || fr_rword_op);
    wire borrow  = is_push && !immf;                    // PUSH of a row, REL: the row goes through the hold register

    // ------------------------------------------------------------ register-file controls
    wire [1:0] ha_borrow = H_SHADOW ? HA_SHADOW : HA_ZERO;
    logic [1:0] h_alt_n;
    logic       shadow_ld;
    logic       tr_valid_n;
    logic [6:0] tr_row_n;
    always_comb begin
        h_en       = 1'b1;
        h_d        = h_vis;
        h_alt_n    = HA_NONE;
        shadow_ld  = 1'b0;
        rf_we      = 1'b0;
        rf_waddr   = rb;
        rf_out_we  = 2'b00;
        rf_wipe    = 4'd0;
        rf_raddr   = phys_row;
        unique case (st)
            S_PUFA: begin
                h_en = puf_valid;
                h_d  = puf_data;
            end
            S_PUFB: begin
                h_en     = 1'b0;
                rf_we    = 1'b1;
                rf_waddr = 7'(KEY0) + {5'd0, pidx};
                h_alt_n  = HA_ZERO;
            end
            S_RUN: if (go) begin
                if (fin) begin
                    if (loads_h) h_d = wu_y;
                    if (stores) rf_we = 1'b1;
                    if (r_clear_h) h_alt_n = HA_ZERO;
                end
                if (op == OP_KMOV) h_d = rf_rdata;
                if (op == OP_KEYWR) rf_we = 1'b1;
                if (is_push) begin
                    rf_out_we[eg_wr_slot] = 1'b1;
                    if (borrow) begin
                        h_d       = rf_rdata;
                        shadow_ld = 1'b1;
                        h_alt_n   = ha_borrow;
                    end
                end
                if (op == OP_KEC) begin
                    shadow_ld = 1'b1;
                    h_alt_n   = ha_borrow;
                end
                if (op == OP_WIPE) rf_wipe = fa[3:0];
            end
            S_KMOV2: begin
                rf_we   = 1'b1;
                h_alt_n = HA_ZERO;
            end
            S_KEC: begin
                h_en     = kec_wr_en;
                h_d      = kec_wr_data;
                h_alt_n  = h_alt;
                rf_we    = kec_wr_en;
                rf_waddr = {1'b0, kec_wr_addr};
                rf_raddr = {1'b0, kec_rd_addr};
            end
            S_FRAM: if (fm_fin && fr_rword_op) begin
                h_d   = wu_y;
                rf_we = store;
            end
            S_AUTH: rf_raddr = 7'(LANE0) + {4'd0, astep[2:0]} - 7'd2;
            S_ENDF: if (end_ready) rf_wipe = 4'hF;
            S_ENDI: h_d = 64'd0;
            default: ;
        endcase
        // a row opened in this clock is transparent in the next
        tr_valid_n = rf_we;
        tr_row_n   = rf_waddr;
    end
    assign rd_used = (go && phys_rd) | (st == S_KEC) | ((st == S_AUTH) && (astep >= 4'd2) && (astep < 4'd6));
    assign key_wr      = rf_we && (rf_waddr >= 7'(KEY0)) && (rf_waddr < 7'(KEY0 + N_KEYS));
    assign key_wr_boot = (st == S_PUFB);

    // the shadow of the accumulator and the nonce: enable registers (clock-gated in silicon)
    generate
        if (H_SHADOW) begin : g_shadow
            qsag_ereg #(.W(64)) u_shadow (.clk(clk), .rst_n(srst_n), .en(shadow_ld || (st == S_ENDI)),
                                          .d((st == S_ENDI) ? 64'd0 : h_vis), .q(shadow));
        end else begin : g_noshadow
            assign shadow = 64'd0;
        end
    endgenerate
`ifdef DREGG_TB_BACKDOOR
    wire         nonce_ld = ((st == S_ENT) && ent_valid) || `DREGG_TB_BACKDOOR.bd_fl_we;
    wire [127:0] nonce_d  = `DREGG_TB_BACKDOOR.bd_fl_we ? `DREGG_TB_BACKDOOR.bd_nonce : ent_data;
`else
    wire         nonce_ld = (st == S_ENT) && ent_valid;
    wire [127:0] nonce_d  = ent_data;
`endif
    qsag_ereg #(.W(128)) u_nonce (.clk(clk), .rst_n(srst_n), .en(nonce_ld), .d(nonce_d), .q(nonce));

    // ------------------------------------------------------------ next state
    wire [6:0]  x_set = (op == OP_SETX) ? (fn[0] ? h_vis[6:0] : fa) : x;
    wire        rets  = ret && !taken;
    wire [10:0] pc_inc = pc + 11'd1;
    wire [10:0] pc_n   = rets ? stk0 : (op == OP_DISP) ? disp_addr : taken ? target : pc_inc;

    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) begin
            st       <= S_BOOTW;
            boot_cnt <= '0;
            pidx     <= '0;
            dev_ok   <= 1'b0;
            pc       <= IDLE_ADDR;
            stk0     <= '0;
            stk1     <= '0;
            sp       <= '0;
            c0       <= '0;
            c1       <= '0;
            x        <= '0;
            z        <= 1'b0;
            cyf      <= 1'b0;
            keyed    <= 1'b0;
            dirty    <= 1'b0;
            t_lanes  <= 1'b0;
            t_h      <= 1'b0;
            t_z      <= 1'b0;
            t_cy     <= 1'b0;
            hdr_done <= 1'b0;
            failed   <= 1'b0;
            auth_ok  <= 1'b0;
            active_q <= 1'b0;
            h_alt    <= HA_NONE;
            tr_valid <= 1'b0;
            tr_row   <= '0;
            tr_wipe  <= '0;
            lw_valid <= 1'b0;
            astep    <= '0;
            steps    <= '0;
            off_end  <= 1'b0;
            ir_q     <= '0;
            ir_v     <= 1'b0;
            key_valid   <= 1'b0;
            key_attr    <= '0;
            f_mac       <= 1'b0;
            f_anchor    <= 1'b0;
            v_ok        <= 1'b0;
            nonce_valid <= 1'b0;
        end else begin
            h_alt    <= h_alt_n;
            tr_valid <= tr_valid_n;
            tr_row   <= tr_row_n;
            tr_wipe  <= rf_wipe[2:0];
            if (do_stall) lw_valid <= 1'b0;
            if (IR_STAGE) begin
                if (!ir_v) begin                    // the empty clock: read the ROM at the new address
                    ir_q <= rom_word;
                    ir_v <= 1'b1;
                    if (st == S_RUN) lw_valid <= 1'b0;      // the row written before it has closed
                end else if (fin) begin             // the ROM was read at pc + 1 in this clock
                    ir_q <= rom_word;
                    ir_v <= (pc_n == pc_inc);
                end
                if (st == S_ENDI) ir_v <= 1'b0;
            end

            unique case (st)
                S_BOOTW: begin
                    boot_cnt <= boot_cnt + 4'd1;
                    if (boot_cnt == 4'd15) st <= puf_present ? S_PUFA : S_RUN;
                end
                S_PUFA: if (puf_valid) st <= S_PUFB;
                S_PUFB: begin
                    pidx <= pidx + 2'd1;
                    if (pidx == 2'(N_KDEV - 1)) begin
                        dev_ok <= 1'b1;
                        st     <= S_RUN;
                    end else st <= S_PUFA;
                end
                S_RUN: if (go) begin
                    if (at_idle) begin
                        active_q <= 1'b1;
                        v_ok     <= 1'b0;
                    end
                    if (to_end) begin
                        if (op != OP_END) failed <= 1'b1;
                        st <= S_ENDF;
                    end else if (op == OP_KMOV) st <= S_KMOV2;
                    else if (op == OP_KEC)      st <= S_KEC;
                    else if (is_fram && !fm_fin) st <= S_FRAM;
                    else if (ent_wait_op)       st <= S_ENT;
                    else if (ctl_auth) begin
                        st    <= S_AUTH;
                        astep <= '0;
                    end
                end
                S_KMOV2: st <= S_RUN;
                S_KEC:   if (kec_last) st <= S_RUN;
                S_FRAM:  if (fm_fin) st <= S_RUN;
                S_ENT:   if (ent_valid) begin
                    nonce_valid <= 1'b1;
                    st          <= S_RUN;
                end
                S_AUTH: begin
                    if (astep < 4'd8) begin
                        if (!(auth_din && !fr_din_valid)) astep <= astep + 4'd1;
                    end else if (own_done) begin
                        nonce_valid <= 1'b0;
                        if (own_ok && nonce_valid && !t_lanes) auth_ok <= 1'b1;
                        else                                   z <= 1'b1;
                        st <= S_RUN;
                    end
                end
                S_ENDF: if (end_ready) st <= S_ENDI;
                S_ENDI: begin
                    st       <= S_RUN;
                    pc       <= IDLE_ADDR;
                    stk0     <= '0;
                    stk1     <= '0;
                    sp       <= '0;
                    c0       <= '0;
                    c1       <= '0;
                    x        <= '0;
                    z        <= 1'b0;
                    cyf      <= 1'b0;
                    keyed    <= 1'b0;
                    dirty    <= 1'b0;
                    t_lanes  <= 1'b0;
                    t_h      <= 1'b0;
                    t_z      <= 1'b0;
                    t_cy     <= 1'b0;
                    hdr_done <= 1'b0;
                    failed   <= 1'b0;
                    auth_ok  <= 1'b0;
                    active_q <= 1'b0;
                    lw_valid <= 1'b0;
                    steps    <= '0;
                    off_end  <= 1'b0;
                end
                default: st <= S_BOOTW;
            endcase

            // architectural effects of the instruction that completes in this clock
            if (fin) begin
                steps <= steps + 25'd1;
                // program counter and return stack
                if (op == OP_DISP)   pc <= disp_addr;
                else if (taken)      pc <= target;
                else begin
                    pc <= pc_inc;
                    if (pc == 11'h7FF && !rets) off_end <= 1'b1;
                end
                if (op == OP_CALL) begin
                    stk1 <= stk0;
                    stk0 <= pc_inc;
                    sp   <= sp + 2'd1;
                end else if (rets) begin
                    pc   <= stk0;
                    stk0 <= stk1;
                    sp   <= sp - 2'd1;
                end
                // index register and loop counters
                x <= x_set + {6'd0, xi};
                if (op == OP_SETC) begin
                    if (fa[0]) c1 <= fa[1] ? h_vis[11:0] : {1'b0, target};
                    else       c0 <= fa[1] ? h_vis[11:0] : {1'b0, target};
                end
                if (op == OP_DBNZ) begin
                    if (fa[0]) c1 <= cdec;
                    else       c0 <= cdec;
                end
                // flags
                if (is_cmp && wu_ne) z <= 1'b1;
                if ((op == OP_ADD) || (op == OP_SUB)) cyf <= wu_cy;
                if (is_ctl) begin
                    if (fa == CTL_CLRZ) z <= 1'b0;
                    if (fa == CTL_SETKV) begin
                        key_valid <= 1'b1;
                        key_attr  <= h_vis[3:0];
                    end
                    if (fa == CTL_SETFM) f_mac <= 1'b1;
                    if (fa == CTL_SETFA) f_anchor <= 1'b1;
                    if (fa == CTL_VOK)   v_ok <= !z;
                    if (ctl_nonce && !ent_present) begin
                        nonce_valid <= 1'b0;
                        z           <= 1'b1;
                    end
                end
                if (op == OP_HDR) hdr_done <= 1'b1;
                // rule-driven flags
                t_h  <= r_t_h_n;
                t_z  <= r_t_z_n;
                t_cy <= r_t_cy_n;
                if (r_set_t_lanes) t_lanes <= 1'b1;
                if (r_set_keyed) begin
                    keyed   <= 1'b1;
                    dirty   <= 1'b1;
                    t_lanes <= 1'b1;
                end
                if (r_clr_lanes) begin
                    dirty   <= 1'b0;
                    t_lanes <= 1'b0;
                end
                if (r_clr_dirty) dirty <= 1'b0;
                // the model's last_w: the instruction wrote a row
                lw_valid <= stores || (op == OP_KMOV) || (op == OP_KEYWR);
            end
`ifdef DREGG_TB_BACKDOOR
            // test bench only: place the chip state that fixtures set directly in the model
            if (`DREGG_TB_BACKDOOR.bd_fl_we) begin
                key_valid   <= `DREGG_TB_BACKDOOR.bd_flags[0];
                f_mac       <= `DREGG_TB_BACKDOOR.bd_flags[1];
                f_anchor    <= `DREGG_TB_BACKDOOR.bd_flags[2];
                v_ok        <= `DREGG_TB_BACKDOOR.bd_flags[3];
                key_attr    <= `DREGG_TB_BACKDOOR.bd_flags[7:4];
                nonce_valid <= `DREGG_TB_BACKDOOR.bd_flags[8];
            end
`endif
        end

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, iw[1], pc_p1};     // seq bit 1 is not used by the model either
    /* verilator lint_on UNUSEDSIGNAL */
`ifdef FORMAL
    // Properties of the sequencer and its decoder rules, for every ROM content, every register-file
    // content and every behaviour of the units (all inputs free; lec/fv_seq.sv assumes only that the
    // Keccak unit addresses lanes, which the simulation checks on the real unit).
    logic f_pv;
    initial f_pv = 1'b0;
    wire f_key_a   = (rf_raddr >= 7'(KEY0)) && (rf_raddr < 7'(KEY0 + N_KEYS));
    wire f_pushsrc = (rf_raddr < 7'(KWORK0)) || ((rf_raddr >= 7'(SCRATCH0)) && (rf_raddr < 7'(KEY0)))
                   || ((rf_raddr >= 7'(PIN0)) && (rf_raddr < 7'(OUT0)));
    wire f_effect  = rf_we | (|rf_out_we) | (|rf_wipe) | fm_start | fm_rword | fm_wword | fm_done | eg_hdr | eg_fail
                   | eg_push | fr_take_hdr | fr_take_din | kec_start | ent_req | own_start;
    always_ff @(posedge clk) begin
        f_pv <= 1'b1;
        if (f_pv && srst_n && $past(srst_n)) begin
            // a multi-clock instruction stays the instruction it was started as
            if (st == S_KMOV2) assert (op == OP_KMOV);
            if (st == S_KEC)   assert (op == OP_KEC);
            if (st == S_FRAM)  assert (is_fram);
            if (st == S_ENT)   assert (ctl_nonce);
            if (st == S_AUTH)  assert (ctl_auth);
            // ... its store target is the one that was checked when it started
            if (st == S_KMOV2) assert (rb < 7'(RATE_LANES));
            if (st == S_FRAM && fr_rword_op && store) assert (!((rb >= 7'(KEY0)) && (rb < 7'(KEY0 + N_KEYS))));
            // ... and the return it will make was checked when it started
            if (st == S_KMOV2 || st == S_KEC || st == S_FRAM || st == S_ENT || st == S_AUTH)
                assert (!(ret && ((sp == 2'd0) || (stk0 == IDLE_ADDR) || ({1'b0, stk0} >= rom_len))));
            // the sequencer cannot leave the ROM: no instruction outside the image executes
            assert (!(go && ({1'b0, pc} >= rom_len)));
            assert (!(fin && (st == S_RUN) && (op != OP_DISP) && taken && ({1'b0, target} >= rom_len)));
            // address 0 (idle) is entered only from the last clock of the end action, which follows the wipe
            if (pc == IDLE_ADDR && $past(pc) != IDLE_ADDR) assert ($past(st) == S_ENDI || off_end);
            if (off_end && st == S_RUN && ir_ok) assert (fault_now);
            if (st == S_ENDI) assert ($past(st) == S_ENDF && $past(rf_wipe) == 4'hF);
            if (st == S_RUN && $past(st) == S_ENDI) assert (pc == IDLE_ADDR && !keyed && !dirty && !t_lanes && !t_h && !hdr_done);
            // 8.2 (3): a key row opens only for the boot interface (device-secret rows) or for KEYWR inside
            // the hardwired key range with the authorisation latch set
            assert (!key_wr || key_wr_boot || ((st == S_RUN) && (op == OP_KEYWR) && (pc >= KEY_LO) && (pc <= KEY_HI) && auth_ok));
            assert (!key_wr_boot || ((rf_waddr >= 7'(KEY0)) && (rf_waddr < 7'(KEY0 + N_KDEV))));
            // key rows are read only by the first clock of KMOV, whose data goes to the hold register
            assert (!(rd_used && f_key_a) || ((st == S_RUN) && (op == OP_KMOV)));
            // the response: an out row opens only on a PUSH after the header and inside the declared length;
            // the row that goes through the hold register for it is a lane, scratch, pin or state row; H is
            // pushed only untainted; a tainted lane is pushed only as REL of a rate lane
            assert (rf_out_we == 2'b00 || ((st == S_RUN) && (op == OP_PUSH) && hdr_done && !failed && eg_push_room && eg_can_push));
            assert (!((|rf_out_we) && !immf) || f_pushsrc);
            assert (!((|rf_out_we) && immf && t_h));
            assert (!((|rf_out_we) && !immf && !store && t_lanes && (rf_raddr < 7'(KWORK0))));
            assert (!((|rf_out_we) && !immf && store) || (rf_raddr < 7'(RATE_LANES)));
            assert (!((|rf_out_we) && !immf && dirty && (rf_raddr < 7'(KWORK0))));
            // the FRAM: instructions only inside the record range; data only from the three record rows
            assert (!(fm_start | fm_rword | fm_wword | fm_done) || ((pc >= REC_LO) && (pc <= REC_HI)));
            assert (!fm_wword || (rf_raddr == FRAM_SRC0) || (rf_raddr == FRAM_SRC1) || (rf_raddr == FRAM_SRC2));
            // 8.2 (6): the word unit never reads a row in the clock in which it is transparent
            assert (!(rd_used && (st == S_RUN) && open_hit));
            assert (!((st == S_AUTH) && (tr_valid || (|tr_wipe)) && (astep >= 4'd2)));
            // R4: a capacity lane of a keyed state is never read by the word unit, a PUSH or the FRAM path
            assert (!(rd_used && (st == S_RUN) && keyed && (rf_raddr >= 7'(RATE_LANES)) && (rf_raddr < 7'(KWORK0))));
            // R2: after KMOV the accumulator reads as zero; R5: a lane loaded while the lanes are key-derived
            // taints the accumulator
            if ($past(st) == S_KMOV2) assert ((h_alt == HA_ZERO) && !t_h && keyed && dirty && t_lanes);
            if ($past(fin) && $past(st) == S_RUN && $past(op) == OP_LD && !$past(immf) && ($past(ra) < 7'(KWORK0))
                && $past(t_lanes) && !$past(r_clear_h)) assert (t_h);
            // a refused instruction has no effect
            assert (!(fault_now && f_effect));
            // taint (R7): key-derived data sets no response length, index, loop count, verdict or key attribute
            assert (!(eg_hdr && t_h));
            assert (!(fin && (op == OP_SETX) && fn[0] && t_h));
            assert (!(fin && (op == OP_SETC) && fa[1] && t_h));
            assert (!(fin && is_ctl && (fa == CTL_VOK) && t_z));
            assert (!(fin && is_ctl && (fa == CTL_SETKV) && (t_h || !auth_ok)));
            assert (!(fin && (op == OP_BR) && (((fa == COND_Z || fa == COND_NZ) && t_z) || ((fa == COND_HZ || fa == COND_HNZ) && t_h)
                                              || ((fa == COND_CY || fa == COND_NC) && t_cy))));
            // key-derived data is stored only to lanes (R6)
            assert (!(fin && (st == S_RUN) && stores && r_t_h_n && !(rf_waddr < 7'(KWORK0)) && !r_clear_h) || (op == OP_DIN) || (op == OP_LDF) || (op == OP_LDC) || fr_rword_op);
        end
    end
`endif
    assign verify_ok    = v_ok;
    assign fault_mac    = f_mac;
    assign fault_anchor = f_anchor;
endmodule
`default_nettype wire
