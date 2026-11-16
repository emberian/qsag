// QSAG-NI FPGA accelerator top: AXI4-Lite command/register interface plus one AXI4-Stream
// slave for bulk data, around the five QSAG-NI primitives.
//
// Register map (32-bit words, byte addresses):
//   0x000 CMD       W   [7:0] opcode, [15:8] arg0, [31:16] arg1; a write starts the operation
//   0x004 STATUS    R   [0] busy [1] done [2] ok [3] non-canonical stream limb seen (sticky)
//                       [4] command written while busy (sticky) [5] any engine active
//   0x008 OP_CYCLES R   clocks from command acceptance to completion of the last operation
//   0x00C/0x010     R   TOTAL_CYCLES low/high: clocks during which any engine was active
//   0x014 ARG32     RW  32-bit argument (chain start: heap index of the leaf)
//   0x018 CHAIN_DONE R, 0x01C CHAIN_OK R, 0x024 CHAIN_BUSY R : one bit per chain slot
//   0x020 STREAM    RW  [31] destination (0 chain step memory, 1 fold table), [16:0] write pointer
//   0x028 ID        R   0x51534E49 ("QSNI")
//   0x02C P2_PERMS  R   Poseidon2 permutations completed
//   0x100 + 8*i     RW  operand bank X[i], i < 32 (low word, then high word)
//   0x200 + 8*i     R   result bank  Y[i], i < 12
//
// Operations (X, Y are 64-bit lanes; Ext4 elements are 4 lanes in qsag limb order):
//   0x01 P2_PERM      Y[0..11] = poseidon2_perm12(X[0..11])
//   0x02 P2_JIVE      Y[0..3]  = weighted feed-forward node hash of X[0..11] = [l, r, t]
//   0x03 CHAIN_CFG    tree key = X[0..2], expected top node = X[4..7]; arg0[0] clears DONE/OK
//   0x04 CHAIN_START  slot arg0[4:0], arg1[5:0] sponge steps, leaf heap index ARG32,
//                     initial state X[0..11]; the chain then runs in the background
//   0x05 CHAIN_WAIT   completes when no chain is active; ok = every finished chain matched
//   0x06 CHAIN_READ   Y[0..11] = state of slot arg0[4:0]
//   0x10 EXT4_MAC     Y[0..3] = X[0..3] * X[4..7] + X[8..11]
//   0x11 SC_INIT      sumcheck claim = X[0..3], clears the sticky failure
//   0x12 SC_ROUND     round polynomial c0..c3 = X[0..15], challenge X[16..19]: checks
//                     g(0) + g(1) = claim, then claim = g(challenge) (Horner); Y[0..3] = claim,
//                     ok = no round failed since SC_INIT
//   0x13 FOLD_ROUND   table[k] = table[2k] + X[0..3] * (table[2k+1] - table[2k]) over the
//                     current length, which then halves; Y[0..3] = last entry written
//   0x14 FOLD_SETLEN  log2 of the table length = arg0[5:0]
//   0x20 KEC_LOAD     Keccak state = X[0..24]
//   0x21 KEC_PERMUTE  state[0..16] ^= X[0..16] unless arg0[1]; permute, 12 rounds if arg0[0]
//                     (TurboSHAKE256) else 24; Y[0..11] = state[0..11]
//   0x30 GF_MAC       Y[0..1] = X[0..1] * X[2..3] + X[4..5] in GF(2^128); ok = (== X[6..7])
//   0x3F CLEAR        clears sticky errors and the cycle and permutation counters
//
// Stream beats are 512 bits: a sponge block (8 lanes), a sibling digest (low 256 bits) or a
// fold-table entry (low 256 bits), written at the STREAM pointer, which then increments.
module qsag_ni_fpga_top #(
    parameter int FOLD_TAW   = 16,   // log2 of fold-table entries
    parameter int KECCAK_RPC = 2,
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic         clk,
    input  logic         rst,
    // AXI4-Lite slave
    input  logic [11:0]  s_axil_awaddr,
    input  logic         s_axil_awvalid,
    output logic         s_axil_awready,
    input  logic [31:0]  s_axil_wdata,
    input  logic [3:0]   s_axil_wstrb,
    input  logic         s_axil_wvalid,
    output logic         s_axil_wready,
    output logic [1:0]   s_axil_bresp,
    output logic         s_axil_bvalid,
    input  logic         s_axil_bready,
    input  logic [11:0]  s_axil_araddr,
    input  logic         s_axil_arvalid,
    output logic         s_axil_arready,
    output logic [31:0]  s_axil_rdata,
    output logic [1:0]   s_axil_rresp,
    output logic         s_axil_rvalid,
    input  logic         s_axil_rready,
    // AXI4-Stream slave
    input  logic [511:0] s_axis_tdata,
    input  logic         s_axis_tvalid,
    output logic         s_axis_tready
);
    localparam logic [63:0] GL_P = qsag_ni_pkg::GL_P;
    localparam int GF128_LAT = qsag_ni_pkg::GF128_LAT;
    localparam int SLOTW = 5;
    localparam int STEPW = 6;
    localparam int TAGW  = SLOTW + 2;

    // ------------------------------------------------------------------ registers
    logic [31:0][63:0] x_q;
    logic [11:0][63:0] y_q;
    logic [31:0]       arg32_q, stream_q, op_cycles_q, perms_q;
    logic [63:0]       total_q;
    logic              op_busy, op_done, op_ok, err_noncanon, err_cmd;

    logic        wr_fire, rd_fire, cmd_fire;
    logic [9:0]  wr_word, rd_word;
    assign wr_fire = s_axil_awvalid && s_axil_wvalid && !s_axil_bvalid;
    assign rd_fire = s_axil_arvalid && !s_axil_rvalid;
    assign wr_word = s_axil_awaddr[11:2];
    assign rd_word = s_axil_araddr[11:2];
    assign s_axil_awready = wr_fire;
    assign s_axil_wready  = wr_fire;
    assign s_axil_arready = rd_fire;
    assign s_axil_bresp   = 2'b00;
    assign s_axil_rresp   = 2'b00;
    assign cmd_fire = wr_fire && (wr_word == 10'h000) && !op_busy;

    logic unused_ok;
    assign unused_ok = &{1'b0, s_axil_wstrb, s_axil_awaddr[1:0], s_axil_araddr[1:0]};

    logic [7:0]  cmd_op_q, cmd_a0_q;
    logic [15:0] cmd_a1_q;

    // ------------------------------------------------------------------ Poseidon2 ring + chains
    logic             p2_in_valid, p2_in_ready, p2_in_jive, p2_out_valid, p2_busy;
    logic [767:0]     p2_in_state, p2_out_state;
    logic [TAGW-1:0]  p2_in_tag, p2_out_tag;
    /* verilator lint_off UNUSEDSIGNAL */
    logic             p2_out_jive;
    /* verilator lint_on UNUSEDSIGNAL */

    logic             op_job_valid, op_job_jive;
    logic             eng_job_valid, eng_job_jive, eng_job_last;
    logic [767:0]     eng_job_state;
    logic [SLOTW-1:0] eng_job_slot;
    logic             eng_start_valid, eng_start_ready, eng_rd_valid, eng_rd_done, eng_clr;
    logic [767:0]     eng_rd_state;
    logic [191:0]     tree_key_q;
    logic [255:0]     expect_q;
    logic [31:0]      chain_busy, chain_done, chain_ok;

    assign p2_in_valid = eng_job_valid || op_job_valid;
    assign p2_in_state = eng_job_valid ? eng_job_state : x_q[11:0];
    assign p2_in_jive  = eng_job_valid ? eng_job_jive : op_job_jive;
    assign p2_in_tag   = eng_job_valid ? {1'b1, eng_job_last, eng_job_slot} : '0;

    qsag_poseidon2_12_fpga #(.TAGW(TAGW), .AW(AW), .BW(BW)) u_p2 (
        .clk(clk), .rst(rst),
        .in_valid(p2_in_valid), .in_ready(p2_in_ready), .in_state(p2_in_state),
        .in_jive(p2_in_jive), .in_tag(p2_in_tag),
        .out_valid(p2_out_valid), .out_state(p2_out_state), .out_jive(p2_out_jive),
        .out_tag(p2_out_tag), .busy(p2_busy));

    logic stream_fire, stream_tbl;
    assign stream_tbl = stream_q[31];

    qsag_p2_chain_engine #(.SLOTW(SLOTW), .STEPW(STEPW)) u_chain (
        .clk(clk), .rst(rst), .tree_key(tree_key_q), .exp_root(expect_q), .clr_maps(eng_clr),
        .bw_en(stream_fire && !stream_tbl), .bw_addr(stream_q[SLOTW+STEPW-1:0]),
        .bw_data(s_axis_tdata),
        .start_valid(eng_start_valid), .start_ready(eng_start_ready),
        .start_slot(cmd_a0_q[SLOTW-1:0]), .start_nsponge(cmd_a1_q[5:0]),
        .start_heap(arg32_q), .start_state(x_q[11:0]),
        .rd_valid(eng_rd_valid), .rd_slot(cmd_a0_q[SLOTW-1:0]),
        .rd_done(eng_rd_done), .rd_state(eng_rd_state),
        .job_valid(eng_job_valid), .job_ready(p2_in_ready), .job_state(eng_job_state),
        .job_jive(eng_job_jive), .job_last(eng_job_last), .job_slot(eng_job_slot),
        .res_valid(p2_out_valid && p2_out_tag[TAGW-1]), .res_last(p2_out_tag[SLOTW]),
        .res_slot(p2_out_tag[SLOTW-1:0]), .res_state(p2_out_state),
        .busy_map(chain_busy), .done_map(chain_done), .ok_map(chain_ok));

    // ------------------------------------------------------------------ Ext4 MAC / fold
    logic         fold_start, fold_busy, fold_done, mac_valid, mac_done;
    logic [255:0] fold_res, mac_a, mac_b, mac_c, mac_y;
    logic [5:0]   fold_log2n_q;

    qsag_ext4_mac_bfly #(.TAW(FOLD_TAW), .AW(AW), .BW(BW)) u_ext4 (
        .clk(clk), .rst(rst),
        .tw_en(stream_fire && stream_tbl), .tw_idx(stream_q[FOLD_TAW-1:0]),
        .tw_data(s_axis_tdata[255:0]),
        .fold_start(fold_start), .fold_log2n(fold_log2n_q), .fold_r(x_q[3:0]),
        .fold_busy(fold_busy), .fold_done(fold_done), .fold_res(fold_res),
        .mac_valid(mac_valid), .mac_a(mac_a), .mac_b(mac_b), .mac_c(mac_c),
        .mac_done(mac_done), .mac_y(mac_y));

    // Stream: canonical-range check on every limb that will be used.
    assign s_axis_tready = !rst && !(stream_tbl && fold_busy);
    assign stream_fire   = s_axis_tvalid && s_axis_tready;
    logic [7:0] limb_bad;
    for (genvar i = 0; i < 8; i++) begin : g_canon
        assign limb_bad[i] = (s_axis_tdata[64*i +: 64] >= GL_P);
    end
    logic stream_bad;
    assign stream_bad = stream_tbl ? (|limb_bad[3:0]) : (|limb_bad);

    // Sumcheck g(0) + g(1) = 2*c0 + c1 + c2 + c3 (mod p), per limb.
    logic [255:0] claim_q, acc_q;
    logic         sc_fail_q;
    logic [3:0]   sc_limb_eq;
    for (genvar i = 0; i < 4; i++) begin : g_sc
        logic [66:0] lz;
        logic [64:0] r;
        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] rm;
        /* verilator lint_on UNUSEDSIGNAL */
        logic [63:0] s;
        assign lz = (67'(x_q[i]) << 1) + 67'(x_q[4 + i]) + 67'(x_q[8 + i]) + 67'(x_q[12 + i]);
        assign r  = {1'b0, lz[63:0]} + {30'b0, lz[66:64], 32'b0} - 65'(lz[66:64]);
        assign rm = {1'b0, r} - {2'b0, GL_P};
        assign s  = rm[65] ? r[63:0] : rm[63:0];
        assign sc_limb_eq[i] = (s == claim_q[64*i +: 64]);
    end

    // ------------------------------------------------------------------ Keccak
    logic          kec_start, kec_busy, kec_done, kec_load;
    logic [1599:0] kec_state, kec_in;
    logic [1599:0] kec_hold_q;
    always_comb begin
        kec_in = kec_hold_q;
        if (!cmd_a0_q[1]) kec_in[17*64-1:0] = kec_hold_q[17*64-1:0] ^ x_q[16:0];
    end
    qsag_keccak_turboshake #(.RPC(KECCAK_RPC)) u_keccak (
        .clk(clk), .rst(rst), .start(kec_start), .nr12(cmd_a0_q[0]), .state_i(kec_in),
        .busy(kec_busy), .done(kec_done), .state_o(kec_state));

    // ------------------------------------------------------------------ GF(2^128)
    logic [127:0] gf_r;
    logic [2:0]   gf_cnt;
    qsag_gf128_clmul u_gf (.clk(clk), .a(x_q[1:0]), .b(x_q[3:2]), .r(gf_r));

    // ------------------------------------------------------------------ operation FSM
    typedef enum logic [3:0] {
        O_IDLE, O_P2_OFFER, O_P2_WAIT, O_CH_START, O_CH_WAIT, O_CH_READ,
        O_MAC, O_SC_SUM, O_SC_H, O_FOLD, O_KEC, O_GF, O_FIN
    } op_e;
    op_e        op_st;
    logic [1:0] sc_step;

    assign op_job_valid    = (op_st == O_P2_OFFER);
    assign op_job_jive     = (cmd_op_q == 8'h02);
    assign eng_start_valid = (op_st == O_CH_START);
    assign eng_rd_valid    = (op_st == O_CH_READ) && !eng_rd_done;

    logic engines_busy;
    assign engines_busy = op_busy || p2_busy || (|chain_busy) || fold_busy || kec_busy;

    always_ff @(posedge clk) begin
        fold_start <= 1'b0;
        mac_valid  <= 1'b0;
        kec_start  <= 1'b0;
        kec_load   <= 1'b0;
        eng_clr    <= 1'b0;
        if (rst) begin
            op_st        <= O_IDLE;
            op_busy      <= 1'b0;
            op_done      <= 1'b0;
            op_ok        <= 1'b0;
            err_noncanon <= 1'b0;
            err_cmd      <= 1'b0;
            op_cycles_q  <= '0;
            total_q      <= '0;
            perms_q      <= '0;
            sc_fail_q    <= 1'b0;
            fold_log2n_q <= 6'd1;
            stream_q     <= '0;
            arg32_q      <= '0;
            s_axil_bvalid <= 1'b0;
            s_axil_rvalid <= 1'b0;
        end else begin
            // ---- AXI4-Lite
            if (s_axil_bvalid && s_axil_bready) s_axil_bvalid <= 1'b0;
            if (s_axil_rvalid && s_axil_rready) s_axil_rvalid <= 1'b0;
            if (wr_fire) begin
                s_axil_bvalid <= 1'b1;
                if (wr_word == 10'h000 && op_busy) err_cmd <= 1'b1;
                if (wr_word == 10'h005) arg32_q  <= s_axil_wdata;
                if (wr_word == 10'h008) stream_q <= s_axil_wdata;
                if (wr_word[9:6] == 4'h1) begin
                    if (wr_word[0]) x_q[wr_word[5:1]][63:32] <= s_axil_wdata;
                    else            x_q[wr_word[5:1]][31:0]  <= s_axil_wdata;
                end
            end
            if (rd_fire) begin
                s_axil_rvalid <= 1'b1;
                s_axil_rdata  <= 32'd0;
                case (rd_word)
                    10'h001: s_axil_rdata <= {26'd0, engines_busy, err_cmd, err_noncanon,
                                              op_ok, op_done, op_busy};
                    10'h002: s_axil_rdata <= op_cycles_q;
                    10'h003: s_axil_rdata <= total_q[31:0];
                    10'h004: s_axil_rdata <= total_q[63:32];
                    10'h005: s_axil_rdata <= arg32_q;
                    10'h006: s_axil_rdata <= chain_done;
                    10'h007: s_axil_rdata <= chain_ok;
                    10'h008: s_axil_rdata <= stream_q;
                    10'h009: s_axil_rdata <= chain_busy;
                    10'h00A: s_axil_rdata <= 32'h5153_4E49;
                    10'h00B: s_axil_rdata <= perms_q;
                    default: begin
                        if (rd_word[9:6] == 4'h1)
                            s_axil_rdata <= rd_word[0] ? x_q[rd_word[5:1]][63:32]
                                                       : x_q[rd_word[5:1]][31:0];
                        else if (rd_word[9:6] == 4'h2 && rd_word[5:1] < 5'd12)
                            s_axil_rdata <= rd_word[0] ? y_q[rd_word[4:1]][63:32]
                                                       : y_q[rd_word[4:1]][31:0];
                    end
                endcase
            end

            // ---- stream
            if (stream_fire) begin
                stream_q[16:0] <= stream_q[16:0] + 17'd1;
                if (stream_bad) err_noncanon <= 1'b1;
            end

            // ---- counters
            if (op_busy) op_cycles_q <= op_cycles_q + 32'd1;
            if (engines_busy) total_q <= total_q + 64'd1;
            if (p2_out_valid) perms_q <= perms_q + 32'd1;
            if (fold_done) fold_log2n_q <= fold_log2n_q - 6'd1;

            // ---- operations
            case (op_st)
                O_IDLE: begin
                    if (cmd_fire) begin
                        cmd_op_q    <= s_axil_wdata[7:0];
                        cmd_a0_q    <= s_axil_wdata[15:8];
                        cmd_a1_q    <= s_axil_wdata[31:16];
                        op_busy     <= 1'b1;
                        op_done     <= 1'b0;
                        op_ok       <= 1'b1;
                        op_cycles_q <= '0;
                        case (s_axil_wdata[7:0])
                            8'h01, 8'h02: op_st <= O_P2_OFFER;
                            8'h03: begin
                                tree_key_q <= x_q[2:0];
                                expect_q   <= x_q[7:4];
                                eng_clr    <= s_axil_wdata[8];
                                op_st      <= O_FIN;
                            end
                            8'h04: op_st <= O_CH_START;
                            8'h05: op_st <= O_CH_WAIT;
                            8'h06: op_st <= O_CH_READ;
                            8'h10: begin
                                mac_valid <= 1'b1;
                                mac_a     <= x_q[3:0];
                                mac_b     <= x_q[7:4];
                                mac_c     <= x_q[11:8];
                                op_st     <= O_MAC;
                            end
                            8'h11: begin
                                claim_q   <= x_q[3:0];
                                sc_fail_q <= 1'b0;
                                op_st     <= O_FIN;
                            end
                            8'h12: op_st <= O_SC_SUM;
                            8'h13: begin
                                fold_start <= 1'b1;
                                op_st      <= O_FOLD;
                            end
                            8'h14: begin
                                fold_log2n_q <= s_axil_wdata[13:8];
                                op_st        <= O_FIN;
                            end
                            8'h20: begin
                                kec_load <= 1'b1;
                                op_st    <= O_FIN;
                            end
                            8'h21: begin
                                kec_start <= 1'b1;
                                op_st     <= O_KEC;
                            end
                            8'h30: begin
                                gf_cnt <= 3'd0;
                                op_st  <= O_GF;
                            end
                            8'h3F: begin
                                err_noncanon <= 1'b0;
                                err_cmd      <= 1'b0;
                                total_q      <= '0;
                                perms_q      <= '0;
                                op_st        <= O_FIN;
                            end
                            default: begin
                                op_ok <= 1'b0;
                                op_st <= O_FIN;
                            end
                        endcase
                    end
                end
                O_P2_OFFER: if (p2_in_ready && !eng_job_valid) op_st <= O_P2_WAIT;
                O_P2_WAIT: begin
                    if (p2_out_valid && !p2_out_tag[TAGW-1]) begin
                        y_q   <= p2_out_state;
                        op_st <= O_FIN;
                    end
                end
                O_CH_START: if (eng_start_ready) op_st <= O_FIN;
                O_CH_WAIT: begin
                    if (chain_busy == 32'd0) begin
                        op_ok <= ((chain_done & ~chain_ok) == 32'd0);
                        op_st <= O_FIN;
                    end
                end
                O_CH_READ: begin
                    if (eng_rd_done) begin
                        y_q   <= eng_rd_state;
                        op_st <= O_FIN;
                    end
                end
                O_MAC: begin
                    if (mac_done) begin
                        y_q[3:0] <= mac_y;
                        op_st    <= O_FIN;
                    end
                end
                O_SC_SUM: begin
                    if (!(&sc_limb_eq)) sc_fail_q <= 1'b1;
                    mac_valid <= 1'b1;
                    mac_a     <= x_q[15:12];
                    mac_b     <= x_q[19:16];
                    mac_c     <= x_q[11:8];
                    sc_step   <= 2'd0;
                    op_st     <= O_SC_H;
                end
                O_SC_H: begin
                    if (mac_done) begin
                        acc_q <= mac_y;
                        if (sc_step == 2'd2) begin
                            claim_q  <= mac_y;
                            y_q[3:0] <= mac_y;
                            op_ok    <= !sc_fail_q;
                            op_st    <= O_FIN;
                        end else begin
                            mac_valid <= 1'b1;
                            mac_a     <= mac_y;
                            mac_b     <= x_q[19:16];
                            mac_c     <= (sc_step == 2'd0) ? x_q[7:4] : x_q[3:0];
                            sc_step   <= sc_step + 2'd1;
                        end
                    end
                end
                O_FOLD: begin
                    if (fold_done) begin
                        y_q[3:0] <= fold_res;
                        op_st    <= O_FIN;
                    end
                end
                O_KEC: begin
                    if (kec_done) begin
                        y_q   <= kec_state[767:0];
                        op_st <= O_FIN;
                    end
                end
                O_GF: begin
                    gf_cnt <= gf_cnt + 3'd1;
                    if (gf_cnt == 3'(GF128_LAT)) begin
                        y_q[1:0] <= gf_r ^ x_q[5:4];
                        op_ok    <= ((gf_r ^ x_q[5:4]) == x_q[7:6]);
                        op_st    <= O_FIN;
                    end
                end
                O_FIN: begin
                    op_busy <= 1'b0;
                    op_done <= 1'b1;
                    op_st   <= O_IDLE;
                end
                default: op_st <= O_IDLE;
            endcase
        end
        // Keccak state register: loaded from X, or updated by a finished permutation.
        if (kec_load) kec_hold_q <= x_q[24:0];
        else if (kec_done) kec_hold_q <= kec_state;
    end

    logic unused_acc;
    assign unused_acc = &{1'b0, acc_q, stream_q[30:17], cmd_a0_q[7:5], cmd_a1_q[15:6]};
endmodule
