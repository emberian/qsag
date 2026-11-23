// Dregg-180 Organ 1: Hardware CapTP Object-Capability Vat Membrane (`dregg_captp_vat`).
//
// Hardened Capability Membrane:
//   * Root secret `K_vat`, `zk_pin[0..3]`, and parent `PK.seed[0..1]` (`sh[8..9]`) live in
//     `qsag_sponge`, sharing `qsag_sponge`'s `hold_q` write-hold register and `qsag_wire_engine`'s
//     64-bit equality comparator (`desc_eq_sp`).
//   * Active capability policy `w1[63:0], w2[63:0], p_spend[31:0]` (`160` bits) sits in `latrnq_1`
//     rows behind `icgtp_4` (`qsag_latgate`), cleared in 0 clocks on `srst_n`.
`default_nettype none

module dregg_captp_vat (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    input  wire         permit_control,
    input  wire         kvat_commit,
    output logic        vat_ready,
    input  wire         zk_latch_valid_set,
    input  wire         zk_latch_clear,
    output logic        zk_root_valid,
    input  wire         parent_chk_clr,
    input  wire         parent_we,
    input  wire  [2:0]  parent_idx,
    input  wire  [63:0] desc_wdata,
    input  wire  [63:0] sp_hold_q,
    input  wire         desc_eq_sp,
    input  wire         child_chk_clr,
    input  wire         child_we,
    input  wire  [2:0]  child_idx,
    input  wire         pk_chk_clr,
    input  wire         pk_chk_we,
    input  wire         nfc_auth_ok,
    output wire         need_nfc_guard,
    output wire         nfc_consume_pulse,
    input  wire         dist_valid,
    input  wire         dist_timeout,
    input  wire  [31:0] dist_cycles,
    output wire         dist_consume_pulse,
    input  wire  [15:0] req_right_bit,
    input  wire  [31:0] req_epoch,
    input  wire  [31:0] req_spend,
    input  wire         check_is_zk,
    input  wire         commit_invocation,
    output wire         attenuate_legal,
    output wire         attenuate_step_ok,
    output wire         invoke_legal,
    output wire         need_stateful_fram,
    output wire  [31:0] vat_spend_used
);
    localparam int G_STATEFUL = 0; // w1[16]
    localparam int G_NFC      = 1; // w1[17]
    localparam int G_DIST     = 2; // w1[18]
    localparam int G_PIN_VK   = 3; // w1[19]

    wire [2:0] rn_br;
    qsag_rst_tree #(.N(3)) u_rnt (.a(srst_n), .y(rn_br));

    wire        pmeta_we = parent_we && permit_control && (parent_idx >= 3'd1) && (parent_idx <= 3'd3);
    wire [63:0] pw_w1, pw_w2;
    wire [31:0] p_spend;
    wire        g1, g2, g3;
    qsag_latgate u_cg1 (.clk(clk), .en(pmeta_we && parent_idx == 3'd1), .gclk(g1));
    qsag_latgate u_cg2 (.clk(clk), .en(pmeta_we && parent_idx == 3'd2), .gclk(g2));
    qsag_latgate u_cg3 (.clk(clk), .en(pmeta_we && parent_idx == 3'd3), .gclk(g3));
    qsag_latch_word_rst #(.W(64)) u_lw1 (.gate(g1), .rst_n(rn_br[0]), .d(sp_hold_q),       .q(pw_w1));
    qsag_latch_word_rst #(.W(64)) u_lw2 (.gate(g2), .rst_n(rn_br[1]), .d(sp_hold_q),       .q(pw_w2));
    qsag_latch_word_rst #(.W(32)) u_lw3 (.gate(g3), .rst_n(rn_br[1]), .d(sp_hold_q[31:0]), .q(p_spend));

    wire [15:0] p_rights = pw_w1[15:0];
    wire [15:0] p_guards = pw_w1[31:16];
    wire [31:0] p_maxd   = pw_w1[63:32];
    wire [31:0] p_efloor = pw_w2[31:0];
    wire [31:0] p_eceil  = pw_w2[63:32];

    logic p_vk_nz_q, p_vk_hi_zero_q, p_vk_zk_ok_q, pk_match_q;
    wire  p_vk_pk_ok = pk_match_q && p_vk_hi_zero_q;
    wire  desc_nz    = |desc_wdata;

    // Direct minimal-mux 32-bit `<=` comparisons (eliminating 6x32b front-end mux bloat)
    wire le_ef   = (p_efloor <= (child_we ? desc_wdata[31:0]  : req_epoch));
    wire le_ec   = ((child_we ? desc_wdata[63:32] : req_epoch) <= p_eceil);
    wire le_maxd = ((child_we ? desc_wdata[63:32] : dist_cycles) <= p_maxd);

    logic child_word_ok;
    always_comb begin
        unique case (child_idx)
            3'd0: child_word_ok = 1'b1;
            3'd1: child_word_ok = p_rights[3] &&
                                  ((desc_wdata[15:0]  & ~p_rights) == 16'd0) &&
                                  ((desc_wdata[31:16] &  p_guards) == p_guards) &&
                                  le_maxd;
            3'd2: child_word_ok = le_ef && le_ec && (desc_wdata[31:0] <= desc_wdata[63:32]);
            3'd3: child_word_ok = (desc_wdata[31:0] <= p_spend) && (desc_wdata[31:0] != 32'd0);
            default: child_word_ok = !(p_guards[G_PIN_VK] || p_vk_nz_q) || desc_eq_sp;
        endcase
    end

    logic       att_ok_q;
    logic [7:0] att_seen_q;
    assign attenuate_legal   = vat_ready && att_ok_q && (att_seen_q == 8'hFF);
    assign attenuate_step_ok = vat_ready && att_ok_q && child_word_ok;

    wire [32:0] next_spend = {1'b0, vat_spend_used} + {1'b0, req_spend};
    wire right_ok = (p_rights & req_right_bit) == req_right_bit;
    wire epoch_ok = le_ef && le_ec;
    wire spend_ok = (next_spend <= {1'b0, p_spend});

    wire vk_ok   = check_is_zk ? (zk_root_valid && p_vk_zk_ok_q) : (!p_guards[G_PIN_VK] || p_vk_pk_ok);
    wire nfc_ok  = !p_guards[G_NFC]  || nfc_auth_ok;
    wire dist_ok = !p_guards[G_DIST] || (dist_valid && !dist_timeout && le_maxd);

    assign invoke_legal       = !child_we && vat_ready && right_ok && epoch_ok && spend_ok && vk_ok && nfc_ok && dist_ok;
    assign need_stateful_fram = p_guards[G_STATEFUL];
    assign need_nfc_guard     = p_guards[G_NFC];
    assign nfc_consume_pulse  = commit_invocation && invoke_legal && p_guards[G_NFC];
    assign dist_consume_pulse = commit_invocation && invoke_legal && p_guards[G_DIST];

    wire spend_clr = kvat_commit && permit_control;
    wire spend_inc = commit_invocation && invoke_legal && permit_control;
    qsag_ereg #(.W(32)) u_spu (
        .clk(clk), .rst_n(rn_br[2]), .en(spend_clr | spend_inc),
        .d(spend_clr ? 32'd0 : next_spend[31:0]), .q(vat_spend_used)
    );

    always_ff @(posedge clk or negedge rn_br[2]) begin
        if (!rn_br[2]) begin
            vat_ready      <= 1'b0;
            zk_root_valid  <= 1'b0;
            p_vk_nz_q      <= 1'b0;
            p_vk_hi_zero_q <= 1'b0;
            p_vk_zk_ok_q   <= 1'b0;
            pk_match_q     <= 1'b0;
            att_ok_q       <= 1'b0;
            att_seen_q     <= 8'd0;
        end else begin
            if (kvat_commit && permit_control)
                vat_ready <= 1'b1;
            if (zk_latch_clear)
                zk_root_valid <= 1'b0;
            else if (zk_latch_valid_set && permit_control)
                zk_root_valid <= 1'b1;

            if (parent_chk_clr) begin
                p_vk_nz_q      <= 1'b0;
                p_vk_hi_zero_q <= 1'b1;
                p_vk_zk_ok_q   <= 1'b1;
            end else if (parent_we && permit_control && parent_idx[2]) begin
                if (desc_nz)                       p_vk_nz_q      <= 1'b1;
                if (parent_idx >= 3'd6 && desc_nz) p_vk_hi_zero_q <= 1'b0;
                if (!desc_eq_sp)                   p_vk_zk_ok_q   <= 1'b0;
            end

            if (pk_chk_clr) begin
                pk_match_q <= 1'b1;
            end else if (pk_chk_we && permit_control) begin
                if (!desc_eq_sp) pk_match_q <= 1'b0;
            end

            if (child_chk_clr) begin
                att_ok_q   <= 1'b1;
                att_seen_q <= 8'd0;
            end else if (child_we && permit_control) begin
                if (!child_word_ok) att_ok_q <= 1'b0;
                att_seen_q[child_idx] <= 1'b1;
            end
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = rst_n;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
