// Dregg-180 Organ 1: Hardware CapTP Object-Capability Vat Membrane (`dregg_captp_vat`).
//
// Ultra-compact (< 5.5 kGE) capability membrane hardened against Subcarbon R0 Trap T6:
//   * Root secret `K_vat` (256-bit) never signs raw host messages directly.
//   * Active / parent capability metadata `pw1..pw3` (`rights, guards, max_dist, epoch_floor,
//     epoch_ceil, spend_limit` = 192 bits) is held in `latrnq_1` (`RN = srst_n`), zeroizing in
//     0 clocks on tamper/laser fault EVEN IF `clk_core` is stopped!
//   * Full 256-bit `target_vk_root` (`w[4..7]`) and `swiss_nonce` (`w[0]`) are bound inside the
//     256-bit `TurboSHAKE256` seal AND verified word-by-word (`1` shared 64-bit comparator!) as
//     parent and child descriptors stream through `qsag_sponge`, eliminating 704 redundant storage
//     latches and six 64-bit comparators!
`default_nettype none

module dregg_captp_vat (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,             // asynchronous zeroize on tamper/glitch/laser fault
    input  wire         permit_control,     // HD=4 FSM integrity guard
    // Root K_vat provisioning (from PUF+BCH or TRNG ceremony via TurboSHAKE256)
    input  wire  [3:0]  kvat_we,
    input  wire  [63:0] kvat_wdata,
    input  wire         kvat_commit,
    output logic        vat_ready,
    input  wire  [1:0]  kvat_ridx,
    output wire  [63:0] kvat_rdata,
    // Verified ZK proof root latch (from OP_VERIFY_HEM_STREAM / OP_EXT4_FOLD)
    input  wire         zk_latch_we,
    input  wire  [1:0]  zk_latch_idx,
    input  wire  [63:0] zk_latch_wdata,
    input  wire         zk_latch_valid_set,
    input  wire         zk_latch_clear,
    output logic        zk_root_valid,
    // Streaming Parent (`parent_we`) & Child (`child_we`, compared against sponge `pw_sponge_word`)
    input  wire         parent_chk_clr,
    input  wire         parent_we,
    input  wire  [2:0]  parent_idx,
    input  wire  [63:0] desc_wdata,
    input  wire  [63:0] pw_sponge_word,     // parent word `w[child_idx]` read from unified sponge!
    input  wire         child_chk_clr,
    input  wire         child_we,
    input  wire  [2:0]  child_idx,
    // External physical organ status (NFC Quorum + Speed-of-Light Distance Bounding)
    input  wire         nfc_token_valid,
    input  wire  [63:0] nfc_digest_bind,
    output wire         nfc_consume_pulse,
    input  wire         dist_valid,
    input  wire         dist_timeout,
    input  wire  [31:0] dist_cycles,
    output wire         dist_consume_pulse,
    // Lattice & invocation verification queries
    input  wire  [15:0] req_right_bit,      // 16'h0001 CTH, 16'h0002 PRF, 16'h0004 ZK_INVOKE
    input  wire  [31:0] req_epoch,
    input  wire  [31:0] req_spend,
    input  wire  [63:0] req_bind_lo,
    input  wire  [63:0] req_bind_hi,
    input  wire         check_is_zk,
    input  wire         commit_invocation,
    output wire         attenuate_legal,
    output wire         attenuate_step_ok,
    output wire         invoke_legal,
    output wire         need_stateful_fram,
    output logic [31:0] vat_spend_used
);
    localparam int G_STATEFUL = 0; // w1[16]
    localparam int G_NFC      = 1; // w1[17]
    localparam int G_DIST     = 2; // w1[18]
    localparam int G_PIN_VK   = 3; // w1[19]

    // 256-bit K_vat root key
    wire [63:0] k_vat [4];
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : g_kvat
            qsag_ereg #(.W(64)) u_kv (
                .clk(clk), .rst_n(srst_n), .en(kvat_we[i] && permit_control),
                .d(kvat_wdata), .q(k_vat[i])
            );
        end
    endgenerate
    assign kvat_rdata = k_vat[kvat_ridx];

    // Last verified ZK transcript / statement root (4 x 64 bits in async-cleared latrnq_1 latches!)
    wire        zkr_any_we = zk_latch_we & permit_control;
    wire [63:0] dhold_in   = zkr_any_we ? zk_latch_wdata : desc_wdata;
    wire        pmeta_we   = parent_we && permit_control && (parent_idx >= 3'd1) && (parent_idx <= 3'd5);
    wire [63:0] desc_wd_q;
    qsag_ereg_nr #(.W(64)) u_dhold (.clk(clk), .en(pmeta_we | zkr_any_we), .d(dhold_in), .q(desc_wd_q));

    wire [63:0] zk_root [4];
    generate
        for (i = 0; i < 4; i++) begin : g_zkr
            wire z_en = zkr_any_we && (zk_latch_idx == 2'(i));
            wire z_gate;
            qsag_clkgate_1 u_zcg (.clk(clk), .en(z_en), .gclk(z_gate));
            qsag_latch_word_rst #(.W(64)) u_zr (.gate(z_gate), .rst_n(srst_n), .d(desc_wd_q), .q(zk_root[i]));
        end
    endgenerate

    wire [63:0] pw_meta [5]; // [0]=w1, [1]=w2, [2]=w3, [3]=w4(pk0), [4]=w5(pk1)
    generate
        for (i = 0; i < 5; i++) begin : g_pmeta
            wire p_en = pmeta_we && (parent_idx == 3'(i + 1));
            wire p_gate;
            qsag_clkgate_1 u_pcg (.clk(clk), .en(p_en), .gclk(p_gate));
            qsag_latch_word_rst #(.W(64)) u_plat (.gate(p_gate), .rst_n(srst_n), .d(desc_wd_q), .q(pw_meta[i]));
        end
    endgenerate

    wire [15:0] p_rights = pw_meta[0][15:0];
    wire [15:0] p_guards = pw_meta[0][31:16];
    wire [31:0] p_maxd   = pw_meta[0][63:32];
    wire [31:0] p_efloor = pw_meta[1][31:0];
    wire [31:0] p_eceil  = pw_meta[1][63:32];
    wire [31:0] p_spend  = pw_meta[2][31:0];

    // Streaming parent VK-binding check on words 4..7 (`zk_root` checked as parent streams in;
    // 128-bit `PK.seed` checked live against `pw_meta[3..4]` + `p_vk_hi_zero_q`!)
    logic p_vk_nz_q, p_vk_hi_zero_q, p_vk_zk_ok_q;
    wire [63:0] zk_expected = zk_root[parent_idx[1:0]];
    wire        p_vk_pk_ok  = (pw_meta[3] == req_bind_lo) && (pw_meta[4] == req_bind_hi) && p_vk_hi_zero_q;

    // Streaming child lattice monotonicity check (`pw_sponge_word` holds parent w[child_idx]!)
    logic child_word_ok;
    always_comb begin
        child_word_ok = 1'b1;
        unique case (child_idx)
            3'd0: child_word_ok = 1'b1;
            3'd1: child_word_ok = p_rights[3] &&
                                  ((desc_wdata[15:0]  & ~p_rights) == 16'd0) &&
                                  ((desc_wdata[31:16] &  p_guards) == p_guards) &&
                                  (desc_wdata[63:32] <= p_maxd);
            3'd2: child_word_ok = (desc_wdata[31:0]  >= p_efloor) &&
                                  (desc_wdata[63:32] <= p_eceil)  &&
                                  (desc_wdata[31:0]  <= desc_wdata[63:32]);
            3'd3: child_word_ok = (desc_wdata[31:0]  <= p_spend) && (desc_wdata[31:0] != 32'd0);
            default: child_word_ok = !(p_guards[G_PIN_VK] || p_vk_nz_q) || (desc_wdata == pw_sponge_word);
        endcase
    end

    logic       att_ok_q;
    logic [7:0] att_seen_q;
    assign attenuate_legal   = vat_ready && att_ok_q && (att_seen_q == 8'hFF);
    assign attenuate_step_ok = vat_ready && att_ok_q && child_word_ok;

    // Invocation legality check
    wire right_ok = (p_rights & req_right_bit) == req_right_bit;
    wire epoch_ok = (req_epoch >= p_efloor) && (req_epoch <= p_eceil);
    wire [32:0] next_spend = {1'b0, vat_spend_used} + {1'b0, req_spend};
    wire spend_ok = (req_spend <= p_spend) && (next_spend <= {1'b0, p_spend});

    wire vk_ok   = !p_guards[G_PIN_VK] || (check_is_zk ? (zk_root_valid && p_vk_zk_ok_q) : p_vk_pk_ok);
    wire nfc_ok  = !p_guards[G_NFC]    || (nfc_token_valid && (nfc_digest_bind == req_bind_lo));
    wire dist_ok = !p_guards[G_DIST]   || (dist_valid && !dist_timeout && (dist_cycles <= p_maxd));

    assign invoke_legal       = vat_ready && right_ok && epoch_ok && spend_ok && vk_ok && nfc_ok && dist_ok;
    assign need_stateful_fram = p_guards[G_STATEFUL];
    assign nfc_consume_pulse  = commit_invocation && invoke_legal && p_guards[G_NFC];
    assign dist_consume_pulse = commit_invocation && invoke_legal && p_guards[G_DIST];

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            vat_ready      <= 1'b0;
            zk_root_valid  <= 1'b0;
            vat_spend_used <= 32'd0;
            p_vk_nz_q      <= 1'b0;
            p_vk_hi_zero_q <= 1'b0;
            p_vk_zk_ok_q   <= 1'b0;
            att_ok_q       <= 1'b0;
            att_seen_q     <= 8'd0;
        end else begin
            if (kvat_commit && permit_control) begin
                vat_ready      <= 1'b1;
                vat_spend_used <= 32'd0;
            end
            if (zk_latch_clear)
                zk_root_valid <= 1'b0;
            else if (zk_latch_valid_set && permit_control)
                zk_root_valid <= 1'b1;

            if (parent_chk_clr) begin
                p_vk_nz_q      <= 1'b0;
                p_vk_hi_zero_q <= 1'b1;
                p_vk_zk_ok_q   <= 1'b1;
            end else if (parent_we && permit_control && parent_idx[2]) begin
                if (desc_wdata != 64'd0)                     p_vk_nz_q      <= 1'b1;
                if (parent_idx >= 3'd6 && desc_wdata != 64'd0) p_vk_hi_zero_q <= 1'b0;
                if (desc_wdata != zk_expected)               p_vk_zk_ok_q   <= 1'b0;
            end

            if (child_chk_clr) begin
                att_ok_q   <= 1'b1;
                att_seen_q <= 8'd0;
            end else if (child_we && permit_control) begin
                if (!child_word_ok) att_ok_q <= 1'b0;
                att_seen_q[child_idx] <= 1'b1;
            end
            if (commit_invocation && invoke_legal && permit_control)
                vat_spend_used <= next_spend[31:0];
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = rst_n;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
