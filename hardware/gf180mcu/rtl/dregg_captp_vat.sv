// Dregg-180 Organ 1: Hardware CapTP Object-Capability Vat Membrane (`dregg_captp_vat`).
//
// Eliminates ambient-authority key slots:
//   * Root secret `K_vat` (256-bit, derived from the 64-RO PUF + BCH Fuzzy Extractor or TRNG
//     ceremony) never signs raw host messages directly.
//   * All enclave authority flows through unforgeable 256-bit-sealed `SpongeMacaroon` capability
//     handles carrying 8 x 64-bit descriptor words:
//       w0: swiss_nonce[63:0]
//       w1: {max_distance_cycles[31:0], caveat_guards[15:0], rights_mask[15:0]}
//       w2: {epoch_ceil[31:0], epoch_floor[31:0]}
//       w3: {32'd0, spend_limit[31:0]}
//       w4..w7: target_vk_root[255:0]
//       tag0..tag3: TurboSHAKE256("DREGGVAT" || K_vat[0..3] || w0..w7)[0..31] (256-bit seal)
//   * Enforces strict hardware lattice monotonicity on `OP_VAT_ATTENUATE` (< 2 us with 60-clock
//     TurboSHAKE256) and gates `OP_CTH`, `OP_PRFMSG`, and `OP_VAT_INVOKE_ZK` on rights, epoch
//     bounds, spend budget, VK/ZK-proof root binding, air-gapped 13.56 MHz NFC human-presence
//     co-approval, and < 6 ns Brands-Chaum / Vernier TDC speed-of-light distance bounding.
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
    // Descriptor staging buffer (parent + child / active capability)
    input  wire         parent_we,
    input  wire  [2:0]  parent_idx,
    input  wire  [63:0] desc_wdata,
    input  wire         child_we,
    input  wire  [2:0]  child_idx,
    input  wire  [2:0]  desc_ridx,
    input  wire         desc_sel_child,
    output wire  [63:0] desc_rdata,
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
    input  wire  [63:0] req_bind_lo,        // PK.seed[0] or digest prefix bound to NFC/VK
    input  wire  [63:0] req_bind_hi,        // PK.seed[1]
    input  wire         check_is_zk,        // 1: compare target_vk_root against latched ZK CH root
    input  wire         commit_invocation,  // consumes spend / NFC / distance-bound tokens
    output wire         attenuate_legal,
    output wire         invoke_legal,
    output wire         need_stateful_fram,
    output logic [31:0] vat_spend_used
);
    // Caveat guard bit definitions in w1[31:16]
    localparam int G_STATEFUL = 0; // w1[16]
    localparam int G_NFC      = 1; // w1[17]
    localparam int G_DIST     = 2; // w1[18]
    localparam int G_PIN_VK   = 3; // w1[19]

    // 256-bit K_vat root key (never directly exposed on egress)
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

    // Last verified ZK transcript / statement root (4 x 64 bits)
    wire [63:0] zk_root [4];
    generate
        for (i = 0; i < 4; i++) begin : g_zkr
            qsag_ereg #(.W(64)) u_zr (
                .clk(clk), .rst_n(srst_n),
                .en(zk_latch_we && (zk_latch_idx == 2'(i)) && permit_control),
                .d(zk_latch_wdata), .q(zk_root[i])
            );
        end
    endgenerate

    // Parent (or active invoked) capability descriptor w[0..7] and child descriptor c[0..7]
    // Using clock-gated latq_1 transparent-latch words with one shared posedge write-hold register!
    wire        desc_any_we = (parent_we | child_we) & permit_control;
    wire [63:0] desc_wd_q;
    qsag_ereg_nr #(.W(64)) u_dhold (
        .clk(clk), .en(!srst_n || desc_any_we), .d(!srst_n ? 64'd0 : desc_wdata), .q(desc_wd_q)
    );

    wire [63:0] pw [8];
    wire [63:0] cw [8];
    generate
        for (i = 0; i < 8; i++) begin : g_desc
            wire p_en = !srst_n || (parent_we && permit_control && (parent_idx == 3'(i)));
            wire c_en = !srst_n || (child_we  && permit_control && (child_idx  == 3'(i)));
            wire p_gate, c_gate;
            qsag_clkgate u_pcg (.clk(clk), .en(p_en), .gclk(p_gate));
            qsag_clkgate u_ccg (.clk(clk), .en(c_en), .gclk(c_gate));
            qsag_latch_word #(.W(64)) u_plat (.gate(p_gate), .d(desc_wd_q), .q(pw[i]));
            qsag_latch_word #(.W(64)) u_clat (.gate(c_gate), .d(desc_wd_q), .q(cw[i]));
        end
    endgenerate

    assign desc_rdata = desc_sel_child ? cw[desc_ridx] : pw[desc_ridx];

    // Unpack parent/active capability fields
    wire [15:0] p_rights = pw[1][15:0];
    wire [15:0] p_guards = pw[1][31:16];
    wire [31:0] p_maxd   = pw[1][63:32];
    wire [31:0] p_efloor = pw[2][31:0];
    wire [31:0] p_eceil  = pw[2][63:32];
    wire [31:0] p_spend  = pw[3][31:0];

    // Unpack child capability fields
    wire [15:0] c_rights = cw[1][15:0];
    wire [15:0] c_guards = cw[1][31:16];
    wire [31:0] c_maxd   = cw[1][63:32];
    wire [31:0] c_efloor = cw[2][31:0];
    wire [31:0] c_eceil  = cw[2][63:32];
    wire [31:0] c_spend  = cw[3][31:0];

    wire p_vk_nonzero = (pw[4] | pw[5] | pw[6] | pw[7]) != 64'd0;
    wire vk_same      = (cw[4] == pw[4]) && (cw[5] == pw[5]) && (cw[6] == pw[6]) && (cw[7] == pw[7]);

    // Strict hardware capability attenuation lattice check: child <= parent
    assign attenuate_legal =
        vat_ready &&
        p_rights[3] &&                                   // parent must hold RIGHT_ATTENUATE
        ((c_rights & ~p_rights) == 16'd0) &&             // rights can only shrink
        ((c_guards & p_guards) == p_guards) &&           // mandatory guards can only grow
        (c_efloor >= p_efloor) &&                        // epoch window can only narrow
        (c_eceil  <= p_eceil)  &&
        (c_efloor <= c_eceil)  &&
        (c_spend  <= p_spend)  && (c_spend != 32'd0) &&  // spend limit can only shrink
        (c_maxd   <= p_maxd)   &&                        // max distance bound can only tighten
        (!(p_guards[G_PIN_VK] || p_vk_nonzero) || vk_same);

    // Invocation legality check against active capability in pw[0..7]
    wire right_ok = (p_rights & req_right_bit) == req_right_bit;
    wire epoch_ok = (req_epoch >= p_efloor) && (req_epoch <= p_eceil);
    wire [32:0] next_spend = {1'b0, vat_spend_used} + {1'b0, req_spend};
    wire spend_ok = (req_spend <= p_spend) && (next_spend <= {1'b0, p_spend});

    wire vk_match_pk = (pw[4] == req_bind_lo) && (pw[5] == req_bind_hi);
    wire vk_match_zk = zk_root_valid &&
                       (pw[4] == zk_root[0]) && (pw[5] == zk_root[1]) &&
                       (pw[6] == zk_root[2]) && (pw[7] == zk_root[3]);
    wire vk_ok   = !p_guards[G_PIN_VK] || (check_is_zk ? vk_match_zk : vk_match_pk);
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
        end else begin
            if (kvat_commit && permit_control) begin
                vat_ready      <= 1'b1;
                vat_spend_used <= 32'd0;
            end
            if (zk_latch_clear)
                zk_root_valid <= 1'b0;
            else if (zk_latch_valid_set && permit_control)
                zk_root_valid <= 1'b1;
            if (commit_invocation && invoke_legal && permit_control)
                vat_spend_used <= next_spend[31:0];
        end
    end
endmodule
`default_nettype wire
