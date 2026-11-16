// Canonical width-12 Goldilocks Poseidon2 (crates/qsag-accel poseidon2_perm12: R_F = 8,
// R_P = 22, x^7, M_E = M4 (x) P3, M_I = J + diag(-64, 1, 2, ..., 1024)) as an area-compact
// folded core: ONE round stage (12 S-box lanes on external rounds, lane 0 alone on the 22
// internal rounds, zero-multiplier linear layers) closed into a ring of P2_RING_LEN stages.
//
// A permutation is a token that goes round the ring P2_PASSES = 31 times (pass 0 is the initial
// M_E, passes 1..4 and 27..30 the external rounds, 5..26 the internal rounds). The ring is
// C-slow: every one of its P2_RING_LEN stages can hold an independent permutation, so up to
// P2_RING_LEN jobs are in flight on the same 576 DSP slices. Latency P2_PASSES * P2_RING_LEN
// clocks per job, throughput one permutation per 31 clocks when the ring is full.
//
// `in_jive` selects the weighted feed-forward compression of Canopy and fixed-tweak Merkle
// nodes: with in_state = [l0..l3, r0..r3, t0..t3], out_state[64*i +: 64] for i < 4 is
// perm(in)[i] + l_i + 2*r_i + 4*t_i (mod p). The feed-forward rides the final lazy reduction.
// Inputs may be any 64-bit values; outputs are canonical.
module qsag_poseidon2_12_fpga #(
    parameter int TAGW = 8,
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic            clk,
    input  logic            rst,
    input  logic            in_valid,
    output logic            in_ready,
    input  logic [767:0]    in_state,
    input  logic            in_jive,
    input  logic [TAGW-1:0] in_tag,
    output logic            out_valid,
    output logic [767:0]    out_state,
    output logic            out_jive,
    output logic [TAGW-1:0] out_tag,
    output logic            busy
);
    localparam int P2_SBOX_LAT = qsag_ni_pkg::P2_SBOX_LAT;
    localparam int P2_LIN_LAT = qsag_ni_pkg::P2_LIN_LAT;
    localparam int FFW = 4 * 67;
    localparam int MW  = 5 + 1 + TAGW + FFW;   // pass, jive, tag, feed-forward
    localparam int DL  = P2_SBOX_LAT + P2_LIN_LAT;

    // Entry register of the ring.
    logic           e_valid;
    logic [MW-1:0]  e_meta;
    logic [767:0]   e_state;

    // Token metadata alongside the round stage.
    logic [DL-1:0]    v_sr;
    logic [DL*MW-1:0] m_sr;
    always_ff @(posedge clk) begin
        if (rst) v_sr <= '0;
        else     v_sr <= {v_sr[DL-2:0], e_valid};
        m_sr <= {m_sr[(DL-1)*MW-1:0], e_meta};
    end

    // Precompute linear-layer controls one clock before the S-box / linear boundary
    // (`m_sr[(P2_SBOX_LAT-2)*MW +: MW]`, since P2_SBOX_LAT = 13 >= 2) and register them so
    // the 31-entry round-constant ROM and muxes never add depth to `qsag_p2_linear` Stage 1.
    logic [MW-1:0]    pre_meta;
    logic [4:0]       pre_pass;
    logic             pre_jive;
    logic [FFW-1:0]   pre_ff;
    assign pre_meta = m_sr[(P2_SBOX_LAT-2)*MW +: MW];
    assign pre_pass = pre_meta[MW-1 -: 5];
    assign pre_jive = pre_meta[MW-6];
    assign pre_ff   = pre_meta[FFW-1:0];

    logic             pre_mi;
    logic [1:0]       pre_sel, mid_sel;
    logic             lin_mi;
    assign pre_mi  = (pre_pass >= 5'd5) && (pre_pass <= 5'd26);
    assign pre_sel = (pre_pass == 5'd0) ? 2'd0 : (pre_mi ? 2'd1 : 2'd2);

    logic [767:0] rc;
    qsag_p2_rc u_rc (.pass(pre_pass), .rc(rc));

    logic [12*67-1:0] pre_addend, lin_addend;
    always_comb begin
        for (int i = 0; i < 12; i++) pre_addend[67*i +: 67] = 67'(rc[64*i +: 64]);
        if (pre_pass == 5'd30) begin
            pre_addend = '0;
            if (pre_jive) pre_addend[FFW-1:0] = pre_ff;
        end
    end

    always_ff @(posedge clk) begin
        mid_sel    <= pre_sel;
        lin_mi     <= pre_mi;
        lin_addend <= pre_addend;
    end

    logic [767:0] r_state;
    qsag_p2_round #(.KIND(0), .AW(AW), .BW(BW)) u_round (
        .clk(clk), .in_state(e_state), .mid_sel(mid_sel), .lin_mi(lin_mi),
        .lin_addend(lin_addend), .out_state(r_state));

    // Token leaving the round stage.
    logic            r_valid;
    logic [MW-1:0]   r_meta;
    logic [4:0]      r_pass;
    logic            recirc;
    assign r_valid = v_sr[DL-1];
    assign r_meta  = m_sr[(DL-1)*MW +: MW];
    assign r_pass  = r_meta[MW-1 -: 5];
    assign recirc  = r_valid && (r_pass != 5'd30);
    assign in_ready = !recirc && !rst;

    // Shallow CSA + split-add feed-forward of a new job: l + 2r + 4t, below 7 * 2^64.
    logic [FFW-1:0] in_ff;
    for (genvar i = 0; i < 4; i++) begin : g_ff
        wire [3*67-1:0] ff_terms = {
            67'(in_state[64*(8 + i) +: 64]) << 2,
            67'(in_state[64*(4 + i) +: 64]) << 1,
            67'(in_state[64*i       +: 64])
        };
        qsag_sum_csa #(.W(67), .N(3), .CHUNK(24)) u_ff (
            .x(ff_terms), .y(in_ff[67*i +: 67]));
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            e_valid   <= 1'b0;
            out_valid <= 1'b0;
        end else begin
            e_valid   <= recirc || in_valid;
            out_valid <= r_valid && !recirc;
        end
        if (recirc) begin
            e_meta  <= {r_pass + 5'd1, r_meta[MW-6:0]};
            e_state <= r_state;
        end else begin
            e_meta  <= {5'd0, in_jive, in_tag, in_ff};
            e_state <= in_state;
        end
        out_state <= r_state;
        out_jive  <= r_meta[MW-6];
        out_tag   <= r_meta[FFW +: TAGW];
    end

    assign busy = e_valid || (|v_sr) || out_valid;
endmodule
