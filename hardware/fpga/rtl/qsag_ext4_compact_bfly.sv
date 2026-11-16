// Pipelined single-multiplier Ext4 MAC and in-place BRAM fold for ECP5_COMPACT.
// Instantiates ONE dedicated pipelined Goldilocks multiplier (`qsag_gl64_dsp_mul`: 16 MULT18X18D),
// streaming all 16 limb products at 1 product/clock (24 clocks per Ext4 MAC vs 125 clocks stalled)
// with registered BRAM read outputs and shallow CSA + split-carry accumulators (<= 16 levels).
module qsag_ext4_compact_bfly #(
    parameter int TAW = 11,
    parameter int AW  = 16,
    parameter int BW  = 16
) (
    input  logic           clk,
    input  logic           rst,
    input  logic           tw_en,
    input  logic [TAW-1:0] tw_idx,
    input  logic [255:0]   tw_data,
    input  logic           fold_start,
    input  logic [5:0]     fold_log2n,
    input  logic [255:0]   fold_r,
    output logic           fold_busy,
    output logic           fold_done,
    output logic [255:0]   fold_res,
    input  logic           mac_valid,
    input  logic [255:0]   mac_a,
    input  logic [255:0]   mac_b,
    input  logic [255:0]   mac_c,
    output logic           mac_done,
    output logic [255:0]   mac_y
);
    localparam logic [63:0] GL_P   = qsag_ni_pkg::GL_P;
    localparam int          ML     = qsag_ni_pkg::GL_MUL_LAT; // 5
    localparam logic [71:0] BIAS_P = {8'b0, GL_P};            // p == 0 (mod p), ensures 8x - x + p > 0

    typedef enum logic [2:0] {IDLE, RD_WAIT, RD_REG, SUB_REG, STREAM_MAC, WRITE} state_t;
    state_t st;

    logic [TAW-2:0] pair_idx, last_pair;
    logic [255:0]   a_q, b_q, c_q, r_q, ev_rd, od_rd, ev_q, od_q;
    logic [4:0]     step;
    logic [71:0]    acc_q, red_in_q;
    logic [63:0]    mul_r, red_r;

    // Polynomial limb permutation: [0, 2, 1, 3] is an involution ({v[0], v[1]}? Wait:
    // v=0->0, v=1->2, v=2->1, v=3->3: that IS {v[0], v[1]}!).
    function automatic logic [1:0] pidx(input logic [1:0] v);
        pidx = {v[0], v[1]};
    endfunction

    // During STREAM_MAC, step = 0..15 issues (i = step[1:0], k = step[3:2], j = k - i).
    wire [1:0] in_k = step[3:2];
    wire [1:0] in_i = step[1:0];
    wire [1:0] in_j = in_k - in_i;

    qsag_gl64_dsp_mul #(.AW(AW), .BW(BW)) u_mul (
        .clk(clk),
        .a(a_q[64*pidx(in_i) +: 64]),
        .b(b_q[64*pidx(in_j) +: 64]),
        .r(mul_r));

    // Product arrives at step_out = step - ML (for step >= ML, step < ML + 16).
    wire [4:0] out_step = step - 5'(ML);
    wire [1:0] out_k    = out_step[3:2];
    wire [1:0] out_i    = out_step[1:0];
    wire       out_wrap = (out_i > out_k);

    // Shallow carry-save accumulation: base = (out_i == 0) ? c_q[pidx(out_k)] : acc_q.
    // If out_wrap (weight 7): base + 8*mul_r + ~mul_r + 1 + BIAS_P (since ~mul_r + 1 mod 2^72 = -mul_r,
    // and 8*mul_r - mul_r >= 0 for all mul_r >= 0!).
    wire [71:0] acc_base = (out_i == 2'd0) ? 72'(c_q[64*pidx(out_k) +: 64]) : acc_q;
    wire [4*72-1:0] acc_terms = out_wrap
        ? {72'd1, ~{8'd0, mul_r}, {5'd0, mul_r, 3'd0}, acc_base}
        : {72'd0, 72'd0,          {8'd0, mul_r},       acc_base};
    logic [71:0] acc_next;
    qsag_sum_csa #(.W(72), .N(4), .CHUNK(24)) u_acc (.x(acc_terms), .y(acc_next));

    // When out_i == 3 (at step = ML + 3, ML + 7, ML + 11, ML + 15), red_in_q latches acc_next;
    // 2 clocks later (step = ML + 6, ML + 10, ML + 14, ML + 18), red_r holds canonical mac_y limb!
    qsag_gl64_reduce u_red (.clk(clk), .x({64'd0, red_in_q}), .r(red_r));
    wire [4:0] red_step = step - 5'(ML + 6);
    wire [1:0] red_k    = red_step[3:2];

    wire           we_int = (st == WRITE);
    wire [TAW-1:0] wr_idx = we_int ? {1'b0, pair_idx} : tw_idx;
    wire [255:0]   wr_dat = we_int ? mac_y : tw_data;

    qsag_sdp_bram #(.AW(TAW-1), .DW(256)) u_ev (
        .clk(clk), .we((we_int || tw_en) && !wr_idx[0]),
        .wa(wr_idx[TAW-1:1]), .wd(wr_dat), .ra(pair_idx), .rd(ev_rd));
    qsag_sdp_bram #(.AW(TAW-1), .DW(256)) u_od (
        .clk(clk), .we((we_int || tw_en) &&  wr_idx[0]),
        .wa(wr_idx[TAW-1:1]), .wd(wr_dat), .ra(pair_idx), .rd(od_rd));

    // Shallow parallel modular subtraction on REGISTERED BRAM outputs (ev_q, od_q) -> diff_d.
    logic [255:0] diff_d;
    for (genvar n = 0; n < 4; n++) begin : g_sub
        wire [63:0] od_n = od_q[64*n +: 64];
        wire [63:0] ev_n = ev_q[64*n +: 64];
        /* verilator lint_off UNUSEDSIGNAL */
        logic [64:0] dr, dp;
        /* verilator lint_on UNUSEDSIGNAL */
        qsag_sum_csa #(.W(65), .N(3), .CHUNK(24)) u_dr (
            .x({65'd1, ~{1'b0, ev_n}, {1'b0, od_n}}), .y(dr));
        qsag_sum_csa #(.W(65), .N(3), .CHUNK(24)) u_dp (
            .x({{1'b0, GL_P} + 65'd1, ~{1'b0, ev_n}, {1'b0, od_n}}), .y(dp));
        assign diff_d[64*n +: 64] = dr[64] ? dp[63:0] : dr[63:0];
    end
    logic unused_bias;
    assign unused_bias = &{1'b0, BIAS_P};

    always_ff @(posedge clk) begin
        fold_done <= 1'b0;
        mac_done  <= 1'b0;
        if (rst) begin
            st        <= IDLE;
            fold_busy <= 1'b0;
        end else begin
            case (st)
                IDLE: begin
                    if (fold_start) begin
                        fold_busy <= 1'b1;
                        pair_idx  <= '0;
                        last_pair <= (TAW-1)'((64'd1 << (fold_log2n - 6'd1)) - 64'd1);
                        r_q       <= fold_r;
                        st        <= RD_WAIT;
                    end else if (mac_valid) begin
                        a_q  <= mac_a;
                        b_q  <= mac_b;
                        c_q  <= mac_c;
                        step <= 5'd0;
                        st   <= STREAM_MAC;
                    end
                end
                RD_WAIT: st <= RD_REG;
                RD_REG: begin
                    ev_q <= ev_rd;
                    od_q <= od_rd;
                    st   <= SUB_REG;
                end
                SUB_REG: begin
                    a_q  <= r_q;
                    b_q  <= diff_d;
                    c_q  <= ev_q;
                    step <= 5'd0;
                    st   <= STREAM_MAC;
                end
                STREAM_MAC: begin
                    if (step >= 5'(ML) && step < 5'(ML + 16)) begin
                        acc_q <= acc_next;
                        if (out_i == 2'd3) red_in_q <= acc_next;
                    end
                    if (step >= 5'(ML + 6) && red_step[1:0] == 2'd0) begin
                        mac_y[64*pidx(red_k) +: 64] <= red_r;
                    end
                    if (step == 5'(ML + 18)) begin
                        if (fold_busy) begin
                            st <= WRITE;
                        end else begin
                            mac_done <= 1'b1;
                            st       <= IDLE;
                        end
                    end else begin
                        step <= step + 5'd1;
                    end
                end
                WRITE: begin
                    fold_res <= mac_y;
                    if (pair_idx == last_pair) begin
                        fold_busy <= 1'b0;
                        fold_done <= 1'b1;
                        st        <= IDLE;
                    end else begin
                        pair_idx <= pair_idx + (TAW-1)'(1);
                        st       <= RD_WAIT;
                    end
                end
                default: st <= IDLE;
            endcase
        end
    end
    logic unused_dq;
    assign unused_dq = &{1'b0, out_step[4], red_step[4]};
endmodule
