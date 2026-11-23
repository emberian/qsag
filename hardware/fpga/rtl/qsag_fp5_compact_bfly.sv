// Each issue consumes one b coefficient and one or five cyclic convolution terms.
// A and 3*A share a write address. R uses the same storage while folding.
module qsag_fp5_compact_bfly #(
    parameter int TAW = 11, AW = 16, BW = 16,
    parameter bit PARALLEL_5 = 1'b0
) (
    input logic clk, rst, tw_en,
    input logic [TAW-1:0] tw_idx,
    input logic [319:0] tw_data,
    input logic fold_start, mac_valid,
    input logic [5:0] fold_log2n,
    output logic fold_busy, fold_done, mac_done,
    input logic in_lane_we,
    input logic [1:0] in_sel,
    input logic [2:0] in_lane_idx,
    input logic [63:0] in_lane_data,
    output logic out_lane_valid,
    output logic [2:0] out_lane_idx,
    output logic [63:0] out_lane_data
);
    localparam logic [63:0] P = qsag_ni_pkg::GL_P;
    localparam int ML = qsag_ni_pkg::GL_MUL_LAT;
    localparam int LANES = PARALLEL_5 ? 5 : 1;

    function automatic [63:0] triple(input logic [63:0] x);
        logic [65:0] t;
        t = {1'b0,x,1'b0} + {2'b0,x};
        if (t >= 66'(P)*2) triple = 64'(t - 66'(P)*2);
        else if (t >= 66'(P)) triple = 64'(t - 66'(P));
        else triple = t[63:0];
    endfunction

    typedef enum logic [2:0] {IDLE, READ_PAIR, LOAD_PAIR, ISSUE, DRAIN, EMIT} state_t;
    state_t state;
    logic [TAW-2:0] pair_idx, last_pair;
    logic [2:0] k, j, limb;
    logic [63:0] a[5], a3[5], b[5], c[5], result[5], ev[5], od[5];
    logic [ML-1:0] valid_q, first_q, last_q, finish_q;
    logic [2:0] target_q[ML];
    wire issue = state == ISSUE;
    wire last_issue = j == 4 && (PARALLEL_5 || k == 4);
    wire storing = state == EMIT && fold_busy;
    wire [TAW-1:0] wr_addr = storing ? {1'b0,pair_idx} : tw_idx;
    for (genvar n=0; n<5; n++) begin : g_table
        wire we = storing ? limb == n : tw_en;
        wire [63:0] wd = storing ? result[n] : tw_data[64*n+:64];
        qsag_sdp_bram #(.AW(TAW-1),.DW(64),.NO_RW_CHECK(1),.FORCE_BRAM(1)) u_ev
            (.clk,.we(we && !wr_addr[0]),.wa(wr_addr[TAW-1:1]),.wd,.ra(pair_idx),.rd(ev[n]));
        qsag_sdp_bram #(.AW(TAW-1),.DW(64),.NO_RW_CHECK(1),.FORCE_BRAM(1)) u_od
            (.clk,.we(we && wr_addr[0]),.wa(wr_addr[TAW-1:1]),.wd,.ra(pair_idx),.rd(od[n]));
    end
    wire [64:0] diff = {1'b0,od[limb]} - {1'b0,ev[limb]};
    always_ff @(posedge clk) begin
        if (in_lane_we && (in_sel == 0 || in_sel == 3)) begin
            a[in_lane_idx] <= in_lane_data;
            a3[in_lane_idx] <= triple(in_lane_data);
        end
        if (state == LOAD_PAIR) begin
            b[limb] <= diff[64] ? diff[63:0] + P : diff[63:0];
            c[limb] <= ev[limb];
        end else if (in_lane_we) begin
            if (in_sel == 1) b[in_lane_idx] <= in_lane_data;
            if (in_sel == 2) c[in_lane_idx] <= in_lane_data;
        end
        target_q[0] <= k;
        for (int i=1; i<ML; i++) target_q[i] <= target_q[i-1];
        valid_q <= {valid_q[ML-2:0],issue && !rst};
        if (rst) valid_q <= '0;
        first_q <= {first_q[ML-2:0],j == 0};
        last_q <= {last_q[ML-2:0],j == 4};
        finish_q <= {finish_q[ML-2:0],last_issue};
    end

    for (genvar n=0; n<LANES; n++) begin : g_mul
        wire [2:0] dest = PARALLEL_5 ? 3'(n) : k;
        wire wrap = dest < j;
        wire [2:0] i = dest - j + (wrap ? 3'd5 : 3'd0);
        logic [63:0] product;
        qsag_gl64_dsp_mul #(.AW(AW),.BW(BW),.REG_OUT(1)) u_mul
            (.clk,.a(wrap ? a3[i] : a[i]),.b(b[j]),.r(product));
        wire [2:0] dest_out = PARALLEL_5 ? 3'(n) : target_q[ML-1];
        logic [63:0] acc;
        wire [63:0] prev = first_q[ML-1] ? c[dest_out] : acc;
        wire [64:0] sum = {1'b0,prev} + {1'b0,product};
        wire [63:0] reduced = sum >= {1'b0,P} ? sum[63:0] - P : sum[63:0];
        always_ff @(posedge clk) if (valid_q[ML-1]) begin
            acc <= reduced;
            if (last_q[ML-1]) result[dest_out] <= reduced;
        end
    end
    assign out_lane_valid = state == EMIT && (!fold_busy || pair_idx == last_pair);
    assign out_lane_idx = limb;
    assign out_lane_data = result[limb];
    assign mac_done = state == EMIT && !fold_busy && limb == 4;
    assign fold_done = state == EMIT && fold_busy && pair_idx == last_pair && limb == 4;

    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            fold_busy <= 0;
        end else case (state)
            IDLE: begin
                k <= 0;
                j <= 0;
                if (fold_start) begin
                    fold_busy <= 1;
                    pair_idx <= 0;
                    last_pair <= (TAW-1)'((64'd1 << (fold_log2n-1)) - 1);
                    state <= READ_PAIR;
                end else if (mac_valid) state <= ISSUE;
            end
            READ_PAIR: begin limb <= 0; state <= LOAD_PAIR; end
            LOAD_PAIR: begin
                limb <= limb + 1'b1;
                if (limb == 4) begin k <= 0; j <= 0; state <= ISSUE; end
            end
            ISSUE: begin
                j <= j == 4 ? 0 : j + 1'b1;
                if (j == 4) k <= k + 1'b1;
                if (last_issue) state <= DRAIN;
            end
            DRAIN: if (valid_q[ML-1] && finish_q[ML-1]) begin limb <= 0; state <= EMIT; end
            EMIT: begin
                limb <= limb + 1'b1;
                if (limb == 4) begin
                    if (fold_busy && pair_idx != last_pair) begin
                        pair_idx <= pair_idx + 1'b1;
                        state <= READ_PAIR;
                    end else begin fold_busy <= 0; state <= IDLE; end
                end
            end
            default: state <= IDLE;
        endcase
    end
endmodule
