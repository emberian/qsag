// Serial Ext4 MAC and in-place BRAM fold. Shares the top's single Goldilocks multiplier.
// Every transaction snapshots its operands. A fold consumes one pair before writing its
// result, so in-place writes always trail reads, including the last two-entry fold.
module qsag_ext4_compact_bfly #(parameter int TAW = 12) (
    input logic clk, rst, tw_en,
    input logic [TAW-1:0] tw_idx,
    input logic [255:0] tw_data,
    input logic fold_start,
    input logic [5:0] fold_log2n,
    input logic [255:0] fold_r,
    output logic fold_busy, fold_done,
    output logic [255:0] fold_res,
    input logic mac_valid,
    input logic [255:0] mac_a, mac_b, mac_c,
    output logic mac_done,
    output logic [255:0] mac_y,
    output logic mul_valid,
    input logic mul_ready,
    output logic [63:0] mul_a, mul_b,
    input logic mul_done,
    input logic [63:0] mul_r
);
    localparam logic [63:0] P = qsag_ni_pkg::GL_P;
    typedef enum logic [3:0] {IDLE, READ, LOAD, OFFER, WAIT_MUL, REDUCE, WRITE} state_t;
    state_t st;
    logic [TAW-2:0] pair_idx, last_pair;
    logic [TAW-1:0] write_idx;
    logic [255:0] a, b, c, r_q, ev, od, diff;
    logic [1:0] k, i, count;
    logic [71:0] acc, term, acc_next;
    logic [63:0] reduced;
    logic [1:0] j;
    function automatic logic [1:0] pidx(input logic [1:0] v);
        pidx = {v[0],v[1]};
    endfunction
    assign j = k-i;
    assign mul_a = a[64*pidx(i) +:64];
    assign mul_b = b[64*pidx(j) +:64];
    assign mul_valid = st == OFFER && !rst;
    assign term = i > k ? ((72'(mul_r) << 3) - 72'(mul_r)) : 72'(mul_r);
    qsag_add_split #(.W(72)) u_add (.a(acc), .b(term), .y(acc_next));
    qsag_gl64_reduce u_red (.clk(clk), .x({64'd0,acc}), .r(reduced));
    assign write_idx = {1'b0,pair_idx};
    wire we = st == WRITE;
    wire [TAW-1:0] wa = we ? write_idx : tw_idx;
    wire [255:0] wd = we ? mac_y : tw_data;
    qsag_sdp_bram #(.AW(TAW-1),.DW(256)) u_ev (
        .clk(clk),.we((we || tw_en) && !wa[0]),.wa(wa[TAW-1:1]),.wd(wd),.ra(pair_idx),.rd(ev));
    qsag_sdp_bram #(.AW(TAW-1),.DW(256)) u_od (
        .clk(clk),.we((we || tw_en) && wa[0]),.wa(wa[TAW-1:1]),.wd(wd),.ra(pair_idx),.rd(od));
    for (genvar n=0;n<4;n++) begin : g_sub
        wire [64:0] d = {1'b0,od[64*n +:64]} - {1'b0,ev[64*n +:64]};
        assign diff[64*n +:64] = d[64] ? d[63:0]+P : d[63:0];
    end
    always_ff @(posedge clk) begin
        fold_done <= 1'b0; mac_done <= 1'b0;
        if (rst) begin st <= IDLE; fold_busy <= 0; end
        else case (st)
            IDLE: if (fold_start) begin
                fold_busy <= 1; pair_idx <= 0;
                last_pair <= (TAW-1)'((64'd1 << (fold_log2n-1'b1))-1'b1);
                r_q <= fold_r; st <= READ;
            end else if (mac_valid) begin
                a <= mac_a; b <= mac_b; c <= mac_c;
                k <= 0; i <= 0; acc <= 72'(mac_c[63:0]); st <= OFFER;
            end
            READ: st <= LOAD;
            LOAD: begin
                a <= r_q; b <= diff; c <= ev; k <= 0; i <= 0; acc <= 72'(ev[63:0]); st <= OFFER;
            end
            OFFER: if (mul_ready) st <= WAIT_MUL;
            WAIT_MUL: if (mul_done) begin
                acc <= acc_next;
                if (i == 3) begin count <= 0; st <= REDUCE; end
                else begin i <= i+1'b1; st <= OFFER; end
            end
            REDUCE: if (count == 2) begin
                mac_y[64*pidx(k) +:64] <= reduced;
                if (k == 3) begin
                    if (fold_busy) st <= WRITE;
                    else begin mac_done <= 1; st <= IDLE; end
                end else begin
                    k <= k+1'b1; i <= 0; acc <= 72'(c[64*pidx(k+2'd1) +:64]); st <= OFFER;
                end
            end else count <= count+1'b1;
            WRITE: begin
                fold_res <= mac_y;
                if (pair_idx == last_pair) begin fold_busy <= 0; fold_done <= 1; st <= IDLE; end
                else begin pair_idx <= pair_idx+1'b1; st <= READ; end
            end
            default: st <= IDLE;
        endcase
    end
endmodule
