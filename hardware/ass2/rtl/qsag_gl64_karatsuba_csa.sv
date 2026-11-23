// Compact 1-bit/clock (64-step) Iterative Shift-Add Multiplier, 128-step GF(2^128) Accumulator,
// and Shared Upper/Lower 64-bit Cryptographic Scratch (`prod_q[127:64]` doubles as `operand_b`!).
module qsag_gl64_karatsuba_csa (
    input  logic         clk, srst_n,
    input  logic         cancel_i = 1'b0,
    input  logic         start, mode_gl,
    input  logic         gf_clr_i, gf_step_i,
    input  logic [127:0] gf_next_i,
    input  logic         fold_we_i,
    input  logic [63:0]  fold_val_i,
    input  logic         b_we_i = 1'b0,
    input  logic [63:0]  b_val_i = 64'd0,
    input  logic [63:0]  opa, opb, opc,
    output logic         step_active_o,
    output logic [63:0]  mul_add_a_o,
    output logic [63:0]  mul_add_b_o,
    input  logic [63:0]  mul_add_sum_i,
    input  logic         mul_add_cout_i,
    output logic         last,
    output logic [127:0] prod128
);
    logic [6:0]   step_q;
    logic [127:0] prod_q;

    wire [63:0] mc          = mode_gl ? opc : 64'd0;
    wire        step_active = (step_q >= 7'd1) && (step_q <= 7'd64);

    assign step_active_o = step_active;
    assign mul_add_a_o   = prod_q[127:64];
    assign mul_add_b_o   = prod_q[0] ? opa : 64'd0;

    wire lo_en = cancel_i || (step_q == 7'd0 && start) || step_active || gf_clr_i || gf_step_i || fold_we_i;
    wire hi_en = cancel_i || (step_q == 7'd0 && start) || step_active || gf_clr_i || gf_step_i || b_we_i;

    wire [63:0] lo_d = (cancel_i || gf_clr_i) ? 64'd0
                     : gf_step_i   ? gf_next_i[63:0]
                     : fold_we_i   ? fold_val_i
                     : step_active ? {mul_add_sum_i[0], prod_q[63:1]}
                     :               opb;
    wire [63:0] hi_d = (cancel_i || gf_clr_i) ? 64'd0
                     : gf_step_i   ? gf_next_i[127:64]
                     : b_we_i      ? b_val_i
                     : step_active ? {mul_add_cout_i, mul_add_sum_i[63:1]}
                     :               mc;

    qsag_ass2_cg_dff #(.W(64)) u_prod_lo (
        .clk(clk), .rst_n(srst_n), .en(lo_en), .d(lo_d), .q(prod_q[63:0])
    );
    qsag_ass2_cg_dff #(.W(64)) u_prod_hi (
        .clk(clk), .rst_n(srst_n), .en(hi_en), .d(hi_d), .q(prod_q[127:64])
    );

    assign prod128 = prod_q;
    assign last    = (step_q == 7'd65);

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) step_q <= 7'd0;
        else if (cancel_i) step_q <= 7'd0;
        else if (step_q == 7'd0) begin
            if (start) step_q <= 7'd1;
        end else if (step_q <= 7'd64) begin
            step_q <= step_q + 7'd1;
        end else begin
            step_q <= 7'd0;
        end
    end
endmodule
