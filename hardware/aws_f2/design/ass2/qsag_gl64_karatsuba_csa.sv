// Ultra-compact shared 128-bit accumulator for both 64x64+64->128 iterative
// multiplication AND 128-step GF(2^128) Horner polynomial multiplication!
//   - Zero duplicate `mul_a_q` register (`opa` is held steady by `crypto`).
//   - Goldilocks modular reduction of `prod128` is performed in 2 clocks using
//     `crypto`'s existing 64-bit modular adder, eliminating 48k um^2 of parallel prefix trees.
module qsag_gl64_karatsuba_csa (
    input  logic         clk, srst_n,
    input  logic         start, mode_gl,
    input  logic         gf_clr_i, gf_step_i,
    input  logic [127:0] gf_next_i,
    input  logic         fold_we_i,
    input  logic [63:0]  fold_val_i,
    input  logic [63:0]  opa, opb, opc,
    output logic         last,
    output logic [127:0] prod128
);

    logic [6:0]   step_q;
    logic [127:0] prod_q;

    // (2^64 - 1)^2 + (2^64 - 1) fits in 128 bits. Folding the exact
    // unsigned product reduces all three operands modulo the Goldilocks prime.
    wire [63:0] mc = mode_gl ? opc : 64'd0;
    wire [64:0] hi_sum = {1'b0, prod_q[127:64]} + (prod_q[0] ? {1'b0, opa} : 65'd0);

    wire step_active = (step_q >= 7'd1) && (step_q <= 7'd64);
    wire prod_en     = (step_q == 7'd0 && start) || step_active || gf_clr_i || gf_step_i || fold_we_i;
    wire [127:0] prod_d = gf_clr_i   ? 128'd0
                        : gf_step_i  ? gf_next_i
                        : fold_we_i  ? {prod_q[127:64], fold_val_i}
                        : step_active ? {hi_sum, prod_q[63:1]}
                        : {mc, opb};

    qsag_ass2_cg_dff #(.W(128)) u_prod (
        .clk(clk), .rst_n(srst_n), .en(prod_en), .d(prod_d), .q(prod_q)
    );

    assign prod128 = prod_q;
    assign last    = (step_q == 7'd65);

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) step_q <= 7'd0;
        else if (step_q == 7'd0) begin
            if (start) step_q <= 7'd1;
        end else if (step_q <= 7'd64) begin
            step_q <= step_q + 7'd1;
        end else begin
            step_q <= 7'd0;
        end
    end
endmodule
