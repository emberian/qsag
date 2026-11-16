// QSAG-NI-180 GF(2^128) polynomial accumulator, modulus g(z) = z^128 + z^7 + z^2 + z + 1
// (bit i of a word is the coefficient of z^i, as in qsag-asm).
//
//   acc <- (acc ^ in) * h        one Horner step of a polynomial MAC, 128/D clocks
//
// Digit-serial, most significant digit first: r <- r * z^D + h * digit, reduced each step.
// D = 16 gives the 8-clock multiply; the chip uses D = 2 (64 clocks) to stay inside its area
// budget, the multiply not being on any throughput-critical path.
`default_nettype none

// One digit step: r * z^D + h * d  (mod g). Purely combinational; the unit proven in lec/.
module qsag_gf128_step #(
    parameter int D = 4
) (
    input  wire [127:0]  r,
    input  wire [127:0]  h,
    input  wire [D-1:0]  d,
    output wire [127:0]  o
);
    logic [127+D:0] t;
    logic [D+7:0]   f;
    always_comb begin
        t = {r, {D{1'b0}}};
        for (int i = 0; i < D; i++) if (d[i]) t = t ^ ({{D{1'b0}}, h} << i);
        // fold the D overflow coefficients with z^128 = z^7 + z^2 + z + 1
        f = '0;
        for (int i = 0; i < D; i++) if (t[128+i]) f = f ^ ((D + 8)'(8'h87) << i);
    end
    assign o = t[127:0] ^ 128'(f);
endmodule

module qsag_gf128_clmul #(
    parameter int D = 2
) (
    input  wire          clk,
    input  wire          rst_n,   // control reset
    input  wire          srst_n,  // secret clear
    input  wire          clr,     // acc <- 0
    input  wire          start,   // acc <- (acc ^ {in_hi, in_lo}) * h
    input  wire [127:0]  in,
    input  wire [127:0]  h,
    output wire          busy,
    output logic         done,
    output wire [127:0]  acc
);
    localparam int STEPS = 128 / D;
    logic [127:0] x, r;
    logic [7:0]   cnt;
    logic         run;
    wire  [127:0] step_o;

    qsag_gf128_step #(.D(D)) u_step (.r(r), .h(h), .d(x[127 -: D]), .o(step_o));

    assign busy = run;
    assign acc  = r;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            run  <= 1'b0;
            done <= 1'b0;
            cnt  <= '0;
        end else begin
            done <= 1'b0;
            if (!run && start) begin
                run <= 1'b1;
                cnt <= '0;
            end else if (run) begin
                cnt <= cnt + 8'd1;
                if (cnt == 8'(STEPS - 1)) begin
                    run  <= 1'b0;
                    done <= 1'b1;
                end
            end
        end
    end

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            x <= '0;
            r <= '0;
        end else if (clr) begin
            r <= '0;
        end else if (!run && start) begin
            x <= r ^ in;
            r <= '0;
        end else if (run) begin
            r <= step_o;
            x <= {x[127-D:0], {D{1'b0}}};
        end
    end
endmodule

// Bit-serial specification of the same field product, for the formal proofs only.
module qsag_gf128_ref (
    input  wire [127:0] a,
    input  wire [127:0] b,
    output logic [127:0] p
);
    logic [127:0] v;
    always_comb begin
        p = '0;
        v = a;
        for (int i = 0; i < 128; i++) begin
            if (b[i]) p = p ^ v;
            v = {v[126:0], 1'b0} ^ (v[127] ? 128'h87 : 128'h0);
        end
    end
endmodule
`default_nettype wire
