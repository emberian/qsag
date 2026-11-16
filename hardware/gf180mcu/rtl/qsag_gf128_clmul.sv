// Dregg-180 (QSAG-NI-180) GF(2^128) polynomial accumulator, g(z) = z^128 + z^7 + z^2 + z + 1.
//
// Digit-serial Horner step: acc <- (acc ^ in) * h in 128/D clocks.
// Uses clock-gated secret-cleared registers (qsag_ereg) to eliminate 256 recirculation muxes.
`default_nettype none

module qsag_gf128_step #(
    parameter int D = 4
) (
    input  wire [127:0] r,
    input  wire [127:0] h,
    input  wire [D-1:0] d,
    output wire [127:0] o
);
    logic [127+D:0] t;
    logic [D+7:0]   f;
    always_comb begin
        t = {r, {D{1'b0}}};
        for (int i = 0; i < D; i++) if (d[i]) t = t ^ ({{D{1'b0}}, h} << i);
        f = '0;
        for (int i = 0; i < D; i++) if (t[128+i]) f = f ^ ((D + 8)'(8'h87) << i);
    end
    assign o = t[127:0] ^ 128'(f);
endmodule

module qsag_gf128_clmul #(
    parameter int D = 4
) (
    input  wire          clk,
    input  wire          rst_n,   // control reset
    input  wire          srst_n,  // secret clear
    input  wire          clr,     // acc <- 0
    input  wire          start,   // acc <- (acc ^ in) * h
    input  wire [127:0]  in,
    input  wire [127:0]  h,
    output wire          busy,
    output logic         done,
    output wire [127:0]  acc
);
    localparam int STEPS = 128 / D;
    wire  [127:0] x, r;
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

    wire         x_en = (!clr && !run && start) || (!clr && run);
    wire [127:0] x_d  = (!run && start) ? (r ^ in) : {x[127-D:0], {D{1'b0}}};
    wire         r_en = clr || (!run && start) || run;
    wire [127:0] r_d  = (clr || (!run && start)) ? 128'd0 : step_o;

    qsag_ereg #(.W(128)) u_x (.clk(clk), .rst_n(srst_n), .en(x_en), .d(x_d), .q(x));
    qsag_ereg #(.W(128)) u_r (.clk(clk), .rst_n(srst_n), .en(r_en), .d(r_d), .q(r));
endmodule

module qsag_gf128_ref (
    input  wire  [127:0] a,
    input  wire  [127:0] b,
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
