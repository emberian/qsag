// Poseidon2 width-12 linear layers with zero multipliers and one lazy reduction per lane.
//
//   M_E = M4 (x) P3 : M4 on the lane triples (0,3,6,9), (1,4,7,10), (2,5,8,11), then every
//                     contiguous triple gets its own sum added (crates/qsag-accel poseidon2_apply_me).
//   M_I = J + diag(-64, 1, 2, 4, ..., 1024).
//
// Both are evaluated over the integers with shifts and adds only (lane weights sum to at most
// 28 for M_E and 2^10 + 12 for M_I), a 67-bit addend (next round constants, or the weighted
// feed-forward l + 2r + 4t) joins the same carry-save sum, and the 76-bit result is reduced once:
//   lo + t*2^64 = lo + t*(2^32 - 1)  (mod p),  t < 2^12, followed by one conditional subtract.
// Inputs may be any 64-bit values; outputs are canonical. Latency P2_LIN_LAT = 2.
// FIXED = 0 builds M_E only, FIXED = 1 builds M_I only, FIXED = -1 selects per cycle with `mi`.
module qsag_p2_linear #(
    parameter int FIXED = -1
) (
    input  logic            clk,
    input  logic [767:0]    x,
    input  logic            mi,
    input  logic [12*67-1:0] addend,
    output logic [767:0]    y
);
    localparam logic [63:0] GL_P = qsag_ni_pkg::GL_P;
    localparam int LW = 76;

    logic unused_ok;
    assign unused_ok = &{1'b0, mi};

    logic [12*LW-1:0] sel;

    if (FIXED != 1) begin : g_me
        logic [12*LW-1:0] me;
        // m4[c][k]: row k of M4 on column c, 67 bits.
        logic [12*67-1:0] m4;
        for (genvar c = 0; c < 3; c++) begin : g_col
            logic [66:0] b0, b1, b2, b3, s;
            assign b0 = 67'(x[64*(c)     +: 64]);
            assign b1 = 67'(x[64*(c + 3) +: 64]);
            assign b2 = 67'(x[64*(c + 6) +: 64]);
            assign b3 = 67'(x[64*(c + 9) +: 64]);
            assign s  = b0 + b1 + b2 + b3;
            assign m4[67*(4*c + 0) +: 67] = s + b0 + (b1 << 1);
            assign m4[67*(4*c + 1) +: 67] = s + b1 + (b2 << 1);
            assign m4[67*(4*c + 2) +: 67] = s + b2 + (b3 << 1);
            assign m4[67*(4*c + 3) +: 67] = s + b3 + (b0 << 1);
        end
        for (genvar k = 0; k < 4; k++) begin : g_row
            logic [LW-1:0] t;
            assign t = LW'(m4[67*(k) +: 67]) + LW'(m4[67*(4 + k) +: 67]) + LW'(m4[67*(8 + k) +: 67]);
            for (genvar c = 0; c < 3; c++) begin : g_out
                assign me[LW*(3*k + c) +: LW] = t + LW'(m4[67*(4*c + k) +: 67]);
            end
        end
    end

    if (FIXED != 0) begin : g_mi
        logic [12*LW-1:0] mi_s;
        logic [LW-1:0] s;
        always_comb begin
            s = '0;
            for (int i = 0; i < 12; i++) s = s + LW'(x[64*i +: 64]);
        end
        // -64*x0 as 64*(2p - x0): non-negative for every 64-bit x0.
        logic [65:0] neg0;
        assign neg0 = {1'b0, GL_P, 1'b0} - 66'(x[63:0]);
        assign mi_s[0 +: LW]  = s + (LW'(neg0) << 6);
        assign mi_s[LW +: LW] = s + LW'(x[64 +: 64]);
        for (genvar i = 2; i < 12; i++) begin : g_lane
            assign mi_s[LW*i +: LW] = s + (LW'(x[64*i +: 64]) << (i - 1));
        end
    end

    if (FIXED == 0)      begin : g_sel_me assign sel = g_me.me;   end
    else if (FIXED == 1) begin : g_sel_mi assign sel = g_mi.mi_s; end
    else                 begin : g_sel_dy assign sel = mi ? g_mi.mi_s : g_me.me; end

    logic [12*LW-1:0] lazy_q;
    for (genvar i = 0; i < 12; i++) begin : g_red
        always_ff @(posedge clk) lazy_q[LW*i +: LW] <= sel[LW*i +: LW] + LW'(addend[67*i +: 67]);

        logic [63:0] lo;
        logic [11:0] t;
        logic [64:0] r;
        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] rm;
        /* verilator lint_on UNUSEDSIGNAL */
        assign {t, lo} = lazy_q[LW*i +: LW];
        assign r  = {1'b0, lo} + {21'b0, t, 32'b0} - 65'(t);
        assign rm = {1'b0, r} - {2'b0, GL_P};
        always_ff @(posedge clk) y[64*i +: 64] <= rm[65] ? r[63:0] : rm[63:0];
    end
endmodule
