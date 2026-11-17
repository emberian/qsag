// Area proxy (from the architecture lane's skeleton, not simulated): clock, reset and tamper unit of the v2 architecture without the tunable oscillator:
// pad clock selected by a strap, a free-running reference (input `osc`, the ring itself is a few cells),
// frequency-window and loss-of-clock detector, reset synchronisers, secret-reset latch with tamper blanking.
// The shield / canary block (existing dregg_shield_canaries, 16,058 um^2) is separate.
`default_nettype none
module px_clkmon (
    input  wire clk_pad, osc, rst_n_pad, strap_osc, tamper_n, prov, zeroize, sensor_evt,
    input  wire [11:0] win_lo, win_hi,
    output wire clk_core,
    output logic rst_core_n, secret_rst_n,
    output logic clk_fault, tamper_latched,
    output wire [15:0] diag
);
    // strap-selected clock (combinational select at reset; a glitch-free mux is two gated flops per side)
    logic ga, gb, ga_s, gb_s;
    always_ff @(negedge clk_pad or negedge rst_n_pad) if (!rst_n_pad) {ga, ga_s} <= 2'b00; else {ga, ga_s} <= {ga_s, ~strap_osc & ~gb};
    always_ff @(negedge osc or negedge rst_n_pad) if (!rst_n_pad) {gb, gb_s} <= 2'b00; else {gb, gb_s} <= {gb_s, strap_osc & ~ga};
    assign clk_core = (clk_pad & ga) | (osc & gb);
    // reset synchroniser
    logic [1:0] rs;
    always_ff @(posedge clk_core or negedge rst_n_pad) if (!rst_n_pad) rs <= 2'b00; else rs <= {rs[0], 1'b1};
    assign rst_core_n = rs[1];
    // frequency window: count pad clocks in 4096 reference periods
    logic [11:0] ref_cnt, pad_cnt, pad_gray, pad_snap;
    logic [11:0] g1, g2;
    always_ff @(posedge clk_pad or negedge rst_n_pad) if (!rst_n_pad) pad_cnt <= '0; else pad_cnt <= pad_cnt + 12'd1;
    always_ff @(posedge clk_pad or negedge rst_n_pad) if (!rst_n_pad) pad_gray <= '0; else pad_gray <= (pad_cnt >> 1) ^ pad_cnt;
    function automatic [11:0] g2b(input [11:0] g);
        for (int i = 0; i < 12; i++) g2b[i] = ^(g >> i);
    endfunction
    logic [11:0] last;
    wire  [11:0] now_b = g2b(g2);
    wire  [11:0] delta = now_b - last;
    always_ff @(posedge osc or negedge rst_n_pad) begin
        if (!rst_n_pad) begin ref_cnt <= '0; g1 <= '0; g2 <= '0; last <= '0; pad_snap <= '0; clk_fault <= 1'b0; end
        else begin
            g1 <= pad_gray; g2 <= g1;
            ref_cnt <= ref_cnt + 12'd1;
            if (ref_cnt == 12'hFFF) begin
                last <= now_b; pad_snap <= delta;
                if (prov && (delta < win_lo || delta > win_hi)) clk_fault <= 1'b1;
            end
        end
    end
    // tamper: armed by lifecycle, blanked for 4096 clocks after reset
    logic [12:0] blank;
    logic [1:0] ts;
    always_ff @(posedge clk_core or negedge rst_n_pad) begin
        if (!rst_n_pad) begin blank <= '0; ts <= 2'b11; tamper_latched <= 1'b0; end
        else begin
            ts <= {ts[0], tamper_n};
            if (!blank[12]) blank <= blank + 13'd1;
            if (prov && blank[12] && (!ts[1] || sensor_evt || clk_fault)) tamper_latched <= 1'b1;
        end
    end
    // secret reset: asynchronous assert, synchronous release
    logic [1:0] ss;
    wire s_async_n = rst_n_pad & ~tamper_latched;
    logic zq;
    always_ff @(posedge clk_core or negedge rst_n_pad) if (!rst_n_pad) zq <= 1'b0; else zq <= zeroize;
    always_ff @(posedge clk_core or negedge s_async_n) if (!s_async_n) ss <= 2'b00; else ss <= zq ? 2'b00 : {ss[0], 1'b1};
    assign secret_rst_n = ss[1];
    assign diag = {clk_fault, tamper_latched, ga, gb, pad_snap};
endmodule
`default_nettype wire
