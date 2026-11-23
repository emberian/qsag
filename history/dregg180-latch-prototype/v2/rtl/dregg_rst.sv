// Dregg-180 v2 reset and zeroise control (ARCHITECTURE.md 5.2 "Zeroisation", 6.6 "Reset").
//
//   por_n      reset pad: asynchronous assert, synchronous release (two flops)
//   tamper_n   tamper pad, asynchronous. A low level sets the tamper latch without a clock; the latch
//              holds the secret reset until the next pad reset. (Arming by lifecycle is stage 6.)
//   zreq       control fault raised by the sequencer in this clock
//
//   rst_n      system reset: the reset controller's own flops and the control-fault flag
//   srst_n     secret reset: RN of every latch of the register file, of the hold register and of every
//              other flop of the core. It is an AND of flop and latch outputs only: the synchronised
//              pad reset, the tamper latch, the one-clock zeroise flop. Assertion needs no clock.
//   fault_control   a control fault has happened since the last pad reset (FAULT pin)
`default_nettype none

module dregg_rst (
    input  wire  clk,
    input  wire  por_n,
    input  wire  tamper_n,
    input  wire  zreq,
    output wire  rst_n,
    output wire  srst_n,
    output logic fault_control,
    output wire  tampered
);
    qsag_rst_sync u_rs (.clk(clk), .arst_n(por_n), .rst_n(rst_n));

    // tamper latch: set asynchronously by the pad, cleared only by the pad reset
    wire tl;
    qsag_srlatch u_tl (.rn(por_n), .sn(tamper_n), .q(tl));
    assign tampered = tl;

    // zeroise: one clock of secret reset after a control fault
    logic z_q;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            z_q           <= 1'b0;
            fault_control <= 1'b0;
        end else begin
            z_q <= zreq;
            if (zreq) fault_control <= 1'b1;
        end

    wire s0;
    qsag_clkand2 u_a0 (.a(rst_n), .b(~z_q), .y(s0));
    qsag_clkand2 u_a1 (.a(s0), .b(~tl), .y(srst_n));
endmodule
`default_nettype wire
