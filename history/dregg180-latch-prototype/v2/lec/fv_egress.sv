// Formal harness for dregg_egress: every input free (properties in dregg_egress, ifdef FORMAL).
`default_nettype none
module fv_egress (
    input wire clk, input wire [7:0] req_op, input wire hdr, input wire fail, input wire [15:0] hdr_n,
    input wire hdr_ok, input wire push, input wire flush, input wire [127:0] out_q, input wire out_take
);
    logic init = 1'b1;
    always_ff @(posedge clk) init <= 1'b0;
    wire srst_n = !init;
    /* verilator lint_off PINCONNECTEMPTY */
    dregg_egress dut (
        .clk(clk), .srst_n(srst_n), .req_op(req_op), .hdr(hdr), .fail(fail), .hdr_n(hdr_n), .hdr_ok(hdr_ok),
        .push(push), .can_push(), .wr_slot(), .push_room(), .flush(flush), .flushed(), .idle(), .out_q(out_q),
        .out_valid(), .out_data(), .out_take(out_take), .out_sel()
    );
endmodule
`default_nettype wire
