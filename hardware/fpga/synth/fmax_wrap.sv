// Pin-frugal place-and-route wrappers for Fmax & utilization signoff with nextpnr-ecp5 on
// `LFE5U-85F-6BG381C` ($45 ECP5-85F): every DUT input comes from a serial shift register fed by
// one pin, synchronous reset is 2-stage synchronized + replicated on-chip (eliminating raw pad
// `<async> -> clk` skew), and all outputs XOR-reduce into one registered pin so zero logic is
// trimmed.
module fmax_gl64_dsp_mul (input logic clk, input logic si, output logic so);
    logic [127:0] sr;
    logic [63:0]  r;
    always_ff @(posedge clk) begin sr <= {sr[126:0], si}; so <= ^r; end
    qsag_gl64_dsp_mul #(.AW(16), .BW(16)) dut (.clk(clk), .a(sr[63:0]), .b(sr[127:64]), .r(r));
endmodule

module fmax_p2_sbox7 (input logic clk, input logic si, output logic so);
    logic [63:0] sr, y;
    always_ff @(posedge clk) begin sr <= {sr[62:0], si}; so <= ^y; end
    qsag_p2_sbox7 #(.AW(16), .BW(16)) dut (.clk(clk), .x(sr), .y(y));
endmodule

module fmax_ext4_mac (input logic clk, input logic si, output logic so);
    logic [767:0] sr;
    logic [255:0] y;
    always_ff @(posedge clk) begin sr <= {sr[766:0], si}; so <= ^y; end
    qsag_ext4_mac #(.AW(16), .BW(16)) dut (
        .clk(clk), .a(sr[255:0]), .b(sr[511:256]), .c(sr[767:512]), .y(y));
endmodule

module fmax_ext5_mac (input logic clk, input logic si, output logic so);
    logic [959:0] sr;
    logic [319:0] y;
    always_ff @(posedge clk) begin sr <= {sr[958:0], si}; so <= ^y; end
    qsag_ext5_mac #(.AW(16), .BW(16)) dut (
        .clk(clk), .a(sr[319:0]), .b(sr[639:320]), .c(sr[959:640]), .y(y));
endmodule

module fmax_p2_linear (input logic clk, input logic si, output logic so);
    logic [767:0]     sr, y;
    logic [12*67-1:0] ad;
    logic             mi;
    always_ff @(posedge clk) begin
        sr <= {sr[766:0], si};
        ad <= {ad[12*67-2:0], sr[767]};
        mi <= ad[12*67-1];
        so <= ^y;
    end
    qsag_p2_linear #(.FIXED(-1)) dut (.clk(clk), .x(sr), .mi(mi), .addend(ad), .y(y));
endmodule

module fmax_keccak #(parameter int RPC = 2) (input logic clk, input logic rst, input logic si, output logic so);
    logic          rst_s0, rst_s1;
    logic [1599:0] sr, st;
    logic          busy, done, go;
    always_ff @(posedge clk) begin
        rst_s0 <= rst;
        rst_s1 <= rst_s0;
        sr     <= {sr[1598:0], si};
        go     <= !busy && sr[1599];
        so     <= ^st ^ done;
    end
    qsag_keccak_turboshake #(.RPC(RPC)) dut (
        .clk(clk), .rst(rst_s1), .start(go), .nr12(sr[0]), .state_i(sr), .busy(busy), .done(done), .state_o(st));
endmodule

module fmax_keccak_compact (input logic clk, input logic rst, input logic si, output logic so);
    logic        rst_s0, rst_s1;
    logic [72:0] sr;
    logic        rdy, busy, done, rdv;
    logic [63:0] rdd;
    always_ff @(posedge clk) begin
        rst_s0 <= rst;
        rst_s1 <= rst_s0;
        sr     <= {sr[71:0], si};
        so     <= ^{rdy, busy, done, rdv, rdd};
    end
    qsag_keccak_compact dut (
        .clk(clk), .rst(rst_s1), .bank_sel(1'b0),
        .cmd_valid(sr[72]), .cmd_ready(rdy), .cmd_op(sr[71:70]), .cmd_nr12(sr[69]),
        .cmd_idx(sr[68:64]), .cmd_wdata(sr[63:0]),
        .busy(busy), .done(done), .rd_valid(rdv), .rd_data(rdd));
endmodule

module fmax_gf128_clmul (input logic clk, input logic si, output logic so);
    logic [255:0] sr;
    logic [127:0] r;
    always_ff @(posedge clk) begin sr <= {sr[254:0], si}; so <= ^r; end
    qsag_gf128_clmul dut (.clk(clk), .a(sr[127:0]), .b(sr[255:128]), .r(r));
endmodule

// Complete ultra-compact accelerator (`18 / 156` MULT18X18D = 11.5%).
module fmax_compact_top(input logic clk, input logic rst, input logic si, output logic so);
    logic         rst_s0, rst_s1;
    logic [578:0] sr;
    logic         awready, wready, bvalid, arready, rvalid, tready;
    logic [1:0]   bresp, rresp;
    logic [31:0]  rdata;
    always_ff @(posedge clk) begin
        rst_s0 <= rst;
        rst_s1 <= rst_s0;
        sr     <= {sr[577:0], si};
        so     <= ^{awready, wready, bvalid, arready, rvalid, tready, bresp, rresp, rdata};
    end
    qsag_ni_fpga_top #(
        .PROFILE_COMPACT(1), .ECP5_FULLRATE(0), .CHAIN_SLOTW(2), .FOLD_TAW(9), .TS_SAW(9), .KECCAK_RPC(1), .AW(16), .BW(16)
    ) dut (
        .clk(clk), .rst(rst_s1),
        .s_axis_tdata(sr[511:0]), .s_axis_tvalid(sr[512]), .s_axis_tready(tready),
        .s_axil_awaddr(sr[524:513]), .s_axil_awvalid(sr[525]), .s_axil_awready(awready),
        .s_axil_wdata(sr[557:526]), .s_axil_wstrb(sr[561:558]), .s_axil_wvalid(sr[562]), .s_axil_wready(wready),
        .s_axil_bready(sr[563]), .s_axil_bvalid(bvalid), .s_axil_bresp(bresp),
        .s_axil_araddr(sr[575:564]), .s_axil_arvalid(sr[576]), .s_axil_arready(arready),
        .s_axil_rready(sr[577]), .s_axil_rvalid(rvalid), .s_axil_rresp(rresp), .s_axil_rdata(rdata));
    wire unused_ok = &{1'b0, sr[578]};
endmodule

// Complete full-rate pipelined ECP5-85F accelerator (`117 / 156` MULT18X18D = 75.0%:
// 81-DSP 1-MAC/clk Ext4 + 36-DSP 1-Sbox/clk Poseidon2 + 1-RAM 30-clk/rnd Keccak + zk-Hem v2).
module fmax_ecp5_fullrate_top(input logic clk, input logic rst, input logic si, output logic so);
    logic         rst_s0, rst_s1;
    logic [578:0] sr;
    logic         awready, wready, bvalid, arready, rvalid, tready;
    logic [1:0]   bresp, rresp;
    logic [31:0]  rdata;
    always_ff @(posedge clk) begin
        rst_s0 <= rst;
        rst_s1 <= rst_s0;
        sr     <= {sr[577:0], si};
        so     <= ^{awready, wready, bvalid, arready, rvalid, tready, bresp, rresp, rdata};
    end
    qsag_ni_fpga_top #(
        .PROFILE_COMPACT(1), .ECP5_FULLRATE(1), .CHAIN_SLOTW(2), .FOLD_TAW(9), .TS_SAW(9), .KECCAK_RPC(1), .AW(16), .BW(16)
    ) dut (
        .clk(clk), .rst(rst_s1),
        .s_axis_tdata(sr[511:0]), .s_axis_tvalid(sr[512]), .s_axis_tready(tready),
        .s_axil_awaddr(sr[524:513]), .s_axil_awvalid(sr[525]), .s_axil_awready(awready),
        .s_axil_wdata(sr[557:526]), .s_axil_wstrb(sr[561:558]), .s_axil_wvalid(sr[562]), .s_axil_wready(wready),
        .s_axil_bready(sr[563]), .s_axil_bvalid(bvalid), .s_axil_bresp(bresp),
        .s_axil_araddr(sr[575:564]), .s_axil_arvalid(sr[576]), .s_axil_arready(arready),
        .s_axil_rready(sr[577]), .s_axil_rvalid(rvalid), .s_axil_rresp(rresp), .s_axil_rdata(rdata));
    wire unused_ok = &{1'b0, sr[578]};
endmodule
