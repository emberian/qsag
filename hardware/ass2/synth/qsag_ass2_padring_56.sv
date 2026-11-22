// Foundry 56-Pad `SLOT_0P5X0P5` Padring Wrapper for `ASS2-0P5`:
//   - Straps `HOST_DQ[7:0]` (`bidir[7:0]`) to programmable-drive `gf180mcu_fd_io__bi_t`
//     with `PDRV = HOST_DQ_PDRV` (default `2'b01` = 8 mA, `SL = 1` slow slew) + 33 Ohm
//     board series termination, eliminating the 24 mA `bi_24t` South-bank SSN ground bounce.
module qsag_ass2_padring_56 #(
    parameter logic [1:0] HOST_DQ_PDRV = 2'b01 // 2'b01 = 8 mA, 2'b00 = 4 mA
) (
    inout wire        clk_pad,
    inout wire        rst_n_pad,
    inout wire [3:0]  input_pads,
    inout wire [37:0] bidir_pads,
    inout wire [3:0]  analog_pads,
    inout wire        vdd,
    inout wire        vss,
    inout wire        dvdd,
    inout wire        dvss
);
    wire        clk_c, rst_n_c;
    wire [3:0]  in_c, in_pu, in_pd;
    wire [37:0] b_in, b_out, b_oe, b_cs, b_sl, b_ie, b_pu, b_pd;

    gf180mcu_fd_io__in_s u_clk_pad (
        .PAD(clk_pad), .Y(clk_c), .PU(1'b0), .PD(1'b0),
        .DVDD(dvdd), .DVSS(dvss), .VDD(vdd), .VSS(vss)
    );
    gf180mcu_fd_io__in_s u_rst_pad (
        .PAD(rst_n_pad), .Y(rst_n_c), .PU(1'b0), .PD(1'b1),
        .DVDD(dvdd), .DVSS(dvss), .VDD(vdd), .VSS(vss)
    );

    for (genvar i = 0; i < 4; i++) begin : g_inputs
        gf180mcu_fd_io__in_c u_in_pad (
            .PAD(input_pads[i]), .Y(in_c[i]), .PU(in_pu[i]), .PD(in_pd[i]),
            .DVDD(dvdd), .DVSS(dvss), .VDD(vdd), .VSS(vss)
        );
    end

    // South/East `HOST_DQ[7:0]`: `bi_t` strapped to controlled `8 mA / 4 mA` drive + `SL = 1`
    for (genvar i = 0; i < 8; i++) begin : g_host_dq
        gf180mcu_fd_io__bi_t u_dq_pad (
            .PAD(bidir_pads[i]), .A(b_out[i]), .Y(b_in[i]),
            .OE(b_oe[i]), .IE(b_ie[i]), .CS(b_cs[i]), .SL(b_sl[i]),
            .PU(b_pu[i]), .PD(b_pd[i]),
            .PDRV0(HOST_DQ_PDRV[0]), .PDRV1(HOST_DQ_PDRV[1]),
            .DVDD(dvdd), .DVSS(dvss), .VDD(vdd), .VSS(vss)
        );
    end

    for (genvar i = 8; i < 38; i++) begin : g_bidir
        gf180mcu_fd_io__bi_t u_bi_pad (
            .PAD(bidir_pads[i]), .A(b_out[i]), .Y(b_in[i]),
            .OE(b_oe[i]), .IE(b_ie[i]), .CS(b_cs[i]), .SL(b_sl[i]),
            .PU(b_pu[i]), .PD(b_pd[i]),
            .PDRV0(1'b1), .PDRV1(1'b0),
            .DVDD(dvdd), .DVSS(dvss), .VDD(vdd), .VSS(vss)
        );
    end

    for (genvar i = 0; i < 4; i++) begin : g_analog
        gf180mcu_fd_io__asig_5p0 u_ana_pad (
            .ASIG5V(analog_pads[i]), .DVDD(dvdd), .DVSS(dvss), .VDD(vdd), .VSS(vss)
        );
    end

    qsag_ass2_enclave_top u_core_top (
        .clk(clk_c), .rst_n(rst_n_c),
        .input_in(in_c), .input_pu(in_pu), .input_pd(in_pd),
        .bidir_in(b_in), .bidir_out(b_out), .bidir_oe(b_oe),
        .bidir_cs(b_cs), .bidir_sl(b_sl), .bidir_ie(b_ie),
        .bidir_pu(b_pu), .bidir_pd(b_pd)
    );
endmodule
