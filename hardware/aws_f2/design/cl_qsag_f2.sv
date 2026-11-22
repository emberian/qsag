// F2 HDK synthesis entry point. The bus/core top also elaborates stand-alone.
module cl_qsag_f2 (
    `include "cl_ports.vh"
);
    `include "cl_id_defines.vh"
    (* ASYNC_REG="TRUE" *) logic [1:0] ddr_reset_pipe;
    always_ff @(posedge clk_main_a0 or negedge rst_main_n)
        if (!rst_main_n) ddr_reset_pipe <= 0;
        else ddr_reset_pipe <= {ddr_reset_pipe[0],1'b1};
    wire rst_main_n_sync = ddr_reset_pipe[1];
    cl_qsag_f2_top #(.PCI_ID(`CL_SH_ID0)) u_shell (.*);
    sh_ddr #(.DDR_PRESENT(0)) SH_DDR (
        .clk(clk_main_a0),
        .rst_n(rst_main_n_sync),
        .stat_clk(clk_main_a0),
        .stat_rst_n(rst_main_n_sync),
        .CLK_DIMM_DP(CLK_DIMM_DP),
        .CLK_DIMM_DN(CLK_DIMM_DN),
        .M_ACT_N(M_ACT_N),
        .M_MA(M_MA),
        .M_BA(M_BA),
        .M_BG(M_BG),
        .M_CKE(M_CKE),
        .M_ODT(M_ODT),
        .M_CS_N(M_CS_N),
        .M_CLK_DN(M_CLK_DN),
        .M_CLK_DP(M_CLK_DP),
        .M_PAR(M_PAR),
        .M_DQ(M_DQ),
        .M_ECC(M_ECC),
        .M_DQS_DP(M_DQS_DP),
        .M_DQS_DN(M_DQS_DN),
        .cl_RST_DIMM_N(RST_DIMM_N),
        .cl_sh_ddr_axi_awid('0),
        .cl_sh_ddr_axi_awaddr('0),
        .cl_sh_ddr_axi_awlen('0),
        .cl_sh_ddr_axi_awsize('0),
        .cl_sh_ddr_axi_awvalid('0),
        .cl_sh_ddr_axi_awburst('0),
        .cl_sh_ddr_axi_awuser('0),
        .cl_sh_ddr_axi_awready(),
        .cl_sh_ddr_axi_wdata('0),
        .cl_sh_ddr_axi_wstrb('0),
        .cl_sh_ddr_axi_wlast('0),
        .cl_sh_ddr_axi_wvalid('0),
        .cl_sh_ddr_axi_wready(),
        .cl_sh_ddr_axi_bid(),
        .cl_sh_ddr_axi_bresp(),
        .cl_sh_ddr_axi_bvalid(),
        .cl_sh_ddr_axi_bready('0),
        .cl_sh_ddr_axi_arid('0),
        .cl_sh_ddr_axi_araddr('0),
        .cl_sh_ddr_axi_arlen('0),
        .cl_sh_ddr_axi_arsize('0),
        .cl_sh_ddr_axi_arvalid('0),
        .cl_sh_ddr_axi_arburst('0),
        .cl_sh_ddr_axi_aruser('0),
        .cl_sh_ddr_axi_arready(),
        .cl_sh_ddr_axi_rid(),
        .cl_sh_ddr_axi_rdata(),
        .cl_sh_ddr_axi_rresp(),
        .cl_sh_ddr_axi_rlast(),
        .cl_sh_ddr_axi_rvalid(),
        .cl_sh_ddr_axi_rready('0),
        .sh_ddr_stat_bus_addr('0),
        .sh_ddr_stat_bus_wdata('0),
        .sh_ddr_stat_bus_wr('0),
        .sh_ddr_stat_bus_rd('0),
        .sh_ddr_stat_bus_ack(),
        .sh_ddr_stat_bus_rdata(),
        .ddr_sh_stat_int(),
        .sh_cl_ddr_is_ready()
    );
    assign cl_sh_ddr_stat_ack = 1;
    assign cl_sh_ddr_stat_rdata = 0;
    assign cl_sh_ddr_stat_int = 0;
    `include "unused_cl_sda_template.inc"
    `include "unused_apppf_irq_template.inc"
    assign cl_sh_status0 = 0;
    assign cl_sh_status1 = 0;
    assign cl_sh_status2 = 0;
    assign cl_sh_dma_rd_full = 0;
    assign cl_sh_dma_wr_full = 0;
    assign cl_sh_dma_pcis_ruser = 0;
    assign tdo = 0;
    assign cl_sh_pcim_awid = '0;
    assign cl_sh_pcim_awaddr = '0;
    assign cl_sh_pcim_awlen = '0;
    assign cl_sh_pcim_awsize = '0;
    assign cl_sh_pcim_awburst = '0;
    assign cl_sh_pcim_awcache = '0;
    assign cl_sh_pcim_awlock = '0;
    assign cl_sh_pcim_awprot = '0;
    assign cl_sh_pcim_awqos = '0;
    assign cl_sh_pcim_awuser = '0;
    assign cl_sh_pcim_awvalid = '0;
    assign cl_sh_pcim_wid = '0;
    assign cl_sh_pcim_wdata = '0;
    assign cl_sh_pcim_wstrb = '0;
    assign cl_sh_pcim_wlast = '0;
    assign cl_sh_pcim_wuser = '0;
    assign cl_sh_pcim_wvalid = '0;
    assign cl_sh_pcim_bready = '0;
    assign cl_sh_pcim_arid = '0;
    assign cl_sh_pcim_araddr = '0;
    assign cl_sh_pcim_arlen = '0;
    assign cl_sh_pcim_arsize = '0;
    assign cl_sh_pcim_arburst = '0;
    assign cl_sh_pcim_arcache = '0;
    assign cl_sh_pcim_arlock = '0;
    assign cl_sh_pcim_arprot = '0;
    assign cl_sh_pcim_arqos = '0;
    assign cl_sh_pcim_aruser = '0;
    assign cl_sh_pcim_arvalid = '0;
    assign cl_sh_pcim_rready = '0;
    assign hbm_apb_paddr_1 = '0;
    assign hbm_apb_pprot_1 = '0;
    assign hbm_apb_psel_1 = '0;
    assign hbm_apb_penable_1 = '0;
    assign hbm_apb_pwrite_1 = '0;
    assign hbm_apb_pwdata_1 = '0;
    assign hbm_apb_pstrb_1 = '0;
    assign hbm_apb_pready_1 = '0;
    assign hbm_apb_prdata_1 = '0;
    assign hbm_apb_pslverr_1 = '0;
    assign hbm_apb_paddr_0 = '0;
    assign hbm_apb_pprot_0 = '0;
    assign hbm_apb_psel_0 = '0;
    assign hbm_apb_penable_0 = '0;
    assign hbm_apb_pwrite_0 = '0;
    assign hbm_apb_pwdata_0 = '0;
    assign hbm_apb_pstrb_0 = '0;
    assign hbm_apb_pready_0 = '0;
    assign hbm_apb_prdata_0 = '0;
    assign hbm_apb_pslverr_0 = '0;
    assign PCIE_EP_TXP = '0;
    assign PCIE_EP_TXN = '0;
    assign PCIE_RP_PERSTN = '0;
    assign PCIE_RP_TXP = '0;
    assign PCIE_RP_TXN = '0;
endmodule
