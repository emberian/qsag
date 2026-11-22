// Simulation-only bank observation. Keep the production core pin list intact.
module ass2_cosim_top (
    input  logic        clk, rst_n, start_i,
    output logic        mem_en_o, mem_we_o,
    output logic [7:0]  mem_wstrb_o,
    output logic [63:0] mem_addr_o, mem_wdata_o,
    input  logic [63:0] mem_rdata_i,
    input  logic        mem_fault_i,
    output logic        insn_retire_o, trap_o, halted_o,
    output logic [63:0] pc_o, ecause_o, instret_o, cycles_o,
    output wire  [63:0] regs[16], spg[25]
);
    wire [63:0] u_phys, u_r4;
    wire [7:0]  u_dbg_b;
    wire        u_tamp, u_zpulse, u_dbg_we, u_dbg_rd;
    qsag_ass2_core dut(
        .clk, .rst_n, .start_i, .tamper_zeroize_n(1'b1), .jtag_test_mode_i(1'b0),
        .zeroize_first_i(1'b0), .dbg_halt_i(1'b0), .start_pc_i(64'b0),
        .arg_regs_we_i(1'b0), .arg_reg_addr_i(4'b0), .arg_reg_data_i(64'b0),
        .mem_en_o, .mem_we_o, .mem_wstrb_o, .mem_addr_o, .mem_wdata_o,
        .mem_rdata_i, .mem_ready_i(1'b1), .mem_fault_i,
        .insn_retire_o, .trap_o, .halted_o, .zeroize_pulse_o(u_zpulse),
        .pc_o, .ecause_o, .instret_o, .cycles_o,
        .phys_cycles_o(u_phys), .r4_o(u_r4),
        .tampered_o(u_tamp), .dbg_we_o(u_dbg_we), .dbg_byte_o(u_dbg_b),
        .dbg_in_i(64'b0), .dbg_rd_o(u_dbg_rd)
    );
    wire unused_cosim = ^{u_phys, u_r4, u_dbg_b, u_tamp, u_zpulse, u_dbg_we, u_dbg_rd};
    assign regs = dut.regs;
    assign spg  = dut.spg;
endmodule
