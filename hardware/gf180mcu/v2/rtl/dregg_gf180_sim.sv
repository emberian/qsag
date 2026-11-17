// Behavioural stand-ins for the gf180mcu_fd_sc_mcu7t5v0 cells that dregg_regfile instantiates by name
// (simulation and lint only; with QSAG_GF180_CELLS the library's own cells are used and this file is empty).
`default_nettype none
`ifndef QSAG_GF180_CELLS
/* verilator lint_off DECLFILENAME */
/* verilator lint_off UNUSEDSIGNAL */
module gf180mcu_fd_sc_mcu7t5v0__buf_4 (input wire I, output wire Z);
    assign Z = I;
endmodule
module gf180mcu_fd_sc_mcu7t5v0__buf_8 (input wire I, output wire Z);
    assign Z = I;
endmodule
module gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 (input wire I, output wire Z);
    assign Z = I;
endmodule
module gf180mcu_fd_sc_mcu7t5v0__and2_1 (input wire A1, input wire A2, output wire Z);
    assign Z = A1 & A2;
endmodule
module gf180mcu_fd_sc_mcu7t5v0__and2_4 (input wire A1, input wire A2, output wire Z);
    assign Z = A1 & A2;
endmodule
module gf180mcu_fd_sc_mcu7t5v0__nand2_1 (input wire A1, input wire A2, output wire ZN);
    assign ZN = ~(A1 & A2);
endmodule
module gf180mcu_fd_sc_mcu7t5v0__nand3_1 (input wire A1, input wire A2, input wire A3, output wire ZN);
    assign ZN = ~(A1 & A2 & A3);
endmodule
module gf180mcu_fd_sc_mcu7t5v0__nand4_1 (input wire A1, input wire A2, input wire A3, input wire A4, output wire ZN);
    assign ZN = ~(A1 & A2 & A3 & A4);
endmodule
module gf180mcu_fd_sc_mcu7t5v0__nor2_1 (input wire A1, input wire A2, output wire ZN);
    assign ZN = ~(A1 | A2);
endmodule
module gf180mcu_fd_sc_mcu7t5v0__or3_1 (input wire A1, input wire A2, input wire A3, output wire Z);
    assign Z = A1 | A2 | A3;
endmodule
// Word-line gate. The cell samples E while CLK is low and passes the high phase. As in qsag_latgate
// (qsag_cells.sv), the zero-delay model opens with the non-blocking update of the rising edge, together
// with the hold register, and closes on the falling edge.
module gf180mcu_fd_sc_mcu7t5v0__icgtp_4 (input wire CLK, input wire E, input wire TE, output wire Q);
    logic open_q;
    always_ff @(posedge CLK or negedge CLK) open_q <= CLK ? (E | TE) : 1'b0;
    assign Q = open_q;
endmodule
/* verilator lint_off LATCH */
/* verilator lint_off COMBDLY */
module gf180mcu_fd_sc_mcu7t5v0__latrnq_1 (input wire D, input wire E, input wire RN, output wire Q);
    logic qr;
    always_latch begin
        if (!RN)    qr <= 1'b0;
        else if (E) qr <= D;
    end
    assign Q = qr;
endmodule
`ifdef DREGG_TB_BACKDOOR
// Test bench only: the same latch with a direct-placement port (fixtures that put keys into key rows).
module dregg_tb_latrnq (input wire D, input wire E, input wire RN, output wire Q, input wire bd_we, input wire bd_d);
    logic qr;
    always_latch begin
        if (!RN)        qr <= 1'b0;
        else if (E)     qr <= D;
        else if (bd_we) qr <= bd_d;
    end
    assign Q = qr;
endmodule
`endif
/* verilator lint_on COMBDLY */
/* verilator lint_on LATCH */
/* verilator lint_on UNUSEDSIGNAL */
`endif
`default_nettype wire
