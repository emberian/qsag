(* blackbox *)
module gf180mcu_fd_ip_sram__sram512x8m8wm1 (
    input wire CLK, CEN, GWEN,
    input wire [7:0] WEN,
    input wire [8:0] A,
    input wire [7:0] D,
    output wire [7:0] Q
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__latrnq_1 (
    input wire D, E, RN,
    output wire Q
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__dffrnq_1 (
    input wire CLK, D, RN,
    output wire Q
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__dffrnq_2 (
    input wire CLK, D, RN,
    output wire Q
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__dffq_1 (
    input wire CLK, D,
    output wire Q
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__icgtp_2 (
    input wire CLK, E, TE,
    output wire Q
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 (
    input wire I,
    output wire Z
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 (
    input wire I,
    output wire Z
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__clkbuf_2 (
    input wire I,
    output wire Z
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__buf_2 (
    input wire I,
    output wire Z
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__buf_4 (
    input wire I,
    output wire Z
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__buf_16 (
    input wire I,
    output wire Z
);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nand2_1 (input wire A1, A2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nand2_2 (input wire A1, A2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__or2_2 (input wire A1, A2, output wire Z);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nand3_1 (input wire A1, A2, A3, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nand4_1 (input wire A1, A2, A3, A4, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nand4_2 (input wire A1, A2, A3, A4, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nor2_1 (input wire A1, A2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__nor2_2 (input wire A1, A2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__inv_1 (input wire I, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__inv_2 (input wire I, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__aoi22_1 (input wire A1, A2, B1, B2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__aoi22_2 (input wire A1, A2, B1, B2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__aoi222_1 (input wire A1, A2, B1, B2, C1, C2, output wire ZN);
endmodule

(* blackbox *)
module gf180mcu_fd_sc_mcu7t5v0__dffsnq_1 (input wire CLK, D, SETN, output wire Q);
endmodule
