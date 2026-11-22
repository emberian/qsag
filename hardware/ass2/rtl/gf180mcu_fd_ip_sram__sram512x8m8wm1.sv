`ifdef GF180_SRAM_MACRO
`ifndef QSAG_EXTERNAL_SRAM_MODEL
(* blackbox *) module gf180mcu_fd_ip_sram__sram512x8m8wm1 (
    input wire CLK, CEN, GWEN,
    input wire [7:0] WEN, D,
    input wire [8:0] A,
    output logic [7:0] Q
);
`ifdef VERILATOR
    // Functional view of the macro for the byte-mask and bank-select tests.
    logic [7:0] mem [512];
    always_ff @(posedge CLK) if (!CEN) begin
        if (GWEN) Q<=mem[A];
        else mem[A]<=(mem[A] & WEN) | (D & ~WEN);
    end
`endif
endmodule
`endif
`endif
