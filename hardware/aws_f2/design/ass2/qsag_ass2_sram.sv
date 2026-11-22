// Single-macro 512 x 8-bit (`512 B`) SRAM wrapper for `ASS2-0P5` (`SLOT_0P5X0P5`):
//   - Instantiated twice in `qsag_ass2_enclave_top`:
//       `SRAM1` = 512 B authenticated loadable `I-SRAM` (`0x0000_1000 .. 0x0000_11FF`)
//       `SRAM0` = 512 B enclave `D-SRAM` + mailboxes    (`0x0001_0000 .. 0x0001_01FF`)
module qsag_ass2_sram (
    input  logic       clk,
    input  logic       en,
    input  logic       we,
    input  logic [8:0] addr,
    input  logic [7:0] wdata,
    output logic [7:0] rdata
);
`ifdef GF180_SRAM_MACRO
    // The macro-enable setup tables are highly slew sensitive at SS.
    wire cen, gwen;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_16 u_cen (.I(!en), .Z(cen));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_16 u_gwen (.I(!we), .Z(gwen));
    gf180mcu_fd_ip_sram__sram512x8m8wm1 u_macro (
        .CLK (clk),
        .CEN (cen),
        .GWEN(gwen),
        .WEN ({8{gwen}}),
        .A   (addr),
        .D   (wdata),
        .Q   (rdata)
    );
`else
    logic [7:0] mem [512];
    always_ff @(posedge clk) begin
        if (en) begin
            if (we) mem[addr] <= wdata;
            rdata <= mem[addr];
        end
    end
`endif
endmodule
