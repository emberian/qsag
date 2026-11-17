// Test-bench microcode ROM: same interface as the generated dregg_urom, contents loaded through a
// clocked port so that one compiled simulation can run every ROM image of the model's test suites.
//   ld_sel 0: word[ld_addr] <= ld_data[27:0]
//          1: const[ld_addr[6:0]] <= ld_data (and marks it present)
//          2: dispatch[ld_addr[7:0]] <= {hit, class[1:0], addr[10:0]} = ld_data[13:0]
//          3: {rom_used, rom_len} <= ld_data[23:0]; also clears every table (words to ILL)
`default_nettype none

module dregg_urom_sim (
    input  wire         clk,
    input  wire         ld_we,
    input  wire  [1:0]  ld_sel,
    input  wire  [10:0] ld_addr,
    input  wire  [63:0] ld_data,
    input  wire  [10:0] rom_addr,
    output wire  [27:0] rom_word,
    input  wire  [6:0]  const_idx,
    output wire  [63:0] const_data,
    output wire         const_ok,
    input  wire  [7:0]  disp_op,
    output wire         disp_hit,
    output wire  [10:0] disp_addr,
    output wire  [1:0]  disp_class,
    output logic [11:0] rom_len,
    output logic [11:0] rom_used
);
`include "dregg_defs.svh"
    logic [27:0] words [2048];
    logic [63:0] consts [128];
    logic [127:0] cvalid;
    logic [13:0] disp [256];

    always_ff @(posedge clk) if (ld_we) begin
        unique case (ld_sel)
            2'd0: words[ld_addr] <= ld_data[27:0];
            2'd1: begin
                consts[ld_addr[6:0]] <= ld_data;
                cvalid[ld_addr[6:0]] <= 1'b1;
            end
            2'd2: disp[ld_addr[7:0]] <= ld_data[13:0];
            default: begin
                rom_len  <= ld_data[11:0];
                rom_used <= ld_data[23:12];
                cvalid   <= '0;
                for (int i = 0; i < 2048; i++) words[i] <= {OP_ILL, 23'd0};
                for (int i = 0; i < 256; i++) disp[i] <= '0;
            end
        endcase
    end
    assign rom_word   = words[rom_addr];
    assign const_data = cvalid[const_idx] ? consts[const_idx] : 64'd0;
    assign const_ok   = cvalid[const_idx];
    assign disp_hit   = disp[disp_op][13];
    assign disp_class = disp[disp_op][12:11];
    assign disp_addr  = disp[disp_op][10:0];
endmodule
`default_nettype wire
