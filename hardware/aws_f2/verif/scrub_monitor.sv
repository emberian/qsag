// Observe writes at both physical SRAM ports in every vat. Sampling on the
// destination clock catches a skipped address even if the RAM started at zero.
module scrub_monitor (
  input wire clk, erase, iwrite, dwrite,
  input wire [8:0] iaddr, daddr,
  input wire [7:0] idata, ddata
);
  bit [511:0] seen;
  bit sweeping;
  always @(posedge clk) begin
    if (erase) begin
      if (!(iwrite && dwrite && iaddr == daddr && idata == 0 && ddata == 0))
        $fatal(1, "incomplete simultaneous vat SRAM write");
      seen[iaddr] <= 1; sweeping <= 1;
    end else if (sweeping) begin
      if (!(&seen)) $fatal(1, "vat SRAM address missed during scrub");
      seen <= 0; sweeping <= 0;
    end
  end
endmodule
bind qsag_ass2_enclave_top scrub_monitor check_scrub (.clk, .erase,
  .iwrite(u_isram.en && u_isram.we), .dwrite(u_dsram.en && u_dsram.we),
  .iaddr(u_isram.addr), .daddr(u_dsram.addr), .idata(u_isram.wdata), .ddata(u_dsram.wdata));
