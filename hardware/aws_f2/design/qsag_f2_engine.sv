// One private NI, operand SRAM, and 256-descriptor issue queue. The same
// queue accepts streamed beats or byte-strobed staging followed by a doorbell.
module qsag_f2_engine (
  input wire clk, lock, erase,
  input wire [12:0] erase_addr,
  input wire dma_mem, stage, enqueue, doorbell, mmio_push,
  input wire [12:0] row,
  input wire [63:0] strb,
  input wire [511:0] wdata,
  input wire [7:0] ring_base,
  input wire [8:0] ring_len,
  input wire [92:0] mmio_cmd,
  output wire [511:0] mem_q,
  output wire idle, fail, page_paused,
  output wire [15:0] page_window_base,
  output wire [16:0] page_window_end,
  output wire [8:0] free_beats,
  output wire [31:0] checks,
  output logic [31:0] retired,
  output logic [63:0] reply
);
  (* ram_style = "block" *) logic [511:0] fifo[256];
  logic [511:0] beat;
  logic [8:0] head, tail;
  logic [1:0] issue_slot;
  logic loaded;
  wire ready, rsp;
  wire [63:0] rsp_data;
  wire consume = loaded && ready;
  wire fetch = !lock && head != tail && (!loaded || (consume && &issue_slot));
  wire [92:0] cmd = loaded ? beat[128*issue_slot +: 93] : mmio_cmd;
  assign idle = ready && !rsp && !loaded && head == tail;
  assign free_beats = 9'd256 - (tail - head);
  wire [7:0] fifo_addr = erase ? erase_addr[7:0] : stage ? row[7:0] : tail[7:0];
  always_ff @(posedge clk) begin
    for (int i=0; i<64; i++)
      if (erase || ((stage || enqueue) && strb[i]))
        fifo[fifo_addr][8*i +: 8] <= erase ? 8'd0 : wdata[8*i +: 8];
    if (lock) beat <= 0;
    else if (fetch) beat <= fifo[head[7:0]];
    if (lock) begin
      head <= 0; tail <= 0; loaded <= 0; issue_slot <= 0; retired <= 0; reply <= 0;
    end else begin
      if (consume) begin issue_slot <= issue_slot + 1'b1; if (&issue_slot) loaded <= 0; end
      if (fetch) begin head <= head + 1'b1; loaded <= 1; issue_slot <= 0; end
      if (enqueue) tail <= tail + 1'b1;
      if (doorbell) begin
        head <= {1'b0, ring_base};
        tail <= {1'b0, ring_base} + ring_len;
      end
      if (rsp) begin reply <= rsp_data; retired <= retired + 1'b1; end
    end
  end
  qsag_ni_asic_top u_ni (
    .clk, .rst(lock), .cmd_valid(!lock && (loaded || mmio_push)), .cmd_ready(ready),
    .cmd_op(cmd[92:85]), .cmd_idx(cmd[84:80]), .cmd_addr({8'd0,cmd[79:64]}), .cmd_data(cmd[63:0]),
    .host_en(erase || dma_mem), .host_row(erase ? erase_addr[12:0] : row),
    .host_strb(erase ? '1 : strb), .host_data(erase ? '0 : wdata), .host_q(mem_q),
    .fail, .checks, .page_paused, .page_window_base, .page_window_end, .rsp_valid(rsp), .rsp_data
  );
endmodule
