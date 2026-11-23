`include "cl_qsag_f2_defines.vh"
module cl_qsag_f2_top #(parameter int N_NI = 2, parameter logic [31:0] PCI_ID = `QSAG_TEST_ID) (
  input logic         clk_main_a0,
  input logic         rst_main_n,
  input logic         sh_cl_flr_assert,
  output logic         cl_sh_flr_done,
  output logic [31:0]  cl_sh_id0,
  output logic [31:0]  cl_sh_id1,
  output logic [15:0]  cl_sh_status_vled,
  input logic [15:0]  sh_cl_dma_pcis_awid,
  input logic [63:0]  sh_cl_dma_pcis_awaddr,
  input logic [7:0]   sh_cl_dma_pcis_awlen,
  input logic [2:0]   sh_cl_dma_pcis_awsize,
  input logic [1:0]   sh_cl_dma_pcis_awburst,
  input logic         sh_cl_dma_pcis_awvalid,
  output logic         cl_sh_dma_pcis_awready,
  input logic [511:0] sh_cl_dma_pcis_wdata,
  input logic [63:0]  sh_cl_dma_pcis_wstrb,
  input logic         sh_cl_dma_pcis_wlast,
  input logic         sh_cl_dma_pcis_wvalid,
  output logic         cl_sh_dma_pcis_wready,
  output logic [15:0]  cl_sh_dma_pcis_bid,
  output logic [1:0]   cl_sh_dma_pcis_bresp,
  output logic         cl_sh_dma_pcis_bvalid,
  input logic         sh_cl_dma_pcis_bready,
  input logic [15:0]  sh_cl_dma_pcis_arid,
  input logic [63:0]  sh_cl_dma_pcis_araddr,
  input logic [7:0]   sh_cl_dma_pcis_arlen,
  input logic [2:0]   sh_cl_dma_pcis_arsize,
  input logic [1:0]   sh_cl_dma_pcis_arburst,
  input logic         sh_cl_dma_pcis_arvalid,
  output logic         cl_sh_dma_pcis_arready,
  output logic [15:0]  cl_sh_dma_pcis_rid,
  output logic [511:0] cl_sh_dma_pcis_rdata,
  output logic [1:0]   cl_sh_dma_pcis_rresp,
  output logic         cl_sh_dma_pcis_rlast,
  output logic         cl_sh_dma_pcis_rvalid,
  input logic         sh_cl_dma_pcis_rready,
  input logic [31:0]  ocl_cl_awaddr,
  input logic         ocl_cl_awvalid,
  output logic         cl_ocl_awready,
  input logic [31:0]  ocl_cl_wdata,
  input logic [3:0]   ocl_cl_wstrb,
  input logic         ocl_cl_wvalid,
  output logic         cl_ocl_wready,
  output logic [1:0]   cl_ocl_bresp,
  output logic         cl_ocl_bvalid,
  input logic         ocl_cl_bready,
  input logic [31:0]  ocl_cl_araddr,
  input logic         ocl_cl_arvalid,
  output logic         cl_ocl_arready,
  output wire  [31:0]  cl_ocl_rdata,
  output logic [1:0]   cl_ocl_rresp,
  output logic         cl_ocl_rvalid,
  input logic         ocl_cl_rready
);
  if (N_NI < 1 || N_NI > 4) begin : bad_parameter
    initial $error("N_NI must be 1..4");
  end
  localparam int IW = N_NI > 2 ? 2 : 1;
  wire clk = clk_main_a0;
  (* ASYNC_REG = "TRUE" *) logic [1:0] reset_pipe;
  always_ff @(posedge clk or negedge rst_main_n)
    if (!rst_main_n) reset_pipe <= 0;
    else reset_pipe <= {reset_pipe[0],1'b1};
  logic clk_ass2;
`ifdef VERILATOR
  always_ff @(posedge clk_main_a0 or negedge reset_pipe[1])
    if (!reset_pipe[1]) clk_ass2 <= 0;
    else clk_ass2 <= !clk_ass2;
`else
  BUFGCE_DIV #(.BUFGCE_DIVIDE(2), .IS_CE_INVERTED(1'b0),
    .IS_CLR_INVERTED(1'b0), .IS_I_INVERTED(1'b0)) u_ass2_clock
    (.I(clk_main_a0), .CE(1'b1), .CLR(!reset_pipe[1]), .O(clk_ass2));
`endif
  logic erase, flr_seen, trigger;
  logic [14:0] erase_addr;
  logic [31:0] scrub_epoch;
  wire bus_reset = !reset_pipe[1] || sh_cl_flr_assert;
  wire lock = bus_reset || erase || trigger;
  assign cl_sh_flr_done = reset_pipe[1] && sh_cl_flr_assert && flr_seen && !erase;
  always_ff @(posedge clk) begin
    flr_seen <= sh_cl_flr_assert && reset_pipe[1];
    if (!reset_pipe[1]) begin
      erase <= 1; erase_addr <= 0; scrub_epoch <= 0;
    end else if ((sh_cl_flr_assert && !flr_seen) || trigger) begin
      erase <= 1; erase_addr <= 0; scrub_epoch <= scrub_epoch + 32'd1;
    end else if (erase) begin
      erase_addr <= erase_addr + 1'b1;
      if (&erase_addr) erase <= 0;
    end
  end
  assign cl_sh_id0 = PCI_ID;
  assign cl_sh_id1 = `QSAG_MAGIC;
  logic [63:0] cycles;
  always_ff @(posedge clk) if (!reset_pipe[1]) cycles <= 0; else cycles <= cycles + 1'b1;

  // One active PCIS burst. AW and AR arbitrate a single wide SRAM port.
  logic writing, reading, wbad, rbad;
  logic [63:0] wa, ra;
  logic [7:0] wleft, rleft;
  logic [IW-1:0] rsel;
  wire [1:0] wi = wa[21:20];
  wire [1:0] ri = ra[21:20];
  wire [N_NI-1:0] idle, fail, page_paused;
  wire [15:0] page_window_base[N_NI];
  wire [16:0] page_window_end[N_NI];
  wire [8:0] free_beats[N_NI];
  wire [31:0] checks[N_NI], retired[N_NI];
  wire [63:0] reply[N_NI];
  wire [511:0] mem_q[N_NI];
  logic [31:0] arg[N_NI][3];
  logic [31:0] ring_addr, ring_len;
  wire [1:0] ring_engine = ring_addr[21:20];
  wire port_busy = writing || reading || cl_sh_dma_pcis_rvalid;
  assign cl_sh_dma_pcis_awready = !bus_reset && !port_busy && !cl_sh_dma_pcis_bvalid;
  assign cl_sh_dma_pcis_arready = cl_sh_dma_pcis_awready && !sh_cl_dma_pcis_awvalid;
  // 512-bit aligned INCR, restricted to a single 4 KiB AXI page.
  function automatic logic valid_addr(input logic [63:0] a, input logic [7:0] len,
      input logic [2:0] size, input logic [1:0] burst);
    return (a[19:0] < 20'h84000 || a[19:16] == 4'hc) && a[63:22] == 0 && int'(a[21:20]) < N_NI && size == 6 && burst == 1
      && (len == 0 || a[5:0] == 0) && (9'(a[11:6]) + 9'(len) < 64);
  endfunction
  wire [63:0] aw = sh_cl_dma_pcis_awaddr, ar = sh_cl_dma_pcis_araddr;
  wire full_beat = &sh_cl_dma_pcis_wstrb;
  wire is_stream = wa[19:16] == 4'hc;
  wire is_stage = wa[19:14] == 6'h20;
  wire wlast_ok = sh_cl_dma_pcis_wlast == (wleft == 0);
  wire beat_bad = wbad || !wlast_ok || (is_stream && !full_beat);
  assign cl_sh_dma_pcis_wready = !bus_reset && writing;
  wire wfire = cl_sh_dma_pcis_wready && sh_cl_dma_pcis_wvalid;
  wire rissue = !bus_reset && reading && (!cl_sh_dma_pcis_rvalid || sh_cl_dma_pcis_rready);
  assign cl_sh_dma_pcis_rdata = !lock && cl_sh_dma_pcis_rvalid && cl_sh_dma_pcis_rresp == 0 ? mem_q[rsel] : '0;
  always_ff @(posedge clk) begin
    if (bus_reset) begin
      writing <= 0; reading <= 0; cl_sh_dma_pcis_bvalid <= 0; cl_sh_dma_pcis_rvalid <= 0;
      wa <= 0; ra <= 0; wbad <= 0; rbad <= 0; wleft <= 0; rleft <= 0; rsel <= 0;
      cl_sh_dma_pcis_bid <= 0; cl_sh_dma_pcis_rid <= 0; cl_sh_dma_pcis_rlast <= 0;
      cl_sh_dma_pcis_bresp <= 0; cl_sh_dma_pcis_rresp <= 0;
    end else begin
      if (sh_cl_dma_pcis_bready) cl_sh_dma_pcis_bvalid <= 0;
      if (sh_cl_dma_pcis_rready) cl_sh_dma_pcis_rvalid <= 0;
      if (cl_sh_dma_pcis_awready && sh_cl_dma_pcis_awvalid) begin
        writing <= 1; wa <= aw; wleft <= sh_cl_dma_pcis_awlen; cl_sh_dma_pcis_bid <= sh_cl_dma_pcis_awid;
        wbad <= lock || !valid_addr(aw, sh_cl_dma_pcis_awlen, sh_cl_dma_pcis_awsize, sh_cl_dma_pcis_awburst)
          || (aw[19:16] == 4'hc && {1'b0,sh_cl_dma_pcis_awlen} >= free_beats[IW'(aw[21:20])])
          || (aw[19:16] != 4'hc && (aw[19] && aw[19:14] != 6'h20 || !idle[IW'(aw[21:20])]))
          || (!aw[19] && page_paused[IW'(aw[21:20])] && (
                {aw[18:6], 3'd0} < page_window_base[IW'(aw[21:20])] ||
                ({1'b0, aw[18:6], 3'd0} + ({6'd0, sh_cl_dma_pcis_awlen, 3'd0} + 17'd8) > page_window_end[IW'(aw[21:20])])));
      end
      if (wfire) begin
        wa <= wa + 64; wleft <= wleft - 1'b1; wbad <= beat_bad;
        if (wleft == 0 || sh_cl_dma_pcis_wlast) begin
          writing <= 0; cl_sh_dma_pcis_bvalid <= 1; cl_sh_dma_pcis_bresp <= beat_bad ? 2'd2 : 0;
        end
      end
      if (cl_sh_dma_pcis_arready && sh_cl_dma_pcis_arvalid) begin
        reading <= 1; ra <= ar; rleft <= sh_cl_dma_pcis_arlen; cl_sh_dma_pcis_rid <= sh_cl_dma_pcis_arid;
        rbad <= lock || !valid_addr(ar, sh_cl_dma_pcis_arlen, sh_cl_dma_pcis_arsize, sh_cl_dma_pcis_arburst)
          || ar[19] || !idle[IW'(ar[21:20])];
      end
      if (rissue) begin
        rsel <= IW'(ri); ra <= ra + 64; rleft <= rleft - 1'b1;
        cl_sh_dma_pcis_rvalid <= 1; cl_sh_dma_pcis_rlast <= rleft == 0;
        cl_sh_dma_pcis_rresp <= rbad ? 2'd2 : 0;
        if (rleft == 0) reading <= 0;
      end
    end
  end

  // AXI-Lite address and data channels have independent holding registers.
  logic has_aw, has_w, rejected_write;
  logic [31:0] addr, wd;
  logic [3:0] ws;
  wire zeroize_pending = has_aw && has_w && !cl_ocl_bvalid && addr == 'h28;
  assign cl_ocl_awready = reset_pipe[1] && !sh_cl_flr_assert && !has_aw && !cl_ocl_bvalid;
  assign cl_ocl_wready = reset_pipe[1] && !sh_cl_flr_assert && !has_w && !cl_ocl_bvalid;
  assign cl_ocl_arready = reset_pipe[1] && !sh_cl_flr_assert && !trigger && !zeroize_pending && (!cl_ocl_rvalid || ocl_cl_rready);
  wire write_req = has_aw && has_w && !cl_ocl_bvalid && !lock && !rejected_write && (&ws);
  wire [31:0] vat_status[3];
  wire [7:0] vat_rx[3];
  wire [2:0] vat_ctl[3];
  logic [N_NI-1:0] push;
  logic [2:0] ctrl_we, xfer_we;
  logic bell, csr_ok;
  wire [31:0] anchor_status;
  wire [511:0] vat_response[3];
  wire [255:0] fram_seal_key[3];
  wire [63:0] entropy_word[3];
  wire entropy_epoch, keys_ready;
  logic custody_used;
  wire seed_open = keys_ready && !custody_used && !anchor_status[4];
  wire seed_addr = addr >= 'h30 && addr <= 'h4c && addr[1:0] == 0;
  wire seed_write = write_req && seed_open && seed_addr;
  wire seed_complete;
  wire seed_commit = write_req && seed_open && seed_complete && addr == 'h50 && wd == 1;
  always_ff @(posedge clk)
    if (lock) custody_used <= 0;
    else if (|ctrl_we || |xfer_we) custody_used <= 1;
  wire [9:0] bus_events = {
    cl_ocl_awready && ocl_cl_awvalid, cl_ocl_wready && ocl_cl_wvalid,
    cl_ocl_bvalid && ocl_cl_bready, cl_ocl_arready && ocl_cl_arvalid,
    cl_ocl_rvalid && ocl_cl_rready, cl_sh_dma_pcis_awready && sh_cl_dma_pcis_awvalid,
    wfire, cl_sh_dma_pcis_bvalid && sh_cl_dma_pcis_bready,
    cl_sh_dma_pcis_arready && sh_cl_dma_pcis_arvalid, cl_sh_dma_pcis_rvalid && sh_cl_dma_pcis_rready};
  qsag_f2_cloud_entropy_anchor u_entropy (.clk, .clk_ass2, .reset_n(reset_pipe[1]),
    .lock, .bus_events, .seed_write, .seed_index(addr[4:2] ^ 3'd4), .seed_data(wd),
    .seed_commit, .seed_complete, .status(anchor_status), .vat_response, .fram_seal_key,
    .entropy_word, .entropy_epoch, .keys_ready);
  // Prevent a simultaneous AXI address acceptance from racing an OCL issue.
  wire dma_exclusive = port_busy || sh_cl_dma_pcis_awvalid || sh_cl_dma_pcis_arvalid;
  always_comb begin
    push = '0; ctrl_we = 0; xfer_we = 0; bell = 0; csr_ok = 0;
    if (write_req) begin
      case (addr)
        'h10, 'h14: csr_ok = 1;
        'h28: csr_ok = wd == 1 && !dma_exclusive && !cl_ocl_rvalid;
        'h18: begin
          bell = wd == 1 && !dma_exclusive && ring_addr[31:22] == 0 && int'(ring_engine) < N_NI
            && ring_addr[19:14] == 6'h20 && ring_addr[5:0] == 0 && ring_len != 0 && ring_len <= 256 && idle[IW'(ring_engine)];
          csr_ok = bell;
        end
        default: begin
          csr_ok = seed_write || seed_commit;
          for (int i=0; i<N_NI; i++) begin
            if (addr == (i+1)*4096 || addr == (i+1)*4096+4 || addr == (i+1)*4096+8) csr_ok = 1;
            if (addr == (i+1)*4096+12 && wd == 1 && idle[i] && !dma_exclusive) begin push[i]=1; csr_ok=1; end
          end
          for (int i=0; i<3; i++) begin
            if (addr == (i+1)*65536 && wd < 8 && keys_ready && !vat_status[i][0]) begin ctrl_we[i]=1; csr_ok=1; end
            if (addr == (i+1)*65536+4 && wd < 768 && keys_ready && anchor_status[0] && vat_ctl[i] == 1 && !vat_status[i][0]) begin xfer_we[i]=1; csr_ok=1; end
          end
        end
      endcase
    end
  end
  always_ff @(posedge clk) begin
    trigger <= 0;
    if (!reset_pipe[1] || sh_cl_flr_assert) begin
      has_aw <= 0; has_w <= 0; rejected_write <= 0; cl_ocl_bvalid <= 0; cl_ocl_bresp <= 0;
      addr <= 0; wd <= 0; ws <= 0;
    end else begin
      if (ocl_cl_bready) cl_ocl_bvalid <= 0;
      if (cl_ocl_awready && ocl_cl_awvalid) begin has_aw <= 1; addr <= ocl_cl_awaddr; end
      if (cl_ocl_wready && ocl_cl_wvalid) begin has_w <= 1; wd <= ocl_cl_wdata; ws <= ocl_cl_wstrb; end
      // Either AXI half can arrive during a scrub and remain pending until
      // afterwards. Drain that transaction with SLVERR and wipe WDATA now.
      if (lock) begin
        wd <= 0;
        if (has_aw || has_w || (cl_ocl_awready && ocl_cl_awvalid) ||
            (cl_ocl_wready && ocl_cl_wvalid)) rejected_write <= 1;
      end
      if (has_aw && has_w && !cl_ocl_bvalid) begin
        rejected_write <= 0;
        has_aw <= 0; has_w <= 0; cl_ocl_bvalid <= 1; cl_ocl_bresp <= csr_ok ? 0 : 2'd2;
        trigger <= csr_ok && addr == 'h28;
        wd <= 0;
      end
    end
    if (lock) begin ring_addr <= 0; ring_len <= 0; end
    else if (write_req) begin
      if (addr == 'h10) ring_addr <= wd;
      if (addr == 'h14) ring_len <= wd;
    end
  end
  for (genvar i=0; i<N_NI; i++) begin : engines
    for (genvar j=0; j<3; j++) begin : args
      always_ff @(posedge clk)
        if (lock) arg[i][j] <= 0;
        else if (write_req && addr == (i+1)*4096+4*j) arg[i][j] <= wd;
    end
    wire store = wfire && !beat_bad && wi == 2'(i);
    (* KEEP_HIERARCHY="yes" *) qsag_f2_engine u_engine (
      .clk, .lock, .erase, .erase_addr(erase_addr[12:0]), .dma_mem((store && !wa[19]) || (rissue && !rbad && ri == 2'(i))),
      .stage(store && is_stage), .enqueue(store && is_stream), .doorbell(bell && ring_engine == 2'(i)),
      .mmio_push(push[i]), .row(writing ? wa[18:6] : ra[18:6]),
      .strb(writing ? sh_cl_dma_pcis_wstrb : 64'd0), .wdata(sh_cl_dma_pcis_wdata),
      .ring_base(ring_addr[13:6]), .ring_len(ring_len[8:0]),
      .mmio_cmd({arg[i][2][28:0],arg[i][1],arg[i][0]}),
      .mem_q(mem_q[i]), .idle(idle[i]), .fail(fail[i]), .page_paused(page_paused[i]),
      .page_window_base(page_window_base[i]), .page_window_end(page_window_end[i]),
      .free_beats(free_beats[i]), .checks(checks[i]), .retired(retired[i]), .reply(reply[i])
    );
  end
  wire [2:0] vat_fault, vat_pass, vat_tamper;
  for (genvar i=0; i<3; i++) begin : vats
    (* KEEP_HIERARCHY="yes" *) qsag_f2_ass2_bridge #(.VAT_ID(i)) u_bridge (.clk, .clk_ass2, .shell_reset_n(reset_pipe[1]), .lock, .erase, .erase_addr,
      .cloud_response(vat_response[i]), .cloud_word(entropy_word[i]), .cloud_epoch(entropy_epoch),
      .cloud_ok(anchor_status[0]), .cloud_rct(anchor_status[1]), .cloud_apt(anchor_status[2]),
      .seal_key(fram_seal_key[i]), .keys_ready, .ctrl_we(ctrl_we[i]), .xfer_we(xfer_we[i]), .data(wd[10:0]),
      .status(vat_status[i]), .rx(vat_rx[i]), .control(vat_ctl[i]));
    assign {vat_tamper[i],vat_fault[i],vat_pass[i]} = vat_status[i][5:3];
  end
  assign cl_sh_status_vled = {3'd0, vat_tamper, vat_fault, vat_pass, lock, |fail, !(&idle), |vat_pass};
  logic [31:0] csr_read_q;
  assign cl_ocl_rdata = (!reset_pipe[1] || sh_cl_flr_assert || trigger) ? 0 : csr_read_q;
  logic [31:0] rd;
  logic rd_ok;
  always_comb begin
    rd = 0; rd_ok = 1;
    case (ocl_cl_araddr)
      'h0: rd = `QSAG_MAGIC;
      'h4: rd = `QSAG_ABI;
      'h8: rd = N_NI;
      'hc: rd = {15'd0,lock,8'd3,8'd4};
      'h54: rd = lock ? 0 : anchor_status;
      'h10: rd = ring_addr;
      'h14: rd = ring_len;
      'h1c: for (int i=0; i<N_NI; i++) rd += retired[i];
      'h20: rd = cycles[31:0];
      'h24: rd = cycles[63:32];
      'h28: rd = 32'(lock || !keys_ready);
      'h2c: rd = scrub_epoch;
      default: begin
        rd_ok = 0;
        for (int i=0; i<N_NI; i++) begin
          case (ocl_cl_araddr - (i+1)*4096)
            16: begin rd_ok=!lock; rd={14'd0,free_beats[i],6'd0,|free_beats[i],fail[i],idle[i]}; end
            20: begin rd_ok=!lock; rd=checks[i]; end
            24: begin rd_ok=!lock; rd=reply[i][31:0]; end
            28: begin rd_ok=!lock; rd=reply[i][63:32]; end
            32: begin rd_ok=!lock; rd=retired[i]; end
            default: ;
          endcase
        end
        for (int i=0; i<3; i++) begin
          case (ocl_cl_araddr - (i+1)*65536)
            0: begin rd_ok=!lock; rd=32'(vat_ctl[i]); end
            8: begin rd_ok=!lock; rd=vat_status[i]; end
            12: begin rd_ok=!lock; rd=32'(vat_rx[i]); end
            default: ;
          endcase
        end
      end
    endcase
  end
  always_ff @(posedge clk) begin
    if (!reset_pipe[1] || sh_cl_flr_assert || trigger) begin cl_ocl_rvalid <= 0; csr_read_q <= 0; cl_ocl_rresp <= 0; end
    else begin
      if (ocl_cl_rready) cl_ocl_rvalid <= 0;
      if (cl_ocl_arready && ocl_cl_arvalid) begin
        cl_ocl_rvalid <= 1; csr_read_q <= rd_ok ? rd : 0; cl_ocl_rresp <= rd_ok ? 0 : 2'd2;
      end
    end
  end
endmodule
