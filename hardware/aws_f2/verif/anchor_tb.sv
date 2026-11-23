// Focused fault injection and storage tests. Only the testbench observes keys/RAM.
module anchor_tb;
  bit clk, slow;
  always #2 clk = !clk;
  always @(posedge clk) slow <= !slow;
  bit reset_n, lock, seed_write, seed_commit;
  logic [2:0] index_word;
  logic [31:0] data_word, status;
  wire complete, epoch, ready;
  logic [2:0] bus_phase;
  always @(posedge clk) bus_phase <= bus_phase + 1'b1;
  wire [9:0] bus_events = {9'd0,bus_phase[1]};
  wire [511:0] response[3];
  wire [255:0] keys[3];
  wire [63:0] words[3];
  qsag_f2_cloud_entropy_anchor dut (.clk, .clk_ass2(slow), .reset_n, .lock,
    .bus_events, .seed_write, .seed_commit, .seed_index(index_word), .seed_data(data_word),
    .seed_complete(complete), .status, .vat_response(response), .fram_seal_key(keys),
    .entropy_word(words), .entropy_epoch(epoch), .keys_ready(ready));
  bit cs_n=1, sck, mosi, erase, rst;
  logic [14:0] erase_addr;
  wire miso;
  qsag_f2_fram_model fram (.clk, .rst, .erase, .erase_addr, .cs_n, .sck, .mosi,
    .miso, .seal_key(256'h50dc2fdef53ae6803b86c231bade73cddcd5c5a4e25f6bf02d74f8d9ecaf292e));
  task automatic clocks(int n);
    repeat (n) @(negedge clk);
  endtask
  task automatic restart;
    reset_n=0; lock=1; clocks(8); reset_n=1; clocks(8); lock=0; clocks(2);
  endtask
  task automatic spi(input byte value, output byte result);
    for (int i=7; i>=0; i--) begin
      mosi=value[i]; clocks(8); result[i]=miso; sck=1; clocks(8); sck=0;
    end
  endtask
  task automatic transact(input bit write_op, input logic [14:0] address,
                          input byte first, second);
    byte rx;
    if (write_op) begin cs_n=0; spi(6,rx); cs_n=1; clocks(2); end
    cs_n=0; spi(write_op ? 2 : 3, rx); spi(8'(address >> 8), rx); spi(8'(address), rx);
    spi(first,rx); if (!write_op && rx != first) $fatal(1,"read %x got %x expected %x",address,rx,first);
    spi(second,rx); if (!write_op && rx != second) $fatal(1,"sequential read");
    cs_n=1; clocks(2);
  endtask
  task automatic sample_clock;
    while (!(dut.fresh && dut.is_temp_clk)) clocks(1);
    clocks(1);
  endtask
  // Independent binary scoreboard exists only in the testbench. Check both
  // event and idle cycles, including the 16-bit source counter rollover.
  logic [15:0] source_time, time_m, time_s, expected_event;
  logic saw_wrap;
  logic expected_fresh;
  logic [32:0] expected_sample;
  always @(posedge slow) begin
    if (dut.adc_reset) begin source_time <= 0; saw_wrap <= 0; end
    else begin
      source_time <= dut.slow_time;
      if (&dut.slow_time) saw_wrap <= 1;
    end
  end
  always @(posedge clk) begin
    if (!reset_n) begin
      {time_m,time_s,expected_event} <= '0;
      {expected_fresh,expected_sample} <= '0;
    end else begin
      time_m <= source_time; time_s <= time_m;
      if (|bus_events) expected_event <= time_s;
      expected_fresh <= dut.fresh_edge;
      if (dut.fresh_edge) expected_sample <= {dut.sample,dut.sample_time,dut.is_temp};
    end
  end
  always @(negedge clk) begin
    if (reset_n && (dut.event_slow_time !== expected_event ||
        {dut.fresh,dut.sample_clk,dut.sample_time_clk,dut.is_temp_clk} !==
        {expected_fresh,expected_sample})) $fatal(1,"CDC timestamp or conversion alignment");
  end
  // Re-run the six jobs under a controlled, identical all-zero BAR seed.
  // This direct unit stimulus can pulse commit without the top's admission gate.
  task automatic rederive_zero_master;
    seed_commit=1; clocks(1); seed_commit=0; clocks(100);
    if (!ready || dut.master != 0) $fatal(1,"KDF test setup");
  endtask
  logic [255:0] first_ephem, first_key[3];
  logic [511:0] first_response[3];
  // Check the byte positions at the actual permutation input for all six
  // jobs. Neither input value is exported from the simulation.
  always @(posedge clk) begin
    if (dut.start && dut.ephem_ready && dut.job < 6) begin
      int offset;
      offset = dut.job[0] ? 144 : 152;
      if (dut.block_in[offset +: 8] != 8'(dut.vat) ||
          dut.block_in[offset+8 +: 256] != dut.master ||
          dut.block_in[offset+264 +: 96] != dut.dna_uid ||
          dut.block_in[offset+360 +: 256] != dut.fpga_ephem_secret)
        $fatal(1,"incorrect vat KDF transcript");
    end
  end
  initial begin
    lock=1; clocks(8); reset_n=1;
    wait (!dut.adc_reset);
    repeat (97) @(posedge slow); @(negedge slow);
    if (dut.dna_complete || dut.dna_latched != 96'h5153_4147_4632_5655_3437_5021)
      $fatal(1,"serial DNA bit order or length");
    @(posedge slow); @(negedge slow);
    if (!dut.dna_complete) $fatal(1,"DNA completion");
    clocks(4);
    if (dut.dna_uid != dut.SIM_DNA_VALUE || !dut.dna_ready || dut.ephem_ready || ready) $fatal(1,"DNA completion edge");
    lock=0;
    clocks(33000);
    if (status != 9) $fatal(1,"healthy startup");
    first_ephem = dut.fpga_ephem_secret;
    if (!dut.ephem_ready || first_ephem == 0) $fatal(1,"ephemeral bootstrap");
    for (int i=0; i<3; i++) begin
      first_key[i] = keys[i]; first_response[i] = response[i];
      if (keys[i] == 0 || response[i] == 0) $fatal(1,"unseeded vat material");
    end
    for (int i=0; i<8; i++) begin
      seed_write=1; index_word=3'(i); data_word=32'h03020100 + 32'h04040404*i; clocks(1);
    end
    seed_write=0;
    if (!complete) $fatal(1,"incomplete mailbox");
    seed_commit=1; clocks(1); seed_commit=0; clocks(100);
    if (dut.seed_words != 0 || status != 'h10019) $fatal(1,"commit");
    if (first_ephem != dut.fpga_ephem_secret) $fatal(1,"commit discarded private secret");
    for (int i=0; i<3; i++)
      if (keys[i] == first_key[i] || response[i] == first_response[i] ||
          keys[i] == 0 || response[i] == 0) $fatal(1,"seeded key derivation");
    transact(1,127,8'h12,8'h34);
    transact(1,32767,8'h56,8'h78);
    if (fram.mem[127] != {1'b1,8'h12 ^ 8'hf6} || fram.mem[128] != {1'b1,8'h34 ^ 8'hb2} ||
        fram.mem[32767] != {1'b1,8'h56 ^ 8'hf1} || fram.mem[0] != {1'b1,8'h78 ^ 8'h37})
      $fatal(1,"address-bound ciphertext");
    rst=1; clocks(4); rst=0;
    transact(0,127,8'h12,8'h34);
    transact(0,32767,8'h56,8'h78);
    lock=1; rst=1; erase=1;
    clocks(1);
    if (dut.ephem_ready || dut.fpga_ephem_secret != 0 || ready) $fatal(1,"late lock clear");
    for (int i=0; i<32768; i++) begin erase_addr=15'(i); clocks(1); end
    for (int i=0; i<32768; i++) if (fram.mem[i] != 9'h0ff) $fatal(1,"scrub %x",i);
    if (dut.master != 0 || dut.ratchet != 0 || dut.seed_words != 0 || dut.u_hash.state != 0)
      $fatal(1,"secret state survived lock");
    for (int i=0; i<3; i++)
      if (keys[i] != 0 || words[i] != 0 || response[i] != 0) $fatal(1,"vat material survived lock");
    erase=0; rst=0; lock=0; clocks(100);
    if (!ready || first_ephem == dut.fpga_ephem_secret) $fatal(1,"new unseeded epoch");
    transact(0,32767,8'hff,8'hff);
    for (int i=0; i<3; i++) begin
      if (first_key[i]==keys[i] || first_response[i]==response[i])
        $fatal(1,"same zero master, new private epoch failed to rotate");
      first_key[i]=keys[i]; first_response[i]=response[i];
    end
    rederive_zero_master();
    for (int i=0; i<3; i++)
      if (first_key[i]!=keys[i] || first_response[i]!=response[i]) $fatal(1,"zero-master control");
    clocks(131080);
    if (!saw_wrap) $fatal(1,"timestamp rollover coverage");
    restart();
    force dut.raw=0;
    repeat (39) sample_clock();
    if (status[1]) $fatal(1,"early RCT");
    sample_clock();
    if (!status[1] || status[0]) $fatal(1,"RCT cutoff");
    release dut.raw;
    restart();
    for (int i=0; i<1023; i++) begin
      if (i%5==4) begin force dut.raw=1; end else begin force dut.raw=0; end
      sample_clock();
    end
    if (status[2:0] != 0) $fatal(1,"early APT");
    force dut.raw=0; sample_clock();
    if (status[2:0] != 4) $fatal(1,"APT cutoff or release on failed window");
    $display("PASS exact RCT/APT cutoffs, DNA readout, Gray rollover and aligned DRDY, private inputs in all KDF transcripts, zero-master epoch rotation, ciphertext vector, FRAM boundary and wrap, secret and full BRAM wipe");
    $finish;
  end
endmodule
