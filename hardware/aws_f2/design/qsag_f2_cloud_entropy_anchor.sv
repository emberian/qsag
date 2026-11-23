// Seed admission is one-shot between global scrubs, before the first vat command.
module qsag_f2_cloud_entropy_anchor (
  input wire clk, clk_ass2, reset_n, lock,
  input wire [9:0] bus_events,
  input wire seed_write, seed_commit,
  input wire [2:0] seed_index,
  input wire [31:0] seed_data,
  output wire seed_complete,
  output wire [31:0] status,
  output logic [511:0] vat_response[3],
  output logic [255:0] fram_seal_key[3],
  output logic [63:0] entropy_word[3],
  output logic entropy_epoch,
  output wire keys_ready
);
  // DCLK at 125 MHz. ADC divider 32 leaves ADCCLK below 5.2 MHz.
  // Read only conversions completed on the temperature, VCCINT and VCCAUX channels.
  (* ASYNC_REG="TRUE" *) logic [1:0] adc_reset_pipe;
  always_ff @(posedge clk_ass2 or negedge reset_n)
    if (!reset_n) adc_reset_pipe <= 0;
    else adc_reset_pipe <= {adc_reset_pipe[0],1'b1};
  wire adc_reset = !adc_reset_pipe[1];

  // UG570: READ presents DNA[0] at DOUT. Sample before each rising SHIFT.
  localparam logic [95:0] SIM_DNA_VALUE = 96'h5153_4147_4632_5655_3437_5021;
  logic [6:0] dna_cycle;
  logic [95:0] dna_latched, dna_uid;
  logic dna_complete, dna_ready;
  wire dna_read = !adc_reset && dna_cycle == 0;
  wire dna_shift = dna_cycle >= 1 && dna_cycle <= 96;
  wire dna_dout;
`ifdef VERILATOR
  logic [95:0] dna_sr;
  always_ff @(posedge clk_ass2)
    if (dna_read) dna_sr <= SIM_DNA_VALUE;
    else if (dna_shift) dna_sr <= {1'b0,dna_sr[95:1]};
  assign dna_dout = dna_sr[0];
`else
  DNA_PORTE2 #(.SIM_DNA_VALUE(SIM_DNA_VALUE)) u_dna
    (.CLK(clk_ass2), .READ(dna_read), .SHIFT(dna_shift), .DIN(1'b0), .DOUT(dna_dout));
`endif
  always_ff @(posedge clk_ass2) begin
    if (adc_reset) begin dna_cycle <= 0; dna_latched <= 0; end
    else if (!dna_complete) begin
      if (dna_shift) dna_latched <= {dna_dout,dna_latched[95:1]};
      if (dna_cycle != 97) dna_cycle <= dna_cycle + 1'b1;
    end
  end

  // Clear the completion flag even when BUFGCE_DIV is held in reset.
  always_ff @(posedge clk_ass2 or negedge reset_n)
    if (!reset_n) dna_complete <= 0;
    else if (!adc_reset && dna_cycle == 97) dna_complete <= 1;

  // The source holds the entire identifier until external reset. Capture once
  // after the destination observes its synchronized completion flag.
  (* ASYNC_REG = "TRUE" *) logic [1:0] dna_sync;
  always_ff @(posedge clk) begin
    if (!reset_n) begin dna_sync <= 0; dna_ready <= 0; dna_uid <= 0; end
    else begin
      dna_sync <= {dna_sync[0],dna_complete};
      if (dna_sync[1] && !dna_ready) begin dna_uid <= dna_latched; dna_ready <= 1; end
    end
  end

  wire eoc, drdy;
  wire [5:0] channel;
  wire [15:0] adc_data;
  logic den;
  logic [7:0] daddr;
`ifdef VERILATOR
  logic [1:0] cadence;
  logic [1:0] model_channel;
  logic [15:0] model_noise, model_data;
  logic model_ready;
  assign channel = {4'd0,model_channel};
  assign eoc = &cadence;
  assign {drdy,adc_data} = {model_ready,model_data};
  always_ff @(posedge clk_ass2) begin
    if (adc_reset) begin
      cadence <= 0; model_channel <= 0; model_noise <= 16'h5ab1;
      model_ready <= 0; model_data <= 0;
    end else begin
      cadence <= cadence + 1'b1; model_ready <= den;
      if (eoc) model_channel <= model_channel == 2 ? 0 : model_channel + 1'b1;
      if (den) begin
        model_noise <= {model_noise[14:0], ^(model_noise & 16'hb400)};
        model_data <= {5'b10011,daddr[1:0],model_noise[8:0]};
      end
    end
  end
`else
  SYSMONE4 #(.INIT_40(16'h0000), .INIT_41(16'h2000), .INIT_42(16'h2000),
             .INIT_48(16'h0700)) u_adc (
    .DCLK(clk_ass2), .RESET(adc_reset), .DADDR(daddr), .DEN(den), .DWE(1'b0),
    .DI(16'd0), .DO(adc_data), .DRDY(drdy), .CHANNEL(channel), .EOC(eoc),
    .CONVST(1'b0), .CONVSTCLK(1'b0), .VAUXN(16'd0), .VAUXP(16'd0),
    .VP(1'b0), .VN(1'b0), .I2C_SCLK(1'b1), .I2C_SDA(1'b1));
`endif
  logic [15:0] slow_time, slow_gray_q;
  logic [15:0] sample_time;
  logic [15:0] sample;
  logic sample_toggle, is_temp;
  always_ff @(posedge clk_ass2) begin
    if (adc_reset) begin
      slow_gray_q <= 0; slow_time <= 0; sample_time <= 0; sample_toggle <= 0; is_temp <= 0;
      den <= 0; daddr <= 0; sample <= 0;
    end else begin
      slow_gray_q <= (slow_time >> 1) ^ slow_time;
      slow_time <= slow_time + 1'b1;
      den <= eoc && channel < 3;
      if (eoc) daddr <= {2'b00,channel};
      if (drdy) begin
        sample <= adc_data; sample_time <= slow_time[15:0]; is_temp <= daddr == 0;
        sample_toggle <= !sample_toggle;
      end
    end
  end
  (* ASYNC_REG = "TRUE" *) logic [2:0] toggle_sync;
  (* ASYNC_REG = "TRUE" *) logic [15:0] slow_gray_m, slow_gray_s;
  wire fresh_edge = toggle_sync[2] != toggle_sync[1];
  logic fresh, is_temp_clk;
  logic [15:0] sample_clk, sample_time_clk, event_slow_time;
  logic [31:0] main_time, last_event;
  function automatic logic [15:0] decode_gray(input logic [15:0] gray);
    for (int i=0; i<16; i++) decode_gray[i] = ^(gray >> i);
  endfunction
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      toggle_sync <= 0; slow_gray_m <= 0; slow_gray_s <= 0;
      {fresh,is_temp_clk,sample_clk,sample_time_clk} <= '0;
      main_time <= 0; last_event <= 0; event_slow_time <= 0;
    end else begin
      toggle_sync <= {toggle_sync[1:0],sample_toggle};
      slow_gray_m <= slow_gray_q;
      slow_gray_s <= slow_gray_m;
      fresh <= fresh_edge;
      // DRDY holds its bundle until the next conversion.
      if (fresh_edge) {sample_clk,sample_time_clk,is_temp_clk} <= {sample,sample_time,is_temp};
      main_time <= main_time + 1'b1;
      if (|bus_events) begin last_event <= main_time; event_slow_time <= decode_gray(slow_gray_s); end
    end
  end

  // Test the unconditioned temperature code LSB (10-bit MSB-justified ADC).
  // Supply readings and bus timing never mask a failed temperature source.
  logic [9:0] window_pos, match_count;
  logic [5:0] run_len;
  logic prev_bit, ref_bit, warm, rct_fail, apt_fail, sysmon_ready;
  logic [17:0] silence;
  logic lock_q;
  always_ff @(posedge clk) lock_q <= lock;
  wire restart_health = lock && !lock_q;
  wire raw = sample_clk[6];
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      window_pos <= 0; match_count <= 0; run_len <= 0; prev_bit <= 0;
      ref_bit <= 0; warm <= 0; rct_fail <= 0; apt_fail <= 0;
      sysmon_ready <= 0; silence <= 0;
    end else if (restart_health) begin
      window_pos <= 0; match_count <= 0; run_len <= 0;
      warm <= 0; sysmon_ready <= 0; silence <= 0;
    end else if (fresh && is_temp_clk) begin
      sysmon_ready <= 1; silence <= 0; prev_bit <= raw;
      if (raw != prev_bit || run_len == 0) run_len <= 1;
      else if (run_len >= 39) rct_fail <= 1;
      else run_len <= run_len + 1'b1;
      window_pos <= window_pos + 1'b1;
      if (window_pos == 0) begin ref_bit <= raw; match_count <= 1; end
      else if (raw == ref_bit) begin
        if (match_count >= 819) apt_fail <= 1;
        else match_count <= match_count + 1'b1;
      end
      if (&window_pos) warm <= 1;
    end else if (&silence) begin sysmon_ready <= 0; warm <= 0; window_pos <= 0; end
    else silence <= silence + 1'b1;
  end
  wire healthy = warm && sysmon_ready && !rct_fail && !apt_fail;

  logic [255:0] pool;
  wire [255:0] incoming = {166'd0,bus_events,main_time-last_event,event_slow_time,
                           fresh ? sample_clk : 16'd0,sample_time_clk};
  always_ff @(posedge clk) begin
    // This unkeyed collection register can warm during scrub. Neither a seed
    // nor a previous generator state feeds it.
    if (!reset_n || restart_health) pool <= 0;
    else pool <= {pool[254:0],1'b0} ^ (pool[255] ? 256'h425 : 256'd0) ^ incoming;
  end

  logic [255:0] seed_words, master, ratchet;
  logic [7:0] written;
  logic seeded;
  logic [15:0] epoch_count;
  assign seed_complete = &written;
  always_ff @(posedge clk) begin
    if (lock) begin seed_words <= 0; master <= 0; written <= 0; seeded <= 0; epoch_count <= 0; end
    else if (seed_commit) begin
      master <= seed_words; seed_words <= 0; written <= 0; seeded <= 1; epoch_count <= epoch_count + 1'b1;
    end else if (seed_write) begin
      seed_words[32*seed_index +: 32] <= seed_data; written[seed_index] <= 1;
    end
  end
  // Interleave the two KDF jobs per vat, then periodically refresh three
  // independent output lanes and an unpublished 256-bit ratchet.
  logic [2:0] job;
  logic busy;
  logic [7:0] period;
  wire [1:0] vat = job[2:1];
  logic ephem_ready;
  logic [255:0] fpga_ephem_secret;
  assign keys_ready = ephem_ready && job == 6 && !lock;
  assign status = {epoch_count,11'd0,seeded,sysmon_ready,apt_fail,rct_fail,healthy && keys_ready};
  wire start = !lock && !seed_commit && !busy &&
               (ephem_ready ? (job < 6 || (healthy && period == 0)) : (dna_ready && healthy));
  logic [1087:0] block_in;
  localparam logic [127:0] EPHEM_TAG = {<<8{"QSAG.F2.EPHEM/v2"}};
  localparam logic [143:0] PUF_TAG = {<<8{"QSAG.F2.PUF_KDF/v2"}};
  localparam logic [151:0] FRAM_TAG = {<<8{"QSAG.F2.FRAM_KDF/v2"}};
  always_comb begin
    block_in = 0;
    if (!ephem_ready)
      block_in[519:0] = {8'h1f,main_time,pool,dna_uid,EPHEM_TAG};
    else if (job == 6)
      block_in[839:0] = {8'h1f,ratchet,pool,fpga_ephem_secret,64'h32474e522e324651};
    else if (job[0])
      block_in[767:0] = {8'h1f,fpga_ephem_secret,dna_uid,master,6'd0,vat,PUF_TAG};
    else
      block_in[775:0] = {8'h1f,fpga_ephem_secret,dna_uid,master,6'd0,vat,FRAM_TAG};
    block_in[1087:1080] = 8'h80;
  end
  wire [1087:0] digest;
  wire done;
  qsag_f2_turboshake u_hash (.clk, .clear(lock || seed_commit), .start, .block_in, .done, .digest);
  wire unused_digest = ^digest[1087:512];
  always_ff @(posedge clk) begin
    if (lock) begin fpga_ephem_secret <= 0; ephem_ready <= 0; end
    else if (!seed_commit && done && !ephem_ready && healthy) begin
      fpga_ephem_secret <= digest[255:0]; ephem_ready <= 1;
    end
    if (lock || seed_commit) begin
      job <= 0; busy <= 0; period <= 0; ratchet <= 0; entropy_epoch <= 0;
      for (int i=0; i<3; i++) begin vat_response[i] <= 0; fram_seal_key[i] <= 0; entropy_word[i] <= 0; end
    end else begin
      period <= period + 1'b1;
      if (start) busy <= 1;
      if (done) begin
        busy <= 0;
        if (ephem_ready && job < 6) begin
          if (job[0]) vat_response[vat] <= digest[511:0];
          else fram_seal_key[vat] <= digest[255:0];
          job <= job + 1'b1;
        end else if (ephem_ready && healthy) begin
          for (int i=0; i<3; i++) entropy_word[i] <= digest[64*i +: 64];
          ratchet <= digest[447:192]; entropy_epoch <= !entropy_epoch;
        end
      end
    end
  end
endmodule
