// Byte transaction engine. CS is held independently for an entire ASS2 frame.
// Mode 0, MSB first per byte, x1 receives on DQ1. DQ direction comes from
// the target's actual pad OEs. Each SCK half-cycle spans eight enclave clocks.
module qsag_f2_ass2_bridge #(parameter int VAT_ID = 0) (
  input wire clk, clk_ass2, shell_reset_n, lock, erase,
  input wire [14:0] erase_addr,
  input wire [511:0] cloud_response,
  input wire [63:0] cloud_word,
  input wire cloud_epoch, cloud_ok, cloud_rct, cloud_apt, keys_ready,
  input wire [255:0] seal_key,
  input wire ctrl_we, xfer_we,
  input wire [10:0] data,
  output wire [31:0] status,
  output wire [7:0] rx,
  output wire [2:0] control
);
  logic [2:0] ctl;
  logic [7:0] tx, received;
  logic [1:0] mode;
  logic [3:0] divcnt;
  logic [2:0] remaining;
  logic active, sck;
  wire [37:0] pins, oe, pad_in;
  wire [3:0] unused_pu, unused_pd;
  wire [37:0] unused_cs, unused_sl, unused_ie, unused_pullup, unused_pulldown;
  wire miso;
  logic release_n;
  always_ff @(posedge clk or negedge shell_reset_n)
    if (!shell_reset_n) release_n <= 1'b0;
    else release_n <= !lock && keys_ready && !ctl[1] && cloud_ok;
  (* ASYNC_REG="TRUE" *) logic [1:0] reset_pipe;
  always_ff @(posedge clk_ass2 or negedge release_n)
    if (!release_n) reset_pipe <= 0;
    else reset_pipe <= {reset_pipe[0],1'b1};
  wire reset_n = reset_pipe[1];
  wire tamper_n = !ctl[2];
  wire cs_n = !ctl[0] || !release_n || !tamper_n;
  wire [7:0] drive = mode == 2 ? tx : mode == 1 ? {4'd0,tx[7:4]} : {7'd0,tx[7]};
  // Synchronize the level and generate scrub addresses at the RAM clock.
  // A global erase lasts 16384 vat clocks for two 512-byte RAMs in parallel.
  (* ASYNC_REG = "TRUE" *) logic [1:0] erase_sync;
  wire vat_erase = erase_sync[1];
  logic [8:0] vat_addr;
  always_ff @(posedge clk_ass2 or negedge shell_reset_n)
    if (!shell_reset_n) erase_sync <= 0;
    else erase_sync <= {erase_sync[0],erase};
  always_ff @(posedge clk_ass2) begin
    if (!vat_erase) vat_addr <= 0;
    else vat_addr <= vat_addr + 1'b1;
  end

  // The serial data changes on the falling phase and is consumed on the
  // rising phase, eight vat clocks later. CS precedes the first rising edge.
  (* ASYNC_REG = "TRUE" *) logic [10:0] spi_meta, spi_sync;
  wire vat_cs, vat_tamper, vat_sck;
  wire [7:0] vat_drive;
  assign {vat_cs,vat_tamper,vat_sck,vat_drive} = spi_sync;
  always_ff @(posedge clk_ass2) begin
    spi_meta <= {cs_n,tamper_n,sck,drive};
    spi_sync <= spi_meta;
  end

  // The KDF holds response stable before reset release and throughout use.
  // The epoch toggle qualifies its word, held for 256 main cycles.
  logic response_captured;
  logic [511:0] response_q;
  logic [63:0] word_q;
  logic epoch_q;
  (* ASYNC_REG = "TRUE" *) logic [1:0] epoch_sync;
  (* ASYNC_REG = "TRUE" *) logic [2:0] health_meta, health_sync;
  wire ok_q, rct_q, apt_q;
  assign {ok_q,rct_q,apt_q} = health_sync;
  always_ff @(posedge clk_ass2 or negedge reset_n) begin
    if (!reset_n) begin
      {epoch_sync,epoch_q,word_q,response_q,response_captured} <= '0;
      {health_meta,health_sync} <= '0;
    end else begin
      epoch_sync <= {epoch_sync[0],cloud_epoch};
      if (epoch_sync[1] != epoch_q) begin word_q <= cloud_word; epoch_q <= epoch_sync[1]; end
      health_meta <= {cloud_ok,cloud_rct,cloud_apt};
      health_sync <= health_meta;
      if (!response_captured) begin response_q <= cloud_response; response_captured <= 1; end
    end
  end
  assign pad_in = {10'd0,1'b1,vat_tamper,miso,6'd0,vat_sck,10'd0,vat_drive};

  // Mask DQ at the source before crossing. Its destination samples only on
  // the SPI receive phase. FRAM SCK and MOSI likewise have a half-bit setup.
  logic [7:0] vat_dq;
  always_ff @(posedge clk_ass2) vat_dq <= pins[7:0] & oe[7:0];
  (* ASYNC_REG = "TRUE" *) logic [7:0] dq_meta, dq_q;
  (* ASYNC_REG = "TRUE" *) logic [3:0] status_meta, status_q;
  (* ASYNC_REG = "TRUE" *) logic [2:0] fram_meta, fram_q;
  always_ff @(posedge clk) begin
    status_meta <= {pins[17:16],pins[20],pins[19]};
    dq_meta <= vat_dq;
    fram_meta <= pins[24:22];
    {status_q,dq_q,fram_q} <= {status_meta,dq_meta,fram_meta};
  end
  assign control = ctl;
  assign rx = received;
  assign status = {26'd0,ctl[2],status_q,active};
  qsag_ass2_enclave_top #(.VAT_ID(VAT_ID)) u_vat (
    .clk(clk_ass2), .rst_n(reset_n), .erase(vat_erase), .erase_addr(vat_addr),
    .cloud_response(response_q), .cloud_word(word_q), .cloud_epoch(epoch_q),
    .cloud_ok(ok_q), .cloud_rct(rct_q), .cloud_apt(apt_q),
    .input_in({vat_cs,3'd0}), .input_pu(unused_pu), .input_pd(unused_pd),
    .bidir_in(pad_in), .bidir_out(pins), .bidir_oe(oe),
    .bidir_cs(unused_cs), .bidir_sl(unused_sl), .bidir_ie(unused_ie),
    .bidir_pu(unused_pullup), .bidir_pd(unused_pulldown)
  );
  qsag_f2_fram_model u_anchor (.clk, .rst(!release_n || !tamper_n), .erase, .erase_addr, .seal_key,
    .cs_n(fram_q[0]), .sck(fram_q[1]), .mosi(fram_q[2]), .miso);
  always_ff @(posedge clk) begin
    if (lock) ctl <= 0;
    else if (ctrl_we) ctl <= data[2:0];
    if (cs_n || lock || ctrl_we) begin
      active <= 0; sck <= 0; tx <= 0; received <= 0; remaining <= 0; divcnt <= 0; mode <= 0;
    end else if (xfer_we) begin
      tx <= data[7:0]; received <= 0; mode <= data[9:8]; divcnt <= 0;
      remaining <= data[9] ? 0 : data[8] ? 1 : 7; active <= 1;
    end else if (active) begin
      divcnt <= divcnt + 1'b1;
      if (&divcnt) begin
        sck <= !sck;
        if (!sck) begin
          case (mode)
            2: received <= dq_q;
            1: received <= {received[3:0], dq_q[3:0]};
            default: received <= {received[6:0], dq_q[1]};
          endcase
        end else begin
          tx <= mode == 1 ? tx << 4 : tx << 1;
          remaining <= remaining - 1'b1;
          if (remaining == 0) active <= 0;
        end
      end
    end
  end
  wire unused = ^{oe[37:8],pins[37:25],pins[21],pins[18],pins[15:8],data[10]};
endmodule
