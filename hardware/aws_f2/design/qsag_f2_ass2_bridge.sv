// Byte transaction engine. CS is held independently for an entire ASS2 frame.
// Mode 0, MSB first per byte, x1 receives on DQ1. DQ direction comes from
// the target's actual pad OEs. Each SCK half-cycle spans four enclave clocks.
module qsag_f2_ass2_bridge #(parameter int VAT_ID = 0) (
  input wire clk, clk_ass2, lock, erase,
  input wire [14:0] erase_addr,
  input wire ctrl_we, xfer_we,
  input wire [10:0] data,
  output wire [31:0] status,
  output wire [7:0] rx,
  output wire [2:0] control
);
  logic [2:0] ctl;
  logic [7:0] tx, received;
  logic [1:0] mode;
  logic [2:0] divcnt, remaining;
  logic active, sck;
  wire [37:0] pins, oe, pad_in;
  wire [3:0] unused_pu, unused_pd;
  wire [37:0] unused_cs, unused_sl, unused_ie, unused_pullup, unused_pulldown;
  wire miso;
  wire reset_n = !lock && !ctl[1];
  // Global wipe is a reset. Local tamper is a separately latched pad event.
  wire tamper_n = lock || !ctl[2];
  wire cs_n = !ctl[0] || !reset_n || !tamper_n;
  wire [7:0] drive = mode == 2 ? tx : mode == 1 ? {4'd0,tx[7:4]} : {7'd0,tx[7]};
  assign pad_in = {10'd0,1'b1,tamper_n,miso,6'd0,sck,10'd0,(drive & ~oe[7:0]) | (pins[7:0] & oe[7:0])};
  assign control = ctl;
  assign rx = received;
  assign status = {26'd0,ctl[2],pins[17:16],pins[20],pins[19],active};
  qsag_ass2_enclave_top #(.VAT_ID(VAT_ID)) u_vat (
    .clk(clk_ass2), .rst_n(reset_n), .erase, .erase_addr(erase_addr[9:1]),
    .input_in({cs_n,3'd0}), .input_pu(unused_pu), .input_pd(unused_pd),
    .bidir_in(pad_in), .bidir_out(pins), .bidir_oe(oe),
    .bidir_cs(unused_cs), .bidir_sl(unused_sl), .bidir_ie(unused_ie),
    .bidir_pu(unused_pullup), .bidir_pd(unused_pulldown)
  );
  qsag_f2_fram_model u_anchor (.clk, .rst(!reset_n || !tamper_n), .erase, .erase_addr,
    .cs_n(pins[22]), .sck(pins[23]), .mosi(pins[24]), .miso);
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
            2: received <= pins[7:0];
            1: received <= {received[3:0], pins[3:0]};
            default: received <= {received[6:0], pins[1]};
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
