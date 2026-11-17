// Area proxy (from the architecture lane's skeleton, not simulated): SPI-only host link for the v2 architecture. SCK domain: one 64-bit shift register for
// both directions, bit counter, diagnostic read. Core domain: one ingress word register with a toggle
// handshake; the egress word comes from the register file's out rows (not in this module).
`default_nettype none
module px_spi (
    input  wire         clk, rst_n,
    input  wire         sck, cs_n, mosi,
    output wire         miso,
    // core side
    output logic [63:0] rx_word,
    output wire         rx_valid,
    input  wire         rx_take,
    input  wire  [63:0] tx_word,
    input  wire         tx_valid,
    output wire         tx_take,
    input  wire  [63:0] diag
);
    logic [63:0] sr;
    logic [5:0]  bitc;
    logic [7:0]  cmd;
    logic [3:0]  cmdc;
    logic        is_diag, is_rd, rx_tgl, tx_tgl;
    wire srst_n = rst_n & ~cs_n;
    wire cmd_done = cmdc[3];
    always_ff @(posedge sck or negedge srst_n) begin
        if (!srst_n) begin sr <= '0; bitc <= '0; cmd <= '0; cmdc <= '0; is_diag <= 1'b0; is_rd <= 1'b0; end
        else if (!cmd_done) begin
            cmd  <= {cmd[6:0], mosi};
            cmdc <= cmdc + 4'd1;
            if (cmdc == 4'd7) begin
                is_diag <= ({cmd[6:0], mosi} == 8'h05);
                is_rd   <= ({cmd[6:0], mosi} == 8'h03);
                sr      <= ({cmd[6:0], mosi} == 8'h05) ? diag : tx_word;
            end
        end else begin
            bitc <= bitc + 6'd1;
            sr   <= (bitc == 6'd63 && is_rd) ? tx_word : {sr[62:0], mosi};
        end
    end
    always_ff @(posedge sck or negedge rst_n) begin
        if (!rst_n) begin rx_tgl <= 1'b0; tx_tgl <= 1'b0; end
        else if (cmd_done && bitc == 6'd63) begin
            if (!is_rd && !is_diag) rx_tgl <= ~rx_tgl;
            if (is_rd) tx_tgl <= ~tx_tgl;
        end
    end
    logic [63:0] sr_n;
    always_ff @(negedge sck or negedge srst_n) if (!srst_n) sr_n <= '0; else sr_n[63] <= sr[63];
    assign miso = sr_n[63];
    // core domain: two-flop synchronisers on the toggles; the shift register is stable when they arrive
    logic [2:0] rxs, txs;
    logic rx_full;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin rxs <= '0; txs <= '0; rx_word <= '0; rx_full <= 1'b0; end
        else begin
            rxs <= {rxs[1:0], rx_tgl};
            txs <= {txs[1:0], tx_tgl};
            if (rxs[2] ^ rxs[1]) begin rx_word <= sr; rx_full <= 1'b1; end
            else if (rx_take) rx_full <= 1'b0;
        end
    end
    assign rx_valid = rx_full;
    assign tx_take  = (txs[2] ^ txs[1]) & tx_valid;
endmodule
`default_nettype wire
