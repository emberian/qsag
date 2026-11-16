// QSAG-NI-180 ANCHOR_SPI: SPI mode-0 master for an external 8-pin FRAM (MB85RS64V, FM25W256).
//
// One transaction moves three 64-bit words (the 24-byte anchor record), least significant byte
// of each word first, each byte most significant bit first:
//   read :  CS_N low, 0x03, addr[15:8], addr[7:0], 24 bytes in,  CS_N high
//   write:  CS_N low, 0x06 (WREN), CS_N high, CS_N low, 0x02, addr[15:8], addr[7:0],
//           24 bytes out, CS_N high
// At each word boundary the master stops the clock and raises `stb` (read: `rx` holds the word;
// write: the engine must present `tx`); it resumes on `go`. SCK = clk / (2 * (div + 1)).
`default_nettype none

module qsag_anchor_spi (
    input  wire         clk,
    input  wire         rst_n,
    input  wire [3:0]   div,
    input  wire         start,
    input  wire         write,
    input  wire [15:0]  addr,
    output logic        stb,
    input  wire         go,
    output wire  [63:0] rx,
    input  wire  [63:0] tx,
    output logic        done,
    output wire         busy,
    // pads
    output logic        cs_n,
    output logic        sck,
    output wire         mosi,
    input  wire         miso
);
    localparam logic [3:0] S_IDLE = 4'd0, S_WREN = 4'd1, S_GAP = 4'd2, S_CMD = 4'd3, S_WAIT = 4'd4,
                           S_DATA = 4'd5, S_END = 4'd6;
    logic [3:0]  st;
    logic [63:0] sr;
    logic [6:0]  bits;      // bits left in the current shift
    logic [1:0]  words;     // words left
    logic [3:0]  dcnt;
    logic        wr_q, ph, miso_q;

    wire tick = (dcnt == 4'd0);
    assign busy = (st != S_IDLE);
    assign mosi = sr[63];
    // received bits enter at the bottom; after 64 shifts byte 0 sits in sr[63:56]
    assign rx = {sr[7:0], sr[15:8], sr[23:16], sr[31:24], sr[39:32], sr[47:40], sr[55:48], sr[63:56]};
    wire [63:0] tx_be = {tx[7:0], tx[15:8], tx[23:16], tx[31:24], tx[39:32], tx[47:40], tx[55:48], tx[63:56]};

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st    <= S_IDLE;
            sr    <= '0;
            bits  <= '0;
            words <= '0;
            dcnt  <= '0;
            wr_q  <= 1'b0;
            miso_q <= 1'b0;
            ph    <= 1'b0;
            stb   <= 1'b0;
            done  <= 1'b0;
            cs_n  <= 1'b1;
            sck   <= 1'b0;
        end else begin
            done <= 1'b0;
            dcnt <= tick ? div : dcnt - 4'd1;
            unique case (st)
                S_IDLE: if (start) begin
                    wr_q  <= write;
                    words <= 2'd3;
                    dcnt  <= div;
                    ph    <= 1'b0;
                    cs_n  <= 1'b0;
                    if (write) begin
                        sr   <= {8'h06, 56'd0};
                        bits <= 7'd8;
                        st   <= S_WREN;
                    end else begin
                        sr   <= {8'h03, addr, 40'd0};
                        bits <= 7'd24;
                        st   <= S_CMD;
                    end
                end
                S_WREN, S_CMD, S_DATA: if (tick) begin
                    ph <= ~ph;
                    if (!ph) begin  // rising edge: the slave and the master sample
                        sck    <= 1'b1;
                        miso_q <= miso;
                    end else begin  // falling edge: shift, so MOSI changes half a cycle before
                        sck  <= 1'b0;   // the next sample
                        sr   <= {sr[62:0], miso_q};
                        bits <= bits - 7'd1;
                        if (bits == 7'd1) begin
                            unique case (st)
                                S_WREN: begin
                                    cs_n <= 1'b1;
                                    st   <= S_GAP;
                                end
                                S_CMD: begin
                                    stb <= wr_q;       // write: ask for the first word
                                    st  <= wr_q ? S_WAIT : S_DATA;
                                    bits <= 7'd64;
                                end
                                default: begin
                                    words <= words - 2'd1;
                                    if (!wr_q) begin
                                        stb <= 1'b1;   // read: a word is ready
                                        st  <= S_WAIT;
                                    end else if (words == 2'd1) begin
                                        cs_n <= 1'b1;
                                        st   <= S_END;
                                    end else begin
                                        stb <= 1'b1;
                                        st  <= S_WAIT;
                                    end
                                end
                            endcase
                        end
                    end
                end
                S_GAP: if (tick) begin
                    ph <= ~ph;
                    if (ph) begin
                        cs_n <= 1'b0;
                        sr   <= {8'h02, addr, 40'd0};
                        bits <= 7'd24;
                        st   <= S_CMD;
                    end
                end
                S_WAIT: if (go) begin
                    stb  <= 1'b0;
                    dcnt <= div;
                    ph   <= 1'b0;
                    bits <= 7'd64;
                    if (wr_q) begin
                        sr <= tx_be;
                        st <= S_DATA;
                    end else if (words == 2'd0) begin
                        cs_n <= 1'b1;
                        st   <= S_END;
                    end else st <= S_DATA;
                end
                S_END: if (tick) begin
                    done <= 1'b1;
                    st   <= S_IDLE;
                end
                default: st <= S_IDLE;
            endcase
        end
    end
endmodule
`default_nettype wire
