// Dregg-180 v2 FRAM port: the five FRAM micro-operations on the kept SPI master (v2/model/units.py
// FramUnit).
//
// One transaction moves a three-word record at byte address 32 * slot:
//   RSTART / WSTART   open (command and address on the wire)        RWORD   next word in
//   WWORD             next word out (tx is the register-file read port)   DONE   close
// Each strobe is raised by the sequencer in the first clock of the instruction; `fin` is high in the
// instruction's last clock. The sequencer may raise a strobe only when the transaction state below
// allows it (dregg_rules turns misuse into a control fault).
//
// Clocks per instruction, including its first, with SCK = clk / 4:
//   RSTART 97, WSTART 133, RWORD 257, WWORD 257: these follow from the master and equal the model.
//   DONE: the master needs 3 clocks after a read and none after a write (it closes by itself after
//   the third word). The model charges 5. DONE_PAD = 1 waits to 5; DONE_PAD = 0 is the natural count.
`default_nettype none

module dregg_fram #(
    parameter bit DONE_PAD = 1'b1
) (
    input  wire         clk,
    input  wire         srst_n,
    input  wire         abort,        // end action: close whatever is open
    input  wire         s_start,
    input  wire         s_write,      // with s_start
    input  wire         s_slot,       // with s_start
    input  wire         s_rword,
    input  wire         s_wword,
    input  wire         s_done,
    input  wire  [63:0] tx,
    output wire  [63:0] rx,           // valid in the clock `fin` is high for RWORD
    output wire         fin,
    output logic        open,         // a transaction is open
    output logic        writing,
    output logic [1:0]  left,         // words left in it
    // pads
    output wire         cs_n,
    output wire         sck,
    output wire         mosi,
    input  wire         miso
);
`include "dregg_defs.svh"

    localparam logic [2:0] F_IDLE = 3'd0, F_START = 3'd1, F_RW = 3'd2, F_WW = 3'd3, F_DONE = 3'd4;
    logic [2:0] st;
    logic       first_rd;     // the next RWORD is the first of its transaction (the master is already shifting)
    logic [2:0] dcnt;
    logic       abort_q;

    wire        a_stb, a_done, a_busy, a_cmd_last, a_word_last;
    wire [63:0] a_rx, a_rx_nxt;
    wire        a_rst_n;
    qsag_clkand2 u_ar (.a(srst_n), .b(~abort_q), .y(a_rst_n));

    // go: resume the master at a word boundary
    //   RWORD after the first: at the instruction's first clock
    //   WWORD: at the instruction's first clock, with the word on tx
    //   DONE after the third word of a read: releases the master from its last word boundary
    // A DONE before the third word cannot end the master at a boundary (it would shift another word):
    // it resets the master instead, as the end action does.
    wire early = s_done && (left != 2'd0);
    wire go = (s_rword && !first_rd) | s_wword | (s_done && !writing && !early);

    dregg_anchor_spi u_spi (
        .clk(clk), .rst_n(a_rst_n), .div(FRAM_DIV),
        .start(s_start), .write(s_write), .addr({10'd0, s_slot, 5'd0}),
        .stb(a_stb), .go(go), .rx(a_rx), .tx(tx), .done(a_done), .busy(a_busy),
        .cmd_last(a_cmd_last), .word_last(a_word_last), .rx_nxt(a_rx_nxt),
        .cs_n(cs_n), .sck(sck), .mosi(mosi), .miso(miso)
    );

    // RWORD: the first word of a read is already on its way when the instruction starts and is taken
    // from `rx` once the master holds at the boundary; later words are taken from the shift register
    // on the edge that completes them.
    wire rw_fin_first = (st == F_RW) &&  first_rd && a_stb;
    wire rw_fin_next  = (st == F_RW) && !first_rd && a_word_last;
    assign rx = first_rd ? a_rx : a_rx_nxt;

    wire done_ok = !a_busy || a_done;
    wire done_fin = (st == F_DONE) && done_ok && (!DONE_PAD || dcnt == 3'(T_FRAM_DONE));
    // a DONE that finds the master idle and needs no padding ends in its first clock
    wire done_now = s_done && writing && !early && !a_busy && !DONE_PAD;

    assign fin = ((st == F_START) && a_cmd_last) | rw_fin_first | rw_fin_next
               | ((st == F_WW) && a_word_last) | done_fin | done_now;

    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) begin
            st       <= F_IDLE;
            open     <= 1'b0;
            writing  <= 1'b0;
            left     <= '0;
            first_rd <= 1'b0;
            dcnt     <= '0;
            abort_q  <= 1'b0;
        end else begin
            abort_q <= (abort || early) && open;
            if (abort) begin
                st   <= F_IDLE;
                open <= 1'b0;
            end else begin
                unique case (st)
                    F_IDLE: begin
                        dcnt <= 3'd1;
                        if (s_start) begin
                            st       <= F_START;
                            open     <= 1'b1;
                            writing  <= s_write;
                            left     <= 2'd3;
                            first_rd <= !s_write;
                        end else if (s_rword) st <= F_RW;
                        else if (s_wword)     st <= F_WW;
                        else if (s_done) begin
                            open <= 1'b0;
                            if (!done_now) st <= F_DONE;
                        end
                    end
                    F_START: if (a_cmd_last) st <= F_IDLE;
                    F_RW: if (rw_fin_first || rw_fin_next) begin
                        st       <= F_IDLE;
                        left     <= left - 2'd1;
                        first_rd <= 1'b0;
                    end
                    F_WW: if (a_word_last) begin
                        st   <= F_IDLE;
                        left <= left - 2'd1;
                    end
                    F_DONE: begin
                        dcnt <= dcnt + 3'd1;
                        if (done_fin) st <= F_IDLE;
                    end
                    default: st <= F_IDLE;
                endcase
            end
        end
endmodule
`default_nettype wire
