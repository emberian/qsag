// Dregg-180 v2 request framer (v2/model/framing.py): header register, payload accounting, tail mask.
//
// The link hands over 64-bit words with a `first` mark on the first word of a link frame. A request
// is a header word followed by ceil(length / 8) payload words.
//
//   take_hdr   (sequencer, at the idle address) accept in_data as the header of a new request. Only a
//              `first` word is a header; other words arriving while idle are discarded here (words a
//              host sent beyond the stated length, or the rest of a request cut off by a control fault).
//   take_din   consume one payload word (DIN, AUTH)
//   drain      discard the remaining payload words (end action)
//
// Bytes past the stated length in the last payload word are forced to zero before they reach the core.
// A header with a bad magic byte has no payload: its length field is not trusted.
`default_nettype none

module dregg_framer (
    input  wire         clk,
    input  wire         srst_n,
    // link
    input  wire         in_valid,
    input  wire         in_first,
    input  wire  [63:0] in_data,
    output wire         in_take,
    // sequencer
    input  wire         idle,          // the sequencer is at the idle address, waiting for a request
    output wire         hdr_valid,     // a header word is offered
    input  wire         take_hdr,
    input  wire         take_din,
    input  wire         drain,
    output wire         din_valid,     // a payload word is offered (and the request has one left)
    output wire  [63:0] din,           // payload word, tail masked
    output wire         drained,       // no payload word left
    output wire         rem_lt2,
    // fields of the offered header (dispatch) and of the registered one (LDF)
    output wire         in_magic_ok,
    output wire  [7:0]  in_op,
    output logic [63:0] hdr,
    output wire  [21:0] remaining
);
    logic [21:0] rem;
    assign remaining = rem;
    assign drained   = (rem == 22'd0);
    assign rem_lt2   = (rem < 22'd2);

    assign hdr_valid   = idle && in_valid && in_first;
    assign in_magic_ok = (in_data[7:0] == 8'h51);
    assign in_op       = in_data[15:8];
    assign din_valid   = in_valid && !drained;

    wire discard = idle && in_valid && !in_first;
    wire eat     = drain && din_valid;
    assign in_take = take_hdr | take_din | discard | eat;

    // tail mask of the last payload word
    wire [2:0] tail = hdr[26:24];
    logic [63:0] mask;
    always_comb begin
        mask = '1;
        if (rem == 22'd1 && tail != 3'd0)
            for (int b = 0; b < 8; b++)
                if (3'(b) >= tail) mask[8*b +: 8] = 8'h00;
    end
    assign din = in_data & mask;

    wire [23:0] len_in = in_data[47:24];
    wire [21:0] nwords = {1'b0, len_in[23:3]} + {21'd0, |len_in[2:0]};      // ceil(length / 8)

    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) begin
            hdr <= '0;
            rem <= '0;
        end else begin
            if (take_hdr) begin
                hdr <= in_data;
                rem <= in_magic_ok ? nwords : 22'd0;
            end else if ((take_din || eat) && !drained)
                rem <= rem - 22'd1;
        end
endmodule
`default_nettype wire
