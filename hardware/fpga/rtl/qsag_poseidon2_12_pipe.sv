// High-throughput unrolled Poseidon2 width-12 core: the initial M_E stage, 8 external round
// stages (12 S-box units each) and 22 internal round stages (one S-box unit each), fully
// pipelined. One permutation per clock, latency P2_PIPE_LAT clocks; 118 S-box units.
// Same function and feed-forward mode as qsag_poseidon2_12_fpga.
module qsag_poseidon2_12_pipe #(
    parameter int TAGW = 8,
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic            clk,
    input  logic            rst,
    input  logic            in_valid,
    input  logic [767:0]    in_state,
    input  logic            in_jive,
    input  logic [TAGW-1:0] in_tag,
    output logic            out_valid,
    output logic [767:0]    out_state,
    output logic            out_jive,
    output logic [TAGW-1:0] out_tag
);
    localparam int P2_LIN_LAT = qsag_ni_pkg::P2_LIN_LAT;
    localparam int P2_PIPE_LAT = qsag_ni_pkg::P2_PIPE_LAT;
    localparam int FFW = 4 * 67;
    localparam int MW  = 1 + TAGW;
    // The feed-forward is consumed by the last linear layer.
    localparam int FF_LAT = P2_PIPE_LAT - P2_LIN_LAT;

    logic [P2_PIPE_LAT-1:0]    v_sr;
    logic [FFW-1:0]            in_ff, ff_at;
    logic                      jive_at;
    logic [TAGW-1:0]           unused_tag_at;
    for (genvar i = 0; i < 4; i++) begin : g_ff
        assign in_ff[67*i +: 67] = 67'(in_state[64*i +: 64])
                                 + (67'(in_state[64*(4 + i) +: 64]) << 1)
                                 + (67'(in_state[64*(8 + i) +: 64]) << 2);
    end

    logic [767:0] st0;
    always_ff @(posedge clk) begin
        if (rst) v_sr <= '0;
        else     v_sr <= {v_sr[P2_PIPE_LAT-2:0], in_valid};
        st0   <= in_state;
    end

    // Job metadata and the feed-forward ride block-RAM delay lines beside the datapath: the
    // feed-forward to the input of the last linear layer, the tag and mode to the output.
    qsag_bram_delay #(.W(FFW + MW), .N(FF_LAT)) u_ff_dly (
        .clk(clk), .d({in_ff, in_jive, in_tag}), .q({ff_at, jive_at, unused_tag_at}));
    qsag_bram_delay #(.W(MW), .N(P2_PIPE_LAT)) u_meta_dly (
        .clk(clk), .d({in_jive, in_tag}), .q({out_jive, out_tag}));

    logic [31*768-1:0] st;
    for (genvar p = 0; p < 31; p++) begin : g_pass
        localparam int KIND = (p == 0) ? 1 : ((p >= 5 && p <= 26) ? 3 : 2);
        logic [12*67-1:0] addend;
        logic [767:0]     sin;
        if (p == 30) begin : g_last
            assign addend = {{(8*67){1'b0}}, jive_at ? ff_at : {FFW{1'b0}}};
        end else begin : g_rc
            logic [767:0] rc;
            qsag_p2_rc u_rc (.pass(5'(p)), .rc(rc));
            for (genvar i = 0; i < 12; i++) begin : g_l
                assign addend[67*i +: 67] = 67'(rc[64*i +: 64]);
            end
        end
        if (p == 0) begin : g_first
            assign sin = st0;
        end else begin : g_next
            assign sin = st[(p-1)*768 +: 768];
        end
        qsag_p2_round #(.KIND(KIND), .AW(AW), .BW(BW)) u_round (
            .clk(clk), .in_state(sin), .mid_sel(2'd0), .lin_mi(1'b0),
            .lin_addend(addend), .out_state(st[p*768 +: 768]));
    end

    assign out_valid = v_sr[P2_PIPE_LAT-1];
    assign out_state = st[30*768 +: 768];

    logic unused_ok;
    assign unused_ok = &{1'b0, unused_tag_at};
endmodule
