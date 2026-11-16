// Compact Poseidon2 width-12 core for ECP5_COMPACT: instantiates ONE pipelined S-box unit
// (`qsag_p2_sbox7`: 4 multipliers = 64 MULT18X18D on ECP5) and ONE zero-DSP carry-save linear
// layer (`qsag_p2_linear`). External rounds stream all 12 lanes back-to-back at 1 lane/clock
// (25 clocks); the 22 internal rounds stream lane 0 alone (14 clocks).
// Total latency: 602 clocks/permutation (5.6x faster than single-multiplier serial, 12x fewer DSPs
// than the 12-lane ring).
module qsag_p2_compact #(
    parameter int TAGW = 7,
    parameter int AW   = 16,
    parameter int BW   = 16
) (
    input  logic            clk,
    input  logic            rst,
    input  logic            in_valid,
    output logic            in_ready,
    input  logic [767:0]    in_state,
    input  logic            in_jive,
    input  logic [TAGW-1:0] in_tag,
    output logic            out_valid,
    output logic [767:0]    out_state,
    output logic            out_jive,
    output logic [TAGW-1:0] out_tag,
    output logic            busy
);
    localparam int SB_LAT = qsag_ni_pkg::P2_SBOX_LAT; // 13 clocks

    typedef enum logic [1:0] {IDLE, LINEAR, SBOX} state_t;
    state_t st;

    logic [767:0] x, lin_y, rc;
    logic [267:0] ff;
    logic [803:0] addend;
    logic [4:0]   pass, sb_cnt;
    logic [1:0]   lin_cnt;
    logic         mi;

    assign busy     = (st != IDLE) || out_valid;
    assign in_ready = !rst && (st == IDLE);
    assign mi       = (pass >= 5'd5) && (pass <= 5'd26);

    // Shallow carry-save + split-add feed-forward precompute: l + 2*r + 4*t (< 7 * 2^64).
    logic [267:0] ff_d;
    for (genvar i = 0; i < 4; i++) begin : g_ff
        wire [3*67-1:0] f_terms = {
            67'(in_state[64*(i+8) +: 64]) << 2,
            67'(in_state[64*(i+4) +: 64]) << 1,
            67'(in_state[64*i     +: 64])
        };
        qsag_sum_csa #(.W(67), .N(3), .CHUNK(16)) u_ff (
            .x(f_terms), .y(ff_d[67*i +: 67]));
    end

    qsag_p2_rc u_rc (.pass(pass), .rc(rc));
    always_comb begin
        for (int i = 0; i < 12; i++) addend[67*i +: 67] = 67'(rc[64*i +: 64]);
        if (pass == 5'd30) begin
            addend = '0;
            if (out_jive) addend[267:0] = ff;
        end
    end

    qsag_p2_linear u_linear (.clk(clk), .x(x), .mi(mi), .addend(addend), .y(lin_y));

    wire [4:0]  n_lanes   = mi ? 5'd1 : 5'd12;
    wire [3:0]  sb_in_idx = (sb_cnt < n_lanes) ? sb_cnt[3:0] : 4'd0;
    wire [4:0]  sb_out_k  = sb_cnt - 5'(SB_LAT);
    logic [63:0] sb_y;
    qsag_p2_sbox7 #(.AW(AW), .BW(BW)) u_sbox (
        .clk(clk), .x(x[64*sb_in_idx +: 64]), .y(sb_y));

    always_ff @(posedge clk) begin
        out_valid <= 1'b0;
        if (rst) begin
            st        <= IDLE;
            out_valid <= 1'b0;
        end else begin
            case (st)
                IDLE: begin
                    if (in_valid) begin
                        x        <= in_state;
                        out_tag  <= in_tag;
                        out_jive <= in_jive;
                        ff       <= ff_d;
                        pass     <= 5'd0;
                        lin_cnt  <= 2'd0;
                        st       <= LINEAR;
                    end
                end
                LINEAR: begin
                    if (lin_cnt == 2'd2) begin
                        if (pass == 5'd30) begin
                            out_state <= lin_y;
                            out_valid <= 1'b1;
                            st        <= IDLE;
                        end else begin
                            x      <= lin_y;
                            pass   <= pass + 5'd1;
                            sb_cnt <= 5'd0;
                            st     <= SBOX;
                        end
                    end else begin
                        lin_cnt <= lin_cnt + 2'd1;
                    end
                end
                SBOX: begin
                    if (sb_cnt >= 5'(SB_LAT)) begin
                        x[64*sb_out_k[3:0] +: 64] <= sb_y;
                    end
                    if (sb_cnt == 5'(SB_LAT) + n_lanes - 5'd1) begin
                        lin_cnt <= 2'd0;
                        st      <= LINEAR;
                    end else begin
                        sb_cnt <= sb_cnt + 5'd1;
                    end
                end
                default: st <= IDLE;
            endcase
        end
    end
endmodule
