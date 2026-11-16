// Area profile: one permutation at a time, serial S-boxes through a shared multiplier.
// Same job contract as the ring; output is a pulse and the consumer must always accept.
module qsag_p2_compact #(parameter int TAGW = 7) (
    input logic clk, rst, in_valid,
    output logic in_ready,
    input logic [767:0] in_state,
    input logic in_jive,
    input logic [TAGW-1:0] in_tag,
    output logic out_valid,
    output logic [767:0] out_state,
    output logic out_jive,
    output logic [TAGW-1:0] out_tag,
    output logic busy,
    output logic mul_valid,
    input logic mul_ready,
    output logic [63:0] mul_a, mul_b,
    input logic mul_done,
    input logic [63:0] mul_r
);
    typedef enum logic [1:0] {IDLE, LINEAR, OFFER, WAIT_MUL} state_t;
    state_t st;
    logic [767:0] x, lin_y, rc;
    logic [267:0] ff;
    logic [803:0] addend;
    logic [4:0] pass;
    logic [3:0] lane;
    logic [1:0] phase, count;
    logic [63:0] x2, x3, x4;
    logic mi;
    assign busy = st != IDLE || out_valid;
    assign in_ready = !rst && st == IDLE;
    assign mi = pass >= 5'd5 && pass <= 5'd26;
    qsag_p2_rc u_rc (.pass(pass), .rc(rc));
    always_comb begin
        for (int i=0;i<12;i++) addend[67*i +:67] = 67'(rc[64*i +:64]);
        if (pass == 5'd30) begin
            addend = '0;
            if (out_jive) addend[267:0] = ff;
        end
    end
    qsag_p2_linear u_linear (.clk(clk), .x(x), .mi(mi), .addend(addend), .y(lin_y));
    assign mul_valid = st == OFFER && !rst;
    assign mul_a = phase == 2'd0 ? x[64*lane +:64] : phase == 2'd3 ? x3 : x2;
    assign mul_b = phase <= 2'd1 ? x[64*lane +:64] : phase == 2'd2 ? x2 : x4;
    always_ff @(posedge clk) begin
        out_valid <= 1'b0;
        if (rst) begin st <= IDLE; out_valid <= 1'b0; end
        else case (st)
            IDLE: if (in_valid) begin
                x <= in_state; out_tag <= in_tag; out_jive <= in_jive;
                for (int i=0;i<4;i++) ff[67*i +:67] <= 67'(in_state[64*i +:64])
                    + (67'(in_state[64*(i+4) +:64]) << 1) + (67'(in_state[64*(i+8) +:64]) << 2);
                pass <= 0; count <= 0; st <= LINEAR;
            end
            LINEAR: if (count == 2) begin
                if (pass == 30) begin out_state <= lin_y; out_valid <= 1'b1; st <= IDLE; end
                else begin x <= lin_y; pass <= pass+1'b1; lane <= 0; phase <= 0; st <= OFFER; end
            end else count <= count+1'b1;
            OFFER: if (mul_ready) st <= WAIT_MUL;
            WAIT_MUL: if (mul_done) begin
                case (phase)
                    0: x2 <= mul_r;
                    1: x3 <= mul_r;
                    2: x4 <= mul_r;
                    3: x[64*lane +:64] <= mul_r;
                endcase
                if (phase != 3) begin phase <= phase+1'b1; st <= OFFER; end
                else if (!mi && lane != 11) begin lane <= lane+1'b1; phase <= 0; st <= OFFER; end
                else begin count <= 0; st <= LINEAR; end
            end
            default: st <= IDLE;
        endcase
    end
endmodule
