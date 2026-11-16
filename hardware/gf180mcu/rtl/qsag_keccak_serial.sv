// QSAG-NI-180 word-serial Keccak-p[1600, nr] over the sponge register file.
//
// A one-round-per-clock Keccak costs 26 kGE of round logic plus a 2:1 multiplexer on each of
// the 1,600 state flip-flops in gf180mcu_fd_sc_mcu7t5v0 (measured, synth/reports); that is half
// of this die's logic budget. This unit instead permutes the lanes in place through the single
// 64-bit read/write port, 125 clocks per round, with a 5-word ring and one temporary:
//
//   theta-1 (25)  ring <- column parities C[0..4]
//   theta-2 (25)  a[x,y] ^= C[x-1] ^ rol(C[x+1], 1), ring rotating once per column
//   rho-pi  (25)  the 24-lane cycle of pi walked in place with one temporary and a rotator
//   chi     (50)  per plane: five lanes into the ring, a[x,y] <- b[x] ^ (~b[x+1] & b[x+2]),
//                 iota folded into lane 0
//
// The ring and the temporary hold state fragments, so they are cleared with the sponge.
`default_nettype none

module qsag_keccak_serial (
    input  wire         clk,
    input  wire         rst_n,       // control reset
    input  wire         srst_n,      // secret clear (ring, temporary)
    input  wire         start,
    input  wire         turbo,       // 0: 24 rounds, 1: the last 12 rounds
    output wire         busy,
    output logic        done,
    output logic [5:0]  rd_addr,
    input  wire  [63:0] port,
    output logic        wr_en,
    output logic [5:0]  wr_addr,
    output logic [63:0] wr_data
);
    localparam logic [2:0] S_IDLE = 3'd0, S_TH1 = 3'd1, S_TH2 = 3'd2, S_RP0 = 3'd3, S_RP = 3'd4,
                           S_CHL = 3'd5, S_CHC = 3'd6;
    logic [2:0]  st;
    logic [4:0]  rnd;
    logic [2:0]  x, y;
    logic [4:0]  i;
    wire  [63:0] r0, r1, r2, r3, r4, tmp;

    assign busy = (st != S_IDLE);

    // pi lane walk and rho offsets
    logic [4:0] piln;
    logic [5:0] rotc;
    always_comb begin
        unique case (i)
            5'd0:  begin piln = 5'd10; rotc = 6'd1;  end
            5'd1:  begin piln = 5'd7;  rotc = 6'd3;  end
            5'd2:  begin piln = 5'd11; rotc = 6'd6;  end
            5'd3:  begin piln = 5'd17; rotc = 6'd10; end
            5'd4:  begin piln = 5'd18; rotc = 6'd15; end
            5'd5:  begin piln = 5'd3;  rotc = 6'd21; end
            5'd6:  begin piln = 5'd5;  rotc = 6'd28; end
            5'd7:  begin piln = 5'd16; rotc = 6'd36; end
            5'd8:  begin piln = 5'd8;  rotc = 6'd45; end
            5'd9:  begin piln = 5'd21; rotc = 6'd55; end
            5'd10: begin piln = 5'd24; rotc = 6'd2;  end
            5'd11: begin piln = 5'd4;  rotc = 6'd14; end
            5'd12: begin piln = 5'd15; rotc = 6'd27; end
            5'd13: begin piln = 5'd23; rotc = 6'd41; end
            5'd14: begin piln = 5'd19; rotc = 6'd56; end
            5'd15: begin piln = 5'd13; rotc = 6'd8;  end
            5'd16: begin piln = 5'd12; rotc = 6'd25; end
            5'd17: begin piln = 5'd2;  rotc = 6'd43; end
            5'd18: begin piln = 5'd20; rotc = 6'd62; end
            5'd19: begin piln = 5'd14; rotc = 6'd18; end
            5'd20: begin piln = 5'd22; rotc = 6'd39; end
            5'd21: begin piln = 5'd9;  rotc = 6'd61; end
            5'd22: begin piln = 5'd6;  rotc = 6'd20; end
            default: begin piln = 5'd1; rotc = 6'd44; end
        endcase
    end

    wire [63:0] rc;
    qsag_keccak_rc u_rc (.idx(rnd), .rc(rc));

    wire [63:0]  rot_t = (tmp << rotc) | (tmp >> (7'd64 - {1'b0, rotc}));   // rotc is never 0
    wire [5:0]   lane  = {3'd0, x} + 6'd5 * {3'd0, y};

    always_comb begin
        rd_addr = lane;
        wr_addr = lane;
        wr_en   = 1'b0;
        wr_data = '0;
        unique case (st)
            S_TH2: begin
                wr_en   = 1'b1;
                wr_data = port ^ r4 ^ {r1[62:0], r1[63]};
            end
            S_RP0: rd_addr = 6'd1;
            S_RP: begin
                rd_addr = {1'b0, piln};
                wr_addr = {1'b0, piln};
                wr_en   = 1'b1;
                wr_data = rot_t;
            end
            S_CHC: begin
                wr_en   = 1'b1;
                wr_data = r0 ^ (~r1 & r2) ^ ((x == 3'd0 && y == 3'd0) ? rc : 64'd0);
            end
            default: ;
        endcase
    end

    wire last_x = (x == 3'd4);
    wire last_y = (y == 3'd4);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st   <= S_IDLE;
            done <= 1'b0;
            rnd  <= '0;
            x    <= '0;
            y    <= '0;
            i    <= '0;
        end else begin
            done <= 1'b0;
            unique case (st)
                S_IDLE: if (start) begin
                    st  <= S_TH1;
                    rnd <= turbo ? 5'd12 : 5'd0;
                    x   <= '0;
                    y   <= '0;
                end
                S_TH1, S_TH2: begin  // column-major walk
                    y <= last_y ? 3'd0 : y + 3'd1;
                    if (last_y) begin
                        x <= last_x ? 3'd0 : x + 3'd1;
                        if (last_x) st <= (st == S_TH1) ? S_TH2 : S_RP0;
                    end
                end
                S_RP0: begin
                    i  <= '0;
                    st <= S_RP;
                end
                S_RP: begin
                    i <= i + 5'd1;
                    if (i == 5'd23) st <= S_CHL;
                end
                S_CHL: begin  // row-major: load plane y
                    x <= last_x ? 3'd0 : x + 3'd1;
                    if (last_x) st <= S_CHC;
                end
                S_CHC: begin
                    x <= last_x ? 3'd0 : x + 3'd1;
                    if (last_x) begin
                        y <= last_y ? 3'd0 : y + 3'd1;
                        if (!last_y) st <= S_CHL;
                        else if (rnd == 5'd23) begin
                            st   <= S_IDLE;
                            done <= 1'b1;
                        end else begin
                            rnd <= rnd + 5'd1;
                            st  <= S_TH1;
                        end
                    end
                end
                default: st <= S_IDLE;
            endcase
        end
    end

    // ring and temporary (gated registers; cleared with the secrets)
    wire        th1    = (st == S_TH1);
    wire        shift  = (th1 && y == 3'd0) || (st == S_TH2 && last_y) || st == S_CHC || st == S_CHL;
    wire        rotate = (st == S_TH2) || (st == S_CHC);
    wire [63:0] r4_d   = rotate ? r0 : (th1 && y != 3'd0) ? (r4 ^ port) : port;
    qsag_ereg #(.W(64)) u_r0 (.clk(clk), .rst_n(srst_n), .en(shift), .d(r1), .q(r0));
    qsag_ereg #(.W(64)) u_r1 (.clk(clk), .rst_n(srst_n), .en(shift), .d(r2), .q(r1));
    qsag_ereg #(.W(64)) u_r2 (.clk(clk), .rst_n(srst_n), .en(shift), .d(r3), .q(r2));
    qsag_ereg #(.W(64)) u_r3 (.clk(clk), .rst_n(srst_n), .en(shift), .d(r4), .q(r3));
    qsag_ereg #(.W(64)) u_r4 (.clk(clk), .rst_n(srst_n), .en(shift | th1), .d(r4_d), .q(r4));
    qsag_ereg #(.W(64)) u_tmp (.clk(clk), .rst_n(srst_n), .en(st == S_RP0 || st == S_RP), .d(port), .q(tmp));
endmodule
`default_nettype wire
