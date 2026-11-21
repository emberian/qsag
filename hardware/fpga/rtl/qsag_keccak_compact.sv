// Bertoni-Daemen Order-4 (`N^4 = I mod 5`) Single-Pass In-Place Compact Keccak-p[1600] /
// TurboSHAKE256 Core (`Keccak-implementation-3.2` §2.4.1 Early Parity & §2.5 In-Place Schedule).
//
// Replaces the 2-RAM 92-clk/round ping-pong core with:
//   - ONE 32x64 simple dual-port RAM (`u_amem`, -50% RAM),
//   - Order-4 address mapping N(x, y) = (x, (x + 2y) mod 5): since 12 = 3*4 and 24 = 6*4, BOTH
//     Keccak-p[1600,12] (TurboSHAKE256) and Keccak-f[1600] (SHA3/SHAKE/cSHAKE) finish in exact
//     canonical FIPS-202 lane order with ZERO post-shuffle cycles,
//   - Simultaneous read of plane Y and write of plane Y-1 (`N^(s+1)(x, Y) != N^(s+1)(x, Y-1)`),
//     plus early column-parity accumulation (`c_next[x] ^= chi[x]`) so only round 0 needs a theta
//     pre-scan: 30 clocks/round (26 + 12*30 = 386 clks for 12r, 26 + 24*30 = 746 clks for 24r,
//     3.0x faster than the 92-clk/round baseline).
//
// Commands (`cmd_valid && cmd_ready`):
//   2'd0 LOAD_LANE : a_mem[cmd_idx] <= cmd_wdata (1 clock)
//   2'd1 XOR_LANE  : a_mem[cmd_idx] <= a_mem[cmd_idx] ^ cmd_wdata (2 clocks)
//   2'd2 PERMUTE   : Keccak-f[1600] (cmd_nr12=0, 24r) or Keccak-p[1600,12] (cmd_nr12=1, 12r)
//   2'd3 READ_LANE : pulses `rd_valid` with `rd_data = a_mem[cmd_idx]` (1 clock)
module qsag_keccak_compact (
    input  logic        clk,
    input  logic        rst,
    input  logic        bank_sel,
    input  logic        cmd_valid,
    output logic        cmd_ready,
    input  logic [1:0]  cmd_op,
    input  logic        cmd_nr12,
    input  logic [4:0]  cmd_idx,
    input  logic [63:0] cmd_wdata,
    output logic        busy,
    output logic        done,
    output logic        rd_valid,
    output logic [63:0] rd_data
);
    function automatic logic [63:0] round_const(input logic [4:0] r);
        case (r)
            5'd0:  round_const = 64'h0000000000000001;
            5'd1:  round_const = 64'h0000000000008082;
            5'd2:  round_const = 64'h800000000000808A;
            5'd3:  round_const = 64'h8000000080008000;
            5'd4:  round_const = 64'h000000000000808B;
            5'd5:  round_const = 64'h0000000080000001;
            5'd6:  round_const = 64'h8000000080008081;
            5'd7:  round_const = 64'h8000000000008009;
            5'd8:  round_const = 64'h000000000000008A;
            5'd9:  round_const = 64'h0000000000000088;
            5'd10: round_const = 64'h0000000080008009;
            5'd11: round_const = 64'h000000008000000A;
            5'd12: round_const = 64'h000000008000808B;
            5'd13: round_const = 64'h800000000000008B;
            5'd14: round_const = 64'h8000000000008089;
            5'd15: round_const = 64'h8000000000008003;
            5'd16: round_const = 64'h8000000000008002;
            5'd17: round_const = 64'h8000000000000080;
            5'd18: round_const = 64'h000000000000800A;
            5'd19: round_const = 64'h800000008000000A;
            5'd20: round_const = 64'h8000000080008081;
            5'd21: round_const = 64'h8000000000008080;
            5'd22: round_const = 64'h0000000080000001;
            5'd23: round_const = 64'h8000000080008008;
            default: round_const = 64'h0;
        endcase
    endfunction

    function automatic logic [2:0] mod5_small(input logic [4:0] v);
        if      (v >= 5'd25) mod5_small = 3'(v - 5'd25);
        else if (v >= 5'd20) mod5_small = 3'(v - 5'd20);
        else if (v >= 5'd15) mod5_small = 3'(v - 5'd15);
        else if (v >= 5'd10) mod5_small = 3'(v - 5'd10);
        else if (v >= 5'd5)  mod5_small = 3'(v - 5'd5);
        else                 mod5_small = v[2:0];
    endfunction

    // Address of logical lane (x, y) under N^p (p in 0..3):
    //   N^0(x,y) = (x, y), N^1(x,y) = (x, x+2y), N^2(x,y) = (x, 3x+4y), N^3(x,y) = (x, 2x+3y).
    function automatic logic [4:0] n4_addr(
        input logic [1:0] p,
        input logic [2:0] x,
        input logic [2:0] y
    );
        logic [2:0] ay;
        logic [4:0] x2, x3, y2, y3, y4;
        x2 = {1'b0, x, 1'b0};
        x3 = {1'b0, x, 1'b0} + {2'd0, x};
        y2 = {1'b0, y, 1'b0};
        y3 = {1'b0, y, 1'b0} + {2'd0, y};
        y4 = {y, 2'b00};
        case (p)
            2'd0: ay = y;
            2'd1: ay = mod5_small({2'd0, x} + y2);
            2'd2: ay = mod5_small(x3 + y4);
            2'd3: ay = mod5_small(x2 + y3);
        endcase
        n4_addr = {ay, 2'b00} + {2'd0, ay} + {2'd0, x};
    endfunction

    function automatic logic [2:0] x_of(input logic [4:0] k);
        case (k)
            5'd0, 5'd5, 5'd10, 5'd15, 5'd20: x_of = 3'd0;
            5'd1, 5'd6, 5'd11, 5'd16, 5'd21: x_of = 3'd1;
            5'd2, 5'd7, 5'd12, 5'd17, 5'd22: x_of = 3'd2;
            5'd3, 5'd8, 5'd13, 5'd18, 5'd23: x_of = 3'd3;
            default:                         x_of = 3'd4;
        endcase
    endfunction

    function automatic logic [5:0] rho_rom(input logic [4:0] k);
        case (k)
            5'd0:  rho_rom = 6'd0;   5'd1:  rho_rom = 6'd1;   5'd2:  rho_rom = 6'd62;
            5'd3:  rho_rom = 6'd28;  5'd4:  rho_rom = 6'd27;  5'd5:  rho_rom = 6'd36;
            5'd6:  rho_rom = 6'd44;  5'd7:  rho_rom = 6'd6;   5'd8:  rho_rom = 6'd55;
            5'd9:  rho_rom = 6'd20;  5'd10: rho_rom = 6'd3;   5'd11: rho_rom = 6'd10;
            5'd12: rho_rom = 6'd43;  5'd13: rho_rom = 6'd25;  5'd14: rho_rom = 6'd39;
            5'd15: rho_rom = 6'd41;  5'd16: rho_rom = 6'd45;  5'd17: rho_rom = 6'd15;
            5'd18: rho_rom = 6'd21;  5'd19: rho_rom = 6'd8;   5'd20: rho_rom = 6'd18;
            5'd21: rho_rom = 6'd2;   5'd22: rho_rom = 6'd61;  5'd23: rho_rom = 6'd56;
            5'd24: rho_rom = 6'd14;
            default: rho_rom = 6'd0;
        endcase
    endfunction

    function automatic logic [63:0] rotl64(input logic [63:0] v, input logic [5:0] sh);
        logic [63:0] s0, s1, s2, s3, s4;
        s0 = sh[0] ? {v[62:0],  v[63]}    : v;
        s1 = sh[1] ? {s0[61:0], s0[63:62]} : s0;
        s2 = sh[2] ? {s1[59:0], s1[63:60]} : s1;
        s3 = sh[3] ? {s2[55:0], s2[63:56]} : s2;
        s4 = sh[4] ? {s3[47:0], s3[63:48]} : s3;
        rotl64 = sh[5] ? {s4[31:0], s4[63:32]} : s4;
    endfunction

    typedef enum logic [2:0] {
        K_IDLE, K_XOR_WR, K_RD_OUT, K_THETA0, K_ROUND
    } state_e;
    state_e st;

    logic [4:0]       rnd, hold_idx;
    logic [1:0]       n_step;
    logic [63:0]      hold_wdata;
    logic [4:0]       cnt;
    logic [2:0]       blk, col, blk_prev, col_prev;
    logic [4:0][63:0] c_par, c_next, b_buf;
    logic [3:0][63:0] w_buf; // holds lanes 1..4 of completed chi plane during writeback
    logic [4:0][63:0] d_par;

    for (genvar x = 0; x < 5; x++) begin : g_d
        localparam int XM1 = (x + 4) % 5;
        localparam int XP1 = (x + 1) % 5;
        assign d_par[x] = c_par[XM1] ^ {c_par[XP1][62:0], c_par[XP1][63]};
    end

    logic        a_we;
    logic [4:0]  a_wa, a_ra;
    logic [63:0] a_wd, a_rd;
    qsag_sdp_bram #(.AW(6), .DW(64)) u_amem (
        .clk(clk), .we(a_we), .wa({bank_sel, a_wa}), .wd(a_wd), .ra({bank_sel, a_ra}), .rd(a_rd));

    wire [1:0] p_cur  = n_step + 2'd1;
    wire [4:0] k_th   = cnt - 5'd1;
    wire [2:0] k_th_x = x_of(k_th);

    // Previous cycle's read coordinates (blk_prev in 0..4, col_prev in 0..4):
    // Logical source lane in A^(s) is (col_prev, y_src) where y_src = (col_prev + 2*blk_prev) % 5,
    // which lands in plane `blk_prev` at X = y_src!
    wire [2:0]  y_src   = mod5_small({2'd0, col_prev} + {1'b0, blk_prev, 1'b0});
    wire [4:0]  k_src   = {y_src, 2'b00} + {2'd0, y_src} + {2'd0, col_prev};
    wire [63:0] b_rot   = rotl64(a_rd ^ d_par[col_prev], rho_rom(k_src));

    // Complete 5-lane plane assembled when `col == 3'd0 && blk >= 3'd1` (`col_prev == 3'd4`):
    logic [4:0][63:0] plane_in, plane_chi;
    always_comb begin
        for (int x = 0; x < 5; x++)
            plane_in[x] = (y_src == 3'(x)) ? b_rot : b_buf[x];
        for (int x = 0; x < 5; x++) begin
            plane_chi[x] = plane_in[x] ^ (~plane_in[(x + 1) % 5] & plane_in[(x + 2) % 5]);
        end
        if (blk_prev == 3'd0)
            plane_chi[0] = plane_chi[0] ^ round_const(rnd);
    end

    assign cmd_ready = !rst && (st == K_IDLE);
    assign busy      = (st != K_IDLE);

    wire [2:0] wr_plane = blk - 3'd1;
    wire [63:0] wr_lane = (col == 3'd0) ? plane_chi[0] : w_buf[col - 3'd1];

    always_comb begin
        a_we = 1'b0;
        a_wa = cmd_idx;
        a_wd = cmd_wdata;
        a_ra = cmd_idx;

        case (st)
            K_IDLE: begin
                if (cmd_valid && !rst) begin
                    if (cmd_op == 2'd0) begin
                        a_we = 1'b1;
                        a_wa = cmd_idx;
                        a_wd = cmd_wdata;
                    end
                    a_ra = cmd_idx;
                end
            end
            K_XOR_WR: begin
                a_we = 1'b1;
                a_wa = hold_idx;
                a_wd = a_rd ^ hold_wdata;
            end
            K_THETA0: begin
                a_ra = (cnt < 5'd25) ? cnt : 5'd0;
            end
            K_ROUND: begin
                a_ra = (blk < 3'd5) ? n4_addr(p_cur, col, blk) : 5'd0;
                if (blk >= 3'd1) begin
                    a_we = 1'b1;
                    a_wa = n4_addr(p_cur, col, wr_plane);
                    a_wd = wr_lane;
                end
            end
            default: ;
        endcase
    end

    always_ff @(posedge clk) begin
        done     <= 1'b0;
        rd_valid <= 1'b0;
        if (rst) begin
            st <= K_IDLE;
        end else begin
            case (st)
                K_IDLE: begin
                    if (cmd_valid) begin
                        hold_idx   <= cmd_idx;
                        hold_wdata <= cmd_wdata;
                        case (cmd_op)
                            2'd0: st <= K_IDLE;
                            2'd1: st <= K_XOR_WR;
                            2'd2: begin
                                rnd    <= cmd_nr12 ? 5'd12 : 5'd0;
                                n_step <= 2'd0;
                                c_par  <= '0;
                                cnt    <= 5'd0;
                                st     <= K_THETA0;
                            end
                            2'd3: st <= K_RD_OUT;
                        endcase
                    end
                end
                K_XOR_WR: st <= K_IDLE;
                K_RD_OUT: begin
                    rd_data  <= a_rd;
                    rd_valid <= 1'b1;
                    st       <= K_IDLE;
                end
                K_THETA0: begin
                    if (cnt >= 5'd1) c_par[k_th_x] <= c_par[k_th_x] ^ a_rd;
                    if (cnt == 5'd25) begin
                        blk      <= 3'd0;
                        col      <= 3'd0;
                        blk_prev <= 3'd0;
                        col_prev <= 3'd0;
                        c_next   <= '0;
                        st       <= K_ROUND;
                    end else begin
                        cnt <= cnt + 5'd1;
                    end
                end
                K_ROUND: begin
                    blk_prev <= blk;
                    col_prev <= col;

                    // Capture rotated plane lane from previous cycle's read (valid on sub = 1..25):
                    if (!(blk == 3'd0 && col == 3'd0) && !(blk == 3'd5 && col >= 3'd1)) begin
                        if (col == 3'd0) begin
                            // `col_prev == 4`: plane `blk_prev` is complete; plane_chi[0] writes
                            // directly this cycle while w_buf[0..3] holds plane_chi[1..4].
                            w_buf[0] <= plane_chi[1];
                            w_buf[1] <= plane_chi[2];
                            w_buf[2] <= plane_chi[3];
                            w_buf[3] <= plane_chi[4];
                        end else begin
                            b_buf[y_src] <= b_rot;
                        end
                    end

                    // Early parity accumulation for next round:
                    if (blk >= 3'd1) begin
                        if (wr_plane == 3'd0)
                            c_next[col] <= wr_lane;
                        else
                            c_next[col] <= c_next[col] ^ wr_lane;
                    end

                    // Advance (blk in 0..5, col in 0..4 -> 30 clocks/round):
                    if (col == 3'd4) begin
                        col <= 3'd0;
                        if (blk == 3'd5) begin
                            if (rnd == 5'd23) begin
                                done <= 1'b1;
                                st   <= K_IDLE;
                            end else begin
                                rnd      <= rnd + 5'd1;
                                n_step   <= n_step + 2'd1;
                                c_par[0] <= c_next[0];
                                c_par[1] <= c_next[1];
                                c_par[2] <= c_next[2];
                                c_par[3] <= c_next[3];
                                c_par[4] <= c_next[4] ^ wr_lane;
                                c_next   <= '0;
                                blk      <= 3'd0;
                            end
                        end else begin
                            blk <= blk + 3'd1;
                        end
                    end else begin
                        col <= col + 3'd1;
                    end
                end
                default: st <= K_IDLE;
            endcase
        end
    end
endmodule
