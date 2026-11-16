// Routing-friendly 64-bit lane-sliced Keccak-p[1600] / TurboSHAKE256 core for compact FPGAs
// (Lattice ECP5-85F). Stores the 25-lane state in two 32x64 block/LUT RAMs (`a_mem`, `b_mem`),
// replacing the 1,600-wire all-to-all rho/pi crossbar with one 64-bit barrel rotator and a
// 2-lane sliding chi window (~700 LUT4s, zero routing congestion, >150 MHz on ECP5-85F-8).
//
// Commands (`cmd_valid && cmd_ready`):
//   2'd0 LOAD_LANE : a_mem[cmd_idx] <= cmd_wdata (1 clock)
//   2'd1 XOR_LANE  : a_mem[cmd_idx] <= a_mem[cmd_idx] ^ cmd_wdata (2 clocks)
//   2'd2 PERMUTE   : Keccak-f[1600] (cmd_nr12=0, 24 rounds) or Keccak-p[1600,12] (cmd_nr12=1,
//                    rounds 12..23); pulses `done` on completion
//   2'd3 READ_LANE : pulses `rd_valid` with `rd_data = a_mem[cmd_idx]` (1 clock)
module qsag_keccak_compact (
    input  logic        clk,
    input  logic        rst,
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

    // B[y, (2x + 3y) % 5]: destination lane index y + 5*((2x + 3y) % 5) for source k = x + 5*y.
    function automatic logic [4:0] pi_rom(input logic [4:0] k);
        case (k)
            5'd0:  pi_rom = 5'd0;   5'd1:  pi_rom = 5'd10;  5'd2:  pi_rom = 5'd20;
            5'd3:  pi_rom = 5'd5;   5'd4:  pi_rom = 5'd15;
            5'd5:  pi_rom = 5'd16;  5'd6:  pi_rom = 5'd1;   5'd7:  pi_rom = 5'd11;
            5'd8:  pi_rom = 5'd21;  5'd9:  pi_rom = 5'd6;
            5'd10: pi_rom = 5'd7;   5'd11: pi_rom = 5'd17;  5'd12: pi_rom = 5'd2;
            5'd13: pi_rom = 5'd12;  5'd14: pi_rom = 5'd22;
            5'd15: pi_rom = 5'd23;  5'd16: pi_rom = 5'd8;   5'd17: pi_rom = 5'd18;
            5'd18: pi_rom = 5'd3;   5'd19: pi_rom = 5'd13;
            5'd20: pi_rom = 5'd14;  5'd21: pi_rom = 5'd24;  5'd22: pi_rom = 5'd9;
            5'd23: pi_rom = 5'd19;  5'd24: pi_rom = 5'd4;
            default: pi_rom = 5'd0;
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
        K_IDLE, K_XOR_WR, K_RD_OUT, K_THETA, K_RHO_PI, K_CHI
    } state_e;
    state_e st;

    logic [4:0]        rnd, hold_idx;
    logic [63:0]       hold_wdata, w0, w1;
    logic [5:0]        cnt;
    logic [2:0]        y_idx, s_idx;
    logic [4:0][63:0]  c_par;
    logic [4:0][63:0]  d_par;

    for (genvar x = 0; x < 5; x++) begin : g_d
        localparam int XM1 = (x + 4) % 5;
        localparam int XP1 = (x + 1) % 5;
        assign d_par[x] = c_par[XM1] ^ {c_par[XP1][62:0], c_par[XP1][63]};
    end

    logic        a_we, b_we;
    logic [4:0]  a_wa, a_ra, b_wa, b_ra;
    logic [63:0] a_wd, a_rd, b_wd, b_rd;

    qsag_sdp_bram #(.AW(5), .DW(64)) u_amem (
        .clk(clk), .we(a_we), .wa(a_wa), .wd(a_wd), .ra(a_ra), .rd(a_rd));
    qsag_sdp_bram #(.AW(5), .DW(64)) u_bmem (
        .clk(clk), .we(b_we), .wa(b_wa), .wd(b_wd), .ra(b_ra), .rd(b_rd));

    logic [4:0] row_base;
    always_comb begin
        case (y_idx)
            3'd0: row_base = 5'd0;
            3'd1: row_base = 5'd5;
            3'd2: row_base = 5'd10;
            3'd3: row_base = 5'd15;
            default: row_base = 5'd20;
        endcase
    end

    wire [4:0] k_prev = 5'(cnt - 6'd1);
    wire [2:0] k_x    = x_of(k_prev);
    wire [2:0] chi_col_rd = (s_idx < 3'd5) ? s_idx : (s_idx - 3'd5);
    wire [2:0] chi_col_wr = s_idx - 3'd3;

    assign cmd_ready = !rst && (st == K_IDLE);
    assign busy      = (st != K_IDLE);
    assign rd_data   = a_rd;

    always_comb begin
        a_we = 1'b0;
        a_wa = cmd_idx;
        a_wd = cmd_wdata;
        a_ra = cmd_idx;
        b_we = 1'b0;
        b_wa = 5'd0;
        b_wd = 64'd0;
        b_ra = row_base + 5'(chi_col_rd);

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
            K_THETA: begin
                a_ra = (cnt < 6'd25) ? cnt[4:0] : 5'd0;
            end
            K_RHO_PI: begin
                a_ra = (cnt < 6'd25) ? cnt[4:0] : 5'd0;
                if (cnt >= 6'd1) begin
                    b_we = 1'b1;
                    b_wa = pi_rom(k_prev);
                    b_wd = rotl64(a_rd ^ d_par[k_x], rho_rom(k_prev));
                end
            end
            K_CHI: begin
                if (s_idx >= 3'd3) begin
                    a_we = 1'b1;
                    a_wa = row_base + 5'(chi_col_wr);
                    a_wd = (w0 ^ (~w1 & b_rd))
                         ^ ((y_idx == 3'd0 && s_idx == 3'd3) ? round_const(rnd) : 64'd0);
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
                                rnd   <= cmd_nr12 ? 5'd12 : 5'd0;
                                c_par <= '0;
                                cnt   <= 6'd0;
                                st    <= K_THETA;
                            end
                            2'd3: st <= K_RD_OUT;
                        endcase
                    end
                end
                K_XOR_WR: st <= K_IDLE;
                K_RD_OUT: begin
                    rd_valid <= 1'b1;
                    st       <= K_IDLE;
                end
                K_THETA: begin
                    if (cnt >= 6'd1) c_par[k_x] <= c_par[k_x] ^ a_rd;
                    if (cnt == 6'd25) begin
                        cnt <= 6'd0;
                        st  <= K_RHO_PI;
                    end else begin
                        cnt <= cnt + 6'd1;
                    end
                end
                K_RHO_PI: begin
                    if (cnt == 6'd25) begin
                        y_idx <= 3'd0;
                        s_idx <= 3'd0;
                        st    <= K_CHI;
                    end else begin
                        cnt <= cnt + 6'd1;
                    end
                end
                K_CHI: begin
                    if (s_idx == 3'd1) begin
                        w0 <= b_rd;
                    end else if (s_idx == 3'd2) begin
                        w1 <= b_rd;
                    end else if (s_idx >= 3'd3 && s_idx <= 3'd6) begin
                        w0 <= w1;
                        w1 <= b_rd;
                    end
                    if (s_idx == 3'd7) begin
                        s_idx <= 3'd0;
                        if (y_idx == 3'd4) begin
                            if (rnd == 5'd23) begin
                                done <= 1'b1;
                                st   <= K_IDLE;
                            end else begin
                                rnd   <= rnd + 5'd1;
                                c_par <= '0;
                                cnt   <= 6'd0;
                                st    <= K_THETA;
                            end
                        end else begin
                            y_idx <= y_idx + 3'd1;
                        end
                    end else begin
                        s_idx <= s_idx + 3'd1;
                    end
                end
                default: st <= K_IDLE;
            endcase
        end
    end
endmodule
