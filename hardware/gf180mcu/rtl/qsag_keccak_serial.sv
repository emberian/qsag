// Dregg-180 (QSAG-NI-180) ultra-compact 64-bit word-serial in-place Keccak-p[1600, nr] engine.
//
//   * Operates directly over `qsag_sponge`'s scalar 64-bit `rd_addr/port` + `wr_addr/wr_data` ports
//     (`0` wide sponge crossbar muxes!).
//   * Ring-shifted 5x64-bit `cd[0..4]` column-parity & D-sheet ring (`0` data muxes / XORs on
//     `cd[0..3]`, `1` shared 64-bit XOR on `cd[4]`) + `1` 6-stage logarithmic 64-bit barrel rotator
//     (`384` mux2_1 cells vs dual variable shifters), saving > 68,000 um^2 while executing 12-round
//     TurboSHAKE256 in 817 clocks and 24-round SHAKE256 in 1,609 clocks (~2x faster than bit-serial!).
`default_nettype none

module qsag_keccak_serial (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    input  wire         start,
    input  wire         turbo,       // 0: 24 rounds, 1: last 12 rounds
    input  wire         fault_inj,   // EAL6+ Bellcore / laser fault-injection self-test hook
    output wire         busy,
    output logic        done,
    output logic [5:0]  rd_addr,
    input  wire  [63:0] port,
    output logic        wr_en,
    output logic [5:0]  wr_addr,
    output logic [63:0] wr_data
);
    function automatic logic [4:0] pi_lane(input logic [4:0] s);
        unique case (s)
            5'd0:  pi_lane = 5'd1;   5'd1:  pi_lane = 5'd10;  5'd2:  pi_lane = 5'd7;
            5'd3:  pi_lane = 5'd11;  5'd4:  pi_lane = 5'd17;  5'd5:  pi_lane = 5'd18;
            5'd6:  pi_lane = 5'd3;   5'd7:  pi_lane = 5'd5;   5'd8:  pi_lane = 5'd16;
            5'd9:  pi_lane = 5'd8;   5'd10: pi_lane = 5'd21;  5'd11: pi_lane = 5'd24;
            5'd12: pi_lane = 5'd4;   5'd13: pi_lane = 5'd15;  5'd14: pi_lane = 5'd23;
            5'd15: pi_lane = 5'd19;  5'd16: pi_lane = 5'd13;  5'd17: pi_lane = 5'd12;
            5'd18: pi_lane = 5'd2;   5'd19: pi_lane = 5'd20;  5'd20: pi_lane = 5'd14;
            5'd21: pi_lane = 5'd22;  5'd22: pi_lane = 5'd9;   5'd23: pi_lane = 5'd6;
            default: pi_lane = 5'd1;
        endcase
    endfunction

    function automatic logic [5:0] rho_sh(input logic [4:0] s);
        unique case (s)
            5'd0:  rho_sh = 6'd1;   5'd1:  rho_sh = 6'd3;   5'd2:  rho_sh = 6'd6;
            5'd3:  rho_sh = 6'd10;  5'd4:  rho_sh = 6'd15;  5'd5:  rho_sh = 6'd21;
            5'd6:  rho_sh = 6'd28;  5'd7:  rho_sh = 6'd36;  5'd8:  rho_sh = 6'd45;
            5'd9:  rho_sh = 6'd55;  5'd10: rho_sh = 6'd2;   5'd11: rho_sh = 6'd14;
            5'd12: rho_sh = 6'd27;  5'd13: rho_sh = 6'd41;  5'd14: rho_sh = 6'd56;
            5'd15: rho_sh = 6'd8;   5'd16: rho_sh = 6'd25;  5'd17: rho_sh = 6'd43;
            5'd18: rho_sh = 6'd62;  5'd19: rho_sh = 6'd18;  5'd20: rho_sh = 6'd39;
            5'd21: rho_sh = 6'd61;  5'd22: rho_sh = 6'd20;  default: rho_sh = 6'd44;
        endcase
    endfunction

    function automatic logic [2:0] mod5_of(input logic [4:0] idx);
        if (idx >= 5'd20)      mod5_of = 3'(idx - 5'd20);
        else if (idx >= 5'd15) mod5_of = 3'(idx - 5'd15);
        else if (idx >= 5'd10) mod5_of = 3'(idx - 5'd10);
        else if (idx >= 5'd5)  mod5_of = 3'(idx - 5'd5);
        else                   mod5_of = idx[2:0];
    endfunction

    // Single 6-stage logarithmic 64-bit left rotator (384 mux2_1 cells, 6 gate levels)
    function automatic logic [63:0] rol64(input logic [63:0] x, input logic [5:0] sh);
        logic [63:0] t0, t1, t2, t3, t4;
        begin
            t0    = sh[0] ? {x[62:0],  x[63]}    : x;
            t1    = sh[1] ? {t0[61:0], t0[63:62]} : t0;
            t2    = sh[2] ? {t1[59:0], t1[63:60]} : t1;
            t3    = sh[3] ? {t2[55:0], t2[63:56]} : t2;
            t4    = sh[4] ? {t3[47:0], t3[63:48]} : t3;
            rol64 = sh[5] ? {t4[31:0], t4[63:32]} : t4;
        end
    endfunction

    localparam logic [2:0] K_IDLE = 3'd0, K_TH0 = 3'd1, K_THD = 3'd2,
                           K_RHO  = 3'd3, K_CR  = 3'd4, K_CW  = 3'd5;
    logic [2:0] st;
    logic [4:0] rnd;
    logic [4:0] step;
    logic [2:0] row_y;

    wire [63:0] cd [5];
    wire [63:0] w0, w1, b0_save, b1_save;

    assign busy = (st != K_IDLE);

    wire [63:0] rc;
    qsag_keccak_rc u_rc (.idx(rnd), .rc(rc));

    wire [4:0]  idx_m2  = step - 5'd2;
    wire [5:0]  cur_sh  = rho_sh(idx_m2);
    wire [4:0]  src_ln  = pi_lane(idx_m2);
    wire [2:0]  src_x   = mod5_of(src_ln);
    wire [63:0] cd_rho  = (src_x == 3'd0) ? cd[0] : (src_x == 3'd1) ? cd[1] :
                          (src_x == 3'd2) ? cd[2] : (src_x == 3'd3) ? cd[3] : cd[4];
    wire [63:0] rot_out = rol64(w0 ^ cd_rho, cur_sh);

    wire [4:0]  row_base = 5'd5 * {2'd0, row_y};
    wire [63:0] chi_b2   = (step == 5'd3) ? b0_save : (step == 5'd4) ? b1_save : port;
    wire [63:0] iota_xor = (row_y == 3'd0 && step == 5'd0)
                           ? (rc ^ ((fault_inj && rnd == 5'd18) ? 64'h0000_0000_0001_0000 : 64'd0))
                           : 64'd0;
    wire [63:0] chi_out  = w0 ^ (~w1 & chi_b2) ^ iota_xor;

    wire [4:0]  dst_ln   = pi_lane((step == 5'd25) ? 5'd0 : (step - 5'd1));

    always_comb begin
        rd_addr = 6'd0;
        wr_en   = 1'b0;
        wr_addr = 6'd0;
        wr_data = 64'd0;
        unique case (st)
            K_TH0: rd_addr = {1'b0, step};
            K_RHO: begin
                if (step == 5'd0) begin
                    rd_addr = 6'd0;
                    wr_en   = 1'b1;
                    wr_addr = 6'd0;
                    wr_data = port ^ cd[0];
                end else if (step == 5'd1) begin
                    rd_addr = 6'd1;
                end else begin
                    rd_addr = {1'b0, dst_ln};
                    wr_en   = 1'b1;
                    wr_addr = {1'b0, dst_ln};
                    wr_data = rot_out;
                end
            end
            K_CR: rd_addr = {1'b0, row_base + step};
            K_CW: begin
                rd_addr = {1'b0, row_base + step + 5'd2};
                wr_en   = 1'b1;
                wr_addr = {1'b0, row_base + step};
                wr_data = chi_out;
            end
            default: ;
        endcase
    end

    // Ring-shifted cd[0..4]: cd[0..3] are pure shift registers (0 XORs, 0 muxes); cd[4] has 1 XOR!
    wire        cd_shift = (st == K_TH0) || (st == K_THD) || (st == K_CW);
    wire [63:0] thd_rhs  = (step == 5'd4) ? w1 : cd[1];
    wire [63:0] xor_lhs  = (st == K_THD)  ? ((step == 5'd0) ? cd[4] : w0) :
                           (st == K_TH0)  ? ((step < 5'd5)  ? 64'd0 : cd[0]) :
                                            ((row_y == 3'd0) ? 64'd0 : cd[0]);
    wire [63:0] xor_rhs  = (st == K_THD)  ? {thd_rhs[62:0], thd_rhs[63]} :
                           (st == K_TH0)  ? port : chi_out;
    wire [63:0] cd4_next = xor_lhs ^ xor_rhs;

    genvar gx;
    generate
        for (gx = 0; gx < 4; gx++) begin : g_cd_sh
            qsag_ereg #(.W(64)) u_cd (.clk(clk), .rst_n(srst_n), .en(cd_shift), .d(cd[gx + 1]), .q(cd[gx]));
        end
    endgenerate
    qsag_ereg #(.W(64)) u_cd4 (.clk(clk), .rst_n(srst_n), .en(cd_shift), .d(cd4_next), .q(cd[4]));

    wire w_clr = !srst_n;
    wire w0_en = w_clr || (st == K_THD && step <= 5'd3) ||
                 (st == K_RHO && step >= 5'd1 && step <= 5'd24) ||
                 (st == K_CR && step == 5'd0) || (st == K_CW && step <= 5'd3);
    wire [63:0] w0_d = w_clr ? 64'd0 : (st == K_THD) ? cd[0] : (st == K_CW) ? w1 : port;

    wire w1_en = w_clr || (st == K_THD && step == 5'd0) ||
                 (st == K_CR && step == 5'd1) || (st == K_CW && step <= 5'd3);
    wire [63:0] w1_d = w_clr ? 64'd0 : (st == K_THD) ? cd[0] : (st == K_CW) ? chi_b2 : port;

    qsag_ereg_nr #(.W(64)) u_w0 (.clk(clk), .en(w0_en), .d(w0_d), .q(w0));
    qsag_ereg_nr #(.W(64)) u_w1 (.clk(clk), .en(w1_en), .d(w1_d), .q(w1));

`ifdef QSAG_LATCH_RF
    wire b0_gate, b1_gate;
    qsag_clkgate_1 u_b0cg (.clk(clk), .en(st == K_CR && step == 5'd1), .gclk(b0_gate));
    qsag_clkgate_1 u_b1cg (.clk(clk), .en(st == K_CW && step == 5'd0), .gclk(b1_gate));
    qsag_latch_word_rst #(.W(64)) u_b0s (.gate(b0_gate), .rst_n(srst_n), .d(w0), .q(b0_save));
    qsag_latch_word_rst #(.W(64)) u_b1s (.gate(b1_gate), .rst_n(srst_n), .d(w1), .q(b1_save));
`else
    qsag_ereg_nr #(.W(64)) u_b0s (.clk(clk), .en(w_clr || (st == K_CR && step == 5'd0)), .d(w_clr ? 64'd0 : port), .q(b0_save));
    qsag_ereg_nr #(.W(64)) u_b1s (.clk(clk), .en(w_clr || (st == K_CR && step == 5'd1)), .d(w_clr ? 64'd0 : port), .q(b1_save));
`endif

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st    <= K_IDLE;
            done  <= 1'b0;
            rnd   <= '0;
            step  <= '0;
            row_y <= '0;
        end else begin
            done <= 1'b0;
            unique case (st)
                K_IDLE: if (start) begin
                    rnd  <= turbo ? 5'd12 : 5'd0;
                    step <= 5'd0;
                    st   <= K_TH0;
                end
                K_TH0: begin
                    if (step == 5'd24) begin
                        step <= 5'd0;
                        st   <= K_THD;
                    end else step <= step + 5'd1;
                end
                K_THD: begin
                    if (step == 5'd4) begin
                        step <= 5'd0;
                        st   <= K_RHO;
                    end else step <= step + 5'd1;
                end
                K_RHO: begin
                    if (step == 5'd25) begin
                        step  <= 5'd0;
                        row_y <= 3'd0;
                        st    <= K_CR;
                    end else step <= step + 5'd1;
                end
                K_CR: begin
                    if (step == 5'd1) begin
                        step <= 5'd0;
                        st   <= K_CW;
                    end else step <= step + 5'd1;
                end
                K_CW: begin
                    if (step == 5'd4) begin
                        step <= 5'd0;
                        if (row_y == 3'd4) begin
                            if (rnd == 5'd23) begin
                                done <= 1'b1;
                                st   <= K_IDLE;
                            end else begin
                                rnd <= rnd + 5'd1;
                                st  <= K_THD;
                            end
                        end else begin
                            row_y <= row_y + 3'd1;
                            st    <= K_CR;
                        end
                    end else step <= step + 5'd1;
                end
                default: st <= K_IDLE;
            endcase
        end
    end
endmodule
`default_nettype wire
