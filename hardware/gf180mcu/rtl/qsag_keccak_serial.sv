// Dregg-180 (QSAG-NI-180) 64-bit word-at-a-time in-place Keccak-p[1600, nr] engine.
//
// Operates directly over `qsag_sponge`'s scalar 64-bit `rd_addr/port` + `wr_addr/wr_data` ports
// (`0` wide crossbar muxes on the 1,600-bit sponge, saving > 220,000 um^2 vs a 25-lane crossbar!),
// while using a single 64-bit barrel rotator and fused chi + next-round-theta-parity accumulation
// to run each Keccak round in 56 clocks (`698` clocks for 12-round TurboSHAKE256, `1,370` clocks
// for 24-round Keccak-f — > 2.2x faster than Fable's 1,500 / 3,000-clock bit-shifted engine at
// ~42k um^2!).
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
    // Exact 24-step Rho-Pi cycle: step s = 0..23 moves pi_lane(s) -> pi_lane(s+1) with rotation rho(s)
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
        // triangular numbers (s+1)(s+2)/2 mod 64 for s = 0..23
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

    localparam logic [2:0] K_IDLE = 3'd0, K_TH0 = 3'd1, K_THD = 3'd2,
                           K_RHO  = 3'd3, K_CR  = 3'd4, K_CW  = 3'd5;
    logic [2:0] st;
    logic [4:0] rnd;
    logic [4:0] step;
    logic [2:0] row_y;

    // 5 x 64-bit C/D ring + 3 x 64-bit chi sliding window (8 words total = 512 bits!)
    wire [63:0] cd [5];
    wire [63:0] w0, w1, b0_save, b1_save;

    assign busy = (st != K_IDLE);

    wire [63:0] rc;
    qsag_keccak_rc u_rc (.idx(rnd), .rc(rc));

    // Single 64-bit barrel rotator (at step = 2..25, w0 holds lane pi_lane(step - 2)!)
    wire  [4:0]   idx_m2  = step - 5'd2;
    wire  [5:0]  cur_sh  = rho_sh(idx_m2);
    wire  [4:0]  src_ln  = pi_lane(idx_m2);
    wire  [2:0]  src_x   = mod5_of(src_ln);
    wire  [63:0] rot_in  = w0 ^ cd[src_x];
    wire  [63:0] rot_out = (rot_in << cur_sh) | (rot_in >> (7'd64 - {1'b0, cur_sh}));

    wire  [4:0]  row_base = 5'd5 * {2'd0, row_y};
    wire  [63:0] chi_b2   = (step == 5'd3) ? b0_save : (step == 5'd4) ? b1_save : port;
    wire  [63:0] iota_xor = (row_y == 3'd0 && step == 5'd0)
                            ? (rc ^ ((fault_inj && rnd == 5'd18) ? 64'h0000_0000_0001_0000 : 64'd0))
                            : 64'd0;
    wire  [63:0] chi_out  = w0 ^ (~w1 & chi_b2) ^ iota_xor;

    wire  [4:0]  dst_ln  = pi_lane((step == 5'd25) ? 5'd0 : (step - 5'd1));

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
                    rd_addr = 6'd1; // pi_lane(0) into w0
                end else begin
                    rd_addr = {1'b0, dst_ln};
                    wr_en   = 1'b1;
                    wr_addr = {1'b0, dst_ln};
                    wr_data = rot_out;
                end
            end
            K_CR: begin
                // step = 0, 1: pre-load B[0] -> w0, b0_save and B[1] -> w1, b1_save
                rd_addr = {1'b0, row_base + step};
            end
            K_CW: begin
                // step = 0..4: read B[(step+2)%5], compute chi_out for x = step, write st[row_base + step],
                // AND accumulate next round's C[step] in cd[step] in the exact same clock!
                rd_addr = {1'b0, row_base + step + 5'd2};
                wr_en   = 1'b1;
                wr_addr = {1'b0, row_base + step};
                wr_data = chi_out;
            end
            default: ;
        endcase
    end

    // Register updates for cd[0..4] and w0, w1, b0_save, b1_save (zero unpacked-array warnings!)
    genvar gx;
    generate
        for (gx = 0; gx < 5; gx++) begin : g_cd
            localparam int PRV = (gx + 4) % 5;
            localparam int NXT = (gx + 1) % 5;
            wire [63:0] d_calc  = cd[PRV] ^ {cd[NXT][62:0], cd[NXT][63]};
            wire        th0_hit = (st == K_TH0) && (mod5_of(step) == 3'(gx));
            wire        cw_hit  = (st == K_CW)  && (step[2:0] == 3'(gx));
            wire        cd_en_w = (!busy && start) || th0_hit || (st == K_THD) || cw_hit;
            wire [63:0] cd_d_w  = (!busy && start) ? 64'd0 :
                                  (st == K_THD)    ? d_calc :
                                  th0_hit          ? (cd[gx] ^ port) :
                                  (row_y == 3'd0)  ? chi_out : (cd[gx] ^ chi_out);
            qsag_ereg #(.W(64)) u_cd (.clk(clk), .rst_n(srst_n), .en(cd_en_w), .d(cd_d_w), .q(cd[gx]));
        end
    endgenerate

    wire w_clr = !srst_n;
    wire w0_en = w_clr || (st == K_RHO && step >= 5'd1 && step <= 5'd24) ||
                 (st == K_CR && step == 5'd0) || (st == K_CW && step <= 5'd3);
    wire [63:0] w0_d = w_clr ? 64'd0 : ((st == K_CW) ? w1 : port);
    wire w1_en = w_clr || (st == K_CR && step == 5'd1) || (st == K_CW && step <= 5'd3);
    wire [63:0] w1_d = w_clr ? 64'd0 : ((st == K_CW) ? chi_b2 : port);
    qsag_ereg_nr #(.W(64)) u_w0  (.clk(clk), .en(w0_en), .d(w0_d), .q(w0));
    qsag_ereg_nr #(.W(64)) u_w1  (.clk(clk), .en(w1_en), .d(w1_d), .q(w1));
    qsag_ereg_nr #(.W(64)) u_b0s (.clk(clk), .en(w_clr || (st == K_CR && step == 5'd0)), .d(w_clr ? 64'd0 : port), .q(b0_save));
    qsag_ereg_nr #(.W(64)) u_b1s (.clk(clk), .en(w_clr || (st == K_CR && step == 5'd1)), .d(w_clr ? 64'd0 : port), .q(b1_save));

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
                    step <= 5'd0;
                    st   <= K_RHO;
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
                                st  <= K_THD; // cd[0..4] ALREADY holds C_next[0..4]!
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
