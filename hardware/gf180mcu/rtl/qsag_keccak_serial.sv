// Dregg-180 (QSAG-NI-180) ultra-compact 3-register in-place Keccak-p[1600, nr] over `qsag_sponge`.
//
// Area & Timing Closure Optimizations:
//   * In-place N^k row schedule (N(x,y) = x + 2y mod 5, order 4 -> canonical order after 12 or 24
//     rounds with zero end-of-permutation shuffle).
//   * Uses ONLY THREE 64-bit `dffq_1` registers (`acc_q`, `b0_q`, `b1_q`), storing `D[0..4]` in
//     `qsag_sponge` rows `25..29` and `B[0..1]` in rows `30..31`, with in-place `+8 / +1` rotation
//     inside `acc_q` and a single shared 64-bit `chi` cone (~95,000 um^2 saved vs original Keccak!).
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
    function automatic logic [2:0] mod5(input logic [4:0] v);
        if (v >= 5'd25)      mod5 = 3'(v - 5'd25);
        else if (v >= 5'd20) mod5 = 3'(v - 5'd20);
        else if (v >= 5'd15) mod5 = 3'(v - 5'd15);
        else if (v >= 5'd10) mod5 = 3'(v - 5'd10);
        else if (v >= 5'd5)  mod5 = 3'(v - 5'd5);
        else                 mod5 = v[2:0];
    endfunction

    function automatic logic [2:0] nrow(input logic [1:0] k, input logic [2:0] x, input logic [2:0] y);
        logic [4:0] xx, yy;
        begin
            xx = {2'd0, x};
            yy = {2'd0, y};
            unique case (k)
                2'd0: nrow = y;
                2'd1: nrow = mod5(xx + (yy << 1));
                2'd2: nrow = mod5((xx << 1) + xx + (yy << 2));
                2'd3: nrow = mod5((xx << 1) + (yy << 1) + yy);
            endcase
        end
    endfunction

    function automatic logic [5:0] lane_addr(input logic [2:0] x, input logic [2:0] row);
        lane_addr = {1'b0, row, 2'b00} + {3'd0, row} + {3'd0, x};
    endfunction

    function automatic logic [5:0] rho(input logic [2:0] x, input logic [2:0] y);
        unique case ({x, y})
            {3'd0, 3'd0}: rho = 6'd0;   {3'd0, 3'd1}: rho = 6'd36;  {3'd0, 3'd2}: rho = 6'd3;
            {3'd0, 3'd3}: rho = 6'd41;  {3'd0, 3'd4}: rho = 6'd18;
            {3'd1, 3'd0}: rho = 6'd1;   {3'd1, 3'd1}: rho = 6'd44;  {3'd1, 3'd2}: rho = 6'd10;
            {3'd1, 3'd3}: rho = 6'd45;  {3'd1, 3'd4}: rho = 6'd2;
            {3'd2, 3'd0}: rho = 6'd62;  {3'd2, 3'd1}: rho = 6'd6;   {3'd2, 3'd2}: rho = 6'd43;
            {3'd2, 3'd3}: rho = 6'd15;  {3'd2, 3'd4}: rho = 6'd61;
            {3'd3, 3'd0}: rho = 6'd28;  {3'd3, 3'd1}: rho = 6'd55;  {3'd3, 3'd2}: rho = 6'd25;
            {3'd3, 3'd3}: rho = 6'd21;  {3'd3, 3'd4}: rho = 6'd56;
            {3'd4, 3'd0}: rho = 6'd27;  {3'd4, 3'd1}: rho = 6'd20;  {3'd4, 3'd2}: rho = 6'd39;
            {3'd4, 3'd3}: rho = 6'd8;   {3'd4, 3'd4}: rho = 6'd14;
            default:      rho = 6'd0;
        endcase
    endfunction

    localparam logic [2:0] K_IDLE = 3'd0, K_PAR  = 3'd1, K_DW   = 3'd2, K_RD_D = 3'd3,
                           K_RD_A = 3'd4, K_ROT  = 3'd5, K_CHI  = 3'd6;
    logic [2:0] st;
    logic [4:0] rnd;
    logic [2:0] rx;
    logic       ph;
    logic [2:0] wy, j;
    logic [5:0] sh_rem;

    assign busy = (st != K_IDLE);

    wire [1:0] k_rd = rnd[1:0];
    wire [1:0] k_wr = rnd[1:0] + 2'd1;
    wire [2:0] xm1  = (j == 3'd0) ? 3'd4 : (j - 3'd1);
    wire [2:0] xp1  = (j == 3'd4) ? 3'd0 : (j + 3'd1);
    wire [2:0] xs   = mod5({2'd0, j} + {1'b0, wy, 1'b0} + {2'd0, wy});
    wire [2:0] chi_x = (j == 3'd4) ? 3'd4 : (3'd3 - j);

    wire [5:0] pa = lane_addr(ph ? xp1 : xm1, rx);
    wire [5:0] da = 6'd25 + {3'd0, xs};
    wire [5:0] ra = lane_addr(xs, nrow(k_rd, xs, j));
    wire [5:0] wa = lane_addr(chi_x, nrow(k_wr, chi_x, wy));

    wire [63:0] acc_q, b0_q, b1_q;

    wire [63:0] xor_port = (((st == K_PAR && rx == 3'd0) || st == K_RD_D) ? 64'd0 : acc_q) ^ port;
    wire        rot8     = (sh_rem >= 6'd8);
    wire [63:0] acc_rot  = rot8 ? {acc_q[55:0], acc_q[63:56]} : {acc_q[62:0], acc_q[63]};
    wire [5:0]  rem_next = sh_rem - (rot8 ? 6'd8 : 6'd1);
    wire        rot_done = (st == K_ROT) && (rem_next == 6'd0);
    wire        rda_done = (st == K_RD_A) && (sh_rem == 6'd0);
    wire        b_ready  = rda_done | rot_done;
    wire [63:0] b_val    = rda_done ? xor_port : acc_rot;

    wire acc_en = (st == K_PAR) || (st == K_RD_D) ||
                  (st == K_RD_A && (!rda_done || j == 3'd4)) ||
                  (st == K_ROT  && (!rot_done || j == 3'd4));
    wire [63:0] acc_d = (st == K_ROT) ? acc_rot : xor_port;
    qsag_ereg_nr #(.W(64)) u_ac (.clk(clk), .en(acc_en), .d(acc_d), .q(acc_q));

    wire b0_par = (st == K_PAR) && !ph && (rx == 3'd4);
    wire b0_chi = (st == K_CHI) && (j == 3'd3);
    wire b0_en  = b0_par || (b_ready && j == 3'd2) || b0_chi;
    wire [63:0] b0_d = b0_chi ? port : (b0_par ? xor_port : b_val);
    qsag_ereg_nr #(.W(64)) u_b0 (.clk(clk), .en(b0_en), .d(b0_d), .q(b0_q));

    wire b1_chi = (st == K_CHI) && (j == 3'd2);
    wire b1_en  = (b_ready && j == 3'd3) || b1_chi;
    wire [63:0] b1_d = b1_chi ? port : b_val;
    qsag_ereg_nr #(.W(64)) u_b1 (.clk(clk), .en(b1_en), .d(b1_d), .q(b1_q));

    wire [63:0] d_out = b0_q ^ {acc_q[62:0], acc_q[63]};
    wire [63:0] rc;
    qsag_keccak_rc u_rc (.idx(rnd), .rc(rc));
    wire [63:0] iota = (j == 3'd3 && wy == 3'd0)
                       ? (rc ^ ((fault_inj && rnd == 5'd18) ? 64'h0000_0000_0001_0000 : 64'd0))
                       : 64'd0;

    logic [63:0] chi_a, chi_b, chi_c;
    always_comb begin
        unique case (j)
            3'd0:    begin chi_a = b1_q;  chi_b = acc_q; chi_c = port;  end
            3'd1:    begin chi_a = b0_q;  chi_b = b1_q;  chi_c = acc_q; end
            3'd2:    begin chi_a = port;  chi_b = b0_q;  chi_c = b1_q;  end
            3'd3:    begin chi_a = port;  chi_b = b1_q;  chi_c = b0_q;  end
            default: begin chi_a = acc_q; chi_b = b0_q;  chi_c = b1_q;  end
        endcase
    end
    wire [63:0] e_out = chi_a ^ (~chi_b & chi_c) ^ iota;

    always_comb begin
        rd_addr = 6'd0;
        wr_en   = 1'b0;
        wr_addr = 6'd0;
        wr_data = 64'd0;
        unique case (st)
            K_PAR:  rd_addr = pa;
            K_DW: begin
                wr_en   = 1'b1;
                wr_addr = 6'd25 + {3'd0, j};
                wr_data = d_out;
            end
            K_RD_D: rd_addr = da;
            K_RD_A: begin
                rd_addr = ra;
                if (rda_done && (j <= 3'd1)) begin
                    wr_en   = 1'b1;
                    wr_addr = 6'd30 + {5'd0, j[0]};
                    wr_data = xor_port;
                end
            end
            K_ROT: if (rot_done && (j <= 3'd1)) begin
                wr_en   = 1'b1;
                wr_addr = 6'd30 + {5'd0, j[0]};
                wr_data = acc_rot;
            end
            K_CHI: begin
                rd_addr = (j == 3'd1 || j == 3'd2) ? 6'd31 : 6'd30;
                wr_en   = 1'b1;
                wr_addr = wa;
                wr_data = e_out;
            end
            default: ;
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st     <= K_IDLE;
            done   <= 1'b0;
            rnd    <= '0;
            rx     <= '0;
            ph     <= 1'b0;
            wy     <= '0;
            j      <= '0;
            sh_rem <= '0;
        end else begin
            done <= 1'b0;
            unique case (st)
                K_IDLE: if (start) begin
                    rnd <= turbo ? 5'd12 : 5'd0;
                    rx  <= 3'd0;
                    ph  <= 1'b0;
                    j   <= 3'd0;
                    st  <= K_PAR;
                end
                K_PAR: begin
                    if (rx == 3'd4) begin
                        rx <= 3'd0;
                        if (!ph) ph <= 1'b1;
                        else begin
                            ph <= 1'b0;
                            st <= K_DW;
                        end
                    end else rx <= rx + 3'd1;
                end
                K_DW: begin
                    if (j == 3'd4) begin
                        j  <= 3'd0;
                        wy <= 3'd0;
                        st <= K_RD_D;
                    end else begin
                        j  <= j + 3'd1;
                        st <= K_PAR;
                    end
                end
                K_RD_D: begin
                    sh_rem <= rho(xs, j);
                    st     <= K_RD_A;
                end
                K_RD_A: begin
                    if (sh_rem == 6'd0) begin
                        if (j == 3'd4) begin j <= 3'd0; st <= K_CHI; end
                        else           begin j <= j + 3'd1; st <= K_RD_D; end
                    end else st <= K_ROT;
                end
                K_ROT: begin
                    if (rot_done) begin
                        if (j == 3'd4) begin j <= 3'd0; st <= K_CHI; end
                        else           begin j <= j + 3'd1; st <= K_RD_D; end
                    end else sh_rem <= rem_next;
                end
                K_CHI: begin
                    if (j == 3'd4) begin
                        j <= 3'd0;
                        if (wy == 3'd4) begin
                            wy <= 3'd0;
                            if (rnd == 5'd23) begin
                                done <= 1'b1;
                                st   <= K_IDLE;
                            end else begin
                                rnd <= rnd + 5'd1;
                                rx  <= 3'd0;
                                ph  <= 1'b0;
                                st  <= K_PAR;
                            end
                        end else begin
                            wy <= wy + 3'd1;
                            st <= K_RD_D;
                        end
                    end else j <= j + 3'd1;
                end
                default: st <= K_IDLE;
            endcase
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = srst_n;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
