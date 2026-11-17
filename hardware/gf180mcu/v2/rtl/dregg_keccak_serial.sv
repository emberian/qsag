// Dregg-180 v2 Keccak unit: qsag_keccak_serial (../rtl/qsag_keccak_serial.sv) with one change: its
// seven private work rows (column parities, two saved lanes) are ports to rows of the register file,
// and a `last` strobe marks the final clock. Sequencing, datapath and clock counts are untouched; the
// test bench runs the two modules in lockstep (tb/unit_keccak) and requires identical outputs.
// Generated from the original by a mechanical edit; diff the two files to review.
//
// Dregg-180 (QSAG-NI-180) lane-serial, in-place Keccak-p[1600, nr] over the sponge register file
// (one 64-bit read port, one 64-bit write port).
//
// One pass over the 25 lanes per round (Bertoni, Daemen, Peeters, Van Assche, "Keccak
// implementation overview" 3.2, section 2.5, in-place processing):
//
//   * Row y of the round output E needs the five lanes B[x, y] = ROL(A[x + 3y, x] ^ D[x + 3y], r),
//     i.e. five lanes of the round input, one from each column. The five results are written back
//     into those same five slots, each into the slot of its own column. A logical lane (x, y)
//     therefore stays in column x of the memory, and after k rounds it sits in row
//     N^k(x, y) with N(x, y) = x + 2y (mod 5):
//         k = 0: y      k = 1: x + 2y      k = 2: 3x + 4y      k = 3: 2x + 3y      k = 4: y
//     N has order 4, so after 12 or 24 rounds the state is back in canonical lane order and no
//     final shuffle exists. Lane (0, 0), where iota is added, never moves.
//   * Column parities of the round output are accumulated while it is written (C_nxt, a 5-lane
//     ring that rotates once per written lane), so theta of the next round needs no extra pass.
//     Only the first round is preceded by a 25-read parity pass.
//   * rho is one 64-bit barrel rotator on the read path; chi runs over a 4-lane shift window
//     (plus two saved lanes for the wrap-around terms of a row). Results leave the window four
//     clocks after their first operand was read, which is late enough that the destination slot
//     has always been read (the slot of column x in row y is read at position x + 2y of the row).
//
// Timing: 25 clocks parity pass + 29 clocks per round (25 reads, 25 writes, overlapped by 21):
//     Keccak-p[1600, 12]  373 clocks      Keccak-f[1600]  721 clocks       (+1 for the start pulse)
// (previous two-pass engine: 62 clocks per round, 817 / 1609 clocks).
`default_nettype none

module dregg_keccak_serial (
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
    output logic [63:0] wr_data,
    // the seven work rows, held in the register file
    output wire  [6:0]   kw_we,      // load strobes: column parities 0..4 (together), saved lanes 5, 6
    output wire  [319:0] kc_d,       // data of the column-parity rows
    output wire  [63:0]  kb_d,       // data of the two saved-lane rows
    input  wire  [447:0] kw_q,
    output wire          last
);
    // ------------------------------------------------------------ small arithmetic modulo 5
    function automatic logic [2:0] mod5(input logic [4:0] v);   // v in 0..28
        if (v >= 5'd25)      mod5 = 3'(v - 5'd25);
        else if (v >= 5'd20) mod5 = 3'(v - 5'd20);
        else if (v >= 5'd15) mod5 = 3'(v - 5'd15);
        else if (v >= 5'd10) mod5 = 3'(v - 5'd10);
        else if (v >= 5'd5)  mod5 = 3'(v - 5'd5);
        else                 mod5 = v[2:0];
    endfunction
    // memory row of logical lane (x, y) after k rounds: N^k(x, y)
    function automatic logic [2:0] nrow(input logic [1:0] k, input logic [2:0] x, input logic [2:0] y);
        logic [4:0] xx, yy;
        begin
            xx = {2'd0, x};
            yy = {2'd0, y};
            unique case (k)
                2'd0: nrow = y;
                2'd1: nrow = mod5(xx + (yy << 1));                 //  x + 2y
                2'd2: nrow = mod5((xx << 1) + xx + (yy << 2));     // 3x + 4y
                2'd3: nrow = mod5((xx << 1) + (yy << 1) + yy);     // 2x + 3y
            endcase
        end
    endfunction
    function automatic logic [5:0] lane_addr(input logic [2:0] x, input logic [2:0] row);
        lane_addr = {1'b0, row, 2'b00} + {3'd0, row} + {3'd0, x};   // 5 * row + x
    endfunction
    // rho offsets r[x][y] (FIPS 202, table 2)
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
    // 6-stage logarithmic 64-bit left rotator
    function automatic logic [63:0] rol64(input logic [63:0] x, input logic [5:0] sh);
        logic [63:0] t0, t1, t2, t3, t4;
        begin
            t0    = sh[0] ? {x[62:0],  x[63]}     : x;
            t1    = sh[1] ? {t0[61:0], t0[63:62]} : t0;
            t2    = sh[2] ? {t1[59:0], t1[63:60]} : t1;
            t3    = sh[3] ? {t2[55:0], t2[63:56]} : t2;
            t4    = sh[4] ? {t3[47:0], t3[63:48]} : t3;
            rol64 = sh[5] ? {t4[31:0], t4[63:32]} : t4;
        end
    endfunction

    // ------------------------------------------------------------ sequencing
    localparam logic [1:0] K_IDLE = 2'd0, K_PAR = 2'd1, K_RND = 2'd2;
    logic [1:0] st;
    logic [4:0] rnd;        // round index 0..23 (round constant index)
    logic [4:0] t;          // K_PAR: 0..24, K_RND: 0..28
    logic [2:0] rx, ry;     // read position inside the round: row ry, position rx
    logic [2:0] wj, wy;     // write position inside the round: row wy, column wj

    assign busy = (st != K_IDLE);

    wire rd_act = (st == K_RND) && (t < 5'd25);
    wire wr_act = (st == K_RND) && (t >= 5'd4);
    wire [1:0] k_rd = rnd[1:0];           // 12 and 0 are both multiples of 4
    wire [1:0] k_wr = rnd[1:0] + 2'd1;

    // read: lane B[rx, ry] comes from logical lane (xs, ys) = (rx + 3 ry, rx) of the round input
    wire [2:0] xs = mod5({2'd0, rx} + {1'b0, ry, 1'b0} + {2'd0, ry});
    wire [2:0] ys = rx;
    wire [5:0] ra = lane_addr(xs, nrow(k_rd, xs, ys));
    // write: result E[wj, wy]
    wire [5:0] wa = lane_addr(wj, nrow(k_wr, wj, wy));

    // ------------------------------------------------------------ datapath
    wire [63:0] cnx [5];    // C_nxt ring: parity of the lanes written so far in this round
    wire [63:0] ccu [5];    // C_cur: column parity of the round input
    wire [63:0] bq1, bq2, bq3, bq4, b0s, b1s;

    // theta: D[xs] = C[xs - 1] ^ ROL(C[xs + 1], 1)
    logic [63:0] c_m, c_p;
    always_comb begin
        unique case (xs)
            3'd0:    begin c_m = ccu[4]; c_p = ccu[1]; end
            3'd1:    begin c_m = ccu[0]; c_p = ccu[2]; end
            3'd2:    begin c_m = ccu[1]; c_p = ccu[3]; end
            3'd3:    begin c_m = ccu[2]; c_p = ccu[4]; end
            default: begin c_m = ccu[3]; c_p = ccu[0]; end
        endcase
    end
    wire [63:0] d_x  = c_m ^ {c_p[62:0], c_p[63]};
    // rho (pi is the read order)
    wire [63:0] b_in = rol64(port ^ d_x, rho(xs, ys));

    // chi over the window: E[j] = B[j] ^ (~B[j+1] & B[j+2]); B[j] is bq4 when E[j] is formed
    wire [63:0] chi_a = (wj == 3'd4) ? b0s : bq3;
    wire [63:0] chi_b = (wj <= 3'd2) ? bq2 : (wj == 3'd3) ? b0s : b1s;
    wire [63:0] rc;
    qsag_keccak_rc u_rc (.idx(rnd), .rc(rc));
    wire [63:0] iota = (wj == 3'd0 && wy == 3'd0)
                       ? (rc ^ ((fault_inj && rnd == 5'd18) ? 64'h0000_0000_0001_0000 : 64'd0))
                       : 64'd0;
    wire [63:0] e_out = bq4 ^ (~chi_a & chi_b) ^ iota;

    always_comb begin
        rd_addr = 6'd0;
        wr_en   = 1'b0;
        wr_addr = 6'd0;
        wr_data = 64'd0;
        if (st == K_PAR) rd_addr = {1'b0, t};
        if (rd_act)      rd_addr = ra;
        if (wr_act) begin
            wr_en   = 1'b1;
            wr_addr = wa;
            wr_data = e_out;
        end
    end

    // window: one lane in per clock while a round runs
    wire win_en = (st == K_RND);
    qsag_ereg #(.W(64)) u_bq1 (.clk(clk), .rst_n(srst_n), .en(win_en), .d(b_in), .q(bq1));
    qsag_ereg #(.W(64)) u_bq2 (.clk(clk), .rst_n(srst_n), .en(win_en), .d(bq1),  .q(bq2));
    qsag_ereg #(.W(64)) u_bq3 (.clk(clk), .rst_n(srst_n), .en(win_en), .d(bq2),  .q(bq3));
    qsag_ereg #(.W(64)) u_bq4 (.clk(clk), .rst_n(srst_n), .en(win_en), .d(bq3),  .q(bq4));

    // C_nxt ring: rotates once per accumulated lane; the first five lanes of a pass load it
    wire        par_act  = (st == K_PAR);
    wire        ring_en  = par_act || wr_act;
    wire        ring_ld  = par_act ? (t < 5'd5) : (wy == 3'd0);
    wire [63:0] ring_src = par_act ? port : e_out;
    wire [63:0] ring_hd  = ring_ld ? ring_src : (cnx[0] ^ ring_src);
    genvar gi;
    generate
        for (gi = 0; gi < 4; gi++) begin : g_ring
            qsag_ereg #(.W(64)) u_c (.clk(clk), .rst_n(srst_n), .en(ring_en), .d(cnx[gi + 1]), .q(cnx[gi]));
        end
    endgenerate
    qsag_ereg #(.W(64)) u_c4 (.clk(clk), .rst_n(srst_n), .en(ring_en), .d(ring_hd), .q(cnx[4]));

    // C_cur <- C_nxt on the clock edge that ends a pass; the two saved window lanes B[0], B[1]
    // of the row being read (they are still needed after the window has moved on)
    wire cc_ld  = (par_act && t == 5'd24) || (st == K_RND && t == 5'd28);
    wire b0_ld  = rd_act && (rx == 3'd3);   // bq3 holds B[0] of this row
    wire b1_ld  = rd_act && (rx == 3'd4);   // bq3 holds B[1] of this row
    // The seven work rows are rows of the register file (ARCHITECTURE.md 5.2). The file opens each
    // row in the high phase after its load clock, when the source flops already hold the value of
    // that edge (ring after its last rotation, bq4 = the former bq3), exactly as the private latch
    // rows of qsag_keccak_serial did under QSAG_LATCH_RF.
    assign kw_we = {b1_ld, b0_ld, {5{cc_ld}}};
    assign kc_d  = {cnx[4], cnx[3], cnx[2], cnx[1], cnx[0]};
    assign kb_d  = bq4;
    generate
        for (gi = 0; gi < 5; gi++) begin : g_ccur
            assign ccu[gi] = kw_q[64*gi +: 64];
        end
    endgenerate
    assign b0s = kw_q[64*5 +: 64];
    assign b1s = kw_q[64*6 +: 64];
    // last clock of the permutation: the sequencer's next instruction runs in the clock after it
    assign last = (st == K_RND) && (t == 5'd28) && (rnd == 5'd23);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st   <= K_IDLE;
            done <= 1'b0;
            rnd  <= '0;
            t    <= '0;
            rx   <= '0;
            ry   <= '0;
            wj   <= '0;
            wy   <= '0;
        end else begin
            done <= 1'b0;
            unique case (st)
                K_IDLE: if (start) begin
                    rnd <= turbo ? 5'd12 : 5'd0;
                    t   <= 5'd0;
                    st  <= K_PAR;
                end
                K_PAR: begin
                    if (t == 5'd24) begin
                        t  <= 5'd0;
                        rx <= 3'd0;
                        ry <= 3'd0;
                        wj <= 3'd0;
                        wy <= 3'd0;
                        st <= K_RND;
                    end else t <= t + 5'd1;
                end
                K_RND: begin
                    if (rd_act) begin
                        if (rx == 3'd4) begin
                            rx <= 3'd0;
                            ry <= ry + 3'd1;
                        end else rx <= rx + 3'd1;
                    end
                    if (wr_act) begin
                        if (wj == 3'd4) begin
                            wj <= 3'd0;
                            wy <= wy + 3'd1;
                        end else wj <= wj + 3'd1;
                    end
                    if (t == 5'd28) begin
                        t  <= 5'd0;
                        rx <= 3'd0;
                        ry <= 3'd0;
                        wj <= 3'd0;
                        wy <= 3'd0;
                        if (rnd == 5'd23) begin
                            done <= 1'b1;
                            st   <= K_IDLE;
                        end else rnd <= rnd + 5'd1;
                    end else t <= t + 5'd1;
                end
                default: st <= K_IDLE;
            endcase
        end
    end
endmodule
`default_nettype wire
