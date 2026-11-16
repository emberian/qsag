// Dregg-180 (QSAG-NI-180) 5-lane row-serial in-place Keccak-p[1600, nr] engine.
//
// Executes 1 full Keccak round in 5 clocks (60 clocks for 12-round TurboSHAKE256, 120 clocks for
// 24-round Keccak-f[1600] — 25.0x faster than the 1,500 / 3,000-clock word-serial baseline) with
// ZERO eviction scratch flip-flops:
//   * Column parities D[0..4] are computed combinationally over the 25 sponge wires at `start`
//     and at step k = 4 of each round (when st[0..19] hold rows 0..3 of A_next and a_out[0..4]
//     holds row 4 of A_next), latching into 5 x 64-bit secret-cleared registers (320 bits total,
//     64 bits smaller than the old serial ring + tmp!).
//   * Steps k = 0..4 each consume one diagonal of 5 lanes through fixed wire-only rotations,
//     apply chi + iota, write row k of A_next, and evict still-live lanes into the just-freed
//     diagonal slots so all 25 lanes return to canonical order at k = 4.
`default_nettype none

module qsag_keccak_rc (
    input  wire  [4:0]  idx,
    output logic [63:0] rc
);
    always_comb begin
        unique case (idx)
            5'd0:    rc = 64'h0000_0000_0000_0001;
            5'd1:    rc = 64'h0000_0000_0000_8082;
            5'd2:    rc = 64'h8000_0000_0000_808A;
            5'd3:    rc = 64'h8000_0000_8000_8000;
            5'd4:    rc = 64'h0000_0000_0000_808B;
            5'd5:    rc = 64'h0000_0000_8000_0001;
            5'd6:    rc = 64'h8000_0000_8000_8081;
            5'd7:    rc = 64'h8000_0000_0000_8009;
            5'd8:    rc = 64'h0000_0000_0000_008A;
            5'd9:    rc = 64'h0000_0000_0000_0088;
            5'd10:   rc = 64'h0000_0000_8000_8009;
            5'd11:   rc = 64'h0000_0000_8000_000A;
            5'd12:   rc = 64'h0000_0000_8000_808B;
            5'd13:   rc = 64'h8000_0000_0000_008B;
            5'd14:   rc = 64'h8000_0000_0000_8089;
            5'd15:   rc = 64'h8000_0000_0000_8003;
            5'd16:   rc = 64'h8000_0000_0000_8002;
            5'd17:   rc = 64'h8000_0000_0000_0080;
            5'd18:   rc = 64'h0000_0000_0000_800A;
            5'd19:   rc = 64'h8000_0000_8000_000A;
            5'd20:   rc = 64'h8000_0000_8000_8081;
            5'd21:   rc = 64'h8000_0000_0000_8080;
            5'd22:   rc = 64'h0000_0000_8000_0001;
            default: rc = 64'h8000_0000_8000_8008;
        endcase
    end
endmodule

module qsag_keccak_serial (
    input  wire              clk,
    input  wire              rst_n,       // control reset
    input  wire              srst_n,      // secret clear
    input  wire              start,
    input  wire              turbo,       // 0: 24 rounds, 1: last 12 rounds
    input  wire              fault_inj,   // EAL6+ Bellcore / laser fault-injection self-test hook
    output wire              busy,
    output logic             done,
    input  wire  [25*64-1:0] st_flat_i,
    output logic [24:0]      kc_we,
    output logic [25*64-1:0] kc_wdata
);
    function automatic logic [63:0] rol64(input logic [63:0] v, input int sh);
        if (sh == 0) rol64 = v;
        else         rol64 = (v << sh) | (v >> (64 - sh));
    endfunction

    wire [63:0] st [25];
    genvar gi;
    generate
        for (gi = 0; gi < 25; gi++) begin : g_unpk
            assign st[gi] = st_flat_i[64*gi +: 64];
        end
    endgenerate

    logic       run;
    logic [4:0] rnd;
    logic [2:0] k;
    wire [63:0] d_reg [5];

    assign busy = run;

    wire [63:0] rc;
    qsag_keccak_rc u_rc (.idx(rnd), .rc(rc));

    // 5-lane diagonal read + theta + fixed wire-only rho rotation for step k = 0..4
    logic [63:0] b0, b1, b2, b3, b4;
    always_comb begin
        unique case (k)
            3'd0: begin
                b0 = rol64(st[0]  ^ d_reg[0],  0);
                b1 = rol64(st[6]  ^ d_reg[1], 44);
                b2 = rol64(st[12] ^ d_reg[2], 43);
                b3 = rol64(st[18] ^ d_reg[3], 21);
                b4 = rol64(st[24] ^ d_reg[4], 14);
            end
            3'd1: begin
                b0 = rol64(st[18] ^ d_reg[3], 28);
                b1 = rol64(st[9]  ^ d_reg[4], 20);
                b2 = rol64(st[10] ^ d_reg[0],  3);
                b3 = rol64(st[16] ^ d_reg[1], 45);
                b4 = rol64(st[22] ^ d_reg[2], 61);
            end
            3'd2: begin
                b0 = rol64(st[16] ^ d_reg[1],  1);
                b1 = rol64(st[18] ^ d_reg[2],  6);
                b2 = rol64(st[13] ^ d_reg[3], 25);
                b3 = rol64(st[19] ^ d_reg[4],  8);
                b4 = rol64(st[20] ^ d_reg[0], 18);
            end
            3'd3: begin
                b0 = rol64(st[24] ^ d_reg[4], 27);
                b1 = rol64(st[16] ^ d_reg[0], 36);
                b2 = rol64(st[18] ^ d_reg[1], 10);
                b3 = rol64(st[17] ^ d_reg[2], 15);
                b4 = rol64(st[23] ^ d_reg[3], 56);
            end
            default: begin // k == 3'd4
                b0 = rol64(st[24] ^ d_reg[2], 62);
                b1 = rol64(st[22] ^ d_reg[3], 55);
                b2 = rol64(st[20] ^ d_reg[4], 39);
                b3 = rol64(st[23] ^ d_reg[0], 41);
                b4 = rol64(st[21] ^ d_reg[1],  2);
            end
        endcase
    end

    // Chi + Iota (plus optional single-bit laser fault-injection test hook at round 18, k=0)
    wire [63:0] iota_xor = (k == 3'd0) ? (rc ^ ((fault_inj && rnd == 5'd18) ? 64'h0000_0000_0001_0000 : 64'd0)) : 64'd0;
    wire [63:0] a_out [5];
    assign a_out[0] = b0 ^ (~b1 & b2) ^ iota_xor;
    assign a_out[1] = b1 ^ (~b2 & b3);
    assign a_out[2] = b2 ^ (~b3 & b4);
    assign a_out[3] = b3 ^ (~b4 & b0);
    assign a_out[4] = b4 ^ (~b0 & b1);

    // Combinational column parity C[0..4] and D[0..4]:
    //   - At !run && start: over st[0..24]
    //   - At run && k == 4: over st[0..19] (already holding A_next rows 0..3) and a_out[0..4] (row 4)
    wire [63:0] c_col [5];
    wire [63:0] d_nxt [5];
    generate
        for (gi = 0; gi < 5; gi++) begin : g_par
            wire [63:0] r4_lane = run ? a_out[gi] : st[20 + gi];
            assign c_col[gi] = st[gi] ^ st[5 + gi] ^ st[10 + gi] ^ st[15 + gi] ^ r4_lane;
        end
        for (gi = 0; gi < 5; gi++) begin : g_d
            localparam int PREV = (gi + 4) % 5;
            localparam int NEXT = (gi + 1) % 5;
            assign d_nxt[gi] = c_col[PREV] ^ {c_col[NEXT][62:0], c_col[NEXT][63]};
        end
    endgenerate

    wire load_d = (!run && start) || (run && (k == 3'd4) && (rnd != 5'd23));
    generate
        for (gi = 0; gi < 5; gi++) begin : g_dreg
            qsag_ereg #(.W(64)) u_d (.clk(clk), .rst_n(srst_n), .en(load_d), .d(d_nxt[gi]), .q(d_reg[gi]));
        end
    endgenerate

    // In-place row write + live-lane eviction muxing
    always_comb begin
        kc_we    = 25'd0;
        kc_wdata = '0;
        if (run) begin
            unique case (k)
                3'd0: begin
                    for (int xp = 0; xp < 5; xp++) begin
                        kc_we[xp]             = 1'b1;
                        kc_wdata[64*xp +: 64] = a_out[xp];
                    end
                    kc_we[6]  = 1'b1; kc_wdata[64*6  +: 64] = st[1];
                    kc_we[12] = 1'b1; kc_wdata[64*12 +: 64] = st[2];
                    kc_we[18] = 1'b1; kc_wdata[64*18 +: 64] = st[3];
                    kc_we[24] = 1'b1; kc_wdata[64*24 +: 64] = st[4];
                end
                3'd1: begin
                    for (int xp = 0; xp < 5; xp++) begin
                        kc_we[5 + xp]             = 1'b1;
                        kc_wdata[64*(5+xp) +: 64] = a_out[xp];
                    end
                    kc_we[10] = 1'b1; kc_wdata[64*10 +: 64] = st[5];
                    kc_we[16] = 1'b1; kc_wdata[64*16 +: 64] = st[6];
                    kc_we[18] = 1'b1; kc_wdata[64*18 +: 64] = st[7];
                    kc_we[22] = 1'b1; kc_wdata[64*22 +: 64] = st[8];
                end
                3'd2: begin
                    for (int xp = 0; xp < 5; xp++) begin
                        kc_we[10 + xp]             = 1'b1;
                        kc_wdata[64*(10+xp) +: 64] = a_out[xp];
                    end
                    kc_we[16] = 1'b1; kc_wdata[64*16 +: 64] = st[10];
                    kc_we[18] = 1'b1; kc_wdata[64*18 +: 64] = st[11];
                    kc_we[19] = 1'b1; kc_wdata[64*19 +: 64] = st[12];
                    kc_we[20] = 1'b1; kc_wdata[64*20 +: 64] = st[14];
                end
                3'd3: begin
                    for (int xp = 0; xp < 5; xp++) begin
                        kc_we[15 + xp]             = 1'b1;
                        kc_wdata[64*(15+xp) +: 64] = a_out[xp];
                    end
                    kc_we[23] = 1'b1; kc_wdata[64*23 +: 64] = st[15];
                    kc_we[24] = 1'b1; kc_wdata[64*24 +: 64] = st[19];
                end
                default: begin // 3'd4
                    for (int xp = 0; xp < 5; xp++) begin
                        kc_we[20 + xp]             = 1'b1;
                        kc_wdata[64*(20+xp) +: 64] = a_out[xp];
                    end
                end
            endcase
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            run  <= 1'b0;
            done <= 1'b0;
            rnd  <= '0;
            k    <= '0;
        end else begin
            done <= 1'b0;
            if (!run) begin
                if (start) begin
                    run <= 1'b1;
                    rnd <= turbo ? 5'd12 : 5'd0;
                    k   <= 3'd0;
                end
            end else begin
                if (k == 3'd4) begin
                    k <= 3'd0;
                    if (rnd == 5'd23) begin
                        run  <= 1'b0;
                        done <= 1'b1;
                    end else begin
                        rnd <= rnd + 5'd1;
                    end
                end else begin
                    k <= k + 3'd1;
                end
            end
        end
    end
endmodule
`default_nettype wire
