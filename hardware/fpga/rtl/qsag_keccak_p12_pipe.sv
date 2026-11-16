// High-throughput unrolled 12-stage Keccak-p[1600, 12] pipeline (RFC 9861 TurboSHAKE256,
// rounds 12..23) for VU9P_TURBO Canopy verification: accepts 1 permutation per clock,
// latency 12 clocks, 0 DSPs, ~6 LUT levels between registers.
module qsag_keccak_p12_pipe #(
    parameter int TAGW = 10
) (
    input  logic              clk,
    input  logic              rst,
    input  logic              in_valid,
    input  logic [TAGW-1:0]   in_tag,
    input  logic [1599:0]     in_state,
    output logic              out_valid,
    output logic [TAGW-1:0]   out_tag,
    output logic [1599:0]     out_state
);
    function automatic logic [63:0] rc12(input int idx);
        case (idx)
            0:  rc12 = 64'h000000008000808B;
            1:  rc12 = 64'h800000000000008B;
            2:  rc12 = 64'h8000000000008089;
            3:  rc12 = 64'h8000000000008003;
            4:  rc12 = 64'h8000000000008002;
            5:  rc12 = 64'h8000000000000080;
            6:  rc12 = 64'h000000000000800A;
            7:  rc12 = 64'h800000008000000A;
            8:  rc12 = 64'h8000000080008081;
            9:  rc12 = 64'h8000000000008080;
            10: rc12 = 64'h0000000080000001;
            11: rc12 = 64'h8000000080008008;
            default: rc12 = 64'h0;
        endcase
    endfunction

    function automatic int rho_off(input int i);
        case (i)
            0: rho_off = 0;   1: rho_off = 1;   2: rho_off = 62;  3: rho_off = 28;  4: rho_off = 27;
            5: rho_off = 36;  6: rho_off = 44;  7: rho_off = 6;   8: rho_off = 55;  9: rho_off = 20;
            10: rho_off = 3;  11: rho_off = 10; 12: rho_off = 43; 13: rho_off = 25; 14: rho_off = 39;
            15: rho_off = 41; 16: rho_off = 45; 17: rho_off = 15; 18: rho_off = 21; 19: rho_off = 8;
            20: rho_off = 18; 21: rho_off = 2;  22: rho_off = 61; 23: rho_off = 56; 24: rho_off = 14;
            default: rho_off = 0;
        endcase
    endfunction

    function automatic logic [1599:0] kround(input logic [1599:0] s, input logic [63:0] rc);
        logic [24:0][63:0] a, b, e;
        logic [4:0][63:0]  c, d;
        logic [127:0]      dbl;
        a = s;
        for (int x = 0; x < 5; x++) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        for (int x = 0; x < 5; x++)
            d[x] = c[(x + 4) % 5] ^ {c[(x + 1) % 5][62:0], c[(x + 1) % 5][63]};
        for (int y = 0; y < 5; y++) begin
            for (int x = 0; x < 5; x++) begin
                dbl = {2{a[x + 5*y] ^ d[x]}};
                b[y + 5*((2*x + 3*y) % 5)] = dbl[(64 - rho_off(x + 5*y)) +: 64];
            end
        end
        for (int y = 0; y < 5; y++)
            for (int x = 0; x < 5; x++)
                e[x + 5*y] = b[x + 5*y] ^ (~b[(x + 1) % 5 + 5*y] & b[(x + 2) % 5 + 5*y]);
        e[0] = e[0] ^ rc;
        kround = e;
    endfunction

    logic [11:0]         v_sr;
    logic [12*TAGW-1:0]  t_sr;
    logic [12*1600-1:0]  st_q;

    always_ff @(posedge clk) begin
        if (rst) v_sr <= '0;
        else     v_sr <= {v_sr[10:0], in_valid};
        t_sr <= {t_sr[11*TAGW-1:0], in_tag};
    end

    for (genvar s = 0; s < 12; s++) begin : g_st
        wire [1599:0] prev = (s == 0) ? in_state : st_q[(s-1)*1600 +: 1600];
        always_ff @(posedge clk) st_q[s*1600 +: 1600] <= kround(prev, rc12(s));
    end

    assign out_valid = v_sr[11];
    assign out_tag   = t_sr[11*TAGW +: TAGW];
    assign out_state = st_q[11*1600 +: 1600];
endmodule
