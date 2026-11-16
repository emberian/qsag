// Keccak-p[1600] permutation core in LUT logic: RPC = 1 or 2 rounds per clock.
//   nr12 = 0 : Keccak-f[1600], 24 rounds (SHAKE256 / cSHAKE256 / SHA-3)  -> 24 / RPC clocks
//   nr12 = 1 : Keccak-p[1600, 12], rounds 12..23 (RFC 9861 TurboSHAKE256) -> 12 / RPC clocks
// State lane (x, y) is state[64*(x + 5*y) +: 64], the byte order of FIPS 202 on a little-endian
// lane array. `done` pulses in the cycle `state_o` holds the result; the result stays until the
// next `start`.
module qsag_keccak_turboshake #(
    parameter int RPC = 2
) (
    input  logic          clk,
    input  logic          rst,
    input  logic          start,
    input  logic          nr12,
    input  logic [1599:0] state_i,
    output logic          busy,
    output logic          done,
    output logic [1599:0] state_o
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

    // rho rotation of lane x + 5*y.
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

    function automatic logic [1599:0] keccak_round(input logic [1599:0] s, input logic [63:0] rc);
        logic [24:0][63:0] a, b, e;
        logic [4:0][63:0]  c, d;
        logic [127:0]      dbl;
        a = s;
        for (int x = 0; x < 5; x++) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        for (int x = 0; x < 5; x++)
            d[x] = c[(x + 4) % 5] ^ {c[(x + 1) % 5][62:0], c[(x + 1) % 5][63]};
        // theta, then rho and pi: B[y, 2x + 3y] = rot(A[x, y], rho[x, y]).
        for (int y = 0; y < 5; y++) begin
            for (int x = 0; x < 5; x++) begin
                dbl = {2{a[x + 5*y] ^ d[x]}};
                b[y + 5*((2*x + 3*y) % 5)] = dbl[(64 - rho_off(x + 5*y)) +: 64];
            end
        end
        // chi, iota.
        for (int y = 0; y < 5; y++)
            for (int x = 0; x < 5; x++)
                e[x + 5*y] = b[x + 5*y] ^ (~b[(x + 1) % 5 + 5*y] & b[(x + 2) % 5 + 5*y]);
        e[0] = e[0] ^ rc;
        keccak_round = e;
    endfunction

    logic [4:0]    rnd;
    logic [1599:0] nxt;
    if (RPC == 2) begin : g_two
        assign nxt = keccak_round(keccak_round(state_o, round_const(rnd)), round_const(rnd + 5'd1));
    end else begin : g_one
        assign nxt = keccak_round(state_o, round_const(rnd));
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            busy <= 1'b0;
            done <= 1'b0;
        end else begin
            done <= 1'b0;
            if (start && !busy) begin
                busy <= 1'b1;
            end else if (busy && rnd == 5'(24 - RPC)) begin
                busy <= 1'b0;
                done <= 1'b1;
            end
        end
        if (start && !busy) begin
            state_o <= state_i;
            rnd     <= nr12 ? 5'd12 : 5'd0;
        end else if (busy) begin
            state_o <= nxt;
            rnd     <= rnd + 5'(RPC);
        end
    end
endmodule
