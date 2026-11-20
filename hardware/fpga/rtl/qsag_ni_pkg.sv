// Shared constants of the QSAG-NI FPGA core. Latencies are in clock cycles.
package qsag_ni_pkg;
    // Every design top uses a subset of these.
    /* verilator lint_off UNUSEDPARAM */
    localparam logic [63:0] GL_P = 64'hFFFF_FFFF_0000_0001;  // 2^64 - 2^32 + 1

    localparam int MUL64_LAT    = 3;                       // 9-DSP Solinas-Karatsuba qsag_mul64_dsp
    localparam int RED_LAT      = 2;                       // qsag_gl64_reduce
    localparam int GL_MUL_LAT   = MUL64_LAT + RED_LAT;     // qsag_gl64_dsp_mul (standalone: 5)
    localparam int P2_SBOX_LAT  = 2 * (MUL64_LAT + 1) + GL_MUL_LAT; // qsag_p2_sbox7 (fused: 13)
    localparam int P2_LIN_LAT   = 2;                       // qsag_p2_linear
    localparam int P2_ROUND_LAT = P2_SBOX_LAT + P2_LIN_LAT;// 15
    localparam int P2_RING_LEN  = P2_ROUND_LAT + 1;        // ring core: 16 cycles per pass (496/perm)
    localparam int P2_PASSES    = 31;                      // initial M_E + 8 external + 22 internal
    localparam int P2_PIPE_LAT  = 1 + P2_LIN_LAT + 30 * P2_ROUND_LAT; // unrolled pipe: 453 clocks
    localparam int EXT4_MAC_LAT = 1 + MUL64_LAT + 1 + RED_LAT;        // 9-mul tower Karatsuba: 7
    localparam int EXT5_MAC_LAT = 1 + MUL64_LAT + 1 + RED_LAT;        // 14-mul Karatsuba F_p^5: 7
    localparam int GF128_LAT    = 3;                       // qsag_gf128_clmul
    /* verilator lint_on UNUSEDPARAM */
endpackage
