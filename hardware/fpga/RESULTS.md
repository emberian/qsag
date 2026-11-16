# QSAG-NI FPGA: raw results

Collected 2026-11-16T12:52Z on dregg-build2 from `build/`. Tools: Yosys 0.71+34, Verilator 5.055, Z3 version 4.15.5, "nextpnr-ecp5" -- Next Generation Place and Route (Version nextpnr-0.11.1-92-g5e2718b6).

## Lint
```
lint qsag_ni_fpga_top: 0 warnings
lint qsag_poseidon2_12_pipe: 0 warnings
```
## Simulation: units
```
[PASS] reference model vs Lean oracle vectors / RFC 9861: 118 checks, 0 mismatches
[PASS] gl64 mul (both tilings) / reduce136 / x^7 / Ext4 MAC / GF(2^128): Lean KATs, edges, 200k random: 1680001 checks, 0 mismatches
  ring core: latency 651 clocks/permutation (min=max), 21 jobs in flight, 150 permutations in 5211 clocks (34.74 clocks/perm)
[PASS] Poseidon2 ring core: 4 Lean KATs + 146 random perms / feed-forward hashes, C-slow interleaved: 1718 checks, 0 mismatches
  pipelined core: latency 603 clocks, 1200 permutations out in 1200 consecutive clocks
[PASS] Poseidon2 pipelined core: 4 Lean KATs + 1196 random, back to back: 13617 checks, 0 mismatches
  keccak clocks per permutation: 1 round/clk 24 (f1600) / 12 (p1600,12); 2 rounds/clk 12 / 6
[PASS] Keccak core: Lean SHA3-256/SHAKE256/cSHAKE256 KATs (14 lengths), RFC 9861 TurboSHAKE256, D=0x07: 4482 checks, 0 mismatches
UNITS: 1699936 checks, 0 mismatches, 209136 clocks simulated
```
## Simulation: top
```
[PASS] reference model vs Lean oracle vectors / RFC 9861: 118 checks, 0 mismatches
[PASS] top: ID, P2_PERM/P2_JIVE, EXT4_MAC, SC_ROUND (accept + reject), GF_MAC (accept + reject): 114 checks, 0 mismatches
[PASS] top: SHAKE256 Lean KATs, TurboSHAKE256 (RFC 9861, D=0x07) via KEC ops: 9 checks, 0 mismatches
[PASS] top: BRAM fold engine, 1/2/5/9-variable tables vs fold_first_var model: 20 checks, 0 mismatches
  32 chains x (3 sponge + 7 node) = 320 permutations in 10530 clocks wall (32.9 clocks/perm; a lone permutation takes 651)
[PASS] top: chain engine, 32 concurrent leaf-sponge + Canopy paths (depth 7), one corrupted: 40 checks, 0 mismatches
QSAGSTA1-shaped root verification (modelled operation mix, real data, every result checked)
  shape: nv=20, stages (inv-rate log, fold k, queries) = (2,5,216) (4,3,109) (6,4,74), 72 sumcheck rounds, final 2^8
  Poseidon2 permutations : 11407  (72 transcript, sequential; 11335 leaf-sponge + Canopy node, C-slow on the ring)
  Ext4 MACs              : 9040  (216 sumcheck Horner, 8824 fold butterflies)
  clocks, wall (AXI host with zero think time)  : 488933
    transcript + sumcheck rounds                : 63670  (core-busy 47088 + 1872)
    query leaf hashes + Merkle paths            : 376363
    query folds                                 : 48140
    final evaluation                            : 760
  clocks with any engine active (TOTAL_CYCLES)  : 454232
  fold engine core-busy clocks                  : 29756
  bus traffic: 7060 AXI4-Lite writes, 227130 reads, 20559 stream beats
[PASS] QSAGSTA1-shaped root verification trace: 3252 checks, 0 mismatches
16-variable Ext4 edge fold (65,535 butterflies, in place in block RAM)
  table load over AXI4-Stream : 65538 clocks (one entry per clock)
  16 fold rounds, core-busy   : 65729 clocks (two FOLD_MULTI commands of 8 rounds)
  16 fold rounds, wall        : 66012 clocks (incl. 16 challenges over AXI4-Lite)
[PASS] 16-variable hyperweb edge fold vs fold_first_var model: 4 checks, 0 mismatches
TOP: 3558 checks, 0 mismatches, 639628 clocks simulated
```
## Trace report
```
QSAGSTA1-shaped root verification (modelled operation mix, real data, every result checked)
  shape: nv=20, stages (inv-rate log, fold k, queries) = (2,5,216) (4,3,109) (6,4,74), 72 sumcheck rounds, final 2^8
  Poseidon2 permutations : 11407  (72 transcript, sequential; 11335 leaf-sponge + Canopy node, C-slow on the ring)
  Ext4 MACs              : 9040  (216 sumcheck Horner, 8824 fold butterflies)
  clocks, wall (AXI host with zero think time)  : 488933
    transcript + sumcheck rounds                : 63670  (core-busy 47088 + 1872)
    query leaf hashes + Merkle paths            : 376363
    query folds                                 : 48140
    final evaluation                            : 760
  clocks with any engine active (TOTAL_CYCLES)  : 454232
  fold engine core-busy clocks                  : 29756
  bus traffic: 7060 AXI4-Lite writes, 227130 reads, 20559 stream beats
16-variable Ext4 edge fold (65,535 butterflies, in place in block RAM)
  table load over AXI4-Stream : 65538 clocks (one entry per clock)
  16 fold rounds, core-busy   : 65729 clocks (two FOLD_MULTI commands of 8 rounds)
  16 fold rounds, wall        : 66012 clocks (incl. 16 challenges over AXI4-Lite)
```
## Formal checks (z3)

| result | check | expected | z3 | time | statement |
|---|---|---|---|---|---|
| PASS | `reduce_identity` | unsat | unsat | 0.0s | integers: x + p = V + p*Q0 for x = lo + m 2^64 + h 2^96 + t 2^128 (the Goldilocks reduction identity) |
| PASS | `reduce_range` | unsat | unsat | 0.0s | integers: limbs in range imply 0 < V < 3p (so V is exact in the bit-vector statement) |
| PASS | `gl64_reduce` | unsat | unsat | 1.5s | qsag_gl64_reduce: for all 2^136 inputs, r (2 clocks later) < p and V(x) = r + k*p, k in {0,1,2} |
| PASS | `tiling_identity_26x17` | unsat | unsat | 0.0s | integers: (sum a_i 2^(26i)) * (sum b_j 2^(17j)) = sum a_i b_j 2^(26i+17j) |
| PASS | `tile_bound_12x13` | unsat | unsat | 0.0s | integers: 0 <= a < 2^12 and 0 <= b < 2^13 imply a*b <= (2^12-1)(2^13-1) < 2^43 |
| PASS | `tile_bound_12x17` | unsat | unsat | 0.0s | integers: 0 <= a < 2^12 and 0 <= b < 2^17 imply a*b <= (2^12-1)(2^17-1) < 2^43 |
| PASS | `tile_bound_26x13` | unsat | unsat | 0.0s | integers: 0 <= a < 2^26 and 0 <= b < 2^13 imply a*b <= (2^26-1)(2^13-1) < 2^43 |
| PASS | `tile_bound_26x17` | unsat | unsat | 0.1s | integers: 0 <= a < 2^26 and 0 <= b < 2^17 imply a*b <= (2^26-1)(2^17-1) < 2^43 |
| PASS | `gl64_dsp_mul_26x17_product` | unsat | unsat | 91.4s | qsag_gl64_dsp_mul AW=26 BW=17: for all 2^128 inputs, the product register (4 clocks later) = the weighted sum X of the 12 tile products (tiles: any function within the product bound) |
| PASS | `gl64_dsp_mul_26x17_reduce` | unsat | unsat | 0.2s | qsag_gl64_dsp_mul AW=26 BW=17: for every product register value X, r (2 clocks later) < p and V(X) = r + k*p, k in {0,1,2} |
| PASS | `tiling_identity_16x16` | unsat | unsat | 0.0s | integers: (sum a_i 2^(16i)) * (sum b_j 2^(16j)) = sum a_i b_j 2^(16i+16j) |
| PASS | `tile_bound_16x16` | unsat | unsat | 0.0s | integers: 0 <= a < 2^16 and 0 <= b < 2^16 imply a*b <= (2^16-1)(2^16-1) < 2^32 |
| PASS | `gl64_dsp_mul_16x16_product` | unsat | unsat | 110.5s | qsag_gl64_dsp_mul AW=16 BW=16: for all 2^128 inputs, the product register (4 clocks later) = the weighted sum X of the 16 tile products (tiles: any function within the product bound) |
| PASS | `gl64_dsp_mul_16x16_reduce` | unsat | unsat | 0.2s | qsag_gl64_dsp_mul AW=16 BW=16: for every product register value X, r (2 clocks later) < p and V(X) = r + k*p, k in {0,1,2} |
| PASS | `mut_gl64_reduce_sign` | sat | sat | 0.0s | qsag_gl64_reduce: for all 2^136 inputs, r (2 clocks later) < p and V(x) = r + k*p, k in {0,1,2} |
| PASS | `mut_select_gl64_dsp_mul_product` | unsat | unsat | 94.3s | qsag_gl64_dsp_mul AW=26 BW=17: for all 2^128 inputs, the product register (4 clocks later) = the weighted sum X of the 12 tile products (tiles: any function within the product bound) |
| PASS | `mut_select_gl64_dsp_mul_reduce` | sat | sat | 0.1s | qsag_gl64_dsp_mul AW=26 BW=17: for every product register value X, r (2 clocks later) < p and V(X) = r + k*p, k in {0,1,2} |
| PASS | `mut_tile_mul64_wiring` | sat | sat | 0.3s | qsag_mul64_dsp AW=26 BW=17: p (4 clocks later) = sum of the 12 tile products shifted to their weights (tiles: any function within the product bound) |
| PASS | `mut_shift_gl64_dsp_mul_product` | sat | sat | 1.1s | qsag_gl64_dsp_mul AW=26 BW=17: for all 2^128 inputs, the product register (4 clocks later) = the weighted sum X of the 12 tile products (tiles: any function within the product bound) |
| PASS | `mut_shift_gl64_dsp_mul_reduce` | unsat | unsat | 0.2s | qsag_gl64_dsp_mul AW=26 BW=17: for every product register value X, r (2 clocks later) < p and V(X) = r + k*p, k in {0,1,2} |
| PASS | `gf128_reduce` | unsat | unsat | 61.8s | qsag_gf128_reduce: for all 2^255 inputs, r = c mod (x^128+x^7+x^2+x+1) (spec: XOR of the constants x^i mod P over the set bits) |
| PASS | `mut_gf128_reduce_tap` | sat | sat | 0.7s | qsag_gf128_reduce: for all 2^255 inputs, r = c mod (x^128+x^7+x^2+x+1) (spec: XOR of the constants x^i mod P over the set bits) |
| PASS | `mut_gf128_clmul_kara` | sat | sat | 4.3s | qsag_gf128_clmul: for all 2^256 inputs, r (3 clocks later) = a*b in GF(2^128) (bit-serial spec) |
| PASS | `mut_gf128_clmul_basis_x77` | sat | sat | 6.7s | qsag_gf128_clmul: for all a and b = x^77, r (3 clocks later) = a * x^77 in GF(2^128) |
| open | `try_clmul_kara_w16` | unsat | timeout | 60.0s | qsag_clmul_kara W=16: for all 2^32 inputs, p = carry-less product of a and b |
| open | `try_gf128_clmul_basis_x0` | unsat | timeout | 60.0s | qsag_gf128_clmul: for all a and b = x^0, r (3 clocks later) = a * x^0 in GF(2^128) |
| open | `try_gf128_clmul_basis_x77` | unsat | timeout | 60.0s | qsag_gf128_clmul: for all a and b = x^77, r (3 clocks later) = a * x^77 in GF(2^128) |
| open | `try_gf128_clmul_monolithic` | unsat | timeout | 60.0s | qsag_gf128_clmul: for all 2^256 inputs, r (3 clocks later) = a*b in GF(2^128) (bit-serial spec) |
| open | `try_mul64_wiring_precise_26x17` | unsat | timeout | 60.0s | qsag_mul64_dsp AW=26 BW=17: p (4 clocks later) = sum of the 12 tile products shifted to their weights (bit-precise tiles) |
| open | `try_gl64_dsp_mul_monolithic` | unsat | timeout | 60.0s | qsag_gl64_dsp_mul: r = bvurem(bvmul(a, b), p), one bit-blasted query |

## Canonical-form check of the carry-less multiplier
```
PASS	anf_gf128_clmul_anf	equal	equal	0/128 bits differ, 40832 monomials
PASS	anf_mut_gf128_clmul_anf	different	different	128/128 bits differ, 40832 monomials
```
## Yosys synthesis: xcup
```
== qsag_ext4_mac_bfly_taw10 [xcup]
  LUT (LUT1-6)                 11971
    of which LUT6              824
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     18551
  CARRY8                       0
  CARRY4                       2224
  DSP48E2                      192
  RAMB36E2                     8
  RAMB18E2                     0
  SRL16E/SRLC32E               267
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 43
== qsag_ext4_mac [xcup]
  LUT (LUT1-6)                 10387
    of which LUT6              822
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     17488
  CARRY8                       0
  CARRY4                       2084
  DSP48E2                      192
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               256
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 43
== qsag_gf128_clmul [xcup]
  LUT (LUT1-6)                 5007
    of which LUT6              496
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     639
  CARRY8                       0
  CARRY4                       0
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 3
== qsag_gl64_dsp_mul [xcup]
  LUT (LUT1-6)                 681
    of which LUT6              33
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     1157
  CARRY8                       0
  CARRY4                       156
  DSP48E2                      12
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 35
== qsag_gl64_reduce [xcup]
  LUT (LUT1-6)                 269
    of which LUT6              26
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     130
  CARRY8                       0
  CARRY4                       51
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 21
== qsag_keccak_rpc1 [xcup]
  LUT (LUT1-6)                 3551
    of which LUT6              0
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     1614
  CARRY8                       0
  CARRY4                       2
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 6
== qsag_keccak_rpc2 [xcup]
  LUT (LUT1-6)                 7715
    of which LUT6              484
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     1614
  CARRY8                       0
  CARRY4                       3
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 8
== qsag_ni_fpga_top_taw10 [xcup]
  LUT (LUT1-6)                 84942
    of which LUT6              5585
  MUXF7/F8/F9                  2
  FF (FDRE/FDSE/FDCE/FDPE)     88813
  CARRY8                       0
  CARRY4                       11751
  DSP48E2                      768
  RAMB36E2                     8
  RAMB18E2                     57
  SRL16E/SRLC32E               2084
  LUTRAM (RAM32M/RAM64M/...)   59
  reg-to-reg depth (LUT+carry cells) 2344
== qsag_ni_fpga_top_taw16 [xcup]
  LUT (LUT1-6)                 86496
    of which LUT6              6603
  MUXF7/F8/F9                  3
  FF (FDRE/FDSE/FDCE/FDPE)     88831
  CARRY8                       0
  CARRY4                       11753
  DSP48E2                      768
  RAMB36E2                     464
  RAMB18E2                     57
  SRL16E/SRLC32E               2090
  LUTRAM (RAM32M/RAM64M/...)   59
  reg-to-reg depth (LUT+carry cells) 2344
== qsag_p2_chain_engine [xcup]
  LUT (LUT1-6)                 3168
    of which LUT6              333
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     2498
  CARRY8                       0
  CARRY4                       284
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     57
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   59
  reg-to-reg depth (LUT+carry cells) 32
== qsag_p2_linear [xcup]
  LUT (LUT1-6)                 8659
    of which LUT6              391
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     1680
  CARRY8                       0
  CARRY4                       1409
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 32
== qsag_p2_sbox7 [xcup]
  LUT (LUT1-6)                 2724
    of which LUT6              132
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     4628
  CARRY8                       0
  CARRY4                       624
  DSP48E2                      48
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               64
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 35
== qsag_poseidon2_12_fpga [xcup]
  LUT (LUT1-6)                 44769
    of which LUT6              2003
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     59336
  CARRY8                       0
  CARRY4                       8967
  DSP48E2                      576
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               1818
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 35
== qsag_poseidon2_12_pipe [xcup]
  LUT (LUT1-6)                 511277
    of which LUT6              22414
  MUXF7/F8/F9                  22
  FF (FDRE/FDSE/FDCE/FDPE)     599035
  CARRY8                       0
  CARRY4                       96812
  DSP48E2                      5664
  RAMB36E2                     8
  RAMB18E2                     1
  SRL16E/SRLC32E               23040
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 35
```
## Yosys synthesis: ecp5
```
== qsag_ext4_mac_bfly_taw10 [ecp5]
  LUT4                         13540
  TRELLIS_FF                   21696
  CCU2C                        4143
  L6MUX21/PFUMX                2418
  MULT18X18D                   256
  DP16KD                       16
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 74
== qsag_ext4_mac [ecp5]
  LUT4                         11657
  TRELLIS_FF                   19488
  CCU2C                        3870
  L6MUX21/PFUMX                2390
  MULT18X18D                   256
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 74
== qsag_gf128_clmul [ecp5]
  LUT4                         6363
  TRELLIS_FF                   639
  CCU2C                        0
  L6MUX21/PFUMX                1026
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 5
== qsag_gl64_dsp_mul [ecp5]
  LUT4                         773
  TRELLIS_FF                   1218
  CCU2C                        292
  L6MUX21/PFUMX                174
  MULT18X18D                   16
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 64
== qsag_gl64_reduce [ecp5]
  LUT4                         467
  TRELLIS_FF                   130
  CCU2C                        100
  L6MUX21/PFUMX                151
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 36
== qsag_keccak_rpc1 [ecp5]
  LUT4                         8454
  TRELLIS_FF                   1607
  CCU2C                        3
  L6MUX21/PFUMX                4714
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 6
== qsag_keccak_rpc2 [ecp5]
  LUT4                         12033
  TRELLIS_FF                   1606
  CCU2C                        0
  L6MUX21/PFUMX                4262
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 12
== qsag_ni_fpga_top_taw10 [ecp5]
  LUT4                         101379
  TRELLIS_FF                   119695
  CCU2C                        22359
  L6MUX21/PFUMX                19725
  MULT18X18D                   1024
  DP16KD                       73
  TRELLIS_DPR16X4              406
  reg-to-reg depth (LUT+carry cells) 2346
== qsag_ni_fpga_top_taw16 [ecp5]
  LUT4                         109068
  TRELLIS_FF                   119781
  CCU2C                        22365
  L6MUX21/PFUMX                21729
  MULT18X18D                   1024
  DP16KD                       985
  TRELLIS_DPR16X4              406
  reg-to-reg depth (LUT+carry cells) 2346
== qsag_p2_chain_engine [ecp5]
  LUT4                         4957
  TRELLIS_FF                   3535
  CCU2C                        562
  L6MUX21/PFUMX                891
  MULT18X18D                   0
  DP16KD                       57
  TRELLIS_DPR16X4              406
  reg-to-reg depth (LUT+carry cells) 49
== qsag_p2_linear [ecp5]
  LUT4                         7136
  TRELLIS_FF                   1680
  CCU2C                        2759
  L6MUX21/PFUMX                506
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 48
== qsag_p2_sbox7 [ecp5]
  LUT4                         3092
  TRELLIS_FF                   5256
  CCU2C                        1168
  L6MUX21/PFUMX                696
  MULT18X18D                   64
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 64
== qsag_poseidon2_12_fpga [ecp5]
  LUT4                         47954
  TRELLIS_FF                   86065
  CCU2C                        16916
  L6MUX21/PFUMX                9146
  MULT18X18D                   768
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 64
== qsag_poseidon2_12_pipe [ecp5]
  LUT4                         552907
  TRELLIS_FF                   952519
  CCU2C                        183068
  L6MUX21/PFUMX                101618
  MULT18X18D                   7552
  DP16KD                       17
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 64
```
## nextpnr-ecp5 (LFE5UM5G-85F, CABGA381, speed 8)
```
== fmax_gl64_dsp_mul [nextpnr-ecp5 LFE5UM5G-85F-8]
  Fmax TRELLIS_IO_IN        175.93 MHz
  MULT18X18D               16/156
  TRELLIS_COMB             1352/83640
  TRELLIS_FF               1220/83640
== fmax_gf128_clmul [nextpnr-ecp5 LFE5UM5G-85F-8]
  Fmax TRELLIS_IO_IN        118.15 MHz
  TRELLIS_COMB             6945/83640
  TRELLIS_FF               641/83640
== fmax_keccak_rpc1 [nextpnr-ecp5] FAILED or timed out (rc=124)
== fmax_keccak_rpc1 [nextpnr-ecp5] FAILED or timed out (rc=124)
== fmax_p2_sbox7 [nextpnr-ecp5 LFE5UM5G-85F-8]
  Fmax TRELLIS_IO_IN        131.29 MHz
  MULT18X18D               52/156
  TRELLIS_COMB             4517/83640
  TRELLIS_FF               4240/83640
== fmax_keccak_rpc2 [nextpnr-ecp5] FAILED or timed out (rc=124)
== fmax_p2_linear [nextpnr-ecp5] FAILED or timed out (rc=124)
```
