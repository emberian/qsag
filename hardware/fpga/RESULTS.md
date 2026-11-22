# QSAG-NI FPGA: raw results

Collected 2026-11-22T18:34Z on dregg-build2 from `build/`. Tools: Yosys 0.71+34, Verilator 5.055, Z3 version 4.15.5, "nextpnr-ecp5" -- Next Generation Place and Route (Version nextpnr-0.11.1-92-g5e2718b6).

## Lint
```
lint qsag_ni_fpga_top: 0 warnings
lint qsag_poseidon2_12_pipe: 0 warnings
lint qsag_gf128_tower_mul: 0 warnings
lint qsag_ext5_mac: 0 warnings
- V e r i l a t i o n   R e p o r t: Verilator 5.055 devel rev v5.054-290-ge0ff8e65b (mod)
- Verilator: Built from 2.654 MB sources in 37 modules, into 1.575 MB in 4 C++ files needing 0.000 MB
- Verilator: Walltime 0.251 s (elab=0.053, cvt=0.128, bld=0.000); cpu 0.251 s on 1 threads; allocated 40.227 MB
- V e r i l a t i o n   R e p o r t: Verilator 5.055 devel rev v5.054-290-ge0ff8e65b (mod)
- Verilator: Built from 2.654 MB sources in 37 modules, into 2.353 MB in 7 C++ files needing 0.000 MB
- Verilator: Walltime 0.370 s (elab=0.060, cvt=0.206, bld=0.000); cpu 0.370 s on 1 threads; allocated 49.777 MB
- V e r i l a t i o n   R e p o r t: Verilator 5.055 devel rev v5.054-290-ge0ff8e65b (mod)
- Verilator: Built from 2.654 MB sources in 37 modules, into 59.071 MB in 43 C++ files needing 0.000 MB
- Verilator: Walltime 20.094 s (elab=0.519, cvt=18.869, bld=0.000); cpu 20.093 s on 1 threads; allocated 1013.484 MB
```
## Simulation: units
```
[PASS] reference model vs Lean oracle vectors / RFC 9861 / zk-Hem v2 Fp5: 133 checks, 0 mismatches
[PASS] gl64 mul (9-DSP) / reduce136 / x^7 / Ext4 MAC / Ext5 MAC / GF(2^128): KATs, edges, 200k random: 2680017 checks, 0 mismatches
  ring core: latency 496 clocks/permutation (min=max), 16 jobs in flight, 150 permutations in 4966 clocks (33.11 clocks/perm)
[PASS] Poseidon2 ring core: 4 Lean KATs + 146 random perms / feed-forward hashes, C-slow interleaved: 1718 checks, 0 mismatches
  pipelined core: latency 453 clocks, 1200 permutations out in 1200 consecutive clocks
[PASS] Poseidon2 pipelined core: 4 Lean KATs + 1196 random, back to back: 13617 checks, 0 mismatches
  keccak clocks per permutation: 1 round/clk 24 (f1600) / 12 (p1600,12); 2 rounds/clk 12 / 6; compact N^4=I 746 / 386
[PASS] Keccak cores (parallel 1/2-rpc + compact 1-RAM N^4=I): SHA3/SHAKE/cSHAKE, RFC 9861, 400-bit D=0x07: 4736 checks, 0 mismatches
UNITS: 2700221 checks, 0 mismatches, 213721 clocks simulated
```
## Simulation: top (XCUP_RING)
```
[PASS] reference model vs Lean oracle vectors / RFC 9861 / zk-Hem v2 Fp5: 133 checks, 0 mismatches
[PASS] AXI skew, byte enables, stalled B/R, reset flush: 386 checks, 0 mismatches
[PASS] top: ID, P2_PERM/P2_JIVE, EXT4_MAC, SC_ROUND (accept + reject), GF_MAC (accept + reject): 114 checks, 0 mismatches
[PASS] top: SHAKE256 Lean KATs, TurboSHAKE256 (RFC 9861, D=0x07) via KEC ops: 9 checks, 0 mismatches
[PASS] top: BRAM fold engine, 1/2/5/9-variable tables vs fold_first_var model: 20 checks, 0 mismatches
  32 chains x (3 sponge + 7 node) = 320 permutations in 10325 clocks wall (32.3 clocks/perm; a lone permutation takes 496)
[PASS] top: chain engine, 32 concurrent leaf-sponge + Canopy paths (depth 7), one corrupted: 40 checks, 0 mismatches
REAL PROOF REPLAY [XCUP_RING :: real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B)]
  operations : 2925 Keccak blks, 0 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 86810
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 107288
  breakdown (OP_CYCLES): kec=32909 canopy=14734 p2=0 sc=2310 emac=36790 fold=0
  bus traffic: 1405 AXI4-Lite writes, 18659 reads, 43969 512-bit stream beats
[PASS] real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B): 3733 checks, 0 mismatches
REAL PROOF REPLAY [XCUP_RING :: real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B)]
  operations : 1 Keccak blks, 5792 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 1281993
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 1501211
  breakdown (OP_CYCLES): kec=19 canopy=39088 p2=1122457 sc=2310 emac=37692 fold=0
  bus traffic: 50008 AXI4-Lite writes, 655739 reads, 38417 512-bit stream beats
[PASS] real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B): 30364 checks, 0 mismatches
REAL PROOF REPLAY [XCUP_RING :: real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy)]
  operations : 1052 Keccak blks, 0 P2 perms, 2 Canopy MultiProofs, 2 sumcheck rnds, 3664 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 30877
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 36235
  breakdown (OP_CYCLES): kec=18094 canopy=4130 p2=0 sc=64 emac=8450 fold=136
  bus traffic: 299 AXI4-Lite writes, 5619 reads, 10814 512-bit stream beats
[PASS] real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy): 1060 checks, 0 mismatches
[PASS] real QSAGSTA1 single-bit tamper rejection (proof, TS/P2 Merkle, sumcheck, Ext4): 7 checks, 0 mismatches
[PASS] top: zk-Hem v2 F_{p^5} EXT5_MAC, EXT5_FROB homomorphism, 400-bit Role-1 KEC_STREAM_SPONGE: 386 checks, 0 mismatches
QSAGSTA1-shaped root verification (modelled operation mix, real data, every result checked)
  shape: nv=20, stages (inv-rate log, fold k, queries) = (2,5,216) (4,3,109) (6,4,74), 72 sumcheck rounds, final 2^8
  Poseidon2 permutations : 11407  (72 transcript, sequential; 11335 leaf-sponge + Canopy node, C-slow on the ring)
  Ext4 MACs              : 9040  (216 sumcheck Horner, 8824 fold butterflies)
  clocks, wall (AXI host with zero think time)  : 475111
    transcript + sumcheck rounds                : 57199  (core-busy 35928 + 1872)
    query leaf hashes + Merkle paths            : 368052
    query folds                                 : 49034
    final evaluation                            : 826
  clocks with any engine active (TOTAL_CYCLES)  : 434587
  fold engine core-busy clocks                  : 29756
  bus traffic: 7060 AXI4-Lite writes, 216689 reads, 20559 stream beats
[PASS] QSAGSTA1-shaped root verification trace: 3252 checks, 0 mismatches
16-variable Ext4 edge fold (65,535 butterflies, in place in block RAM)
  table load over AXI4-Stream : 65538 clocks (one entry per clock)
  16 fold rounds, core-busy   : 65729 clocks (two FOLD_MULTI commands of 8 rounds)
  16 fold rounds, wall        : 66143 clocks (incl. 16 challenges over AXI4-Lite)
[PASS] 16-variable hyperweb edge fold vs fold_first_var model: 4 checks, 0 mismatches
TOP: 39509 checks, 0 mismatches, 2286663 clocks simulated
```
## Simulation: top (ECP5_FULLRATE — 117/156 DSPs on $45 ECP5-85F)
```
[PASS] reference model vs Lean oracle vectors / RFC 9861 / zk-Hem v2 Fp5: 133 checks, 0 mismatches
[PASS] AXI skew, byte enables, stalled B/R, reset flush: 386 checks, 0 mismatches
[PASS] top: ID, P2_PERM/P2_JIVE, EXT4_MAC, SC_ROUND (accept + reject), GF_MAC (accept + reject): 110 checks, 0 mismatches
[PASS] top: SHAKE256 Lean KATs, TurboSHAKE256 (RFC 9861, D=0x07) via KEC ops: 7 checks, 0 mismatches
[PASS] top: BRAM fold engine, 1/2/5/9-variable tables vs fold_first_var model: 16 checks, 0 mismatches
  32 chains x (3 sponge + 7 node) = 320 permutations in 420829 clocks wall (1315.1 clocks/perm; a lone permutation takes 496)
[PASS] top: chain engine, 32 concurrent leaf-sponge + Canopy paths (depth 7), one corrupted: 40 checks, 0 mismatches
REAL PROOF REPLAY [ECP5_FULLRATE :: real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B)]
  operations : 2925 Keccak blks, 0 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 2004196
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 2024484
  breakdown (OP_CYCLES): kec=1344763 canopy=620002 p2=0 sc=2574 emac=36790 fold=0
  bus traffic: 1405 AXI4-Lite writes, 401815 reads, 43969 512-bit stream beats
[PASS] real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B): 3733 checks, 0 mismatches
REAL PROOF REPLAY [ECP5_FULLRATE :: real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B)]
  operations : 1 Keccak blks, 5792 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 7675194
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 7894327
  breakdown (OP_CYCLES): kec=829 canopy=1839758 p2=5715199 sc=2574 emac=37692 fold=0
  bus traffic: 50008 AXI4-Lite writes, 3852165 reads, 38417 512-bit stream beats
[PASS] real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B): 30364 checks, 0 mismatches
REAL PROOF REPLAY [ECP5_FULLRATE :: real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy)]
  operations : 1052 Keccak blks, 0 P2 perms, 2 Canopy MultiProofs, 2 sumcheck rnds, 3664 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 1077613
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 1082969
  breakdown (OP_CYCLES): kec=868214 canopy=200738 p2=0 sc=72 emac=8450 fold=136
  bus traffic: 299 AXI4-Lite writes, 146422 reads, 10814 512-bit stream beats
[PASS] real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy): 1060 checks, 0 mismatches
[PASS] real QSAGSTA1 single-bit tamper rejection (proof, TS/P2 Merkle, sumcheck, Ext4): 7 checks, 0 mismatches
[PASS] top: zk-Hem v2 F_{p^5} EXT5_MAC, EXT5_FROB homomorphism, 400-bit Role-1 KEC_STREAM_SPONGE: 386 checks, 0 mismatches
TOP: 36243 checks, 0 mismatches, 11570342 clocks simulated
```
## Simulation: top (ECP5_COMPACT — 18/156 DSPs)
```
[PASS] reference model vs Lean oracle vectors / RFC 9861 / zk-Hem v2 Fp5: 133 checks, 0 mismatches
[PASS] AXI skew, byte enables, stalled B/R, reset flush: 386 checks, 0 mismatches
[PASS] top: ID, P2_PERM/P2_JIVE, EXT4_MAC, SC_ROUND (accept + reject), GF_MAC (accept + reject): 107 checks, 0 mismatches
[PASS] top: SHAKE256 Lean KATs, TurboSHAKE256 (RFC 9861, D=0x07) via KEC ops: 7 checks, 0 mismatches
[PASS] top: BRAM fold engine, 1/2/5/9-variable tables vs fold_first_var model: 16 checks, 0 mismatches
  32 chains x (3 sponge + 7 node) = 320 permutations in 601309 clocks wall (1879.1 clocks/perm; a lone permutation takes 496)
[PASS] top: chain engine, 32 concurrent leaf-sponge + Canopy paths (depth 7), one corrupted: 40 checks, 0 mismatches
REAL PROOF REPLAY [ECP5_COMPACT :: real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B)]
  operations : 2925 Keccak blks, 0 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 2321246
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 2341778
  breakdown (OP_CYCLES): kec=1344763 canopy=620002 p2=0 sc=4994 emac=351420 fold=0
  bus traffic: 1405 AXI4-Lite writes, 404005 reads, 43969 512-bit stream beats
[PASS] real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B): 3733 checks, 0 mismatches
REAL PROOF REPLAY [ECP5_COMPACT :: real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B)]
  operations : 1 Keccak blks, 5792 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 11258276
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 11477735
  breakdown (OP_CYCLES): kec=829 canopy=2650790 p2=8170855 sc=4994 emac=351666 fold=0
  bus traffic: 50008 AXI4-Lite writes, 5488191 reads, 38417 512-bit stream beats
[PASS] real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B): 30364 checks, 0 mismatches
REAL PROOF REPLAY [ECP5_COMPACT :: real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy)]
  operations : 1052 Keccak blks, 0 P2 perms, 2 Canopy MultiProofs, 2 sumcheck rnds, 3664 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 1147685
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 1153141
  breakdown (OP_CYCLES): kec=868214 canopy=200738 p2=0 sc=138 emac=77250 fold=1342
  bus traffic: 299 AXI4-Lite writes, 147647 reads, 10814 512-bit stream beats
[PASS] real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy): 1060 checks, 0 mismatches
[PASS] real QSAGSTA1 single-bit tamper rejection (proof, TS/P2 Merkle, sumcheck, Ext4): 7 checks, 0 mismatches
[PASS] top: zk-Hem v2 F_{p^5} EXT5_MAC, EXT5_FROB homomorphism, 400-bit Role-1 KEC_STREAM_SPONGE: 386 checks, 0 mismatches
TOP: 36240 checks, 0 mismatches, 15741662 clocks simulated
```
## Trace report
```
REAL PROOF REPLAY [XCUP_RING :: real QSAGSTA1 Role-1 (TurboSHAKE256 Canopy, 170,317 B)]
  operations : 2925 Keccak blks, 0 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 86810
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 107288
  breakdown (OP_CYCLES): kec=32909 canopy=14734 p2=0 sc=2310 emac=36790 fold=0
  bus traffic: 1405 AXI4-Lite writes, 18659 reads, 43969 512-bit stream beats
REAL PROOF REPLAY [XCUP_RING :: real QSAGSTA1 Role-2 (Poseidon2 Canopy, 169,741 B)]
  operations : 1 Keccak blks, 5792 P2 perms, 6 Canopy MultiProofs, 66 sumcheck rnds, 16690 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 1281993
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 1501211
  breakdown (OP_CYCLES): kec=19 canopy=39088 p2=1122457 sc=2310 emac=37692 fold=0
  bus traffic: 50008 AXI4-Lite writes, 655739 reads, 38417 512-bit stream beats
REAL PROOF REPLAY [XCUP_RING :: real [CWYZ26] DuetFold (4 statements, cSHAKE256 Canopy)]
  operations : 1052 Keccak blks, 0 P2 perms, 2 Canopy MultiProofs, 2 sumcheck rnds, 3664 Ext4 MACs
  TOTAL_CYCLES (exact hardware engine-active clocks) : 30877
  wall clocks (incl. AXI4-Lite + Y readback checks)  : 36235
  breakdown (OP_CYCLES): kec=18094 canopy=4130 p2=0 sc=64 emac=8450 fold=136
  bus traffic: 299 AXI4-Lite writes, 5619 reads, 10814 512-bit stream beats
QSAGSTA1-shaped root verification (modelled operation mix, real data, every result checked)
  shape: nv=20, stages (inv-rate log, fold k, queries) = (2,5,216) (4,3,109) (6,4,74), 72 sumcheck rounds, final 2^8
  Poseidon2 permutations : 11407  (72 transcript, sequential; 11335 leaf-sponge + Canopy node, C-slow on the ring)
  Ext4 MACs              : 9040  (216 sumcheck Horner, 8824 fold butterflies)
  clocks, wall (AXI host with zero think time)  : 475111
    transcript + sumcheck rounds                : 57199  (core-busy 35928 + 1872)
    query leaf hashes + Merkle paths            : 368052
    query folds                                 : 49034
    final evaluation                            : 826
  clocks with any engine active (TOTAL_CYCLES)  : 434587
  fold engine core-busy clocks                  : 29756
  bus traffic: 7060 AXI4-Lite writes, 216689 reads, 20559 stream beats
16-variable Ext4 edge fold (65,535 butterflies, in place in block RAM)
  table load over AXI4-Stream : 65538 clocks (one entry per clock)
  16 fold rounds, core-busy   : 65729 clocks (two FOLD_MULTI commands of 8 rounds)
  16 fold rounds, wall        : 66143 clocks (incl. 16 challenges over AXI4-Lite)
```
## Formal checks (Z3 + Bitwuzla)

| result | check | expected | solver | time | statement |
|---|---|---|---|---|---|
| PASS | `contract_csa2_66_n3_base` | unsat | unsat | 0.2s | qsag_csa_reduce2 W=66 N=3 base: s + c == sum x_i (mod 2^66) for all 2^198 inputs |
| PASS | `contract_csa2_66_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=66 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_66_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=66 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^264 inputs |
| PASS | `contract_csa2_66_n6_step_rtl` | unsat | unsat | 0.7s | qsag_csa_reduce2 W=66 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_66_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=66 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^396 inputs |
| PASS | `contract_csa2_67_n3_base` | unsat | unsat | 0.2s | qsag_csa_reduce2 W=67 N=3 base: s + c == sum x_i (mod 2^67) for all 2^201 inputs |
| PASS | `contract_csa2_67_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=67 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_67_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=67 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^268 inputs |
| PASS | `contract_csa2_67_n5_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=67 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_67_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=67 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^335 inputs |
| PASS | `contract_csa2_68_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=68 N=3 base: s + c == sum x_i (mod 2^68) for all 2^204 inputs |
| PASS | `contract_csa2_68_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=68 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_68_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=68 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^272 inputs |
| PASS | `contract_csa2_72_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=72 N=3 base: s + c == sum x_i (mod 2^72) for all 2^216 inputs |
| PASS | `contract_csa2_72_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=72 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_72_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^288 inputs |
| PASS | `contract_csa2_72_n6_step_rtl` | unsat | unsat | 0.9s | qsag_csa_reduce2 W=72 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_72_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^432 inputs |
| PASS | `contract_csa2_72_n8_step_rtl` | unsat | unsat | 0.9s | qsag_csa_reduce2 W=72 N=8 RTL triplet + child-sum invariants (M=6) |
| PASS | `contract_csa2_72_n8_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=8 inductive step (from proved M=6): s + c == sum x_i for all 2^576 inputs |
| PASS | `contract_csa2_72_n11_step_rtl` | unsat | unsat | 1.3s | qsag_csa_reduce2 W=72 N=11 RTL triplet + child-sum invariants (M=8) |
| PASS | `contract_csa2_72_n11_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=11 inductive step (from proved M=8): s + c == sum x_i for all 2^792 inputs |
| PASS | `contract_csa2_96_n3_base` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=96 N=3 base: s + c == sum x_i (mod 2^96) for all 2^288 inputs |
| PASS | `contract_csa2_96_n4_step_rtl` | unsat | unsat | 0.8s | qsag_csa_reduce2 W=96 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_96_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=96 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^384 inputs |
| PASS | `contract_csa2_96_n5_step_rtl` | unsat | unsat | 0.8s | qsag_csa_reduce2 W=96 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_96_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=96 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^480 inputs |
| PASS | `contract_csa2_128_n3_base` | unsat | unsat | 0.7s | qsag_csa_reduce2 W=128 N=3 base: s + c == sum x_i (mod 2^128) for all 2^384 inputs |
| PASS | `contract_csa2_128_n4_step_rtl` | unsat | unsat | 1.1s | qsag_csa_reduce2 W=128 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_128_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^512 inputs |
| PASS | `contract_csa2_128_n6_step_rtl` | unsat | unsat | 2.1s | qsag_csa_reduce2 W=128 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_128_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^768 inputs |
| PASS | `contract_csa2_128_n8_step_rtl` | unsat | unsat | 1.6s | qsag_csa_reduce2 W=128 N=8 RTL triplet + child-sum invariants (M=6) |
| PASS | `contract_csa2_128_n8_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=8 inductive step (from proved M=6): s + c == sum x_i for all 2^1024 inputs |
| PASS | `contract_csa2_128_n12_step_rtl` | unsat | unsat | 6.2s | qsag_csa_reduce2 W=128 N=12 RTL triplet + child-sum invariants (M=8) |
| PASS | `contract_csa2_128_n12_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=12 inductive step (from proved M=8): s + c == sum x_i for all 2^1536 inputs |
| PASS | `contract_csa2_136_n3_base` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=136 N=3 base: s + c == sum x_i (mod 2^136) for all 2^408 inputs |
| PASS | `contract_csa2_136_n4_step_rtl` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=136 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_136_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^544 inputs |
| PASS | `contract_csa2_136_n5_step_rtl` | unsat | unsat | 1.1s | qsag_csa_reduce2 W=136 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_136_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^680 inputs |
| PASS | `contract_csa2_136_n7_step_rtl` | unsat | unsat | 1.6s | qsag_csa_reduce2 W=136 N=7 RTL triplet + child-sum invariants (M=5) |
| PASS | `contract_csa2_136_n7_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=7 inductive step (from proved M=5): s + c == sum x_i for all 2^952 inputs |
| PASS | `contract_csa2_136_n10_step_rtl` | unsat | unsat | 2.9s | qsag_csa_reduce2 W=136 N=10 RTL triplet + child-sum invariants (M=7) |
| PASS | `contract_csa2_136_n10_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=10 inductive step (from proved M=7): s + c == sum x_i for all 2^1360 inputs |
| PASS | `contract_csa2_136_n15_step_rtl` | unsat | unsat | 6.6s | qsag_csa_reduce2 W=136 N=15 RTL triplet + child-sum invariants (M=10) |
| PASS | `contract_csa2_136_n15_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=15 inductive step (from proved M=10): s + c == sum x_i for all 2^2040 inputs |
| PASS | `contract_split_33_c17` | unsat | unsat | 0.0s | qsag_add_split W=33 CHUNK=17: y == a + b (mod 2^33) for all 2^66 inputs |
| PASS | `contract_split_33_c33` | unsat | unsat | 0.0s | qsag_add_split W=33 CHUNK=33: y == a + b (mod 2^33) for all 2^66 inputs |
| PASS | `contract_split_65_c16` | unsat | unsat | 0.1s | qsag_add_split W=65 CHUNK=16: y == a + b (mod 2^65) for all 2^130 inputs |
| PASS | `contract_split_65_c34` | unsat | unsat | 0.0s | qsag_add_split W=65 CHUNK=34: y == a + b (mod 2^65) for all 2^130 inputs |
| PASS | `contract_split_66_c16` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=16: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c24` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=24: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c34` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=34: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c66` | unsat | unsat | 0.0s | qsag_add_split W=66 CHUNK=66: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_67_c16` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=16: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_67_c24` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=24: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_67_c34` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=34: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_68_c68` | unsat | unsat | 0.0s | qsag_add_split W=68 CHUNK=68: y == a + b (mod 2^68) for all 2^136 inputs |
| PASS | `contract_split_72_c72` | unsat | unsat | 0.0s | qsag_add_split W=72 CHUNK=72: y == a + b (mod 2^72) for all 2^144 inputs |
| PASS | `contract_split_96_c32` | unsat | unsat | 0.1s | qsag_add_split W=96 CHUNK=32: y == a + b (mod 2^96) for all 2^192 inputs |
| PASS | `contract_split_96_c48` | unsat | unsat | 0.1s | qsag_add_split W=96 CHUNK=48: y == a + b (mod 2^96) for all 2^192 inputs |
| PASS | `contract_split_128_c16` | unsat | unsat | 0.3s | qsag_add_split W=128 CHUNK=16: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_128_c24` | unsat | unsat | 0.2s | qsag_add_split W=128 CHUNK=24: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_128_c32` | unsat | unsat | 0.2s | qsag_add_split W=128 CHUNK=32: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_136_c16` | unsat | unsat | 0.3s | qsag_add_split W=136 CHUNK=16: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_split_136_c24` | unsat | unsat | 0.3s | qsag_add_split W=136 CHUNK=24: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_split_136_c46` | unsat | unsat | 0.2s | qsag_add_split W=136 CHUNK=46: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_sum_csa_66_3_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=3 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_3_c66` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=3 CHUNK=66: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_4_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=4 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_5_c66` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=5 CHUNK=66: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_6_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=6 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_6_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=6 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_67_5_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=67 N=5 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_68_3_c68` | unsat | unsat | 0.0s | qsag_sum_csa W=68 N=3 CHUNK=68: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_68_4_c68` | unsat | unsat | 0.0s | qsag_sum_csa W=68 N=4 CHUNK=68: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_5_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=5 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_7_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=7 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_8_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=8 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_11_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=11 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_96_5_c48` | unsat | unsat | 0.0s | qsag_sum_csa W=96 N=5 CHUNK=48: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c32` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=32: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_9_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=9 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_10_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=10 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_11_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=11 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_12_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=12 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_13_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=13 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_14_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=14 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_15_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=15 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_15_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=15 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `reduce_identity` | unsat | unsat | 0.0s | integers: x + p = V + p*Q0 for x = lo + m 2^64 + h 2^96 + t 2^128 |
| PASS | `reduce_range` | unsat | unsat | 0.0s | integers: limbs in range imply 0 < V < 3p |
| PASS | `ext4_karatsuba_range_limb0` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 0: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext4_karatsuba_range_limb1` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 1: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext4_karatsuba_range_limb2` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 2: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext4_karatsuba_range_limb3` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 3: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext4_karatsuba_modp_limb0` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 0: exact congruence acc - schoolbook == p * Q_k over F_p[v]/(v^4 - 7) |
| PASS | `ext4_karatsuba_modp_limb1` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 1: exact congruence acc - schoolbook == p * Q_k over F_p[v]/(v^4 - 7) |
| PASS | `ext4_karatsuba_modp_limb2` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 2: exact congruence acc - schoolbook == p * Q_k over F_p[v]/(v^4 - 7) |
| PASS | `ext4_karatsuba_modp_limb3` | unsat | unsat | 0.0s | 9-mul Tower Karatsuba limb 3: exact congruence acc - schoolbook == p * Q_k over F_p[v]/(v^4 - 7) |
| PASS | `gl64_reduce_reg1` | unsat | unsat | 9.8s | qsag_gl64_reduce REG_OUT=1: for all 2^136 inputs, r (2 clocks later) < p and V(x) = r + k*p |
| PASS | `gl64_reduce_reg0` | unsat | unsat | 5.3s | qsag_gl64_reduce REG_OUT=0: for all 2^136 inputs, r (1 clocks later) < p and V(x) = r + k*p |
| PASS | `dsp_tile_exact_16x16u` | unsat | unsat | 0.0s | bit-precise 2-stage unsigned DSP cell (16x16u, fits MULT18X18D & DSP48E2): tq == a*b for all 2^32 inputs |
| PASS | `dsp_tile_exact_17x16u` | unsat | unsat | 0.0s | bit-precise 2-stage unsigned DSP cell (17x16u, fits MULT18X18D & DSP48E2): tq == a*b for all 2^33 inputs |
| PASS | `dsp_tile_exact_18x17u` | unsat | unsat | 0.0s | bit-precise 2-stage unsigned DSP cell (18x17u, fits MULT18X18D & DSP48E2): tq == a*b for all 2^35 inputs |
| PASS | `mul33x32_dsp_rtl_csa_exact` | unsat | unsat | 9.3s | unabstracted 3-DSP qsag_mul33x32_dsp RTL (actual CSA gates): zext68(s)+zext68(c) == K33(t0,t1,ts) with zero bit-66 wrap |
| PASS | `mul33x32_dsp_algebra_exact` | unsat | unsat | 0.4s | QF_NIA: for all a in [0,2^33) and b in [0,2^32), K33(t0,t1,ts) == a*b + B33 < 2^66 |
| PASS | `mul64_dsp_wiring_rtl_26x17` | unsat | unsat | 0.5s | 9-DSP qsag_mul64_dsp AW=26 BW=17 RTL pairwise CSA row & sum invariants over all 2^128 inputs |
| PASS | `mul64_dsp_wiring_rtl_16x16` | unsat | unsat | 93.9s | 9-DSP qsag_mul64_dsp AW=16 BW=16 RTL 3-cycle outer Karatsuba equivalence p@s3 == K64 over all 2^128 inputs |
| PASS | `mul64_dsp_wiring_assoc` | unsat | unsat | 0.0s | 9-DSP qsag_mul64_dsp row-grouping associativity over Z/2^128Z |
| PASS | `mul64_dsp_shl_eq_mul` | unsat | unsat | 0.0s | 128-bit ring homomorphism: (x << 32) == x * 2^32 and (x << 64) == x * 2^64 (mod 2^128) |
| PASS | `mul64_dsp_wiring_join` | unsat | unsat | 0.0s | 9-DSP qsag_mul64_dsp Modus Ponens join: pairwise CSA row invariants entail p@s3 == K64(P0,P2,PS,sa,cb) |
| PASS | `mul64_dsp_karatsuba_exact` | unsat | unsat | 0.0s | QF_NIA: outer 32-bit Karatsuba + cb carry-split K64 == a*b in [0, 2^128) for all 2^128 (a, b) |
| PASS | `gl64_dsp_mul_26x17_reg1_product` | unsat | unsat | 0.1s | qsag_gl64_dsp_mul AW=26 BW=17 REG_OUT=1: prod@s3 == exact 128-bit product of a@s0, b@s0 |
| PASS | `gl64_dsp_mul_26x17_reg1_end_to_end` | unsat | unsat | 5.1s | qsag_gl64_dsp_mul AW=26 BW=17 REG_OUT=1: full 5-clk pipeline emits canonical (a*b) mod p |
| PASS | `gl64_dsp_mul_26x17_reg0_product` | unsat | unsat | 0.1s | qsag_gl64_dsp_mul AW=26 BW=17 REG_OUT=0: prod@s3 == exact 128-bit product of a@s0, b@s0 |
| PASS | `gl64_dsp_mul_26x17_reg0_end_to_end` | unsat | unsat | 4.2s | qsag_gl64_dsp_mul AW=26 BW=17 REG_OUT=0: full 4-clk pipeline emits canonical (a*b) mod p |
| PASS | `gl64_dsp_mul_16x16_reg1_product` | unsat | unsat | 0.1s | qsag_gl64_dsp_mul AW=16 BW=16 REG_OUT=1: prod@s3 == exact 128-bit product of a@s0, b@s0 |
| PASS | `gl64_dsp_mul_16x16_reg1_end_to_end` | unsat | unsat | 5.0s | qsag_gl64_dsp_mul AW=16 BW=16 REG_OUT=1: full 5-clk pipeline emits canonical (a*b) mod p |
| PASS | `gl64_dsp_mul_16x16_reg0_product` | unsat | unsat | 0.0s | qsag_gl64_dsp_mul AW=16 BW=16 REG_OUT=0: prod@s3 == exact 128-bit product of a@s0, b@s0 |
| PASS | `gl64_dsp_mul_16x16_reg0_end_to_end` | unsat | unsat | 3.3s | qsag_gl64_dsp_mul AW=16 BW=16 REG_OUT=0: full 4-clk pipeline emits canonical (a*b) mod p |
| PASS | `glue_canonical_remainder` | unsat | unsat | 0.0s | all 2^128 operand pairs: exact 128-bit product and bounded reduction entail r = (a*b) mod p uniquely |
| PASS | `p2_sbox7_rtl_26x17` | unsat | unsat | 0.0s | qsag_p2_sbox7 AW=26 BW=17: 13-cycle RTL pipeline emits glmul(glmul(glmul(x,x),x), glmul(glmul(x,x),glmul(x,x))) |
| PASS | `p2_sbox7_rtl_16x16` | unsat | unsat | 0.0s | qsag_p2_sbox7 AW=16 BW=16: 13-cycle RTL pipeline emits glmul(glmul(glmul(x,x),x), glmul(glmul(x,x),glmul(x,x))) |
| PASS | `p2_sbox7_algebra_modp` | unsat | unsat | 0.2s | ring congruence over Z: 4-mul S-box tree r3*r4 - x^7 == p * Q_tot for all x |
| PASS | `ext4_mac_stage0_26x17` | unsat | unsat | 38.6s | qsag_ext4_mac AW=26 BW=17: all 18 Stage-0 pre-sum registers ma_q[0..8], mb_q[0..8] canonical mod p |
| PASS | `ext4_mac_pipe_26x17` | unsat | unsat | 0.1s | qsag_ext4_mac AW=26 BW=17: 7-cycle RTL Stage-4 accumulators & Stage-6 reducer join over all inputs |
| PASS | `ext4_mac_stage0_16x16` | unsat | unsat | 0.1s | qsag_ext4_mac AW=16 BW=16: all 18 Stage-0 pre-sum registers ma_q[0..8], mb_q[0..8] canonical mod p |
| PASS | `ext4_mac_ecp5_stage4_vfold` | unsat | unsat | 35.3s | qsag_ext4_mac AW=16 BW=16: Stage-4 128->66b Solinas fold v_q[0..8] == V(m[i]) in (0, 3p) |
| PASS | `ext4_mac_ecp5_stage5_acc72` | unsat | unsat | 1.2s | qsag_ext4_mac AW=16 BW=16: Stage-5 72-bit B66 Karatsuba accumulators acc72_q[0..3] exact |
| PASS | `ext4_mac_ecp5_stage6_red72` | unsat | unsat | 11.5s | qsag_ext4_mac AW=16 BW=16: Stage-6 red72 emits canonical y[0..3] < p congruent to acc72_q mod p |
| PASS | `ext4_mac_ecp5_b66_algebra` | unsat | unsat | 0.0s | QF_LIA: 72-bit B66 Karatsuba formulas stay in (0, 120*2^64) and equal Karatsuba + 5p*K over Z |
| PASS | `contract_csa2_66_n3_base` | unsat | unsat | 0.2s | qsag_csa_reduce2 W=66 N=3 base: s + c == sum x_i (mod 2^66) for all 2^198 inputs |
| PASS | `contract_csa2_66_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=66 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_66_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=66 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^264 inputs |
| PASS | `contract_csa2_66_n6_step_rtl` | unsat | unsat | 0.6s | qsag_csa_reduce2 W=66 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_66_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=66 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^396 inputs |
| PASS | `contract_csa2_67_n3_base` | unsat | unsat | 0.2s | qsag_csa_reduce2 W=67 N=3 base: s + c == sum x_i (mod 2^67) for all 2^201 inputs |
| PASS | `contract_csa2_67_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=67 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_67_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=67 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^268 inputs |
| PASS | `contract_csa2_67_n5_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=67 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_67_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=67 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^335 inputs |
| PASS | `contract_csa2_68_n3_base` | unsat | unsat | 0.2s | qsag_csa_reduce2 W=68 N=3 base: s + c == sum x_i (mod 2^68) for all 2^204 inputs |
| PASS | `contract_csa2_68_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=68 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_68_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=68 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^272 inputs |
| PASS | `contract_csa2_72_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=72 N=3 base: s + c == sum x_i (mod 2^72) for all 2^216 inputs |
| PASS | `contract_csa2_72_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=72 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_72_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^288 inputs |
| PASS | `contract_csa2_72_n6_step_rtl` | unsat | unsat | 0.9s | qsag_csa_reduce2 W=72 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_72_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^432 inputs |
| PASS | `contract_csa2_72_n8_step_rtl` | unsat | unsat | 0.6s | qsag_csa_reduce2 W=72 N=8 RTL triplet + child-sum invariants (M=6) |
| PASS | `contract_csa2_72_n8_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=8 inductive step (from proved M=6): s + c == sum x_i for all 2^576 inputs |
| PASS | `contract_csa2_72_n11_step_rtl` | unsat | unsat | 0.9s | qsag_csa_reduce2 W=72 N=11 RTL triplet + child-sum invariants (M=8) |
| PASS | `contract_csa2_72_n11_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=11 inductive step (from proved M=8): s + c == sum x_i for all 2^792 inputs |
| PASS | `contract_csa2_96_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=96 N=3 base: s + c == sum x_i (mod 2^96) for all 2^288 inputs |
| PASS | `contract_csa2_96_n4_step_rtl` | unsat | unsat | 0.5s | qsag_csa_reduce2 W=96 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_96_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=96 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^384 inputs |
| PASS | `contract_csa2_96_n5_step_rtl` | unsat | unsat | 0.6s | qsag_csa_reduce2 W=96 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_96_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=96 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^480 inputs |
| PASS | `contract_csa2_128_n3_base` | unsat | unsat | 0.5s | qsag_csa_reduce2 W=128 N=3 base: s + c == sum x_i (mod 2^128) for all 2^384 inputs |
| PASS | `contract_csa2_128_n4_step_rtl` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=128 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_128_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^512 inputs |
| PASS | `contract_csa2_128_n6_step_rtl` | unsat | unsat | 1.7s | qsag_csa_reduce2 W=128 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_128_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^768 inputs |
| PASS | `contract_csa2_128_n8_step_rtl` | unsat | unsat | 1.6s | qsag_csa_reduce2 W=128 N=8 RTL triplet + child-sum invariants (M=6) |
| PASS | `contract_csa2_128_n8_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=8 inductive step (from proved M=6): s + c == sum x_i for all 2^1024 inputs |
| PASS | `contract_csa2_128_n12_step_rtl` | unsat | unsat | 6.1s | qsag_csa_reduce2 W=128 N=12 RTL triplet + child-sum invariants (M=8) |
| PASS | `contract_csa2_128_n12_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=12 inductive step (from proved M=8): s + c == sum x_i for all 2^1536 inputs |
| PASS | `contract_csa2_136_n3_base` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=136 N=3 base: s + c == sum x_i (mod 2^136) for all 2^408 inputs |
| PASS | `contract_csa2_136_n4_step_rtl` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=136 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_136_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^544 inputs |
| PASS | `contract_csa2_136_n5_step_rtl` | unsat | unsat | 1.1s | qsag_csa_reduce2 W=136 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_136_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^680 inputs |
| PASS | `contract_csa2_136_n7_step_rtl` | unsat | unsat | 2.0s | qsag_csa_reduce2 W=136 N=7 RTL triplet + child-sum invariants (M=5) |
| PASS | `contract_csa2_136_n7_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=7 inductive step (from proved M=5): s + c == sum x_i for all 2^952 inputs |
| PASS | `contract_csa2_136_n10_step_rtl` | unsat | unsat | 4.3s | qsag_csa_reduce2 W=136 N=10 RTL triplet + child-sum invariants (M=7) |
| PASS | `contract_csa2_136_n10_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=10 inductive step (from proved M=7): s + c == sum x_i for all 2^1360 inputs |
| PASS | `contract_csa2_136_n15_step_rtl` | unsat | unsat | 5.0s | qsag_csa_reduce2 W=136 N=15 RTL triplet + child-sum invariants (M=10) |
| PASS | `contract_csa2_136_n15_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=15 inductive step (from proved M=10): s + c == sum x_i for all 2^2040 inputs |
| PASS | `contract_split_33_c17` | unsat | unsat | 0.0s | qsag_add_split W=33 CHUNK=17: y == a + b (mod 2^33) for all 2^66 inputs |
| PASS | `contract_split_33_c33` | unsat | unsat | 0.0s | qsag_add_split W=33 CHUNK=33: y == a + b (mod 2^33) for all 2^66 inputs |
| PASS | `contract_split_65_c16` | unsat | unsat | 0.1s | qsag_add_split W=65 CHUNK=16: y == a + b (mod 2^65) for all 2^130 inputs |
| PASS | `contract_split_65_c34` | unsat | unsat | 0.1s | qsag_add_split W=65 CHUNK=34: y == a + b (mod 2^65) for all 2^130 inputs |
| PASS | `contract_split_66_c16` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=16: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c24` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=24: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c34` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=34: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c66` | unsat | unsat | 0.0s | qsag_add_split W=66 CHUNK=66: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_67_c16` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=16: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_67_c24` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=24: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_67_c34` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=34: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_68_c68` | unsat | unsat | 0.0s | qsag_add_split W=68 CHUNK=68: y == a + b (mod 2^68) for all 2^136 inputs |
| PASS | `contract_split_72_c72` | unsat | unsat | 0.0s | qsag_add_split W=72 CHUNK=72: y == a + b (mod 2^72) for all 2^144 inputs |
| PASS | `contract_split_96_c32` | unsat | unsat | 0.1s | qsag_add_split W=96 CHUNK=32: y == a + b (mod 2^96) for all 2^192 inputs |
| PASS | `contract_split_96_c48` | unsat | unsat | 0.1s | qsag_add_split W=96 CHUNK=48: y == a + b (mod 2^96) for all 2^192 inputs |
| PASS | `contract_split_128_c16` | unsat | unsat | 0.3s | qsag_add_split W=128 CHUNK=16: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_128_c24` | unsat | unsat | 0.2s | qsag_add_split W=128 CHUNK=24: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_128_c32` | unsat | unsat | 0.2s | qsag_add_split W=128 CHUNK=32: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_136_c16` | unsat | unsat | 0.3s | qsag_add_split W=136 CHUNK=16: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_split_136_c24` | unsat | unsat | 0.3s | qsag_add_split W=136 CHUNK=24: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_split_136_c46` | unsat | unsat | 0.2s | qsag_add_split W=136 CHUNK=46: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_sum_csa_66_3_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=3 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_3_c66` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=3 CHUNK=66: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_4_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=4 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_5_c66` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=5 CHUNK=66: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_6_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=6 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_6_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=6 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_67_5_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=67 N=5 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_68_3_c68` | unsat | unsat | 0.0s | qsag_sum_csa W=68 N=3 CHUNK=68: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_68_4_c68` | unsat | unsat | 0.0s | qsag_sum_csa W=68 N=4 CHUNK=68: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_5_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=5 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_7_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=7 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_8_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=8 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_11_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=11 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_96_5_c48` | unsat | unsat | 0.0s | qsag_sum_csa W=96 N=5 CHUNK=48: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c32` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=32: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_9_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=9 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_10_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=10 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_11_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=11 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_12_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=12 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_13_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=13 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_14_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=14 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_15_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=15 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_15_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=15 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `mut_gl64_reduce_sign` | sat | sat | 0.0s | qsag_gl64_reduce REG_OUT=1: for all 2^136 inputs, r (2 clocks later) < p and V(x) = r + k*p |
| PASS | `mut_gl64_reduce_select` | sat | sat | 0.0s | qsag_gl64_reduce REG_OUT=1: for all 2^136 inputs, r (2 clocks later) < p and V(x) = r + k*p |
| PASS | `mut_mul33x32_dsp_tile` | sat | sat | 0.0s | mutant tooth: wrong b-half in 3-DSP qsag_mul33x32_dsp is refuted |
| PASS | `mut_shift_mul64_dsp` | sat | sat | 0.1s | mutant tooth: 1-bit shift fault on p2_s in 9-DSP qsag_mul64_dsp is refuted |
| PASS | `mut_csa_reduce2_shift` | sat | sat | 0.0s | mutant tooth: 3:2 CSA carry shift <<2 instead of <<1 is refuted |
| PASS | `mut_add_split_prefix` | sat | sat | 0.1s | mutant tooth: Kogge-Stone prefix carry drop in qsag_add_split is refuted |
| PASS | `mut_p2_sbox7_port` | sat | sat | 0.0s | mutant tooth: wrong multiplier operand in qsag_p2_sbox7 is refuted |
| PASS | `mut_ext4_ecp5_b66_y1` | sat | sat | 0.3s | mutant tooth: 2*B66+1 bias fault in qsag_ext4_mac AW=16 limb 1 is refuted |
| PASS | `contract_csa2_66_n3_base` | unsat | unsat | 0.2s | qsag_csa_reduce2 W=66 N=3 base: s + c == sum x_i (mod 2^66) for all 2^198 inputs |
| PASS | `contract_csa2_66_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=66 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_66_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=66 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^264 inputs |
| PASS | `contract_csa2_66_n6_step_rtl` | unsat | unsat | 0.6s | qsag_csa_reduce2 W=66 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_66_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=66 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^396 inputs |
| PASS | `contract_csa2_67_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=67 N=3 base: s + c == sum x_i (mod 2^67) for all 2^201 inputs |
| PASS | `contract_csa2_67_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=67 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_67_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=67 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^268 inputs |
| PASS | `contract_csa2_67_n5_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=67 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_67_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=67 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^335 inputs |
| PASS | `contract_csa2_68_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=68 N=3 base: s + c == sum x_i (mod 2^68) for all 2^204 inputs |
| PASS | `contract_csa2_68_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=68 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_68_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=68 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^272 inputs |
| PASS | `contract_csa2_72_n3_base` | unsat | unsat | 0.3s | qsag_csa_reduce2 W=72 N=3 base: s + c == sum x_i (mod 2^72) for all 2^216 inputs |
| PASS | `contract_csa2_72_n4_step_rtl` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=72 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_72_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^288 inputs |
| PASS | `contract_csa2_72_n6_step_rtl` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=72 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_72_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^432 inputs |
| PASS | `contract_csa2_72_n8_step_rtl` | unsat | unsat | 0.9s | qsag_csa_reduce2 W=72 N=8 RTL triplet + child-sum invariants (M=6) |
| PASS | `contract_csa2_72_n8_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=8 inductive step (from proved M=6): s + c == sum x_i for all 2^576 inputs |
| PASS | `contract_csa2_72_n11_step_rtl` | unsat | unsat | 1.3s | qsag_csa_reduce2 W=72 N=11 RTL triplet + child-sum invariants (M=8) |
| PASS | `contract_csa2_72_n11_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=72 N=11 inductive step (from proved M=8): s + c == sum x_i for all 2^792 inputs |
| PASS | `contract_csa2_96_n3_base` | unsat | unsat | 0.4s | qsag_csa_reduce2 W=96 N=3 base: s + c == sum x_i (mod 2^96) for all 2^288 inputs |
| PASS | `contract_csa2_96_n4_step_rtl` | unsat | unsat | 0.8s | qsag_csa_reduce2 W=96 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_96_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=96 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^384 inputs |
| PASS | `contract_csa2_96_n5_step_rtl` | unsat | unsat | 0.8s | qsag_csa_reduce2 W=96 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_96_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=96 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^480 inputs |
| PASS | `contract_csa2_128_n3_base` | unsat | unsat | 0.6s | qsag_csa_reduce2 W=128 N=3 base: s + c == sum x_i (mod 2^128) for all 2^384 inputs |
| PASS | `contract_csa2_128_n4_step_rtl` | unsat | unsat | 1.2s | qsag_csa_reduce2 W=128 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_128_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^512 inputs |
| PASS | `contract_csa2_128_n6_step_rtl` | unsat | unsat | 2.1s | qsag_csa_reduce2 W=128 N=6 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_128_n6_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=6 inductive step (from proved M=4): s + c == sum x_i for all 2^768 inputs |
| PASS | `contract_csa2_128_n8_step_rtl` | unsat | unsat | 1.6s | qsag_csa_reduce2 W=128 N=8 RTL triplet + child-sum invariants (M=6) |
| PASS | `contract_csa2_128_n8_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=8 inductive step (from proved M=6): s + c == sum x_i for all 2^1024 inputs |
| PASS | `contract_csa2_128_n12_step_rtl` | unsat | unsat | 4.5s | qsag_csa_reduce2 W=128 N=12 RTL triplet + child-sum invariants (M=8) |
| PASS | `contract_csa2_128_n12_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=128 N=12 inductive step (from proved M=8): s + c == sum x_i for all 2^1536 inputs |
| PASS | `contract_csa2_136_n3_base` | unsat | unsat | 0.8s | qsag_csa_reduce2 W=136 N=3 base: s + c == sum x_i (mod 2^136) for all 2^408 inputs |
| PASS | `contract_csa2_136_n4_step_rtl` | unsat | unsat | 0.8s | qsag_csa_reduce2 W=136 N=4 RTL triplet + child-sum invariants (M=3) |
| PASS | `contract_csa2_136_n4_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=4 inductive step (from proved M=3): s + c == sum x_i for all 2^544 inputs |
| PASS | `contract_csa2_136_n5_step_rtl` | unsat | unsat | 1.0s | qsag_csa_reduce2 W=136 N=5 RTL triplet + child-sum invariants (M=4) |
| PASS | `contract_csa2_136_n5_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=5 inductive step (from proved M=4): s + c == sum x_i for all 2^680 inputs |
| PASS | `contract_csa2_136_n7_step_rtl` | unsat | unsat | 1.9s | qsag_csa_reduce2 W=136 N=7 RTL triplet + child-sum invariants (M=5) |
| PASS | `contract_csa2_136_n7_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=7 inductive step (from proved M=5): s + c == sum x_i for all 2^952 inputs |
| PASS | `contract_csa2_136_n10_step_rtl` | unsat | unsat | 4.0s | qsag_csa_reduce2 W=136 N=10 RTL triplet + child-sum invariants (M=7) |
| PASS | `contract_csa2_136_n10_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=10 inductive step (from proved M=7): s + c == sum x_i for all 2^1360 inputs |
| PASS | `contract_csa2_136_n15_step_rtl` | unsat | unsat | 7.2s | qsag_csa_reduce2 W=136 N=15 RTL triplet + child-sum invariants (M=10) |
| PASS | `contract_csa2_136_n15_step` | unsat | unsat | 0.0s | qsag_csa_reduce2 W=136 N=15 inductive step (from proved M=10): s + c == sum x_i for all 2^2040 inputs |
| PASS | `contract_split_33_c17` | unsat | unsat | 0.0s | qsag_add_split W=33 CHUNK=17: y == a + b (mod 2^33) for all 2^66 inputs |
| PASS | `contract_split_33_c33` | unsat | unsat | 0.0s | qsag_add_split W=33 CHUNK=33: y == a + b (mod 2^33) for all 2^66 inputs |
| PASS | `contract_split_65_c16` | unsat | unsat | 0.1s | qsag_add_split W=65 CHUNK=16: y == a + b (mod 2^65) for all 2^130 inputs |
| PASS | `contract_split_65_c34` | unsat | unsat | 0.0s | qsag_add_split W=65 CHUNK=34: y == a + b (mod 2^65) for all 2^130 inputs |
| PASS | `contract_split_66_c16` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=16: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c24` | unsat | unsat | 0.1s | qsag_add_split W=66 CHUNK=24: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c34` | unsat | unsat | 0.0s | qsag_add_split W=66 CHUNK=34: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_66_c66` | unsat | unsat | 0.0s | qsag_add_split W=66 CHUNK=66: y == a + b (mod 2^66) for all 2^132 inputs |
| PASS | `contract_split_67_c16` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=16: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_67_c24` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=24: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_67_c34` | unsat | unsat | 0.1s | qsag_add_split W=67 CHUNK=34: y == a + b (mod 2^67) for all 2^134 inputs |
| PASS | `contract_split_68_c68` | unsat | unsat | 0.0s | qsag_add_split W=68 CHUNK=68: y == a + b (mod 2^68) for all 2^136 inputs |
| PASS | `contract_split_72_c72` | unsat | unsat | 0.0s | qsag_add_split W=72 CHUNK=72: y == a + b (mod 2^72) for all 2^144 inputs |
| PASS | `contract_split_96_c32` | unsat | unsat | 0.1s | qsag_add_split W=96 CHUNK=32: y == a + b (mod 2^96) for all 2^192 inputs |
| PASS | `contract_split_96_c48` | unsat | unsat | 0.1s | qsag_add_split W=96 CHUNK=48: y == a + b (mod 2^96) for all 2^192 inputs |
| PASS | `contract_split_128_c16` | unsat | unsat | 0.3s | qsag_add_split W=128 CHUNK=16: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_128_c24` | unsat | unsat | 0.2s | qsag_add_split W=128 CHUNK=24: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_128_c32` | unsat | unsat | 0.2s | qsag_add_split W=128 CHUNK=32: y == a + b (mod 2^128) for all 2^256 inputs |
| PASS | `contract_split_136_c16` | unsat | unsat | 0.3s | qsag_add_split W=136 CHUNK=16: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_split_136_c24` | unsat | unsat | 0.3s | qsag_add_split W=136 CHUNK=24: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_split_136_c46` | unsat | unsat | 0.2s | qsag_add_split W=136 CHUNK=46: y == a + b (mod 2^136) for all 2^272 inputs |
| PASS | `contract_sum_csa_66_3_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=3 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_3_c66` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=3 CHUNK=66: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_4_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=4 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_5_c66` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=5 CHUNK=66: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_6_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=6 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_66_6_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=66 N=6 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_67_5_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=67 N=5 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_68_3_c68` | unsat | unsat | 0.0s | qsag_sum_csa W=68 N=3 CHUNK=68: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_68_4_c68` | unsat | unsat | 0.0s | qsag_sum_csa W=68 N=4 CHUNK=68: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_5_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=5 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_7_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=7 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_8_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=8 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_72_11_c72` | unsat | unsat | 0.0s | qsag_sum_csa W=72 N=11 CHUNK=72: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_96_5_c48` | unsat | unsat | 0.0s | qsag_sum_csa W=96 N=5 CHUNK=48: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_128_12_c32` | unsat | unsat | 0.0s | qsag_sum_csa W=128 N=12 CHUNK=32: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_9_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=9 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_10_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=10 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_11_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=11 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_12_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=12 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_13_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=13 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_14_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=14 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_15_c16` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=15 CHUNK=16: RTL glue over proved CSA + split-carry |
| PASS | `contract_sum_csa_136_15_c24` | unsat | unsat | 0.0s | qsag_sum_csa W=136 N=15 CHUNK=24: RTL glue over proved CSA + split-carry |
| PASS | `ext5_karatsuba_range_limb0` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 0: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext5_karatsuba_range_limb1` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 1: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext5_karatsuba_range_limb2` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 2: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext5_karatsuba_range_limb3` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 3: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext5_karatsuba_range_limb4` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 4: 0 < acc < 2^136 for all 2^128 products and 64-bit c |
| PASS | `ext5_karatsuba_modp_limb0` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 0: exact congruence acc - schoolbook == p * Q_k over F_p[X]/(X^5 - 3) |
| PASS | `ext5_karatsuba_modp_limb1` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 1: exact congruence acc - schoolbook == p * Q_k over F_p[X]/(X^5 - 3) |
| PASS | `ext5_karatsuba_modp_limb2` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 2: exact congruence acc - schoolbook == p * Q_k over F_p[X]/(X^5 - 3) |
| PASS | `ext5_karatsuba_modp_limb3` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 3: exact congruence acc - schoolbook == p * Q_k over F_p[X]/(X^5 - 3) |
| PASS | `ext5_karatsuba_modp_limb4` | unsat | unsat | 0.0s | 14-mul F_{p^5} Karatsuba limb 4: exact congruence acc - schoolbook == p * Q_k over F_p[X]/(X^5 - 3) |
| PASS | `ext5_rtl_stage0_ma0` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[0] (0,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb0` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[0] (0,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma1` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 0 ma_q[1] (1,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb1` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 0 mb_q[1] (1,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma2` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[2] (2,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb2` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 0 mb_q[2] (2,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma3` | unsat | unsat | 0.3s | qsag_ext5_mac RTL Stage 0 ma_q[3] (0, 1): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb3` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 0 mb_q[3] (0, 1): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma4` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[4] (0, 2): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb4` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[4] (0, 2): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma5` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[5] (1, 2): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb5` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[5] (1, 2): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma6` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 0 ma_q[6] (3,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb6` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 0 mb_q[6] (3,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma7` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[7] (4,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb7` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[7] (4,): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma8` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[8] (3, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb8` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[8] (3, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma9` | unsat | unsat | 0.7s | qsag_ext5_mac RTL Stage 0 ma_q[9] (0, 3): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb9` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[9] (0, 3): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma10` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[10] (1, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb10` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[10] (1, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma11` | unsat | unsat | 27.3s | qsag_ext5_mac RTL Stage 0 ma_q[11] (0, 1, 3, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb11` | unsat | unsat | 20.0s | qsag_ext5_mac RTL Stage 0 mb_q[11] (0, 1, 3, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma12` | unsat | unsat | 3.2s | qsag_ext5_mac RTL Stage 0 ma_q[12] (0, 2, 3): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb12` | unsat | unsat | 4.8s | qsag_ext5_mac RTL Stage 0 mb_q[12] (0, 2, 3): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_ma13` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 ma_q[13] (1, 2, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage0_mb13` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 0 mb_q[13] (1, 2, 4): < p and equals exact canonical sum mod p |
| PASS | `ext5_rtl_stage4_acc_limb0` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 1..4: dbg_acc[0]@s5 == exact 136-bit Karatsuba combination of c_0@s0 and m[0..13] |
| PASS | `ext5_rtl_stage4_acc_limb1` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 1..4: dbg_acc[1]@s5 == exact 136-bit Karatsuba combination of c_1@s0 and m[0..13] |
| PASS | `ext5_rtl_stage4_acc_limb2` | unsat | unsat | 0.1s | qsag_ext5_mac RTL Stage 1..4: dbg_acc[2]@s5 == exact 136-bit Karatsuba combination of c_2@s0 and m[0..13] |
| PASS | `ext5_rtl_stage4_acc_limb3` | unsat | unsat | 0.2s | qsag_ext5_mac RTL Stage 1..4: dbg_acc[3]@s5 == exact 136-bit Karatsuba combination of c_3@s0 and m[0..13] |
| PASS | `ext5_rtl_stage4_acc_limb4` | unsat | unsat | 0.0s | qsag_ext5_mac RTL Stage 1..4: dbg_acc[4]@s5 == exact 136-bit Karatsuba combination of c_4@s0 and m[0..13] |
| PASS | `ext5_rtl_stage6_red_join` | unsat | unsat | 0.5s | qsag_ext5_mac 7-cycle RTL Stage 5..6: y[64*k +: 64]@s7 == qred136(dbg_acc[k]@s5) for all k=0..4 |
| PASS | `ext5_mul64_prod_range` | unsat | unsat | 0.0s | Ext5 Stage-1..3 product bound: 0 <= ma, mb < p implies 0 <= ma * mb < 2^128 |
| PASS | `ext5_stage04_link_limb0` | unsat | unsat | 0.0s | Ext5 limb 0 Stage-0..4 ring link: Stage-0 ma/mb + Stage-3 m_i + Stage-4 acc entail acc - sb == p * Q_0 |
| PASS | `ext5_end_to_end_glue_limb0` | unsat | unsat | 0.0s | Ext5 limb 0 end-to-end Modus Ponens: Stage-0..6 + range contracts entail y_0 == schoolbook_0(a,b,c) mod p |
| PASS | `ext5_stage04_link_limb1` | unsat | unsat | 0.0s | Ext5 limb 1 Stage-0..4 ring link: Stage-0 ma/mb + Stage-3 m_i + Stage-4 acc entail acc - sb == p * Q_1 |
| PASS | `ext5_end_to_end_glue_limb1` | unsat | unsat | 0.0s | Ext5 limb 1 end-to-end Modus Ponens: Stage-0..6 + range contracts entail y_1 == schoolbook_1(a,b,c) mod p |
| PASS | `ext5_stage04_link_limb2` | unsat | unsat | 0.0s | Ext5 limb 2 Stage-0..4 ring link: Stage-0 ma/mb + Stage-3 m_i + Stage-4 acc entail acc - sb == p * Q_2 |
| PASS | `ext5_end_to_end_glue_limb2` | unsat | unsat | 0.0s | Ext5 limb 2 end-to-end Modus Ponens: Stage-0..6 + range contracts entail y_2 == schoolbook_2(a,b,c) mod p |
| PASS | `ext5_stage04_link_limb3` | unsat | unsat | 0.0s | Ext5 limb 3 Stage-0..4 ring link: Stage-0 ma/mb + Stage-3 m_i + Stage-4 acc entail acc - sb == p * Q_3 |
| PASS | `ext5_end_to_end_glue_limb3` | unsat | unsat | 0.0s | Ext5 limb 3 end-to-end Modus Ponens: Stage-0..6 + range contracts entail y_3 == schoolbook_3(a,b,c) mod p |
| PASS | `ext5_stage04_link_limb4` | unsat | unsat | 0.0s | Ext5 limb 4 Stage-0..4 ring link: Stage-0 ma/mb + Stage-3 m_i + Stage-4 acc entail acc - sb == p * Q_4 |
| PASS | `ext5_end_to_end_glue_limb4` | unsat | unsat | 0.0s | Ext5 limb 4 end-to-end Modus Ponens: Stage-0..6 + range contracts entail y_4 == schoolbook_4(a,b,c) mod p |
| PASS | `mut_ext5_stage0_wire` | sat | sat | 5.8s | mutant tooth: Stage-0 p4_in wire swap (a1->a2) in qsag_ext5_mac is refuted |
| PASS | `mut_ext5_mac_y0_coeff` | sat | sat | 0.1s | mutant tooth: wrong 4*m0 weight in qsag_ext5_mac Stage-4 t_y0 is refuted |
| PASS | `mut_ext5_stage6_limb` | sat | sat | 0.0s | mutant tooth: wrong c4->c3 carry in qsag_ext5_mac Stage-4 t_y4 is refuted |
| PASS | `gf128_reduce` | unsat | unsat | 0.1s | qsag_gf128_reduce: for all 2^255 inputs, r = c mod (x^128+x^7+x^2+x+1) |
| PASS | `mut_gf128_reduce_tap` | sat | sat | 0.0s | qsag_gf128_reduce: for all 2^255 inputs, r = c mod (x^128+x^7+x^2+x+1) |
| PASS | `mut_gf128_clmul_kara` | sat | sat | 6.9s | qsag_gf128_clmul: for all 2^256 inputs, r (3 clocks later) = a*b in GF(2^128) |
| PASS | `mut_gf128_clmul_basis_x77` | sat | sat | 2.7s | qsag_gf128_clmul: for all a and b = x^77, r (3 clocks later) = a * x^77 |
| PASS | `comp_clmul_kara_w8_base` | unsat | unsat | 0.0s | qsag_clmul_kara W=8 base RTL: p == clmul_spec(a, b) for all 2^16 inputs |
| PASS | `mut_clmul_kara_w8_base` | sat | sat | 0.0s | mutant tooth: shift fault in qsag_clmul_kara W=8 base is refuted |
| PASS | `comp_clmul_row_split_w16` | unsat | unsat | 0.0s | GF(2)[x] inductive 4-quadrant schoolbook decomposition clmul_16(a,b) -> 4 x clmul_8 |
| PASS | `comp_clmul_bilin_h8` | unsat | unsat | 0.0s | GF(2)[x] inductive bilinearity of clmul_8 in both operands over all shifts s < 8 |
| PASS | `comp_clmul_spec_split_w16` | unsat | unsat | 0.0s | GF(2)[x] Karatsuba recombination lemma W=16 (from bilinear H=8) |
| PASS | `comp_clmul_kara_w16_step` | unsat | unsat | 0.0s | qsag_clmul_kara W=16 inductive RTL step (from proved H=8): p == clmul_spec(a, b) for all 2^32 inputs |
| PASS | `mut_comp_clmul_kara_w16` | sat | sat | 0.0s | mutant tooth: dropped lo term in qsag_clmul_kara W=16 step is refuted |
| PASS | `comp_clmul_row_split_w32` | unsat | unsat | 0.0s | GF(2)[x] inductive 4-quadrant schoolbook decomposition clmul_32(a,b) -> 4 x clmul_16 |
| PASS | `comp_clmul_bilin_h16` | unsat | unsat | 0.1s | GF(2)[x] inductive bilinearity of clmul_16 in both operands over all shifts s < 16 |
| PASS | `comp_clmul_spec_split_w32` | unsat | unsat | 0.0s | GF(2)[x] Karatsuba recombination lemma W=32 (from bilinear H=16) |
| PASS | `comp_clmul_kara_w32_step` | unsat | unsat | 0.0s | qsag_clmul_kara W=32 inductive RTL step (from proved H=16): p == clmul_spec(a, b) for all 2^64 inputs |
| PASS | `comp_clmul_row_split_w64` | unsat | unsat | 0.2s | GF(2)[x] inductive 4-quadrant schoolbook decomposition clmul_64(a,b) -> 4 x clmul_32 |
| PASS | `comp_clmul_bilin_h32` | unsat | unsat | 0.2s | GF(2)[x] inductive bilinearity of clmul_32 in both operands over all shifts s < 32 |
| PASS | `comp_clmul_spec_split_w64` | unsat | unsat | 0.0s | GF(2)[x] Karatsuba recombination lemma W=64 (from bilinear H=32) |
| PASS | `comp_clmul_kara_w64_step` | unsat | unsat | 0.0s | qsag_clmul_kara W=64 inductive RTL step (from proved H=32): p == clmul_spec(a, b) for all 2^128 inputs |
| PASS | `comp_clmul_row_split_w128` | unsat | unsat | 0.4s | GF(2)[x] inductive 4-quadrant schoolbook decomposition clmul_128(a,b) -> 4 x clmul_64 |
| PASS | `comp_clmul_bilin_h64` | unsat | unsat | 0.7s | GF(2)[x] inductive bilinearity of clmul_64 in both operands over all shifts s < 64 |
| PASS | `comp_clmul_spec_split_w128` | unsat | unsat | 0.1s | GF(2)[x] Karatsuba recombination lemma W=128 (from bilinear H=64) |
| PASS | `comp_clmul_kara_w128_step` | unsat | unsat | 0.0s | qsag_clmul_kara W=128 inductive RTL step (from proved H=64): p == clmul_spec(a, b) for all 2^256 inputs |
| PASS | `comp_gf128_clmul_basis_x0` | unsat | unsat | 12.7s | qsag_gf128_clmul: for all a and b = x^0, r (3 clocks later) = a * x^0 |
| PASS | `comp_gf128_clmul_basis_x77` | unsat | unsat | 6.7s | qsag_gf128_clmul: for all a and b = x^77, r (3 clocks later) = a * x^77 |
| PASS | `comp_gf128_clmul_pipe_rtl` | unsat | unsat | 0.1s | 3-cycle qsag_gf128_clmul RTL pipeline join: r@s3 == qsag_gf128_reduce(qsag_clmul_kara(a@s0, b@s0)) |
| PASS | `comp_gf128_clmul_end_to_end` | unsat | unsat | 0.1s | Horner-step & polynomial-mod inductive equivalence -> r@s3 == gf_mul_spec(a,b) over all 2^256 inputs |
| PASS | `tower_map_dir0` | unsat | unsat | 0.5s | qsag_gf128_tower_map INVERSE=0: for all 2^128 inputs, RTL == exact Wiedemann matrix |
| PASS | `tower_map_dir1` | unsat | unsat | 0.5s | qsag_gf128_tower_map INVERSE=1: for all 2^128 inputs, RTL == exact Wiedemann matrix |
| PASS | `tower_map_bijection` | unsat | unsat | 1.7s | composed RTL qsag_tower_rt: inv(fwd(e_b)) == e_b and fwd(inv(e_b)) == e_b for all 128 basis inputs |
| PASS | `mut_tower_map_bitflip` | sat | sat | 0.6s | mutant tooth: 1-bit mask flip in qsag_gf128_tower_map is refuted |
| PASS | `tower_mul_rtl_universal` | unsat | unsat | 0.0s | qsag_gf128_tower_mul: for all 2^256 (a,b), 3-cycle RTL == tower_inv(clmul(tower_fwd(a), tower_fwd(b))) |
| PASS | `mut_tower_mul_inv` | sat | sat | 0.0s | mutant tooth: wrong INVERSE=0 output map in qsag_gf128_tower_mul is refuted |
| PASS | `tower_artin_schreier_k0` | unsat | unsat | 2.9s | qsag_gf128_tower_mul 3-cycle RTL: g_0 * (g_0 + g_-1) == 1 |
| PASS | `tower_artin_schreier_k1` | unsat | unsat | 2.0s | qsag_gf128_tower_mul 3-cycle RTL: g_1 * (g_1 + g_0) == 1 |
| PASS | `tower_artin_schreier_k2` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL: g_2 * (g_2 + g_1) == 1 |
| PASS | `tower_artin_schreier_k3` | unsat | unsat | 1.9s | qsag_gf128_tower_mul 3-cycle RTL: g_3 * (g_3 + g_2) == 1 |
| PASS | `tower_artin_schreier_k4` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL: g_4 * (g_4 + g_3) == 1 |
| PASS | `tower_artin_schreier_k5` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL: g_5 * (g_5 + g_4) == 1 |
| PASS | `tower_artin_schreier_k6` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL: g_6 * (g_6 + g_5) == 1 |
| PASS | `tower_kat_0_mul` | unsat | unsat | 1.9s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #0 (mul) |
| PASS | `tower_kat_0_inv` | unsat | unsat | 1.9s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #0 (inv) |
| PASS | `tower_kat_1_mul` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #1 (mul) |
| PASS | `tower_kat_1_inv` | unsat | unsat | 1.9s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #1 (inv) |
| PASS | `tower_kat_2_mul` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #2 (mul) |
| PASS | `tower_kat_2_inv` | unsat | unsat | 1.7s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #2 (inv) |
| PASS | `tower_kat_3_mul` | unsat | unsat | 1.8s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #3 (mul) |
| PASS | `tower_kat_3_inv` | unsat | unsat | 1.9s | qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #3 (inv) |

## Canonical-form check of the carry-less multiplier
```
PASS	anf_gf128_clmul_anf	equal	equal	0/128 bits differ, 40832 monomials
PASS	anf_mut_gf128_clmul_anf	different	different	128/128 bits differ, 40832 monomials
PASS	anf_gf128_tower_mul_anf	equal	equal	0/128 bits differ, 161331 monomials
PASS	anf_mut_gf128_tower_mul_anf	different	different	128/128 bits differ, 161331 monomials
PASS	anf_gf128_tower_rt	equal	equal	0/128 bits differ, universal 2^256 bijection
```
## Yosys synthesis: xcup
```
== qsag_ext4_compact_bfly_taw11 [xcup]
  LUT (LUT1-6)                 13057
    of which LUT6              2586
  MUXF7/F8/F9                  402
  FF (FDRE/FDSE/FDCE/FDPE)     4231
  CARRY8                       0
  CARRY4                       721
  DSP48E2                      9
  RAMB36E2                     0
  RAMB18E2                     30
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 21
== qsag_ext4_mac_bfly_taw10 [xcup]
  LUT (LUT1-6)                 52043
    of which LUT6              11029
  MUXF7/F8/F9                  786
  FF (FDRE/FDSE/FDCE/FDPE)     10443
  CARRY8                       0
  CARRY4                       2903
  DSP48E2                      81
  RAMB36E2                     8
  RAMB18E2                     0
  SRL16E/SRLC32E               267
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 18
== qsag_ext4_mac [xcup]
  LUT (LUT1-6)                 48742
    of which LUT6              11000
  MUXF7/F8/F9                  786
  FF (FDRE/FDSE/FDCE/FDPE)     9380
  CARRY8                       0
  CARRY4                       2615
  DSP48E2                      81
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               256
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 18
== qsag_ext5_mac [xcup]
  LUT (LUT1-6)                 77123
    of which LUT6              18478
  MUXF7/F8/F9                  786
  FF (FDRE/FDSE/FDCE/FDPE)     14266
  CARRY8                       0
  CARRY4                       4258
  DSP48E2                      126
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               320
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 18
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
  reg-to-reg depth (LUT+carry cells) 11
== qsag_gf128_tower_mul [xcup]
  LUT (LUT1-6)                 9541
    of which LUT6              1047
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     639
  CARRY8                       0
  CARRY4                       0
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 11
== qsag_gl64_dsp_mul [xcup]
  LUT (LUT1-6)                 3904
    of which LUT6              735
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     926
  CARRY8                       0
  CARRY4                       216
  DSP48E2                      9
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 18
== qsag_gl64_reduce [xcup]
  LUT (LUT1-6)                 851
    of which LUT6              69
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     130
  CARRY8                       0
  CARRY4                       93
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 14
== qsag_keccak_compact [xcup]
  LUT (LUT1-6)                 3369
    of which LUT6              722
  MUXF7/F8/F9                  213
  FF (FDRE/FDSE/FDCE/FDPE)     1385
  CARRY8                       0
  CARRY4                       40
  DSP48E2                      0
  RAMB36E2                     1
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 18
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
  LUT (LUT1-6)                 7614
    of which LUT6              463
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
== qsag_ni_fpga_top_ecp5_compact [xcup]
  LUT (LUT1-6)                 52101
    of which LUT6              10708
  MUXF7/F8/F9                  482
  FF (FDRE/FDSE/FDCE/FDPE)     21463
  CARRY8                       0
  CARRY4                       1921
  DSP48E2                      18
  RAMB36E2                     23
  RAMB18E2                     131
  SRL16E/SRLC32E               67
  LUTRAM (RAM32M/RAM64M/...)   4
  reg-to-reg depth (LUT+carry cells) 21
== qsag_ni_fpga_top_ecp5_fullrate [xcup]
  LUT (LUT1-6)                 102212
    of which LUT6              21242
  MUXF7/F8/F9                  870
  FF (FDRE/FDSE/FDCE/FDPE)     29240
  CARRY8                       0
  CARRY4                       4752
  DSP48E2                      117
  RAMB36E2                     27
  RAMB18E2                     131
  SRL16E/SRLC32E               399
  LUTRAM (RAM32M/RAM64M/...)   4
  reg-to-reg depth (LUT+carry cells) 24
== qsag_ni_fpga_top_taw10 [xcup]
  LUT (LUT1-6)                 315876
    of which LUT6              59962
  MUXF7/F8/F9                  788
  FF (FDRE/FDSE/FDCE/FDPE)     71522
  CARRY8                       0
  CARRY4                       15694
  DSP48E2                      513
  RAMB36E2                     31
  RAMB18E2                     86
  SRL16E/SRLC32E               2358
  LUTRAM (RAM32M/RAM64M/...)   4
  reg-to-reg depth (LUT+carry cells) 24
== qsag_ni_fpga_top_taw16 [xcup]
  LUT (LUT1-6)                 316985
    of which LUT6              60920
  MUXF7/F8/F9                  786
  FF (FDRE/FDSE/FDCE/FDPE)     71540
  CARRY8                       0
  CARRY4                       15696
  DSP48E2                      513
  RAMB36E2                     487
  RAMB18E2                     86
  SRL16E/SRLC32E               2364
  LUTRAM (RAM32M/RAM64M/...)   4
  reg-to-reg depth (LUT+carry cells) 24
== qsag_p2_chain_engine [xcup]
  LUT (LUT1-6)                 5480
    of which LUT6              316
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     1730
  CARRY8                       0
  CARRY4                       510
  DSP48E2                      0
  RAMB36E2                     11
  RAMB18E2                     57
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   4
  reg-to-reg depth (LUT+carry cells) 13
== qsag_p2_linear [xcup]
  LUT (LUT1-6)                 22901
    of which LUT6              5582
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     1680
  CARRY8                       0
  CARRY4                       1332
  DSP48E2                      0
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               0
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 19
== qsag_p2_sbox7 [xcup]
  LUT (LUT1-6)                 15616
    of which LUT6              2940
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     3512
  CARRY8                       0
  CARRY4                       864
  DSP48E2                      36
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               64
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 24
== qsag_poseidon2_12_fpga [xcup]
  LUT (LUT1-6)                 213672
    of which LUT6              40864
  MUXF7/F8/F9                  0
  FF (FDRE/FDSE/FDCE/FDPE)     46174
  CARRY8                       0
  CARRY4                       11826
  DSP48E2                      432
  RAMB36E2                     0
  RAMB18E2                     0
  SRL16E/SRLC32E               2092
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 24
== qsag_poseidon2_12_pipe [xcup]
  LUT (LUT1-6)                 2319625
    of which LUT6              513748
  MUXF7/F8/F9                  8488
  FF (FDRE/FDSE/FDCE/FDPE)     467735
  CARRY8                       0
  CARRY4                       143322
  DSP48E2                      4248
  RAMB36E2                     4
  RAMB18E2                     1
  SRL16E/SRLC32E               23040
  LUTRAM (RAM32M/RAM64M/...)   0
  reg-to-reg depth (LUT+carry cells) 24
```
## Yosys synthesis: ecp5
```
== qsag_ext4_compact_bfly_taw11 [ecp5]
  LUT4                         12499
  TRELLIS_FF                   5279
  CCU2C                        1275
  L6MUX21/PFUMX                0
  MULT18X18D                   9
  DP16KD                       30
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 56
== qsag_ext4_mac_bfly_taw10 [ecp5]
  LUT4                         24900
  TRELLIS_FF                   11896
  CCU2C                        4062
  L6MUX21/PFUMX                0
  MULT18X18D                   81
  DP16KD                       16
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 71
== qsag_ext4_mac [ecp5]
  LUT4                         23577
  TRELLIS_FF                   10734
  CCU2C                        3789
  L6MUX21/PFUMX                0
  MULT18X18D                   81
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 70
== qsag_ext5_mac [ecp5]
  LUT4                         57302
  TRELLIS_FF                   15546
  CCU2C                        8254
  L6MUX21/PFUMX                0
  MULT18X18D                   126
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 56
== qsag_gf128_clmul [ecp5]
  LUT4                         5776
  TRELLIS_FF                   639
  CCU2C                        0
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 10
== qsag_gf128_tower_mul [ecp5]
  LUT4                         11452
  TRELLIS_FF                   639
  CCU2C                        0
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 10
== qsag_gl64_dsp_mul [ecp5]
  LUT4                         2428
  TRELLIS_FF                   926
  CCU2C                        435
  L6MUX21/PFUMX                0
  MULT18X18D                   9
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 56
== qsag_gl64_reduce [ecp5]
  LUT4                         851
  TRELLIS_FF                   130
  CCU2C                        175
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 20
== qsag_keccak_compact [ecp5]
  LUT4                         5069
  TRELLIS_FF                   1385
  CCU2C                        77
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       2
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 22
== qsag_keccak_rpc1 [ecp5]
  LUT4                         5795
  TRELLIS_FF                   1607
  CCU2C                        3
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 6
== qsag_keccak_rpc2 [ecp5]
  LUT4                         10373
  TRELLIS_FF                   1606
  CCU2C                        0
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 9
== qsag_ni_fpga_top_ecp5_compact [ecp5]
  LUT4                         57576
  TRELLIS_FF                   22712
  CCU2C                        2961
  L6MUX21/PFUMX                0
  MULT18X18D                   18
  DP16KD                       177
  TRELLIS_DPR16X4              22
  reg-to-reg depth (LUT+carry cells) 56
== qsag_ni_fpga_top_ecp5_fullrate [ecp5]
  LUT4                         76116
  TRELLIS_FF                   31159
  CCU2C                        7055
  L6MUX21/PFUMX                0
  MULT18X18D                   117
  DP16KD                       185
  TRELLIS_DPR16X4              22
  reg-to-reg depth (LUT+carry cells) 71
== qsag_ni_fpga_top_taw10 [ecp5]
  LUT4                         229776
  TRELLIS_FF                   90514
  CCU2C                        28736
  L6MUX21/PFUMX                0
  MULT18X18D                   513
  DP16KD                       148
  TRELLIS_DPR16X4              22
  reg-to-reg depth (LUT+carry cells) 71
== qsag_ni_fpga_top_taw16 [ecp5]
  LUT4                         236830
  TRELLIS_FF                   90588
  CCU2C                        28738
  L6MUX21/PFUMX                0
  MULT18X18D                   513
  DP16KD                       1060
  TRELLIS_DPR16X4              22
  reg-to-reg depth (LUT+carry cells) 71
== qsag_p2_chain_engine [ecp5]
  LUT4                         5183
  TRELLIS_FF                   1730
  CCU2C                        946
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       79
  TRELLIS_DPR16X4              22
  reg-to-reg depth (LUT+carry cells) 19
== qsag_p2_linear [ecp5]
  LUT4                         26284
  TRELLIS_FF                   1680
  CCU2C                        2412
  L6MUX21/PFUMX                0
  MULT18X18D                   0
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 24
== qsag_p2_sbox7 [ecp5]
  LUT4                         9712
  TRELLIS_FF                   3768
  CCU2C                        1740
  L6MUX21/PFUMX                0
  MULT18X18D                   36
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 56
== qsag_poseidon2_12_fpga [ecp5]
  LUT4                         146117
  TRELLIS_FF                   63737
  CCU2C                        23533
  L6MUX21/PFUMX                0
  MULT18X18D                   432
  DP16KD                       0
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 56
== qsag_poseidon2_12_pipe [ecp5]
  LUT4                         1630408
  TRELLIS_FF                   699881
  CCU2C                        280246
  L6MUX21/PFUMX                0
  MULT18X18D                   4248
  DP16KD                       9
  TRELLIS_DPR16X4              0
  reg-to-reg depth (LUT+carry cells) 56
```
## nextpnr-ecp5 (LFE5U-85F-6BG381C, $45 ECP5-85F, CABGA381, speed 6)
```
== fmax_gl64_dsp_mul [nextpnr-ecp5 LFE5U-85F-6BG381C | bitstream 308.4 KiB]
  Fmax TRELLIS_IO_IN        50.05 MHz
  MULT18X18D               9/156 (5.8%)
  TRELLIS_COMB             2566/83640 (3.1%)
  TRELLIS_FF               887/83640 (1.1%)
== fmax_p2_sbox7 [nextpnr-ecp5 LFE5U-85F-6BG381C | bitstream 411.1 KiB]
  Fmax TRELLIS_IO_IN        48.59 MHz
  MULT18X18D               36/156 (23.1%)
  TRELLIS_COMB             9933/83640 (11.9%)
  TRELLIS_FF               2852/83640 (3.4%)
== fmax_ext4_mac [nextpnr-ecp5 LFE5U-85F-6BG381C | bitstream 634.1 KiB]
  Fmax TRELLIS_IO_IN        46.23 MHz
  MULT18X18D               81/156 (51.9%)
  TRELLIS_COMB             25365/83640 (30.3%)
  TRELLIS_FF               8832/83640 (10.6%)
== fmax_keccak_compact [nextpnr-ecp5 LFE5U-85F-6BG381C | bitstream 354.1 KiB]
  Fmax TRELLIS_IO_IN        32.83 MHz
  DP16KD                   2/208 (1.0%)
  TRELLIS_COMB             5362/83640 (6.4%)
  TRELLIS_FF               1461/83640 (1.7%)
== fmax_gf128_clmul [nextpnr-ecp5 LFE5U-85F-6BG381C | bitstream 358.9 KiB]
  Fmax TRELLIS_IO_IN        69.84 MHz
  TRELLIS_COMB             6560/83640 (7.8%)
  TRELLIS_FF               641/83640 (0.8%)
== fmax_p2_linear [nextpnr-ecp5 LFE5U-85F-6BG381C | bitstream 582.7 KiB]
  Fmax TRELLIS_IO_IN        34.41 MHz
  TRELLIS_COMB             25240/83640 (30.2%)
  TRELLIS_FF               3217/83640 (3.8%)
```
