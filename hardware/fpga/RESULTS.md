# FPGA implementation results

All frequencies below are final routed clock estimates on the LFE5U-85F-6BG381C, CABGA381, speed 6.

| Timing wrapper | Constraint MHz | Routed MHz | Logic LUT4 | COMB | FF | DSP | BRAM | Packed bytes | Overused |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| [fmax_gl64_dsp_mul](build/synth/fmax_gl64_dsp_mul.pnr.bit) | 50 | 59.545074 | 1460 | 2186 | 887 | 9 | 0 | 311295 | 0 |
| [fmax_p2_sbox7](build/synth/fmax_p2_sbox7.pnr.bit) | 50 | 59.772865 | 5479 | 8115 | 2852 | 36 | 0 | 401613 | 0 |
| [fmax_gf128_clmul](build/synth/fmax_gf128_clmul.pnr.bit) | 65 | 71.341942 | 6560 | 6560 | 641 | 0 | 0 | 367255 | 0 |
| [fmax_keccak_compact](build/synth/fmax_keccak_compact.pnr.bit) | 30 | 35.626492 | 5147 | 5423 | 1461 | 0 | 2 | 356781 | 0 |
| [fmax_p2_linear](build/synth/fmax_p2_linear.pnr.bit) | 45 | 46.097816 | 18392 | 21406 | 3205 | 0 | 0 | 551042 | 0 |
| [fmax_ext5_mac](build/synth/fmax_ext5_mac.pnr.bit) | 25 | 34.724632 | 28402 | 43460 | 6466 | 126 | 0 | 895746 | 0 |
| [fmax_compact_top](build/synth/fmax_compact_top.pnr.bit) | 20 | 33.621357 | 23576 | 29436 | 9378 | 18 | 79 | 931949 | 0 |
| [fmax_ecp5_fullrate_top](build/synth/fmax_ecp5_fullrate_top.pnr.bit) | 20 | 29.859657 | 35153 | 45667 | 12645 | 81 | 77 | 1136914 | 0 |

| Verilator suite | Checks | Mismatches | Simulated clocks | Connected workload TOTAL_CYCLES |
|---|---:|---:|---:|---:|
| [UNITS](build/verif_logs/verify_units.log) | 1,900,209 | 0 | 213,721 | — |
| [COMPACT](build/verif_logs/verify_compact.log) | 1,467 | 0 | 766,828 | 15493 |
| [ECP5_FULLRATE](build/verif_logs/verify_ecp5_fullrate.log) | 1,467 | 0 | 541,928 | 11693 |
| [TOP](build/verif_logs/verify_top.log) | 1,547 | 0 | 201,648 | 3706 |
| [PIPE](build/verif_logs/verify_pipe.log) | 1,547 | 0 | 196,268 | 3492 |

Verilator lint passed. All 461 formal and ANF checks returned their expected result, including deliberately faulty designs. The DSP register-packing checks passed on all three optimized wrappers. [Lint](build/verif_logs/lint.log) · [Formal](build/verif_logs/lec_all.log) · [ANF](build/verif_logs/anf_check.log) · [Packing equivalence](build/verif_logs/ecp5_opt_equiv.log)

## Placement comparison

Each paired trial used seed 1, a 20 MHz clock, HeAP beta 0.65 and timing-driven router2. The unconstrained trials used two threads and the floorplanned trials used one. The floorplanner groups local DSP registers and assigns EBR sites. A stopped trial has no routed Fmax.

| Wrapper | Placement | Last router iteration | Overused | Routed MHz |
|---|---|---:|---:|---:|
| fmax_compact_top | [heap](build/verif_logs/fmax_compact_top-heap.log) | 29 | 1841 | stopped |
| fmax_compact_top | [plan](build/synth/bench/fmax_compact_top-plan.pnr.log) | 48 | 0 | 33.621357 |
| fmax_ecp5_fullrate_top | [heap](build/verif_logs/fmax_ecp5_fullrate_top-heap.log) | 11 | 4346 | stopped |
| fmax_ecp5_fullrate_top | [plan](build/synth/bench/fmax_ecp5_fullrate_top-plan.pnr.log) | 29 | 0 | 29.859657 |

## Differential workload

The deterministic connected workload starts with 16 quintic gate evaluations. Its transcript supplies challenges for an in-place four-variable fold and four linked sumcheck rounds. The openings feed TurboSHAKE256 and Poseidon2 root checks. This measures the generated fixture. A serialized production proof and independently supplied public root are required for a production replay.

| Opcode | COMPACT | ECP5_FULLRATE | TOP | PIPE |
|---|---:|---:|---:|---:|
| 0x03 | 1 | 1 | 1 | 1 |
| 0x04 | 13 | 13 | 2 | 2 |
| 0x05 | 9515 | 6695 | 2494 | 2274 |
| 0x06 | 16 | 16 | 4 | 4 |
| 0x11 | 7 | 7 | 7 | 7 |
| 0x12 | 812 | 452 | 398 | 398 |
| 0x14 | 1 | 1 | 1 | 1 |
| 0x15 | 644 | 344 | 104 | 104 |
| 0x16 | 962 | 642 | 594 | 594 |
| 0x22 | 2237 | 2237 | 57 | 57 |
| 0x24 | 1279 | 1279 | 37 | 43 |

OP_CYCLES sums completed commands by opcode. TOTAL_CYCLES counts clocks with active engines, including background chain work.

## Formal coverage

| Group | Passing obligations |
|---|---:|
| [gl](build/lec/results_gl.txt) | 121 |
| [glmut](build/lec/results_glmut.txt) | 100 |
| [ext5](build/lec/results_ext5.txt) | 181 |
| [gf](build/lec/results_gf.txt) | 4 |
| [comp](build/lec/results_comp.txt) | 23 |
| [tower](build/lec/results_tower.txt) | 21 |
| [anf](build/lec/results_anf.txt) | 5 |
| [xbank](build/lec/results_xbank.txt) | 6 |

The compact arithmetic checks cover modular tripling, canonical accumulation and all 25 monomial issue positions in each schedule. Mutants change the wrap comparison or the triple and must produce counterexamples. GF(2) ANF compares the pipeline against the polynomial definition across every input coefficient.

The DSP equivalence gate checks a ten-clock sequential primitive miter with Z3 and Bitwuzla. For each optimized wrapper it checks the complete mapped netlist at the register cutpoints, including clock, enable, reset, deleted FF fanout and every surviving non-DSP cell.

[SHA-256 checksums of the eight mapped netlists, packed images, reports and verification logs](build/verif_logs/signoff.sha256)
