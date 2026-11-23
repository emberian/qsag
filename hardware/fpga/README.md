# QSAG-NI FPGA accelerator

The accelerator shares a 32-bit AXI4-Lite command interface and a 512-bit AXI4-Stream across four silicon profiles. Field operations use five little-endian 64-bit coefficients over the Goldilocks prime `p = 2^64 - 2^32 + 1`, with `X^5 = 3`. The other engines implement Poseidon2-12, Keccak, TurboSHAKE256, cSHAKE256 and polynomial or tower-basis GF(2^128) multiplication.

## Field commands

Each stream beat carries one Fp5 element in bits 319 through 0. Bits 63 through 0 carry coefficient zero. Advance the beat only on a valid/ready handshake.

| Command | Operands and result |
|---|---|
| `0x11 SC_INIT` | Set the running claim from X[0..4] and clear the sticky sumcheck failure. |
| `0x12 SC_ROUND` | With arg0 = 0, X[0..19] hold four ascending coefficients and X[20..24] holds the challenge. With arg0 = degree (1..255), send the challenge followed by coefficients in descending order. Check g(0) + g(1) against the claim, then write g(r) to the claim and Y[0..4]. |
| `0x13 FOLD_ROUND` | Fold the active table in place with X[0..4]. Y[0..4] receives the final butterfly of the round. |
| `0x14 FOLD_SETLEN` | Set the current table dimension to arg0[5..0]. Stream destination 8 loads one full element per beat. |
| `0x15 FOLD_MULTI` | Apply 1..6 challenges from consecutive groups of five X registers. An optional nonzero arg1[5..0] supplies the initial dimension. |
| `0x16 EXT5_BATCH` | For each of arg1 entries (1..65535), send A, B, C and expected Y on four beats. Hardware checks every result and writes the last one to Y[0..4]. |
| `0x17 EXT5_MAC` | Y[0..4] = X[0..4] × X[5..9] + X[10..14]. |
| `0x18 EXT5_FROB` | Apply the arg0-th Frobenius power to X[0..4], scaling limb i by ζ₅ raised to i × arg0 modulo five. |

STATUS bits 0..4 report busy, done, ok, noncanonical input and command error. Opcode `0x10` sets command error and clears ok. Command `0x3F` clears sticky errors and counters. The RTL header includes the complete register and opcode map. [Top-level interface](rtl/qsag_ni_fpga_top.sv)

## Datapaths

The VU9P_TURBO and XCUP_RING profiles share a seven-stage, 14-product quintic MAC. Their 320-bit even and odd fold banks issue one butterfly per clock. On ECP5, each bank has five 64-bit lanes with separate local write enables. Passive loading accepts one 320-bit element per clock. The working operand port and result writeback are 64 bits wide.

ECP5_COMPACT issues 25 schoolbook products in 25 clocks using one nine-DSP Goldilocks multiplier. ECP5_FULLRATE issues five products per clock for five clocks using 45 DSPs. Wrapped terms use precomputed modular triples. The ECP5 command controller tracks which X limbs are resident in the working banks and reloads operands when another command has used them. A direct register MAC takes 37 or 17 command clocks respectively, including the five-limb result writeback. Both wide profiles take 9 command clocks.

The ECP5 timing wrappers expose serial test pins and use four chain slots, a 512-element fold table and a 512-entry Canopy sibling store. ECP5 profile simulations use 32 slots and a 2,048-element fold table. The wide profile simulations cover a 65,536-element table.

## Measured results

<!-- measured:start -->
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
<!-- measured:end -->

The connected differential workload checks a gate batch, commits its outputs with a 400-bit TurboSHAKE256 transcript, folds a table, chains sumcheck claims at degrees 2, 3, 4 and 9, then verifies Steiner and Poseidon2 Canopy openings. The harness generates its inputs deterministically. The isolated fixture set contains the base-field, Poseidon2, sponge and tower Lean vectors. [Per-opcode counters, placement comparison and verification logs](RESULTS.md)

## Reproduce

Run these commands from the isolated FPGA directory. The remote launcher sets the CAD suite path, scratch directory and six-job compilation limit.

```sh
scripts/remote_run.sh ./verify_fpga.sh all
scripts/remote_run.sh bash lec/ecp5_opt_check.sh
scripts/remote_run.sh bash synth/run_fmax.sh
scripts/remote_run.sh bash scripts/collect_results.sh
```

The PnR gate requires every clock to meet its requested constraint, the final router iteration to report zero overused wires and the packed image to be nonempty. For a placement comparison, set `PLACEMENT=heap` or `PLACEMENT=plan` and pass a distinct output tag to `synth/fmax_ecp5.sh`. [Timing and packing gate](synth/fmax_ecp5.sh)
