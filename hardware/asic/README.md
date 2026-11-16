# QSAG-NI ASIC (`hardware/asic/`)

Synthesizable RTL for the QSAG-NI coprocessor, checked bit-for-bit against qsag's primitives, with a
Yosys/ABC standard-cell flow on four open Liberty libraries. Everything here was built and run on
`bb2` under `/home/build/qsag-ni-asic` (2026-11-16); nothing runs on the Mac.

## Results in brief

| Question | Answer |
|---|---|
| Bit-exact against qsag? | Yes in simulation: 70,724 unit checks and four top-level traces, 0 errors, Verilator `-Wall` 0 warnings. |
| Logic size | **1,049 to 1,182 kGE** mapped (whole top, SRAM excluded), against the 954 kGE analytical budget. It is not under 1 MGE. |
| Clock | Critical stage 14.4 ns (Sky130), 11.8 ns (IHP 130), 3.45 ns (Nangate45), 2.09 ns (ASAP7): 69 / 85 / 290 / 478 MHz, pre-layout, no wire load. |
| Poseidon2-12 permutation | 107 clocks (109 including the command handshake). This is an iterated datapath, not the 30-stage 1 perm/clock pipeline of the budget. |
| Formal equivalence | Proved for the carry-save reducer (RTL and NAND netlist), the final adders and the Obend-emitted specs. **Not proved** for `M_E`, `M_I`, the carry-less multiplier or the full multiplier: those miters time out. |
| Obend | Its `RtlModule` → SystemVerilog → `write_smt2` → z3 flow is real and used here. Its physical stack is model-level; none of it is used. |

## Layout

- `gen/qsag_ref.py`: Python reference transcribed from the Rust sources; `selfcheck` matches 32 fixture vectors.
- `gen/csagen.py`, `gen/gen_rtl.py`: carry-save generator (Dadda trees with the Goldilocks fold built in) and the emitter for `rtl/*_gen.sv`.
- `gen/gen_vectors.py`: unit vectors and top-level command traces with expected responses.
- `rtl/qsag_asic_gl64_csa.sv` (+ `_gen`): Goldilocks multiplier, reducer, final adders, and a conventional reference.
- `rtl/qsag_asic_ext4_p2_shared.sv` (+ `qsag_asic_ext4_p2_gen.sv`): 16 shared product trees for Ext4 multiply-add and the Poseidon2 S-boxes; `M_E`, `M_I`, Canopy feed-forward, round constants.
- `rtl/qsag_asic_keccak_clmul.sv` (+ `qsag_asic_tower_maps_gen.sv`): Keccak at 2 rounds/clock, GF(2^128) multiplier, tower basis maps.
- `rtl/qsag_ni_asic_top.sv`, `rtl/sram_dp_blackbox.sv`: command-driven top and the SRAM macro black box.
- `obend/QsagNi.lean`, `obend/run_obend.sh`, `obend/emitted/`: Obend `RtlModule` specs, emitted `.sv` and Lean miter halves.
- `tb/`, `lec/`, `synth/`: testbenches, miters, synthesis scripts; `synth/RESULTS.md` is the full table.
- `logs/`, `synth/logs/`: every log quoted below. `run_everything.sh` reproduces the lot on `bb2`.

## What matches qsag

Checked against `validation/tests/fixtures/lean_external_oracle_vectors.json` (copied to `fixtures/`):
Goldilocks edge cases, `GoldilocksExt4` products (`v^4 = 7`, limb order `[c0.c0, c0.c1, c1.c0, c1.c1]`),
four Poseidon2-12 permutations, SHAKE256 on the sponge messages, and the `tower128` products.
Round constants come from the SplitMix-style `poseidon2_const_at`; `M_I` is `J + diag(-64, 1, 2, ..., 1024)`.

Not covered by a qsag vector: TurboSHAKE256 from the Canopy midstate, the Canopy node and path, the
2-block Merkle node and the rate-8 sponge. These are checked against the Python transcription of
the Rust code only. The reference's TurboSHAKE256 does reproduce the RFC 9861 empty-message output prefix.

## Microarchitecture

- **Multiplier**: 64×64 Dadda tree (3,843 full adders, 10 stages), then the `2^64 ≡ 2^32 − 1`,
  `2^96 ≡ −1` fold applied to the carry-save rows, then four parallel compound adders that pick
  the canonical result. No carry-propagate adder sits between the tree and the final level.
- **Poseidon2**: full round = 4 multiply cycles + 1 `M_E` cycle; partial round = 3 cycles, with the
  last product entering `M_I` in carry-save form. 1 + 8·5 + 22·3 = 107 clocks.
- **Ext4 multiply-add**: one cycle, 16 trees, each coefficient reduced once.
- **Keccak**: 6 clocks for `Keccak-p[1600,12]`, 12 for 24 rounds, plus a 1600-bit shadow register for the customization midstate.
- **GF(2^128)**: Karatsuba over three 64×64 carry-less trees, single cycle; tower products add two basis maps in and one out.

## Measured clock cycles (Verilator, `logs/sim_top_*.log`)

| Operation | Cycles |
|---|---:|
| Poseidon2-12 permutation | 109 |
| Canopy node (one permutation + feed-forward) | 110 |
| 2-block Merkle node, host-sequenced | 270 |
| Canopy Merkle path, depth 17 / 20 | 1,922 / 2,261 |
| Ext4 multiply-add; GF(2^128) product | 2 |
| `Keccak-p[1600,12]` / `Keccak-f[1600]` | 8 / 14 |
| QSAGSTA1 verification model, Poseidon2 Canopy | 1,029,920 |
| QSAGSTA1 verification model, TurboSHAKE Canopy | 263,637 |
| 16-variable Ext4 fold (65,535 pair folds) | 589,959 |

Single-command figures include 2 clocks of handshake. At the ASAP7 clock these are 2.15 ms, 0.55 ms
and 1.23 ms, roughly 70 to 290 times slower than the budget's 7.5 to 17 µs and 90 µs.

**The QSAGSTA1 rows are a workload model, not a real proof.** `gen_vectors.py` drives 3 openings of
(62, 31, 21) queries at depths (17, 16, 14), 3,000 sumcheck multiply-adds and 600 transcript
permutations over random data. The query counts are my estimate from the 282,000-byte opening size,
not taken from `pcs.rs`. No `QSAGSTA1` proof was parsed or verified, and the `[CWYZ26]`/DuetFold row
is the plain multilinear fold `lo + r·(hi − lo)` only. The traces also load every proof word with
one host command, so command overhead is a large share of the cycle count.

The 16-variable fold needs 2^18 words; the black-boxed macro holds 2^14 (128 KiB). The testbench
runs with `AW = 18`.

## Synthesis (`synth/RESULTS.md`)

kGE is mapped cell area divided by the library's NAND2 area. Delay is ABC `stime` after buffering
and sizing, with no placement and no wire load.

| Stage | Sky130 kGE / ns | IHP 130 | Nangate45 | ASAP7 |
|---|---:|---:|---:|---:|
| S-box cycle, carry-save | 41.0 / 10.04 | 54.7 / 7.53 | 46.0 / 2.55 | 35.5 / 1.41 |
| S-box cycle, conventional (Brent-Kung) | 40.3 / 17.57 | 45.6 / 12.21 | 38.0 / 3.81 | 36.3 / 2.42 |
| S-box cycle, conventional (Kogge-Stone) | 41.9 / 14.52 | 48.1 / 10.89 | 42.7 / 3.44 | 39.1 / 2.10 |
| 128→64 reducer, carry-save | 1.9 / 4.53 | 1.9 / 3.23 | 2.0 / 1.17 | 1.9 / 0.67 |
| 128→64 reducer, conventional | 2.2 / 8.70 | 2.1 / 5.35 | 2.4 / 1.79 | 2.1 / 1.12 |
| Partial round (tree + fold + `M_I`), critical | 92.4 / 14.42 | 139.3 / 11.77 | 93.7 / 3.45 | 78.4 / 2.09 |
| `M_E` + constants | 70.0 / 10.69 | 113.5 / 8.02 | 77.4 / 2.41 | 61.7 / 1.48 |
| Ext4 multiply-add | 640.7 / 12.17 | – | – | 527.4 / 1.71 |
| Keccak, two rounds | 40.6 / 3.40 | 23.7 / 2.07 | 25.1 / 0.78 | 28.2 / 0.43 |
| GF(2^128) multiply | 43.6 / 2.84 | 39.8 / 1.72 | 39.4 / 0.62 | 42.5 / 0.38 |
| **Whole top, logic only** | **1,167** | **1,049** | **1,057** | **1,182** |

- The carry-save multiplier cycle is 1.45 to 1.75 times faster than the conventional one at about the same area.
- The 16 product trees are about 570 kGE of the Sky130 total (35.7 kGE each); flip-flops are about 3% of area.
- The whole-top number uses a fast ABC script (`strash; dretime; map`): the delay-driven script did not finish on the flat netlist inside the 600 s cap. Ext4 on IHP and Nangate45 hit the same cap.
- Generic NAND2/INV counts: multiplier tree 46,422 NAND + 9,046 INV (203,780 transistors, depth 42); reducer 1,464 + 730 (depth 146) against 1,713 + 1,017 (depth 264) conventional.
- No 28 nm, 5 nm or 3 nm figure is given: there is no library for them on `bb2`. ASAP7 is a predictive kit.
- Not done: place and route, OpenROAD/OpenSTA signoff, power.

## Formal equivalence (`logs/lec_sorted.log`, `logs/obend.log`)

Each miter is built by Yosys, written with `write_smt2`, and given to z3 and Bitwuzla (150 s each).

| Miter | Result |
|---|---|
| Four Obend-emitted specs against Obend's Lean half (Obend's own recipe) | unsat; output bit flipped: sat |
| Carry-save reducer = Obend `goldilocksReduce128` spec | unsat (z3 58 s, Bitwuzla 12 s) |
| Same, reducer as a NAND2/INV netlist after `synth` + `abc -g NAND` | unsat (Bitwuzla 15 s; z3 timed out) |
| Reducer with a planted single-input fault | sat |
| Conventional reducer = spec | unsat |
| Parallel final adder = chained final adder (for `x + y < 4p`) | unsat |
| Multiplier fold with one row zero = spec (both rows) | unsat (Bitwuzla; z3 timed out) |
| Reduce-after-add step lemma | unsat |
| `M_E`, `M_I` carry-save lane = reduce(integer sum), all 24 lanes | **undecided** |
| `M_E`, `M_I` with two input lanes swapped | sat |
| Obend chained-add spec = reduce(integer sum) for `M_E`, `M_I` | **undecided** |
| Multiplier fold on two free rows; its planted fault | **undecided** (both) |
| 64×64 carry-less tree; GF(2^128) multiplier = bit-serial definition | **undecided** |
| GF(2^128) multiplier with a planted fault | sat (Bitwuzla) |
| Full multiplier = Obend `fieldMul` spec | **undecided** (expected for a 64×64 multiplier miter) |

Totals: 12 decided as expected, 31 undecided, 0 wrong. For the undecided blocks the evidence is
simulation: 3,003 random vectors each for `M_E` and `M_I`, 22,000 multiplier vectors, and all
16,384 basis-element pairs for the GF(2^128) multiplier.

One early run reported `sat` on `M_I` lanes 9 to 11. The fault was in my reference side (a 72-bit
sum that overflows for the `2^8`..`2^10` diagonals), not in the RTL; widened to 80 bits, those lanes are now undecided like the rest.

## Obend: what is real

- **Real and used**: `Obend.Hardware.HDL` (`RtlModule`, `checkRtlModuleW`, `emitModuleSV`) and
  `Obend.Hardware.YosysLec.emitYosysLecSmt2`. `obend/QsagNi.lean` builds four specs from
  `Obend.Apps.ZkNtt`'s `glCanon`/`glAdd`/`glSub`/`glMul` combinators and runs against the built
  tree at `~/obend/wt-s2-hw-silicon` (8f9f822c) through `LEAN_PATH`, read-only.
- **Limits met**: 64-bit ports and no bit-level operators, so Keccak, the carry-less multiplier and
  the carry-save networks cannot be written as `RtlModule`s. The specs are the word-level chained
  form; the ASIC RTL is hand-written and generated SystemVerilog.
- **Model-level, not used**: `Synth.lean` maps to an abstract 64-bit FPGA BEL model with no cell
  library; `PlaceRoute.lean` checks certificates no tool produces; `Process.lean` holds hand-typed
  corner constants; `TapeoutPipeline.lean` checks a self-generated layout against its own rules.
  The repository contains no Liberty, LEF, DEF or GDS and no OpenROAD/OpenSTA call.
- **`PipelinedZkCrypto.lean`**: a Goldilocks butterfly and a GF(2^64) tower multiplier with real
  proofs, but no Poseidon2 and no `obend-emit-sv` target.
- **`apps/sky130-diode`**: a 1D TCAD diode simulation; unrelated to a digital cell flow.
- `QsagNi.lean` carries no Lean theorem tying its `M_E`/`M_I` modules to a Poseidon2 specification.

## Reproduce

```
./sync.sh push
ssh bb2 'cd /home/build/qsag-ni-asic/src && nohup setsid ./run_everything.sh >/dev/null 2>&1 </dev/null & echo $! > logs/everything.pid'
./sync.sh pull
```

Tools: OSS CAD Suite 2026-11-16 (Yosys 0.71, Verilator 5.055, z3, Bitwuzla) under
`/home/build/qsag-ni-asic/tools`; Liberty files under `/home/build/qsag-ni-asic/pdk` (Sky130 HD tt,
IHP SG13G2 typ, Nangate45 typ, ASAP7 RVT TT merged by `synth/merge_lib.py`). The two large STA1 and
fold traces are regenerated by `run_sim.sh gen` and are not kept here.
