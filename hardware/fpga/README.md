# hardware/fpga — QSAG-NI accelerator core for FPGAs

An FPGA implementation of the five word-local primitives qsag's verifier and recursion path are
made of (Goldilocks, GoldilocksExt4, width-12 Poseidon2, Keccak-p[1600], GF(2^128)), bit-exact
against the qsag crates and the Lean oracle vectors, with an AXI4-Lite / AXI4-Stream wrapper.

Everything here was built and run on the build box (`bb2:/home/build/qsag-ni-fpga`) with the
YosysHQ OSS CAD Suite 2026-11-16 (Yosys 0.71+34, Verilator 5.055, z3 4.15.5, nextpnr-ecp5).
Numbers below are copied from those runs; `RESULTS.md` holds the raw tables.

## What is here

| path | content |
|---|---|
| `rtl/` | the synthesizable SystemVerilog (20 files, no vendor primitives) |
| `tb/` | Verilator testbench `sim_qsag_ni_fpga.cpp`, the independent C++ reference model `qsag_model.h`, the unit harness, and `gen_kat.py` (Lean fixture to C header) |
| `lec/` | `lec.py` (Yosys `write_smt2` + z3 miters and mutants), `anf_check.py` (canonical-form check of the carry-less multiplier) |
| `synth/` | Yosys `synth_xilinx -family xcup` / `synth_ecp5` scripts, nextpnr-ecp5 Fmax wrappers |
| `scripts/gen_p2_rc.py` | writes `rtl/qsag_p2_rc.sv` from the round-constant tables of `crates/qsag-accel/shaders/poseidon2_perm12.comp` |
| `verify_fpga.sh`, `lint.sh` | the gate, one step per 600 s build slot |

## Units

| module | function | architecture | latency (clocks) |
|---|---|---|---|
| `qsag_gl64_dsp_mul` | `(a*b) mod p`, any 64-bit inputs, canonical output | 64x64 tiled on DSP blocks (`qsag_mul64_dsp`: 12 tiles of 26x17 for DSP48E2, 16 tiles of 16x16 for MULT18X18D, each tile with its own operand and product registers), then `qsag_gl64_reduce` | 6 (4 + 2), 1 result/clock |
| `qsag_gl64_reduce` | `x mod p` for `x < 2^136` | `lo + m*2^32 + p - m - h - t*2^32` in one carry chain (`2^64 = 2^32-1`, `2^96 = -1`, `2^128 = -2^32`), then a three-way select; no divider, no multiplier | 2 |
| `qsag_ext4_mac` | `a*b + c` in `F_p[v]/(v^4 - 7)`, qsag limb order | 16 tiled products, each coefficient accumulated exactly (`7x = 8x - x`) and reduced once, as `GoldilocksExt4::mul_add` does | 7, 1 MAC/clock |
| `qsag_ext4_mac_bfly` | radix-2 fold `t[k] = t[2k] + r*(t[2k+1] - t[2k])` over a table, plus a shared MAC port | table in two simple-dual-port block RAMs (even / odd), both read synchronously, fold in place, one butterfly per clock | round over n entries: n/2 + 9 |
| `qsag_poseidon2_12_fpga` | `poseidon2_perm12`, and the weighted feed-forward node hash (`perm(l,r,t)[i] + l_i + 2 r_i + 4 t_i`) | **folded ring**: one round stage (12 S-box lanes, lane 0 alone on internal rounds, zero-multiplier linear layers) closed into a 21-stage ring; a job circulates 31 times; the ring is C-slow, 21 independent jobs share it | 651 per job; 31 clocks/job when full |
| `qsag_poseidon2_12_pipe` | same function | **unrolled**: initial `M_E`, 8 external and 22 internal round stages, 118 S-box units; job metadata and the feed-forward in block-RAM delay lines | 603, 1 permutation/clock |
| `qsag_p2_linear` | `M_E = M4 (x) P3`, `M_I = J + diag(-64, 1, 2, ..., 1024)` plus a 67-bit addend | integer shift-and-add only (lane weights sum to at most 28 and 1036), next round's constants or the feed-forward folded into the same sum, one lazy reduction per lane | 2 |
| `qsag_p2_sbox7` | `x^7 = (x^2 * x) * (x^2)^2` | 4 multipliers in 3 levels | 18 |
| `qsag_p2_chain_engine` | batched leaf-sponge + Canopy Merkle path verification | 32 chain slots, step data (sponge blocks, siblings) and running state in block RAM, 3-stage injector with round-robin pick feeding the ring | per step: 651 + injector |
| `qsag_keccak_turboshake` | Keccak-f[1600] (24 rounds) or Keccak-p[1600,12] (TurboSHAKE256) | 1 or 2 rounds per clock in LUTs | 24/12 (1 rnd/clk), 12/6 (2 rnd/clk) |
| `qsag_gf128_clmul` | product in `GF(2)[x]/(x^128+x^7+x^2+x+1)` | recursive Karatsuba to an 8-bit schoolbook base (81 base products, 5,184 AND gates), two-fold reduction | 3 |
| `qsag_ni_fpga_top` | AXI4-Lite + AXI4-Stream wrapper | register map and operations in the file header | op = unit latency + 2 or 3 |

Parameters match the crates: `p = 2^64 - 2^32 + 1`; Ext4 is `F_{p^2}[v]/(v^2 - u)`, `u^2 = 7`,
i.e. `F_p[v]/(v^4 - 7)` (`crates/qsag-agg/src/field.rs`); Poseidon2 has `R_F = 8`, `R_P = 22`,
S-box `x^7`, round constants from the shader table (the testbench derives them a second way, from
the SplitMix64 definition in `poseidon2.rs`); GF(2^128) is the polynomial-basis MAC field of
`qsag-core` (`rss256.rs`, `triple_f2.rs`), bit `j` = coefficient of `x^j`. It is not the Wiedemann
tower of the fixture's `tower128` vectors; no tower isomorphism unit is built.

The top's command set (see `rtl/qsag_ni_fpga_top.sv`): `P2_PERM`, `P2_JIVE`, `CHAIN_CFG/START/WAIT/READ`
(Canopy verification), `EXT4_MAC`, `SC_INIT/SC_ROUND` (sumcheck round check `g(0)+g(1) = claim` and
Horner evaluation), `FOLD_SETLEN/ROUND/MULTI` (table fold), `KEC_LOAD/KEC_PERMUTE` (SHAKE256, cSHAKE256,
TurboSHAKE256 with host-side padding), `GF_MAC` (`a*b + k`, compared with a tag), `CLEAR`. Cycle
counters: `OP_CYCLES` (per command), `TOTAL_CYCLES` (clocks with any engine active), `P2_PERMS`.
Stream limbs are range-checked (`< p`) with a sticky error flag.

## Running the gate

On the build box, with the suite's `environment` sourced:

```
SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s ./verify_fpga.sh <step>
```

Steps (each fits one slot): `lint`, `units`, `top`, `lec-gl`, `lec-glmut`, `lec-gf`, `lec-anf`,
`lec-try`. `QSAG_FIXTURE` points at `validation/tests/fixtures/lean_external_oracle_vectors.json`
(default: the path relative to this directory). Synthesis: `synth/run_all.sh xcup|ecp5`,
`synth/run_fmax.sh`.

## Verification results (2026-11-16, final RTL)

**Lint.** `verilator --lint-only -Wall` on `qsag_ni_fpga_top` and on `qsag_poseidon2_12_pipe`: 0 warnings.
There are six local `UNUSEDSIGNAL` waivers (adder bits implied by a sign bit, sums whose top bits are
provably zero, one unused status output) and one `UNUSEDPARAM` waiver on the shared-constants package.

**Simulation** (Verilator, registers and inputs randomised at start, `--x-initial unique`):

| run | checks | mismatches | content |
|---|---:|---:|---|
| reference model self-check | 118 | 0 | the C++ model reproduces the Lean oracle vectors (Goldilocks, Ext4, Poseidon2-12, SHA3-256 / SHAKE256 / cSHAKE256 at 14 lengths) and RFC 9861 TurboSHAKE256 |
| units | 1,699,936 | 0 | both multiplier tilings, the 136-bit reducer, `x^7`, Ext4 MAC, GF(2^128): Lean KATs, corner cases (`0, 1, p-1, p, p+1, 2^64-1, 2^32-1, 2^32, ...`, all pairs), 200,000 random vectors per unit; ring core (150 jobs, C-slow interleaved) and pipelined core (1,200 jobs back to back) on the 4 Lean permutation KATs plus random permutations and feed-forward hashes; Keccak at 1 and 2 rounds/clock through whole sponges |
| top | 3,558 | 0 | every command through AXI4-Lite / AXI4-Stream, including rejected sumcheck claims, a rejected GF(2^128) tag and a corrupted Merkle sibling; the two traces below |

What the comparisons rest on: Goldilocks, Ext4, the Poseidon2 permutation and Keccak are checked
against the kernel-verified Lean vectors directly. The Canopy node hash, the rate-8 sponge framing
and GF(2^128) are checked against `tb/qsag_model.h`, which re-implements
`merkle_layer_poseidon2_canopy_at_cpu`, `poseidon2_sponge_hash_limbs_with_cap` and the bit-serial
field product from the crates' definitions (and `x * x^127 = 0x87`, the value `qsag-asm` pins). No
vector was generated by running the Rust crates in this lane.

**Cycle counts** (asserted in the testbench):

| operation | clocks |
|---|---:|
| Goldilocks product / 136-bit reduction / `x^7` / Ext4 MAC / GF(2^128) product | 6 / 2 / 18 / 7 / 3 |
| Poseidon2 permutation, ring core (latency; 21 jobs in flight) | 651 |
| Poseidon2 permutation, pipelined core (latency; 1 per clock) | 603 |
| Keccak-f[1600] / Keccak-p[1600,12], 1 round per clock | 24 / 12 |
| Keccak-f[1600] / Keccak-p[1600,12], 2 rounds per clock | 12 / 6 |
| top `P2_PERM` / `KEC_PERMUTE` (24, 12 rounds) / `EXT4_MAC` / `SC_ROUND` | 654 / 15, 9 / 9 / 26 |
| top fold round over n entries | n/2 + 12 (plus 1 per `FOLD_MULTI` command) |
| chain engine, 32 chains of 10 steps (320 permutations), wall including loading | 10,530 (32.9 per permutation) |

### Trace 1: a QSAGSTA1-shaped root verification

This is a **modelled operation mix**, not a replay of `verify_public_hologram` on a real
`SuccinctSubtreeAggregate`: no proof was produced or parsed here. The shape is a 20-variable WHIR
opening under the fixture's stage geometry `(2,5) (4,3) (6,4)` and the wire-tag-6 query counts
`216 / 109 / 74`, 72 sumcheck rounds (12 folding rounds plus an assumed 3 x 20 for the hologram),
and a final 2^8 evaluation. Every operation runs on real data through the RTL and is compared with
the model: each query is a leaf sponge (2^k Ext4 elements) plus a Canopy path to a committed top
node, then a 2^k-point fold; the transcript is one Poseidon2 permutation per sumcheck round.

| | count / clocks |
|---|---:|
| Poseidon2 permutations | 11,407 (72 transcript, sequential; 11,335 leaf-sponge and node, on the ring) |
| Ext4 MACs | 9,040 (216 Horner, 8,824 fold butterflies) |
| **clocks, wall** (AXI host with zero think time) | **488,933** |
| transcript + sumcheck rounds | 63,670 (permutations 47,088, sumcheck 1,872, rest bus) |
| query leaf hashes + Merkle paths | 376,363 |
| query folds | 48,140 |
| final evaluation | 760 |
| clocks with any engine active (`TOTAL_CYCLES`) | 454,232 |
| bus traffic | 7,060 AXI4-Lite writes, 227,130 reads (status polling), 20,559 stream beats |

The 15,000 to 34,000 clocks of `scripts/quorum_and_consensus_scaling.py`
(`VERIFY_CYCLES_POSEIDON2_ROOT`, `VERIFY_CYCLES_KECCAK_ROOT`) are **not** reproduced by this core:
on this operation mix it needs 14 to 33 times as many. The reason is structural. That model has
one Poseidon2 round per clock (a permutation in about 30 clocks); a 64-bit `x^7` at FPGA clock
rates is 18 pipeline stages, so a round is 21 clocks and a permutation 651. The ring recovers the
throughput for independent work (31 clocks per permutation, 33 measured with loading), which is
what the 11,335 query permutations get, but a hash chain is still latency-bound: the 72 transcript
permutations alone take 47,088 clocks, and 11,407 x 31 = 353,617 is the floor for this top. With
the unrolled core in place of the ring (not wired into the top) the query phase would be bounded by
the longest chain, 34 steps x 603 = 20,502 clocks, and the transcript by 72 x 603 = 43,416.

### Trace 2: a 16-variable Ext4 edge fold

65,535 butterflies, in place in block RAM, checked against the `fold_first_var_ext4` model:
table load 65,538 clocks (one entry per clock over AXI4-Stream), 16 fold rounds 65,729 clocks
core-busy (66,012 wall with the challenges written over AXI4-Lite), 131,550 in total. The script's
`EDGE_FOLD_CYCLES` is 180,000. This is the fold kernel only (one multilinear table, 16 challenges),
not the `[CWYZ26]` accumulator protocol around it.

### Clock period

Yosys has no UltraScale+ place and route, so **no UltraScale+ Fmax is claimed**. The table gives
the measured clock counts at clock rates that are assumptions, not results:

| clock (assumed) | trace 1, wall | trace 2, 16 fold rounds | trace 2 with load |
|---:|---:|---:|---:|
| 100 MHz | 4.89 ms | 657 us | 1.32 ms |
| 200 MHz | 2.44 ms | 329 us | 658 us |
| 300 MHz | 1.63 ms | 219 us | 439 us |
| 400 MHz | 1.22 ms | 164 us | 329 us |

### ECP5 place and route (nextpnr-ecp5, LFE5UM5G-85F, CABGA381, speed grade 8)

Measured on pin-frugal wrappers (`synth/fmax_wrap.sv`), 150 MHz target, one seed, one 600 s slot each:

| unit | Fmax | LUT4 cells | FF | MULT18X18D |
|---|---:|---:|---:|---:|
| `qsag_gl64_dsp_mul` (16x16 tiling) | **175.93 MHz** | 1,352 | 1,220 | 16 / 156 |
| `qsag_p2_sbox7` | **131.29 MHz** | 4,517 | 4,240 | 52 / 156 |
| `qsag_gf128_clmul` | **118.15 MHz** | 6,945 | 641 | 0 |
| `qsag_keccak_turboshake`, 1 and 2 rounds/clk | not routed in the slot | | | |
| `qsag_p2_linear` | not finished in the slot | | | |

The two Keccak runs were still congested (about 6,500 and 8,900 overused wires after 21 router2
iterations, not converging) when the slot ended, with both routers; no Keccak or linear-layer Fmax
is claimed. The flat place-and-route netlist of the S-box uses 52 multipliers where the
hierarchical synthesis table counts 64. At the multiplier's 175.9 MHz, the 651-clock permutation
would take 3.7 us on an ECP5; nothing larger than single units was placed.


## Formal checks

`lec/lec.py` has Yosys read the SystemVerilog and write the transition relation with
`write_smt2` (frontend, `proc`, `flatten`, no optimisation pass), unrolls it over the pipeline
depth and asks z3 for a counterexample. 24 required checks pass; 6 further attempts are recorded
as undecided.

**`qsag_gl64_dsp_mul`: `r = (a*b) mod p` for all 2^128 inputs, `r < p`**, for both tilings
(26x17 and 16x16), as a chain of machine-checked statements:

1. *Product* (z3 on the RTL, 91 s and 111 s): the 128-bit product register, 4 clocks after
   `(a, b)`, equals the weighted sum `X` of the tile outputs. The tile multiply is an
   uninterpreted function constrained only by `tile(x, y) <= (2^wa - 1)(2^wb - 1)`, so the
   statement holds for every such function.
2. *Tile facts* (z3, integers): multiplication satisfies that bound, and
   `(sum a_i 2^(26i)) (sum b_j 2^(17j)) = sum a_i b_j 2^(26i+17j)`. With 1, `X = a*b`.
3. *Reduce* (z3 on the RTL, under 2 s): for every product register value, `r` two clocks later is
   `< p` and `V = r + k p` for some `k` in `{0,1,2}`, where `V = lo + m 2^32 + p - m - h - t 2^32`.
4. *Reduction identity* (z3, integers): `x + p = V + p Q0` and `0 < V < 3p`. With 3,
   `x = r + p (Q0 + k - 1)` and `r < p`, so `r = x mod p`.

`qsag_gl64_reduce` is proved the same way on its own over all 2^136 inputs. Taken on trust:
Yosys's SystemVerilog frontend and `write_smt2`, z3, and that a DSP tile computes the product of
its two operands (the chain's only use of "multiplication"). The joins between the statements
(composition at a named register, uniqueness of the remainder) are arguments on paper, three lines each.

**Mutants** (each must give `sat`): a sign flipped in the reducer; the wrong candidate selected
in the reducer's last stage; a tile wired to the neighbouring `b` chunk; a row shifted by one bit.
All four are refuted, and the statement not touched by a mutation stays `unsat`.

**`qsag_gf128_clmul`.** z3 proves the reduction stage (`qsag_gf128_reduce`, all 2^255 inputs,
62 s) and refutes two mutants in three queries. It does **not** decide the Karatsuba multiplier against its
definition: a 128-bit miter, a single basis element `b = x^j`, and even the same module at 16 bits
all time out (XOR-heavy miters are the classic hard case for SAT). The multiplier is instead
checked completely by `lec/anf_check.py`: a carry-less product is a polynomial over GF(2) in the
input bits, the algebraic normal form of a Boolean function is unique, and the script computes the
ANF of all 128 outputs of the netlist Yosys elaborates (14,318 cells: AND, XOR, flip-flops;
constant folding only) and compares it monomial for monomial with the definition
`r = sum a_i b_j x^(i+j) mod (x^128 + x^7 + x^2 + x + 1)` (40,832 monomials): equal, with every
path crossing exactly 3 registers. A mutant with one Karatsuba term dropped differs in 128/128
outputs. This rests on the Python script and Yosys's frontend and `techmap` rather than on z3.

**Recorded as undecided** (60 s each, `lec-try`): the bit-precise tile wiring miter, the
monolithic `bvurem(bvmul(a, b), p)` miter, and four carry-less miters. They are in the gate so
that a future solver or encoding that closes them shows up as a change.

Not formally checked: Ext4, the Poseidon2 linear layers and cores, Keccak, the engines and the
top. Those rest on the simulation above.

## Synthesis

Yosys 0.71, hierarchy kept (each module synthesised once, counted by instance), so counts are a
little pessimistic against a flat run. `synth_xilinx -family xcup` in this Yosys emits `CARRY4`
(two per `CARRY8`) and, whatever shape the registers have, leaves `AREG/BREG/MREG/PREG = 0`
on inferred DSP48E2: the multiplier's operand and product registers are counted as fabric flops
below, where a vendor flow would absorb them. "Depth" is the longest register-to-register path in
LUT and carry cells inside a module (a 128-bit add is 32 `CARRY4`).

### Xilinx UltraScale+ (`synth_xilinx -family xcup`)

| module | LUT | of which LUT6 | FF | CARRY4 | DSP48E2 | RAMB36E2 | RAMB18E2 | SRL | LUTRAM | depth |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `qsag_gl64_reduce` | 269 | 26 | 130 | 51 | 0 | 0 | 0 | 0 | 0 | 21 |
| `qsag_gl64_dsp_mul` | 681 | 33 | 1,157 | 156 | 12 | 0 | 0 | 0 | 0 | 35 |
| `qsag_p2_sbox7` | 2,724 | 132 | 4,628 | 624 | 48 | 0 | 0 | 64 | 0 | 35 |
| `qsag_p2_linear` (selectable) | 8,659 | 391 | 1,680 | 1,409 | 0 | 0 | 0 | 0 | 0 | 32 |
| `qsag_ext4_mac` | 10,387 | 822 | 17,488 | 2,084 | 192 | 0 | 0 | 256 | 0 | 43 |
| `qsag_ext4_mac_bfly` (2^10 entries) | 11,971 | 824 | 18,551 | 2,224 | 192 | 8 | 0 | 267 | 0 | 43 |
| `qsag_keccak_turboshake` 1 round/clk | 3,551 | 0 | 1,614 | 2 | 0 | 0 | 0 | 0 | 0 | 6 |
| `qsag_keccak_turboshake` 2 rounds/clk | 7,715 | 484 | 1,614 | 3 | 0 | 0 | 0 | 0 | 0 | 8 |
| `qsag_gf128_clmul` | 5,007 | 496 | 639 | 0 | 0 | 0 | 0 | 0 | 0 | 3 |
| `qsag_p2_chain_engine` | 3,168 | 333 | 2,498 | 284 | 0 | 0 | 57 | 0 | 59 | 32 |
| `qsag_poseidon2_12_fpga` (ring) | 44,769 | 2,003 | 59,336 | 8,967 | 576 | 0 | 0 | 1,818 | 0 | 35 |
| `qsag_poseidon2_12_pipe` (unrolled) | 511,277 | 22,414 | 599,035 | 96,812 | 5,664 | 8 | 1 | 23,040 | 0 | 35 |
| **`qsag_ni_fpga_top`**, fold table 2^10 | **84,942** | 5,585 | **88,813** | 11,751 | **768** | 8 | 57 | 2,084 | 59 | 43 (*) |
| **`qsag_ni_fpga_top`**, fold table 2^16 | **86,496** | 6,603 | **88,831** | 11,753 | **768** | 464 | 57 | 2,090 | 59 | 43 (*) |

(*) For the top, the depth is the maximum over its units; Yosys's path report does not follow
paths across kept hierarchy. `CARRY8` is 0 in every row (see above). The top with a 2^16-entry table is 7% of a VU9P's LUTs
and 11% of its DSP slices by count (1,182,240 LUT, 6,840 DSP48E2, 2,160 RAMB36); the unrolled core
alone would take 83% of that device's DSP slices. These are resource counts, not a placed design.

### Lattice ECP5 (`synth_ecp5`)

| module | LUT4 | TRELLIS_FF | CCU2C | L6MUX21+PFUMX | MULT18X18D | DP16KD | DPR16X4 | depth |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `qsag_gl64_reduce` | 467 | 130 | 100 | 151 | 0 | 0 | 0 | 36 |
| `qsag_gl64_dsp_mul` | 773 | 1,218 | 292 | 174 | 16 | 0 | 0 | 64 |
| `qsag_p2_sbox7` | 3,092 | 5,256 | 1,168 | 696 | 64 | 0 | 0 | 64 |
| `qsag_p2_linear` (selectable) | 7,136 | 1,680 | 2,759 | 506 | 0 | 0 | 0 | 48 |
| `qsag_ext4_mac` | 11,657 | 19,488 | 3,870 | 2,390 | 256 | 0 | 0 | 74 |
| `qsag_ext4_mac_bfly` (2^10 entries) | 13,540 | 21,696 | 4,143 | 2,418 | 256 | 16 | 0 | 74 |
| `qsag_keccak_turboshake` 1 round/clk | 8,454 | 1,607 | 3 | 4,714 | 0 | 0 | 0 | 6 |
| `qsag_keccak_turboshake` 2 rounds/clk | 12,033 | 1,606 | 0 | 4,262 | 0 | 0 | 0 | 12 |
| `qsag_gf128_clmul` | 6,363 | 639 | 0 | 1,026 | 0 | 0 | 0 | 5 |
| `qsag_p2_chain_engine` | 4,957 | 3,535 | 562 | 891 | 0 | 57 | 406 | 49 |
| `qsag_poseidon2_12_fpga` (ring) | 47,954 | 86,065 | 16,916 | 9,146 | 768 | 0 | 0 | 64 |
| `qsag_poseidon2_12_pipe` (unrolled) | 552,907 | 952,519 | 183,068 | 101,618 | 7,552 | 17 | 0 | 64 |
| `qsag_ni_fpga_top`, fold table 2^10 | 101,379 | 119,695 | 22,359 | 19,725 | 1,024 | 73 | 406 | 74 (*) |
| `qsag_ni_fpga_top`, fold table 2^16 | 109,068 | 119,781 | 22,365 | 21,729 | 1,024 | 985 | 406 | 74 (*) |

**The top does not fit any ECP5.** The largest part (LFE5U(M5G)-85F) has 83,640 LUT4, 156
MULT18X18D and 208 DP16KD; the Ext4 MAC alone needs 256 multipliers and the ring core 768. What
fits an 85F individually: the Goldilocks multiplier, the S-box, the linear layer, Keccak, the
GF(2^128) multiplier and the chain engine. An ECP5-sized QSAG-NI would need a multiplier-serial
Poseidon2 (one S-box unit, 64 multipliers) and a 4-multiplier Ext4 MAC; neither is built here.

## Known limits

- The QSAGSTA1 trace is a modelled workload; an instrumented replay of the Rust verifier is not done.
- No UltraScale+ timing: no vendor tool was run. The registers are placed for a 26x17 DSP48E2
  flow, but timing closure at any frequency is unverified.
- The per-query fold in trace 1 is the multilinear fold kernel; WHIR's coset fold with twiddles is
  not implemented, nor are out-of-domain checks, proof-of-work checks or proof parsing.
- Keccak padding and the Poseidon2 sponge framing are done by the host; the top exposes
  permutation-level commands.
- The chain engine verifies Poseidon2 Canopy trees only; a TurboSHAKE256 Canopy path engine is not built.
- Inputs to the Ext4 units and stream limbs must be canonical; the stream check flags, it does not block.
- The top uses the ring core. The unrolled core is verified and synthesised standalone.
