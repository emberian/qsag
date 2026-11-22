# hardware/fpga — QSAG-NI Accelerator Core for Lattice ECP5 & Xilinx UltraScale+

Synthesizable, vendor-primitive-free SystemVerilog implementation of the **QSAG-NI** verification and recursion accelerator across four parameterized silicon profiles sharing one unified AXI4-Lite + 512-bit AXI4-Stream ISA (`rtl/qsag_ni_fpga_top.sv`), verified bit-exact against the Lean 4 oracle vectors, real `QSAGSTA1` Role-1/Role-2 proofs, `[CWYZ26]` DuetFold, and `zk-Hem v2` quintic $\mathbb{F}_{p^5} = \mathbb{F}_p[X]/(X^5 - 3)$ extensions.

Raw synthesis, simulation, formal equivalence, and `nextpnr-ecp5` place-and-route outputs are recorded in `RESULTS.md`.

## Silicon Profiles (`rtl/qsag_ni_fpga_top.sv`)

| Profile | Parameters | DSP Usage | Architecture Highlights |
|---|---|---:|---|
| **`VU9P_TURBO`** | `PROFILE_COMPACT=0, P2_UNROLLED=1, KECCAK_PIPE=1, CHAIN_SLOTW=8, FOLD_TAW=16` | `4,825` `DSP48E2` | 1-perm/clk unrolled Poseidon2-12 + 12-stage pipelined Keccak-p[1600,12] + 256 chain slots |
| **`XCUP_RING`** | `PROFILE_COMPACT=0, P2_UNROLLED=0, KECCAK_PIPE=0, CHAIN_SLOTW=5, FOLD_TAW=10/16` | **`513` `DSP48E2`** (`-33%` vs 768) | 16-stage C-slow Poseidon2-12 ring (`432` DSPs) + 1-MAC/clk 9-mul Tower Karatsuba `Ext4` (`81` DSPs) |
| **`ECP5_FULLRATE`** | `PROFILE_COMPACT=1, ECP5_FULLRATE=1, FOLD_TAW=11, KECCAK_RPC=1, AW=16, BW=16` | **`117 / 156` (`75.0%`) `MULT18X18D`** | Fits DSP budget of **one `$45` Lattice `ECP5-85F`**: 81-DSP 1-MAC/clk `Ext4` + 36-DSP 1-Sbox/clk Poseidon2 + 0-DSP 1-RAM $N^4=I$ Keccak |
| **`ECP5_COMPACT`** | `PROFILE_COMPACT=1, ECP5_FULLRATE=0, FOLD_TAW=11, KECCAK_RPC=1, AW=16, BW=16` | **`18 / 156` (`11.5%`) `MULT18X18D`** | Ultra-compact: 9-DSP Tower Karatsuba `Ext4` butterfly + 9-DSP rotating Poseidon2 + 0-DSP 1-RAM Keccak + compact GF($2^{128}$) |

## Key Microarchitectural & Audit Milestones

1. **9-DSP Unsigned Two-Level Karatsuba Goldilocks Multiplier (`qsag_mul33x32_dsp.sv` + `qsag_mul64_dsp.sv`):** Cuts per-multiplier DSPs from `12` (`DSP48E2`) / `16` (`MULT18X18D`) down to **9 DSPs** on *both* families (`<= 18x17u` unsigned DSP tiles). Combined with 9-multiply Tower Karatsuba `Ext4` (`9 x 9 = 81` DSPs vs `256` schoolbook) and `4 x 9 = 36`-DSP `qsag_p2_sbox7`, `ECP5_FULLRATE` fits **`117 / 156` (`75.0%`) `MULT18X18D`** on one `LFE5U-85F-6BG381C`.
2. **Full 400-Bit `0x22 KEC_STREAM_SPONGE` Hardware Verification (`E11` Fix #1):** `flags[6]` (`chk400`) checks all 50 bytes (`[399:0]`, packing upper 16 bits in `flags[63:48]`) of `zk-Hem v2` digests so upper-144-bit (`bytes 32..49`) tampering cannot pass `STATUS.ok`.
3. **Zero-DSP Shift-Add $N^4 = I$ Compact Keccak (`qsag_keccak_compact.sv`, `E11` Fix #2):** Replaces `5'd3 * x` and `5'd5 * y` in `n4_addr` with shift-add `(x << 1) + x` and `(y << 2) + y`, eliminating all 5 unintended combinational `MULT18X18D` DSPs (`0` DSPs, `2` `DP16KD`, post-PnR Fmax up from `28.61 MHz` -> **`32.83 MHz`**).
4. **Canonical 72-Bit Negation Bias (`E11` Fix #3 & `ECP5_FULLRATE` `3*B66`):** `qsag_ext4_compact_bfly.sv` uses `C64_72 = 72'h00_FFFF_FFFE_0000_0003` (`2p - (2^64 - 1)`), and `qsag_ext4_mac.sv` `g_ecp5_post` uses `72'(3) * B66` on `t_y1`, proved algebraically and on RTL in `lec/lec.py`.

## Verification Results (`RESULTS.md`)

- **Lint (`./lint.sh`):** **`0` warnings** across all Verilator `-Wall` configurations (`qsag_ni_fpga_top` default, `PROFILE_COMPACT`, `ECP5_FULLRATE`, `-DQSAG_ECP5_CARRY`, `qsag_poseidon2_12_pipe`, `qsag_gf128_tower_mul`, `qsag_ext5_mac`).
- **Differential Verilator Simulation (`0` mismatches across all 4 suites):**
  - `units` (`sim_UNITS.log`): **`2,700,221` checks, `0` mismatches** (`213,721` clocks).
  - `top` (`XCUP_RING`, `sim_TOP.log`): **`39,509` checks, `0` mismatches** (`2,286,663` clocks; real `QSAGSTA1` Role-1 `86,810` clks, Role-2 `1,281,993` clks, `[CWYZ26]` DuetFold `30,877` clks, `zk-Hem v2` $\mathbb{F}_{p^5}$ MAC/Frobenius + 400-bit `KEC_STREAM_SPONGE` byte-35/byte-49 tamper rejection).
  - `ecp5_fullrate` (`117/156` DSPs, `sim_ECP5_FULLRATE.log`): **`36,243` checks, `0` mismatches** (`11,570,342` clocks; real `QSAGSTA1` Role-1 `2,004,196` clks, Role-2 `7,675,194` clks, DuetFold `1,077,613` clks).
  - `compact` (`18/156` DSPs, `sim_COMPACT.log`): **`36,240` checks, `0` mismatches** (`15,741,662` clocks; real `QSAGSTA1` Role-1 `2,321,246` clks, Role-2 `11,258,276` clks, DuetFold `1,147,685` clks).
- **100% Formal Equivalence (`0` timeouts, `0` undecided):**
  - **`435 / 435` Z3 + Bitwuzla checks `PASS` (`0` non-PASS)** across `gl` (`135`), `glmut` (`101`), `ext5` (`151`), `gf` (`4`), `comp` (`23`, including sliced `comp_clmul_row_split_w128`), and `tower` (`21`), plus `Bitwuzla` `unsat` equivalence of `-DQSAG_ECP5_CARRY` vs CSA.
  - **`128 / 128` exact GF(2) ANF netlist equality** (`lec/anf_check.py`, `40,832` monomials + mutant refutation).

## Synthesis & `nextpnr-ecp5` Place-and-Route (`LFE5U-85F-6BG381C`, `$45` ECP5-85F, Speed 6)

### Routed `nextpnr-ecp5` + `ecppack` Bitstreams (`build/synth/*.pnr.bit`)

| Unit Wrapper | Post-PnR Fmax | `TRELLIS_COMB` (`/ 83,640`) | `TRELLIS_FF` (`/ 83,640`) | `MULT18X18D` (`/ 156`) | `DP16KD` (`/ 208`) | Bitstream (`.bit`) |
|---|---:|---:|---:|---:|---:|---:|
| `fmax_gl64_dsp_mul` | **50.05 MHz** | `2,566` (`3.1%`) | `887` (`1.1%`) | **`9` (`5.8%`)** | `0` | `308.4 KiB` |
| `fmax_p2_sbox7` | **48.59 MHz** | `9,933` (`11.9%`) | `2,852` (`3.4%`) | **`36` (`23.1%`)** | `0` | `411.1 KiB` |
| `fmax_ext4_mac` | **46.23 MHz** | `25,365` (`30.3%`) | `8,832` (`10.6%`) | **`81` (`51.9%`)** | `0` | `634.1 KiB` |
| `fmax_keccak_compact` | **32.83 MHz** | `5,362` (`6.4%`) | `1,461` (`1.7%`) | **`0` (`0.0%`)** | `2` (`1.0%`) | `354.1 KiB` |
| `fmax_gf128_clmul` | **69.84 MHz** | `6,560` (`7.8%`) | `641` (`0.8%`) | `0` | `0` | `358.9 KiB` |
| `fmax_p2_linear` | **34.41 MHz** | `25,240` (`30.2%`) | `3,217` (`3.8%`) | `0` | `0` | `582.7 KiB` |

*Full-top ECP5-85F PnR note:* Both `fmax_compact_top` (`60,419 / 83,640 = 72.2%` `TRELLIS_COMB`, `18 / 156 = 11.5%` `MULT18X18D`, `100–121 / 208` `DP16KD`, `HeAP` post-place `25.98 MHz`) and `fmax_ecp5_fullrate_top` (`79,788 / 83,640 = 95.4%` `TRELLIS_COMB`, `117 / 156 = 75.0%` `MULT18X18D`, `108–129 / 208` `DP16KD`, `HeAP` post-place `34.98 MHz`) legally place on `LFE5U-85F-6BG381C`, but hit `router2` switchbox congestion (`overused` floor `~26k` on `compact_top`) due to `x_q[31:0]` (`2,048`-FF) / `y_q[11:0]` wide muxing and soft CSA horizontal wiring; `-DQSAG_ECP5_CARRY` (`CCU2C` vertical carry trees in `qsag_add_split.sv` / `qsag_sum_csa.sv`, Bitwuzla-proved `UNSAT`) and BRAM-backed `x_q` banking are staged for the next routing pass.

### Yosys Hierarchical Synthesis Summary (`synth/run_all.sh`)

| Module / Top | UltraScale+ LUT / `DSP48E2` / `RAMB36+18` | ECP5 `LUT4` / `CCU2C` / `MULT18X18D` / `DP16KD` |
|---|---|---|
| `qsag_gl64_dsp_mul` | `1,722` / **`9`** / `0` | `2,428` / `435` / **`9`** / `0` |
| `qsag_p2_sbox7` | `15,616` / **`36`** / `0` | `9,712` / `1,740` / **`36`** / `0` |
| `qsag_ext4_mac` | `46,356` / **`81`** / `0` | `23,577` / `3,789` / **`81`** / `0` |
| `qsag_ext5_mac` | `102,420` / **`126`** / `0` | `57,302` / `8,254` / **`126`** / `0` |
| `qsag_keccak_compact` | `3,369` / **`0`** / `1+0` | `5,069` / `77` / **`0`** / `2` |
| `qsag_ni_fpga_top_ecp5_compact` | `52,101` / **`18`** / `23+131` | `57,576` / `2,961` / **`18`** / `177` |
| `qsag_ni_fpga_top_ecp5_fullrate` | `102,212` / **`117`** / `27+131` | `76,116` / `7,055` / **`117`** / `185` |
| `qsag_ni_fpga_top_taw10` (`XCUP_RING`) | `315,876` / **`513`** / `31+86` | — |
| `qsag_ni_fpga_top_taw16` (`XCUP_RING`) | `316,985` / **`513`** / `487+86` | — |
