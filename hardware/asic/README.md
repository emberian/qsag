# QSAG-NI ASIC (`hardware/asic/`)

Synthesizable RTL, formal equivalence proofs, multi-corner static timing/power, and OpenROAD physical implementation for the **QSAG-NI** cryptographic verification coprocessor across four open standard-cell PDKs (`Sky130 HD`, `IHP SG13G2`, `Nangate45`, and `ASAP7`).

## Results in Brief

| Metric | Measured Result |
|---|---|
| **Functional / Real-Proof Bit-Exactness** | **100% PASS (`0` errors, `0` Verilator `-Wall` warnings):** `70,724` unit checks + `8` top-level command/proof traces including real `QSAGSTA1` Role-1 (TurboSHAKE256 Canopy) & Role-2 (Poseidon2 Canopy) proofs, `[CWYZ26]` DuetFold, 16-variable Ext4 fold, and **100% tamper-rejection verification** (`trace_sta1_p2_tamper`, `trace_sta1_ts_tamper`, `trace_duet_comp_tamper`). |
| **Standard-Cell Area (`< 954 kGE` budget)** | **655.19 – 720.15 kGE** hierarchical timing-driven (`655.19 kGE` ASAP7, `660.44 kGE` IHP130, `676.22 kGE` Nangate45, `720.15 kGE` Sky130) and **815 – 914 kGE** flat (`815` IHP130, `829` Nangate45, `891` Sky130, `914` ASAP7) — **strictly `< 954 kGE` across all 4 PDKs**. (512 KiB SRAM = `4 x sram_dp_64x16384_bank` hard macros.) |
| **Multi-Corner Timing & Power (`OpenSTA 3.1.0`)** | **ASAP7 (7 nm TT):** **`531.70 MHz`** (`1.8808 ns`), **`15.883 mW`** (`0.0206 mW` leakage). **Nangate45:** `51.57 MHz` (`19.39 ns` ideal) / `38.79 MHz` (`25.78 ns` `5K_hvratio_1_1` WLM). **IHP130:** `26.57 / 17.55 / 11.20 MHz` (`FF / TT / SS`). **Sky130:** `6.61 MHz` (`151.32 ns`). |
| **OpenROAD Physical Signoff (`Basin-1`)** | **Nangate45 (`1480 x 1480 um = 2.1904 mm^2`, `-8.8%` die area):** Symmetric 4-SRAM Basin-1 (`2` West `R90` + `2` East `R270` inward-facing pin strips), `680.37 kGE` post-PnR stdcells (`31%` util), **`0 / 0 / 0` global-route overflow**, **`0` `TritonRoute` DRC violations** (`16.21 m` wirelength, `3,438,384` vias, `routed_basin1.png`), `38.79 MHz`, `+0.1011 ns` hold WNS (`0` hold violations), `64.37 mW`. **Sky130 (`2960 x 2960 um = 8.7616 mm^2`):** 4 SRAMs placed + CTS + legalized (`734.65 kGE`, `39%` util, `+0.4688 ns` hold WNS). |
| **Formal Equivalence (`0` timeouts / `0` undecided)** | **`115 / 115` SMT miters `OK` (`undecided=0, fail=0`)** in `logs/lec_sorted.log` + **`24 / 24` compositional shared-datapath miters** (`logs/lec_composed.json`) + **`5 / 5` exact GF(2) ANF netlist proofs** (`logs/lec_anf.json`) + **`40 / 40` CSA polynomial weight proofs** (`logs/lec_csa.json`) + **`8 / 8` Lean 4 `Obend` `RtlModule` miters** (`logs/obend.log`), with planted-fault `sat` mutation refutation on every check. |

## Microarchitecture (`< 954 kGE` Shared 9-Multiplier Datapath)

- **9-Tree Solinas–Karatsuba Goldilocks Multiplier (`qsag_gl64_mul_csa`):** Splits $a = a_1 2^{32} + a_0$ and $b = b_1 2^{32} + b_0$ via $a_1 b_1 2^{64} + ((a_0+a_1)(b_0+b_1) - a_0 b_0 - a_1 b_1) 2^{32} + a_0 b_0 \pmod{2^{64} - 2^{32} + 1}$, replacing one $64 \times 64$ Dadda tree with two $32 \times 32$ and one $33 \times 33$ carry-save trees folded directly in carry-save form (`~30.5 kGE` per tree on Nangate45).
- **9-Multiply Tower Karatsuba `Ext4` + Shared `9+3` Poseidon2-12 S-Box (`qsag_asic_ext4_p2_shared.sv`):**
  - $\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[v]/(v^2 - u), u^2 = 7$ uses 3 Karatsuba $\mathbb{F}_{p^2}$ products $\times$ 3 Karatsuba $\mathbb{F}_p$ products = **9 shared `qsag_gl64_mul_csa` instances** (`1` clock per `Ext4` multiply-add, down from 16 trees — saving `> 210 kGE`!).
  - Full Poseidon2 rounds split the 12 $x^7$ S-boxes as **9 lanes (`0..8`) + 3 lanes (`9..11`)** on those same 9 multiplier trees (`163` clocks per width-12 permutation; partial rounds execute 1 S-box + fused carry-save `M_I`).
- **Keccak-p[1600] & Wiedemann GF($2^{128}$) (`qsag_asic_keccak_clmul.sv`):** 2 rounds/clock Keccak (`6` clocks `Keccak-p[1600,12]`, `12` clocks `Keccak-f[1600]`) with midstate shadow register + 1-cycle Karatsuba `GF(2^128)` polynomial (`x^128 + x^7 + x^2 + x + 1`) and Wiedemann tower isomorphism maps.

## Measured Cycle Counts & Real-Proof Verification (`logs/sim_*.log`)

| Workload / Operation | Commands | Cycles | Errors | Notes |
|---|---:|---:|---:|---|
| Unit testbench (`tb_units`) | — | — | **0** (`70,724` checks) | `gl64_mul` (`22,263`), `reduce128` (`22,262`), `M_E` (`3,003`), `M_I` (`3,003`), `gf128` (`19,389`), `tower128` (`504`), `keccak` (`300`) |
| Single Poseidon2-12 perm / Canopy node | 1 | **163 / 164** | **0** | `9+3` full-round S-box split on 9 shared CSA trees |
| Canopy Merkle path (depth 17 / depth 20) | 1 | **2,840 / 3,341** | **0** | Hardware-sequenced path verification |
| `Ext4` multiply-add / `GF(2^128)` product | 1 | **1 / 2** | **0** | Single-cycle 9-tree Tower Karatsuba `Ext4` MAC |
| **Real `QSAGSTA1` Role-2 (Poseidon2 Canopy)** | 26,716 | **227,255** (`218,986` core) | **0** (`148` words) | `0.43 ms` at ASAP7 `531.7 MHz`; tampered proof cleanly rejected (`trace_sta1_p2_tamper`) |
| **Real `QSAGSTA1` Role-1 (TurboSHAKE Canopy)** | 22,661 | **64,926** (`56,631` core) | **0** (`36` words) | `0.12 ms` at ASAP7 `531.7 MHz`; tampered proof cleanly rejected (`trace_sta1_ts_tamper`) |
| **Real `[CWYZ26]` DuetFold** | 433 | **1,156** (`784` core) | **0** (`6` words) | Tampered claim cleanly rejected (`trace_duet_comp_tamper`) |
| **16-variable `Ext4` table fold (`65,535` pairs)** | 262,466 | **852,292** (`147,571` fold) | **0** (`5` words) | 16 in-place fold rounds |

## Repository Layout

- `gen/`: `qsag_ref.py` (bit-exact Python oracle), `csagen.py` & `gen_rtl.py` (Solinas–Karatsuba + Poseidon2 CSA/RTL emitters), `gen_vectors.py` (unit, real-proof, and tamper trace generators).
- `rtl/`: `qsag_asic_gl64_csa.sv`, `qsag_asic_ext4_p2_shared.sv`, `qsag_asic_keccak_clmul.sv`, `qsag_ni_asic_top.sv`, `sram_dp_blackbox.sv`, plus generated `*_gen.sv`.
- `lec/` & `obend/`: Compositional Z3/Bitwuzla SMT miters (`run_lec.sh`, `lec_composed.py`, `lec_anf.py`, `lec_csa.py`) and Lean 4 `Obend` hardware emitters (`obend/QsagNi.lean`).
- `synth/`: `run_synth.sh` / `summarize.py` (stage & flat synthesis), `run_hier.py` (4-PDK hierarchical synthesis), `run_sta.py` (7-corner OpenSTA), `run_openroad.py` & `render_routed_png.py` (Symmetric 4-SRAM Basin-1 OpenROAD floorplan, CTS, global/detailed routing, DRC=0 signoff, and PNG layout renderer), `RESULTS.md`.
