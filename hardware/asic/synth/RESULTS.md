# QSAG-NI v2 ASIC Logic-Area & Foundry Library Characterization (`IHP SG13G2` & `Sky130 HD`)

> **Deployment & Scope Note:** `qsag_ni_asic_top` (`~660–720 kGE` logic + external SRAM) is a full-rate WHIR / `zk-Hem v2` hardware proof-verifier datapath (~`4.8–8.8 mm²` in 130 nm CMOS — far larger than a `1.73 mm²` `GF180MCU` `SLOT_0P5X0P5` shuttle slot). Its real deployable hardware targets in this repository are **Lattice `ECP5-85F`** ([`hardware/fpga/`](../../fpga)) and **AWS EC2 F2 `VU47P`** ([`hardware/aws_f2/`](../../aws_f2)), while our manufacturable `SLOT_0P5X0P5` tapeout enclave is **`ASS2-0P5 / Dregg-64`** ([`hardware/ass2/`](../../ass2)).
>
> Earlier synthesis/OpenROAD comparisons using non-manufacturable academic libraries (`Nangate45`, `ASAP7`) and unverified `sram_dp_64x16384_bank` LEF blackbox stubs have been demoted to [`history/academic-pdk-cosplay/`](../../../history/academic-pdk-cosplay) (see [`history/README.md`](../../../history/README.md)).

`kGE` = mapped standard-cell area divided by the foundry library's 2-input NAND gate (`sky130`: `sky130_fd_sc_hd__nand2_1 = 3.7536 um^2`, `ihp130`: `sg13g2_nand2_1 = 7.2576 um^2`). Dual-port SRAM banks are blackboxed during logic synthesis and excluded from standard-cell `kGE`.

---

## 1. Hierarchical Manufacturable-PDK Logic Synthesis (`synth/hier/{ihp130,sky130}/result.json`)

Shared 9-multiplier Solinas–Karatsuba carry-save architecture (`qsag_asic_ext4_p2_shared.sv` + `qsag_fp5_seq.sv`):

| Foundry PDK | `NAND2` (`um^2`) | Total Stdcell Area (`um^2`) | **Whole-Top Stdcell (`kGE`)** | Sequential (`kGE`) | Mapped Cells |
|---|---:|---:|---:|---:|---:|
| **IHP SG13G2 (130 nm)** | 7.2576 | 4,793,182.54 | **660.44 kGE** | 71.42 | 416,430 |
| **Sky130 HD (130 nm)** | 3.7536 | 2,703,155.04 | **720.15 kGE** | 84.39 | 394,730 |

### Per-Submodule Breakdown (`kGE` / Zero-Wireload ABC `stime` `ns`)

| Submodule | Instances | IHP SG13G2 (`kGE` / `ns`) | Sky130 HD (`kGE` / `ns`) |
|---|---:|---:|---:|
| `qsag_gl64_mul_csa` (Solinas–Karatsuba 64×64 mod $p$) | 9 | 29.24 / 10.44 | 32.16 / 14.02 |
| `qsag_p2_me` (Poseidon2 external $M_E$ + RC) | 1 | 58.68 / 14.03 | 66.12 / 21.06 |
| `qsag_p2_mi_tail` + `qsag_p2_mi_apply` ($M_I$) | 1 + 1 | 34.67 / 9.92 | 39.13 / 14.41 |
| `qsag_p2_canopy_ff` (Jive/Canopy feed-forward) | 1 | 7.56 / 7.33 | 8.29 / 10.46 |
| `qsag_keccak_round` (2 rounds/clk `Keccak-p[1600]`) | 2 | 11.49 / 1.05 | 13.39 / 1.78 |
| `qsag_gf128_mul` (Karatsuba CLMUL + `0x87` reduce) | 1 | 22.01 / 3.04 | 24.81 / 5.48 |
| `qsag_tower128_to_poly` + `poly_to_tower128` | 2 + 1 | 8.37 / 1.45 | 9.68 / 2.86 |
| `qsag_ni_asic_top` (controller, muxes, glue, FFs) | 1 | 207.76 / 8.59 | 216.32 / 12.80 |

---

## 2. Pre-Layout Static Timing Characterization (`OpenSTA 3.1.0`, Ideal Wireload)

| Foundry PDK | Corner | Min Period (`ns`) | **Pre-Layout Fmax (`MHz`)** | Total Power (`mW`) | Leakage (`mW`) |
|---|---|---:|---:|---:|---:|
| **IHP SG13G2** | `ff_m40C_1v32` | **37.63** | **26.57** | 187.840 | 0.1383 |
| **IHP SG13G2** | `tt_025C_1v20` | **56.99** | **17.55** | 117.490 | 0.0598 |
| **IHP SG13G2** | `ss_125C_1v08` | **89.28** | **11.20** | 61.161 | 0.2606 |
| **Sky130 HD** | `tt_025C_1v80` | **151.32** | **6.61** | 112.930 | 0.0010 |
