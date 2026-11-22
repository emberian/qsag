# QSAG-NI ASIC Synthesis, STA, and Physical Signoff Results

kGE = mapped standard-cell area / area of the library's 2-input NAND gate (`sky130`: `sky130_fd_sc_hd__nand2_1 = 3.7536 um^2`, `ihp130`: `sg13g2_nand2_1 = 7.2576 um^2`, `nangate45`: `NAND2_X1 = 0.798 um^2`, `asap7`: `NAND2xp5_ASAP7_75t_R = 0.05832 um^2`). The 512 KiB SRAM (`4 x sram_dp_64x16384_bank`) is instantiated as hard dual-port SRAM macros and excluded from standard-cell kGE.

## 1. Hierarchical Timing-Driven Whole-Top Synthesis (`synth/hier/*/result.json`)

Shared 9-multiplier Solinas–Karatsuba carry-save architecture (`qsag_asic_ext4_p2_shared.sv`: 9 `qsag_gl64_mul_csa` trees shared across 1-cycle Tower Karatsuba `Ext4` multiply-add and `9+3` split Poseidon2-12 S-boxes):

| Library | NAND2 (`um^2`) | Total Stdcell Area (`um^2`) | **Whole-Top Stdcell (`kGE`)** | Sequential (`kGE`) | Mapped Cells | vs. `954 kGE` Budget |
|---|---:|---:|---:|---:|---:|---:|
| **Sky130 HD** | 3.7536 | 2,703,155.04 | **720.15 kGE** | 84.39 | 394,730 | `-24.5%` |
| **IHP SG13G2** | 7.2576 | 4,793,182.54 | **660.44 kGE** | 71.42 | 416,430 | `-30.8%` |
| **Nangate45** | 0.7980 | 539,621.17 | **676.22 kGE** | 59.96 | 434,460 | `-29.1%` |
| **ASAP7 (RVT TT)** | 0.05832 | 38,210.52 | **655.19 kGE** | 66.13 | 385,146 | `-31.3%` |

### Per-Macro Hierarchical Breakdown (`kGE` / ABC `stime` `ns`)

| Submodule | Instances | Sky130 (`kGE` / `ns`) | IHP130 (`kGE` / `ns`) | Nangate45 (`kGE` / `ns`) | ASAP7 (`kGE` / `ns`) |
|---|---:|---:|---:|---:|---:|
| `qsag_gl64_mul_csa` (Solinas–Karatsuba 64x64 mod p) | 9 | 32.16 / 14.02 | 29.24 / 10.44 | 30.48 / 3.77 | 28.52 / 2.24 |
| `qsag_p2_me` (Poseidon2 external `M_E` + RC) | 1 | 66.12 / 21.06 | 58.68 / 14.03 | 60.37 / 4.95 | 59.33 / 3.34 |
| `qsag_p2_mi_tail` + `qsag_p2_mi_apply` (`M_I`) | 1 + 1 | 39.13 / 14.41 | 34.67 / 9.92 | 36.13 / 3.54 | 35.36 / 2.28 |
| `qsag_p2_canopy_ff` (Jive/Canopy feed-forward) | 1 | 8.29 / 10.46 | 7.56 / 7.33 | 7.70 / 2.49 | 7.45 / 1.58 |
| `qsag_ext4_kara_inputs` + `combine` (9-mul `Ext4`) | 1 + 1 | 29.17 / 18.02 | 25.97 / 13.13 | 27.20 / 4.18 | 26.01 / 3.00 |
| `qsag_keccak_round` (2 rounds/clk Keccak-p[1600]) | 2 | 13.39 / 1.78 | 11.49 / 1.05 | 11.67 / 0.42 | 13.26 / 0.25 |
| `qsag_gf128_mul` (Karatsuba CLMUL + `0x87` reduce) | 1 | 24.81 / 5.48 | 22.01 / 3.04 | 21.99 / 1.19 | 24.05 / 0.68 |
| `qsag_tower128_to_poly` + `poly_to_tower128` | 2 + 1 | 9.68 / 2.86 | 8.37 / 1.45 | 8.26 / 0.60 | 9.40 / 0.36 |
| `qsag_ni_asic_top` (controller, muxes, glue, FFs) | 1 | 216.32 / 12.80 | 207.76 / 8.59 | 207.92 / 2.66 | 200.72 / 1.68 |

## 2. Flat Whole-Top Synthesis (`abc -fast`, `synth/logs/summary.txt`)

| Library | Cell Area (`um^2`) | **Flat Stdcell (`kGE`)** | Flip-Flops (`um^2`) | vs. `954 kGE` Budget |
|---|---:|---:|---:|---:|
| **sky130** | 3,344,491 | **891 kGE** | 316,763.8 | `-6.6%` |
| **ihp130** | 5,913,732 | **815 kGE** | 518,350.5 | `-14.6%` |
| **nangate45** | 661,593 | **829 kGE** | 47,847.3 | `-13.1%` |
| **asap7** | 53,285 | **914 kGE** | 3,856.8 | `-4.2%` |

## 3. Standalone Stage Characterization (`synth/summarize.py`)

| module / stage | adders | sky130 kGE | ihp130 kGE | nangate45 kGE | asap7 kGE | sky130 ns | ihp130 ns | nangate45 ns | asap7 ns |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `qsag_gl64_fold` | bk | 5.2 | 4.6 | 5.0 | 4.2 | 2.87 | 2.04 | 0.70 | 0.41 |
| `qsag_gl64_mul_csa` | bk | 33.6 | 39.2 | 34.3 | 29.2 | 13.39 | 9.54 | 3.15 | 1.93 |
| `qsag_gl64_mul_tree` | bk | 26.0 | 24.9 | 25.6 | 23.4 | 5.99 | 4.09 | 1.46 | 0.81 |
| `qsag_keccak_round` | bk | 20.8 | 11.9 | 12.7 | 14.0 | 1.64 | 0.97 | 0.39 | 0.21 |
| `stage_ext4` | bk | 341.6 | 532.4 | 342.1 | 299.4 | 40.15 | 36.66 | 9.09 | 5.85 |
| `stage_gf128` | bk | 25.8 | 23.2 | 22.8 | 24.9 | 4.10 | 2.46 | 0.89 | 0.50 |
| `stage_keccak2` | bk | 40.6 | 23.7 | 25.1 | 28.2 | 3.40 | 2.07 | 0.78 | 0.43 |
| `stage_me` | bk | 73.9 | 111.5 | 78.3 | 65.4 | 17.37 | 13.06 | 3.87 | 2.44 |
| `stage_partial` | bk | 35.9 | 42.6 | 34.6 | 30.9 | 7.77 | 5.67 | 1.71 | 1.07 |
| `stage_partial` | ks | 41.8 | 51.9 | 43.5 | 36.8 | 7.33 | 5.26 | 1.69 | 0.97 |
| `stage_reduce` | bk | 2.0 | 1.8 | 2.0 | 1.8 | 4.38 | 3.34 | 1.13 | 0.69 |
| `stage_reduce` | ks | 3.1 | 2.7 | 3.1 | 2.5 | 4.29 | 2.98 | 1.02 | 0.63 |
| `stage_reduce_ref` | bk | 2.2 | 2.1 | 2.4 | 2.1 | 8.70 | 5.35 | 1.79 | 1.12 |
| `stage_reduce_ref` | ks | 3.2 | 3.3 | 3.6 | 3.1 | 7.23 | 4.68 | 1.57 | 1.03 |
| `stage_sbox` | bk | 34.4 | 41.0 | 35.9 | 29.8 | 13.15 | 9.85 | 3.22 | 1.88 |
| `stage_sbox` | ks | 36.9 | 44.9 | 38.9 | 31.1 | 12.55 | 9.06 | 3.07 | 1.82 |
| `stage_sbox_ref` | bk | 40.3 | 45.6 | 38.0 | 36.3 | 17.57 | 12.21 | 3.81 | 2.42 |
| `stage_sbox_ref` | ks | 41.9 | 48.1 | 42.7 | 39.1 | 14.52 | 10.89 | 3.44 | 2.10 |
| `stage_tower128` | bk | 60.3 | 73.4 | 49.3 | 54.0 | 7.89 | 6.26 | 1.75 | 1.01 |

## 4. Multi-Corner Static Timing & Power (`OpenSTA 3.1.0`, `synth/hier/opensta_summary.json`)

| Library | Corner | Wire-Load Model | Min Period (`ns`) | **Fmax (`MHz`)** | Target Period (`ns`) | Total Power (`mW`) | Leakage (`mW`) |
|---|---|---|---:|---:|---:|---:|---:|
| **ASAP7** | `rvt_tt_025C_0v70` | `ideal` | **1.8808** | **531.70** | 2.0 | **15.883** | 0.0206 |
| **Nangate45** | `tt_ideal` | `ideal` | **19.3900** | **51.57** | 3.5 | 124.990 | 12.2580 |
| **Nangate45** | `tt_wlm_5K` | `5K_hvratio_1_1` | **25.7800** | **38.79** | 4.0 | 126.630 | 12.2580 |
| **IHP130** | `ff_m40C_1v32` | `ideal` | **37.6300** | **26.57** | 10.0 | 187.840 | 0.1383 |
| **IHP130** | `tt_025C_1v20` | `ideal` | **56.9900** | **17.55** | 12.0 | 117.490 | 0.0598 |
| **IHP130** | `ss_125C_1v08` | `ideal` | **89.2800** | **11.20** | 18.0 | 61.161 | 0.2606 |
| **Sky130** | `tt_025C_1v80` | `ideal` | **151.3200** | **6.61** | 15.0 | 112.930 | 0.0010 |

## 5. OpenROAD Basin-1 Physical Implementation (`synth/hier/openroad_all_summary.json`)

Symmetric 4-SRAM Basin-1 floorplan (`2` West `R90` banks with East/inward pin strips + `2` East `R270` banks with West/inward pin strips; all 4 `sram_dp_64x16384_bank` macros and all 1,156 macro pins verified strictly inside core):

| Metric | **Nangate45 Basin-1 (Full Routed Signoff)** | **Sky130 HD Basin-1 (Post-CTS Signoff)** |
|---|---|---|
| Stage | Floorplan + Placement + CTS + Global Route + **TritonRoute `detailed_route` (`DRC=0`)** + STA/Power | Floorplan + Placement + CTS + Detailed Placement + STA/Power |
| Die Dimensions | **`1480 x 1480 um` (`2.1904 mm^2`, `-8.8%` vs `1550 x 1550 um`)** | **`2960 x 2960 um` (`8.7616 mm^2`, `-24.2%` vs `3400 x 3400 um`)** |
| SRAM Banks Placed | `4` (`2` West `R90` + `2` East `R270`, inward pins on `metal3`) | `4` (`2` West `R90` + `2` East `R270`, inward pins on `met3`) |
| Total Design Area | `649,436.0 um^2` (`31.0%` core utilization) | `3,202,026.0 um^2` (`39.0%` core utilization) |
| Post-PnR Stdcell Area | `542,933.9 um^2` = **`680.37 kGE`** (`432,827` stdcells + `1,629` CTS bufs) | `2,757,599.8 um^2` = **`734.65 kGE`** (`4,673` CTS bufs) |
| Global Route Overflow | **`0 / 0 / 0`** (`37.07%` usage, `metal2..metal10`) | — |
| Detailed Route Wirelength / Vias | **`16,211,371 um` (`16.21 m`) / `3,438,384` vias** | — |
| **TritonRoute DRC Violations** | **`0` (`routed_drc.rpt` = `0` bytes)** | — |
| Setup Min Period / Fmax | **`25.7805 ns` / `38.79 MHz`** (`WNS = -15.7805 ns` vs `10.0 ns` target, `5K_hvratio_1_1`) | **`160.7204 ns` / `6.22 MHz`** (`WNS = -140.7204 ns` vs `20.0 ns` target) |
| Hold WNS | **`+0.1011 ns` (`0` hold violations)** | **`+0.4688 ns` (`0` hold violations)** |
| Total / Leakage Power | **`64.370 mW` / `12.332 mW`** (at `100 MHz` ref activity `0.15`) | **`111.380 mW` / `0.001 mW`** (at `50 MHz` ref activity `0.15`) |
| Layout Render | `synth/hier/nangate45/openroad/routed_basin1.png` (`1600x1600`) | — |
