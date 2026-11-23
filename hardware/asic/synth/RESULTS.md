# QSAG-NI v2 foundry synthesis and timing

The complete pure-quintic (`Fp5 = F_p[X]/(X^5 - 3)`, zero quartic residue) `QSAG-NI v2` design was mapped using Yosys at the typical corner of each manufacturable 130 nm open foundry library (`IHP SG13G2` and `Sky130 HD`). The flow links the mapped datapath, controller, and initialized synchronous 32 KiB ROM (`4,096 × 64-bit`). Four 128 KiB dual-port SRAM banks (`512 KiB` total) are area and timing black boxes. A `kGE` is 1,000 library `NAND2` gates by area (`7.2576 µm²` on `IHP SG13G2`, `3.7536 µm²` on `Sky130 HD`).

> **Library note:** `IHP SG13G2` and `Sky130 HD` are the manufacturable 130 nm foundry targets. `Nangate45` (`FreePDK45`) and `ASAP7` are purposely non-manufacturable academic reference libraries and are excluded from foundry signoff. Foundry tapeout signoff requires characterized SRAM/ROM macros, extracted parasitic SPEF interconnect, DRC/LVS, and multi-corner physical signoff.

[Foundry synthesis & OpenSTA log](logs/foundry_synth_sta.log)

## Mapped standard-cell area (pure Quintic `Fp5`)

| Library | `NAND2` (`µm²`) | `AUTO_VERIFY=0` (`kGE`) | `AUTO_VERIFY=1` (`kGE`) | Autonomous Engine excl. ROM (`kGE`) | Synchronous 32 KiB ROM (`kGE`) | Top-level Auto Glue (`kGE`) |
|---|---:|---:|---:|---:|---:|---:|
| **IHP SG13G2** | 7.2576 | **660.996** | **709.610** | 22.994 | 21.068 | 4.552 |
| **Sky130 HD** | 3.7536 | **734.229** | **784.540** | 24.718 | 21.957 | 3.636 |

Engine area excludes the synchronous ROM column (`4,096 × 64-bit`, `25,448` bytes active firmware + constants). Disabling autonomous verification (`AUTO_VERIFY=0`) removes the autonomous engine, the synchronous ROM, and the top-level SRAM/register-file mux glue (`-48.614 kGE` total on `IHP SG13G2`, `-50.311 kGE` total on `Sky130 HD`) and makes `0x50` fail closed (`verify_fail <= 1'b1`).

## OpenSTA pre-layout static timing (`IHP SG13G2` 3-corner + `Sky130 HD` TT)

The ideal reference clock constraint in `synth/run_foundry_v2.py` is `100 ns` (`10 MHz`) with zero I/O delays across unbuffered pre-layout Yosys netlists (SRAM macros modeled as black boxes). All eight unbuffered pre-layout analyses fail that `100 ns` constraint (`-202.93 ns` to `-645.59 ns` worst negative slack). Physical timing closure requires hierarchical buffering, floorplanning, clock-tree synthesis, characterized SRAM macro `.lib`s, and extracted interconnect. [Mapping and STA script](run_foundry_v2.py)

| Library and corner | Min period, `AUTO_VERIFY=0` (`ns`) | Slack, `AUTO_VERIFY=0` (`ns`) | Min period, `AUTO_VERIFY=1` (`ns`) | Slack, `AUTO_VERIFY=1` (`ns`) |
|---|---:|---:|---:|---:|
| **IHP SG13G2 TT** (`1.20 V, 25 °C`) | 488.22 | -388.2245 | 505.88 | -405.8846 |
| **IHP SG13G2 FF** (`1.32 V, −40 °C`) | 302.93 | -202.9302 | 314.15 | -214.1516 |
| **IHP SG13G2 SS** (`1.08 V, 125 °C`) | 719.59 | -619.5864 | 745.59 | -645.5927 |
| **Sky130 HD TT** (`1.80 V, 25 °C`) | 706.07 | -606.0749 | 694.02 | -594.0190 |

## Synchronous FPGA BRAM ROM inference

The synchronous-read `4,096 × 64-bit` (`32 KiB`) `qsag_auto_rom` infers pure dedicated block RAM with **zero fabric LUTs** on both FPGA targets:
- **AMD Virtex UltraScale+ (`synth_xilinx -family xcup`):** `8 × RAMB36E2`, `0` LUTs ([bram_xilinx.log](logs/bram_xilinx.log))
- **Lattice ECP5-85F (`synth_ecp5`):** `16 × DP16KD`, `0` LUTs ([bram_ecp5.log](logs/bram_ecp5.log))
