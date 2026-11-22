# ASS2-0P5 physical implementation

The hbox run uses GF180MCU-D with the foundry 7-track 5 V library. The full run directory is `hbox:dregg180-astra:/work/ass2-pnr`. LibreLane and OpenROAD use eight threads. The chip implements two independent physical clocks, with a 40 ns core target and a 50 ns HOST_SCK target.

## Floorplan and pad ring

| Feature | Physical result |
|---|---|
| Die | 1,936 × 2,531 µm, 2,000 DEF database units per µm |
| Requested core | (442, 442) to (1,494, 2,089) µm |
| SRAM0, data | (490, 500) to (921.86, 984.88) µm, orientation N |
| SRAM1, instruction | (970, 500) to (1,454.88, 931.86) µm, orientation E |
| SRAM keepout | 10 µm row-cut halo on each axis, 48.14 µm between SRAM bodies |
| Package pads | 48 signal and 8 supply pads, 11 south, 17 east, 11 north, 17 west |
| Corner structures | Four foundry ring corners, five wafer.space macros including the logo |
| Global placement | 40,484 DEF components, including pad spacers, corners, taps and endcaps |
| Detailed placement | 42,796 DEF components, zero placement violations, 3,846,040 µm estimated wirelength |

The input RTL matches the upstream SHA-256 manifest. The isolated core synthesis reproduced 767,999.5008 µm² of standard-cell area. The physical SRAM LEF measures 431.86 × 484.88 µm per macro, or 418,800.55 µm² for both. Using those footprints gives 1,186,800.05 µm² before pad-ring logic and physical-only cells, or 68.50% of the requested core rectangle. The upstream area budget used a slightly larger per-SRAM estimate.

The chip wrapper follows the slot pin order and preserves the 38 programmable bidirectional pads from the ASS2 wrapper. Reading back the emitted DEF and its PDK LEFs confirmed all eight HOST_DQ masters are `gf180mcu_fd_io__bi_t`. Their PDRV1, PDRV0 and SL pins have physical tie-cell drivers for 0, 1 and 1 respectively. The foundry assigns those settings to 8 mA and slow slew. [Foundry I/O control table](https://gf180mcu-pdk.readthedocs.io/en/latest/IPs/IO/gf180mcu_fd_io/digital.html)

Each SRAM has VDD and VSS connected and a dedicated orientation-specific PDN grid. OpenROAD's power-grid checker reported all shapes connected on both supplies. PDN generation reported 14 skipped candidate vias on Metal1–Metal4 and Metal3–Metal4.

[Placed-cell floorplan](ass2_0p5_placed_def.png) · [Legalized DEF](artifacts/placed.def.gz) · [Legalized ODB](artifacts/placed.odb.gz) · [Chip wrapper](src/chip_top.sv) · [Physical settings](librelane/ass2.yaml) · [Timing constraints](librelane/ass2.sdc)

## Timing assumptions

The two clocks originate at the package pads and are asynchronous to one another. The SDC uses 0.25 ns uncertainty and 0.15 ns transition. The HOST_DQ input budget is 0–4 ns relative to falling HOST_SCK, with output delays of −1/4 ns relative to rising HOST_SCK. These are working interface assumptions inherited from the reference host interface. The load is 0.05 pF. Other external interfaces have no board timing budget in this run. Package and board signoff require their actual loads and delays.

## Clock trees and post-CTS timing

CTS inserted 756 clock buffers and made 756 subnets across 130 roots, serving 4,721 sinks. OpenROAD legalized the clock-tree checkpoint. The independent post-CTS audit loads the same ODB separately for each PVT, uses the PDK nominal Metal2–Metal4 RC settings, propagates both clocks and reports each clock's worst path. [CTS report](artifacts/reports/30-openroad-cts/cts.rpt) · [STA driver](postcts_sta.tcl)

| Nominal RC, immediately after CTS | Core setup / hold (ns) | HOST_SCK setup / hold (ns) | Setup / hold TNS (ns) |
|---|---:|---:|---:|
| [TT, 25 °C, 5.00 V](artifacts/reports/postcts/tt_025C_5v00.log) | −14.414 / −0.143 | +7.300 / +0.688 | −5,415.478 / −0.266 |
| [FF, −40 °C, 5.50 V](artifacts/reports/postcts/ff_n40C_5v50.log) | 0.000 / −0.224 | +13.733 / +0.335 | 0.000 / −0.503 |
| [SS, 125 °C, 4.50 V](artifacts/reports/postcts/ss_125C_4v50.log) | −59.703 / +0.068 | −7.512 / +1.506 | −44,064.402 / 0.000 |

At TT the worst core setup path runs from instruction register bit 9 to the register bank's write-hold register bit 7. The host domain meets both TT checks at 20 MHz. The core misses its 25 MHz setup target at TT and SS. Hold-first timing repair inserted 24 buffers with a 0.12 ns target margin and reduced estimated hold TNS to zero. Routing uses the saved, legalized hold-repair database. Setup optimization selected 3,782 violating endpoints in the unrestricted pass and 37 in the bounded pass. Neither pass produced a saved setup-repaired database before routing.

The global router repeatedly relaxed CTS spacing on clock-gate subnets. The routing input uses normal PDK spacing on 254 of the 266 subnets that had a CTS nondefault rule and keeps that rule on 12 primary-tree subnets. Global routing uses the available Metal2–Metal5 tracks with zero additional capacity reserve. The run restarted against a private installation of the identical PDK revision, `792ef67037d74c8c51811eab3ce23cf793491296`, after the shared installation disappeared. [Routing input ODB](artifacts/route_input.odb.gz)

## Global routing

OpenROAD generated guides for 33,717 nets. The global router estimated 7,757,794 µm of wire and 383,497 vias. Total routing demand was 754,651 against 1,594,934 units of capacity. Congestion was local enough that the 47.32% average usage masked substantial overflow. [Global routing log](artifacts/reports/01-openroad-globalrouting/openroad-globalrouting.log) · [Route guides](artifacts/global.guide.gz)

| Routing layer | Usage | Total overflow |
|---|---:|---:|
| Metal2 | 55.56% | 3,260 |
| Metal3 | 55.90% | 3,945 |
| Metal4 | 42.82% | 2,710 |
| Metal5 | 30.52% | 1,156 |
| **Total** | **47.32%** | **11,071** |

The detailed router was given these guides with residual overflow. The global router's wirelength and via counts are estimates, and overflow counts measure oversubscribed routing resources. Detailed-routing rule violations are counted independently.
