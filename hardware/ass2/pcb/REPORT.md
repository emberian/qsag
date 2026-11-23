# ASS2-0P5 verification report

On 2026-11-21, KiCad 8.0.3 reported **zero schematic ERC violations**. Its XML netlist agreed pin-for-pin with the independent Python reconstruction. Both custom footprints passed native DRC in a four-layer fixture. The local macOS KiCad 8.0.3 installation supplied `kicad-cli`.

| Check | Observed result |
|---|---|
| Schematic and library | 147 physical component references, 456 physical symbol pins, 92 named nets. All embedded definitions match the project symbol library. Every assigned footprint has the numbered pads required by its symbol. |
| Bare die | 56/56 numbered pads match the slot YAML, the datasheet diagram and numbered table, and the actual placed DEF. Four analog pads are open. The additional EP terminal is grounded. |
| Bond pattern | 52 bonded die pads, 54 wire projections, zero projected wire crossings or overflights of other exposed bond fingers. Nine plated 0.30 mm drills on the die paddle. Each southern supply has two distinct die sites, two exposed fingers and a copper bridge between its fingers. |
| Input bias | The eight combinations of host translation, auxiliary LDO and ASK population passed the fitted-input DC bias check. The DQ buses have idle bias during tri-state intervals. |
| Critical connections | RECT and V5_CHIP are distinct. The gate clamps return to RECT/GND. Q1 and Q2 source to GND, with chip-side drain pullups. All four FRAM signals stay on the private anchor bus and probes. |
| Coil | Sixteen contiguous winding legs, four turns, 40.00 mm square outer copper envelope, 33.28 mm inner dimension, 0.42 mm width and 0.56 mm interturn gap. Including its feeds, the footprint has 598.24 mm of planar copper centerline. |
| Antenna window | The 46 × 46 mm region prohibits traces, vias and pours on In1.Cu, In2.Cu and B.Cu. Additional rules prohibit pads throughout the window except the inner barrel and the L4 crossover corridor. |
| Native footprint DRC | Zero violations, zero unconnected pad groups, zero footprint errors. Deliberately placing a trace inside the window produced a keepout violation on each protected layer. |
| Negative controls | The standalone checker rejected removal of the external clock input wire, a direct RECT-to-V5_CHIP connection, a FRAM data-label substitution and a change from 0.42 to 0.45 mm on one winding segment. |
| Assembly | 78 fitted base components and two default shunts. The 25 printed references are the coil and 24 probe lands. Option quantities are separate from base quantities. |

## What the physical sources establish

The slot fixes die dimensions and pad instance order. The 2,000 DBU/µm placed DEF supplies 56 individual Metal5 terminal positions and 60 × 60 µm terminal rectangles, including the four physical ports on each of its two supply nets. South runs west-to-east and east runs south-to-north. North also runs west-to-east and west also runs south-to-north. A continuously counterclockwise renumbering would misassign both of those banks. The design preserves the coordinates and numbering supported by all three sources.

Only the die outline and Metal5 windows come from the silicon placement. Wire landing targets, wedge dimensions, finger spacing and the thermal array are carrier design choices. The pad 3 bond spans are 0.787 and 0.731 mm in projection. The pad 4 spans are 0.722 and 0.769 mm. Actual loops are longer. The 0.9 nH and 125 mΩ south-bond values are PDN model inputs. Wire geometry, coupling, ground return and the bonding process determine their realized values. [Bond schedule](BOND_MAP.csv)

## Coil model readback

The checker measures the serialized pad primitives, counts the winding legs, verifies their direction and pitch, follows both terminals through the crossover and checks the four-layer stackup. It passes the measured geometry and specified finished copper thickness to the reference calculator and runs the calculator's seven self-tests.

| Quantity | Reference calculation at 13.56 MHz, 25 °C |
|---|---:|
| Nominal current-sheet inductance | 1.4662 µH |
| Modified Wheeler / monomial cross-checks | 1.3767 / 1.5780 µH |
| AC series resistance | 0.9881 Ω |
| Effective self-capacitance | 1.866 pF |
| Target total capacitance / nominal trimmer setting | 93.954 / 8.888 pF |
| Estimated loaded Q / −3 dB bandwidth | 17.88 / 758.6 kHz |
| Predicted trimmer frequency span | 13.139–14.006 MHz |

The calculator models the bare copper geometry, feed allowance and front-end stray loading. Etch tolerance, return environment, the rectifier, the optional ASK branch and the populated board affect the measured result. VNA tuning and cold-rail current measurements remain open. A board-level routing DRC and assembly qualification also remain open.

## Electrical decisions made in the carrier

- J2 retains the Rev. 1.0 5 V pinout. J9 supplies the designated 3.3 V interface using U4/U5. Dedicated ×1 MOSI through U5 and removable JP6 allow simultaneous MOSI/MISO. U4 handles the complete wide bus after the link is opened.
- U6 receives a separate nominal 7 V input. JP2 selects bench 5 V or LDO output upstream of JP1. The chosen 22 µF capacitors provide nominal capacitance margin on VIN, VOUT and VREG. U6 uses the SOIC exposed pad tied to ground. [ADM7150 datasheet](https://www.analog.com/media/en/technical-documentation/data-sheets/ADM7150.pdf)
- U7 and its envelope network implement the reserved ASK evaluation circuit. The detector runs from RECT, with the chip input biased from V5_CHIP when Q2 and JP7 are absent. Its loaded RF performance and protocol behavior have not been measured.
- The schematic uses numeric suffixes on assembly-schedule aliases, including RD1, RG1, CB1 and CT4. CT1–CT3 remain the RF tuning bank. CT4 is the 10 nF tamper capacitor. Short SMA routes and a ground via adjacent to each bypass remain constraints on the eventual board placement.

## Repeating the evidence

The source directory contains the calculator and slot YAML, plus verbatim extracts of the Typst pad definitions and the DEF terminal section. The checker also passed using the complete original Typst file, the compressed placed DEF and the calculator in the read-only source tree. To repeat the latter run from this package in the supplied workspace, use the command below.

```sh
python3 -B verify_carrier_erc.py --self-test \
  --datasheet ../datasheet/dregg64-ass2-datasheet.typ \
  --slot ../pnr/librelane/slot_0p5x0p5.yaml \
  --def-file "${ASS2_PNR_ARTIFACTS:-../pnr/artifacts}/placed.def.gz" \
  --calculator /Users/ember/dev/qsag/hardware/gf180mcu/pcb/planar_nfc_coil_calc.py
```

| Compared input | SHA-256 |
|---|---|
| Full Rev. 1.0 Typst source | `39598888b58dc296bd821df1884079b5dd0b45eb548efb464c2708f8db2a9e63` |
| Placed DEF, gzip file | `97ec3a1053af1a771a6dc8d8989556694b3cf00abbd7ef072699802b9c4a47a9` |
| SLOT_0P5X0P5 YAML | `683e070cbd1137c4f3673aaa0eee92de97e749c71a5c51f42e56d0185c1a5a69` |
| Planar coil calculator | `34d51a9d9d0a2312d89facb2a74ce98287bb765115cabc85cb821c94b3268c6b` |

Standalone ERC reads both symbol definitions and actual transformed symbol pin locations. It joins connected wire points and labels, rejects ambiguous or unlabeled islands, and checks the resulting graph against the component pin contract. Bias checking follows fitted resistive paths and available drivers. It establishes a DC path under the listed population assumptions. Logic thresholds, dynamic contention during host turnaround, injection currents and supply impedance require electrical characterization. Native KiCad ERC and the independent XML comparison provide a second interpretation of the saved schematic.
