# ASS2-0P5 reference carrier

Open [the KiCad 8 project](ass2_0p5_carrier.kicad_pro) and select the schematic. The default assembly brings up the bare die from a current-limited 5.0 V bench supply, with a keyed 5 V SPI port, private FRAM and a cold-rail NFC carrier detector. The optional assemblies add a 3.3 V host port, a regulated auxiliary input and an ASK detector.

| Design file | Use |
|---|---|
| [Schematic](ass2_0p5_carrier.kicad_sch) · [SVG](ass2_0p5_carrier.svg) | Flat circuit drawing with labeled connections. A cross marks each default DNP component. |
| [Symbol library](ass2_0p5.kicad_sym) · [footprint library](ass2.pretty/) | Project-relative library tables resolve both custom libraries. Install the standard KiCad 8 footprints for commercial packages. |
| [Production BOM](BOM_ASS2_0P5.csv) | One row per reference, with MPN, footprint, base and option quantities. Printed copper and shunts are identified separately. |
| [Pin-level netlist](NETLIST_ASS2_0P5.csv) | One row per physical symbol pin. Includes optional components, NCs and the die paddle. |
| [Land-pattern drawing](land_patterns.svg) · [bond schedule](BOND_MAP.csv) | Numbered fingers, individual die sites, PCB destinations and projected bond spans. |
| [Stackup](stackup.kicad_sexpr) · [verification report](REPORT.md) | Four-layer KiCad stackup used for footprint DRC, machine results and physical qualification limits. |

## Power and first bring-up

1. Fit the base BOM. Install the JP1 current-measurement shunt and one shunt on JP2 pins 1–2. Apply current-limited 5.0 V to J1 pin 1, with pin 2 as ground. For an ammeter, open JP1 and connect the meter across its two pins. TP1, TP2 and TP3 expose the bench input, selected feed and chip rail.
2. The pull resistors select the external clock and boot mode 00 with JP3–JP5 open. J6 pin 1 accepts a 5 V-level clock, and pin 2 is ground. Each three-pin strap has 5 V on pin 1, its signal on pin 2 and ground on pin 3. JP3 selects the external clock, JP4 sets BOOT_MODE0 and JP5 sets BOOT_MODE1.
3. Observe the supervisor at TP4 and CLK_IN/16 at TP6. U2 drives RST_N through 100 Ω with a 100 kΩ chip-side pulldown. Its nominal 4.38 V threshold and 200 ms release delay apply to this population. [TPS3839 datasheet](https://www.ti.com/lit/ds/symlink/tps3839.pdf)
4. Connect the normally open tamper contact across J5. Closing it discharges the 10 nF sense capacitor through 1 kΩ. The 10 kΩ pullup sets the nominal 100 µs charging time. TP5 exposes the filtered node.
5. Start J2 SPI at 1 MHz in mode 0. Leave JP7 open during carrier-only testing. Tune CT3 with a weakly coupled VNA loop on the populated board. Probe TANK, RECT, the isolated clock and the ASK input at TP13–TP16. For the cold-rail test, disconnect chip power and monitor chip-rail voltage, injection current and reset while applying the RF field.

U6 has a separate raw input at J8. For the LDO assembly, fit all seven “Aux LDO” rows, apply nominal 7 V at J8 pin 1, then select JP2 pins 2–3 with power removed. Both supply choices pass through JP1. The source selector prevents paralleling the LDO output and bench supply when fitted with a single shunt. CL1–CL5 support VIN, VOUT, VREG, REF/REF_SENSE and BYP. Keep at least 10 µF effective at VOUT and verify MLCC DC-bias derating for the final operating point. [ADM7150 datasheet](https://www.analog.com/media/en/technical-documentation/data-sheets/ADM7150.pdf)

## Host, anchor and expansion connectors

| Connector | Pin assignment |
|---|---|
| J2 · keyed 2×5, 5 V domain | 1 SCK, 2 GND, 3 DQ0, 4 GND, 5 DQ1, 6 GND, 7 CS_N, 8 reset monitor, 9 chip 5 V sense, 10 GND. |
| J3 · expansion, 5 V domain | 1–6 DQ2–DQ7, 7 RDY, 8 IRQ, 9 UART TX, 10 UART RX, 11–18 GPIO0–GPIO7, 19 VERIFY_OK, 20 FAULT, 21–24 JTAG TCK/TMS/TDI/TDO, 25 NFC_CLK_IN, 26 NFC_ASK_IN, 27 NFC_LOAD_MOD, 28 CLK_MON, 29–30 GND. |
| J4 · private FRAM probe header | 1 CS_N, 3 SCK, 5 MOSI/SI, 7 MISO/SO. Even pins are ground. U1 controls this bus. U3 WP_N and HOLD_N are strapped to chip 5 V. TP17–TP20 provide individual probe lands. |
| JRF1 / JRF2 · SMA | JRF1 center to die pad 47, challenge in. JRF2 center to die pad 48, response out. Both shields go to GND. Use short coax and a high-impedance response receiver. |
| J9 · translated host | 1 host-supplied 3.3 V, 2 GND, 3 SCK, 4 CS_N, 5 dedicated ×1 MOSI, 6 GND, 7–14 H_DQ0–H_DQ7, 15 DQ_DIR, 16 DATA_OE_N, 17 CTRL_OE_N, 18 GND. |

All eight die DQ pins have individual 33 Ω series resistors. SCK has its own 33 Ω resistor. The default 5 V assembly uses J2/J3 directly with U4 and U5 omitted. J2 pin 9 is a sense connection. Keep J2/J3 external drivers disconnected when controlling the same bus from J9.

**Translated ×1 SPI.** Fit the “3V3 host” BOM rows and close JP6. U5 drives SCK, CS_N and a separate MOSI path into DQ0. Hold DQ_DIR low so U4 receives all eight chip-side lines. Drive MOSI on J9 pin 5 and receive MISO on J9 pin 8. The host must leave J9 pins 7–14 as inputs. Drive both OE_N controls low after the host rail, pin directions, idle SCK and inactive CS_N are established.

**Translated ×4 or ×8 SPI.** Open JP6 before switching to wide operation. U5 continues to drive SCK and CS_N. U4 carries the full data bus, including the ×1 prefix on H_DQ0. DQ_DIR high selects host-to-chip and low selects chip-to-host. Raise DATA_OE_N before each turnaround, release the prior driver, change direction, then lower DATA_OE_N after both sides meet their enable/disable timing. The host controls this sequence. Each OE_N defaults high. The translator supports partial power-down and supply isolation. [SN74LXC8T245 datasheet](https://www.ti.com/lit/ds/symlink/sn74lxc8t245.pdf)

## COB assembly and layer assignment

The bond map gives DEF window centers in µm from the die south-west corner, with north positive. The bond-site and PCB-finger columns use KiCad footprint-local millimeters with the die center at zero and south positive. F.Fab carries the exact outline and 56 windows. The F.SilkS dot marks the pad 1 end of the south bank. Dwgs.User carries the 54 wire projections. The four analog fingers remain unbonded. EP is an additional PCB terminal.

Bond numbers progress by side S → E → N → W. Within each horizontal side, indices increase west to east. Within each vertical side, they increase south to north. Preserve north pads 29–39 and west pads 40–56 in that physical order when preparing the bonder program.

Specify a wirebond-compatible finger finish and filled, capped, planarized 0.30 mm drills under the ground paddle. All wedge lands and the die paddle have exposed metal and zero paste apertures. Pads 3 and 4 each have two exposed fingers joined at their heels and two die-site targets separated by 28 µm. The bonder must qualify the actual passivation openings, wedge imprint, wire diameter, loop height, die attach and finish before assembly. Place CP1–CP4 at their corresponding supply pairs, with one ground via per bypass and TP21–TP24 at the local returns.

Use a 1.60 mm four-layer board with 35 µm finished L1 copper. L1 carries components, signals and the winding. Use L2 as ground, L3 as power and L4 for signals and ground outside the antenna window. The supplied stackup uses 0.2104 mm outer dielectrics and a 1.0392 mm core. Keep U1, the detector, connectors and planes outside the antenna window.

L1 of the schematic is the printed coil. Its winding occupies 40 × 40 mm, with both electrical terminals accessible outside the 46 mm protected window. The masked F.Cu lead runs from pad 1 to the outer turn. An inner plated barrel connects to a single B.Cu return and an outside barrel on pad 2. The footprint uses a KiCad net tie at the inner end of the winding so PCB DRC recognizes its intentional DC continuity. Preserve its rotation, pads and embedded rule areas as one footprint.

## NFC population

CT1 and CT2 supply 80 pF fixed C0G at 1%, and CT3 is a Voltronics JR150 covering 3–15 pF. All three meet the 100 V minimum. Fit RD1 (4.7 Ω) in series and RB1 (12 kΩ) across the tank. RR1 is 150 Ω in 2010, rated 0.75 W. RG1 is 2.2 kΩ in 1206, rated 0.25 W. [JR150 outline and capacitance range](https://www.knowlescapacitors.com/getattachment/727ef5bd-b9cf-4698-a84c-cd891d1f5273/JR-Series) · [JR series voltage ratings](https://www.knowlescapacitors.com/getmedia/fae461ef-e086-4f0e-af62-725f9d523a26/KNO_Trimmer_Catalog_R5-sm)

D1 feeds RECT, D2 clamps the negative rectifier input, and D3/D4 clamp the Q1 gate to RECT and GND. CR1, RRECT1 and DZ1 terminate RECT. Q1 senses the carrier through its gate. Its drain pullup is 470 Ω to V5_CHIP. The single BAS70 uses pin 1 as anode and pin 3 as cathode. [BAS70 pinout](https://assets.nexperia.com/documents/data-sheet/BAS70.pdf) · [FDV301N datasheet](https://www.onsemi.com/pdf/datasheet/fdv301n-d.pdf)

The reserved ASK option adds a separate D5 envelope branch, D6 input clamp, a RECT-powered TLV3201 and Q2. With JP7 open, RP2 holds the ASIC ASK input high. After characterizing the detector, JP7 connects its isolated drain and adds the shunt listed in the BOM. NFC_LOAD_MOD is available at J3. ASK sensitivity, modulation depth and the board's response to a particular reader require bench characterization. [TLV3201 datasheet](https://www.ti.com/lit/ds/symlink/tlv3201.pdf)

## Rebuild and verify

From this directory, run the following commands with Python 3.10 or newer. The standard library is sufficient for schematic and geometry checks.

```sh
python3 -B generate_carrier.py
python3 -B render_land_patterns.py
python3 -B verify_carrier_erc.py --self-test --netlist NETLIST_ASS2_0P5.csv
kicad-cli sch export svg -o . "$PWD/ass2_0p5_carrier.kicad_sch"
```

The checker discovers the macOS KiCad app and a CLI on PATH. Use `--cli` for another location, `--footprints` for the standard library root, or `--standalone` to omit native tools. Set `KICAD_PYTHON` to the interpreter with matching `pcbnew` bindings for native footprint DRC. The test constructs its boards in a temporary directory. File overrides for checking against the original source checkout are in the [verification report](REPORT.md).

The PCB layout, board routing, Gerbers and physical qualification remain downstream work. This package supplies the electrical design, procurement and bonding schedules, stackup, manufacturing geometry for both custom footprints, and the checks that cover them.
