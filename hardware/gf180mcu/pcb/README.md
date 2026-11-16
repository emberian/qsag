# Dregg-180 reference bring-up board

This is a reference schematic and placement description, not a routed PCB or a
fabrication release. The electrical evidence is in `../spice/`; its pass limits
and model limitations apply here. The earlier `BOM.csv` is a broader exploratory
parts list; the table below describes this specific bring-up circuit.

## Stackup and power

Use a 4-layer, approximately 1.6 mm FR-4 board: L1 components/signals/coil,
L2 ground, L3 5 V and auxiliary power, L4 signals and ground. Keep **all copper,
including ground pours, out of a 46 × 46 mm window under the 40 × 40 mm NFC coil**
on L2/L3/L4, except the short insulated crossover needed to exit the inner turn.
Route that crossover without making a shorted secondary loop. Put the ASIC,
rectifier, and host connector outside the antenna window. Provide a ground via
next to each bypass capacitor and a via array under the exposed package pad.
Confirm the package bonding drawing before assigning connector or footprint pins.

`SLOT_0P5X0P5` has three DVDD and three DVSS pads plus one core VDD/VSS pair
(`../src/slot_defines.svh`). Tie the 5 V domains as specified by `chip_top.sv`.
Use four local 100 nF bypass capacitors and a 4.7 µF bulk capacitor. The PDN deck
assumes 125 mΩ + 1.8 nH per bond and a **1.8 nF on-die decap allocation**; that
allocation needs extracted fillcap capacitance and placement verification.
The foundry DVDD/DVSS cells are specified for 60 mA DC per cell; do not treat
the external regulator rating as permission to exceed pad current limits.
[GF IO cell specifications](https://gf180mcu-pdk.readthedocs.io/en/latest/IPs/IO/gf180mcu_fd_io/datasheet.html)

## Reference schematic connections

1. **Power/reset:** current-limited bench 5.0 V enters through a removable current
   measurement jumper, then the bypass network and ASIC supplies. Connect a
   TPS3839K50 supervisor to the chip-side rail, bypass with 100 nF, and drive
   Schmitt `rst_n` through 100 Ω. Fit a 100 kΩ reset pulldown. K50 trips at
   nominal 4.38 V and has a nominal **200 ms** release delay. A reset supervisor
   does not by itself make a CMOS pad Schmitt: the ASIC must use `in_s`, or fit an
   external noninverting Schmitt buffer. The present RTL/pad selection must be
   checked by its owning lane. TPS3839 is rated −40 to +85 °C; the semiconductor
   deck sweep to +125 °C does not extend that board rating.
   [TI TPS3839 datasheet](https://www.ti.com/lit/ds/symlink/tps3839.pdf)
2. **Tamper:** 10 kΩ pullup to chip 5 V, 10 nF to ground, and a normally open
   grounded tamper contact. Add 1 kΩ between the exposed contact connector and
   the sense node. The nominal 100 µs charging time settles long before the
   supervisor releases reset. Place the capacitor at the ASIC and route away
   from RF/output edges. Verify the ASIC's boot blanking and zeroization behavior
   separately; an RC cannot enforce the RTL security policy.
3. **NFC tank:** four turns, outer side 40 mm, width 0.42 mm, gap 0.56 mm,
   35 µm copper. Calculator values: L=1.4662 µH, Rac=0.988 Ω at 25 °C,
   Cself=1.865 pF, total resonant capacitance 93.95 pF. Start with 68 pF + 12 pF
   C0G and a 3–15 pF trimmer (nominal 8.885 pF before actual front-end loading),
   4.7 Ω series damping, and 12 kΩ bleed. Tune with the populated circuit and a
   weakly coupled VNA loop. The analytic loaded Q≈17.88 is a small-signal estimate;
   rectifier/clamp and gate loading change it substantially. Geometry-derived
   coupling and plane-loss estimates are not an EM extraction.
4. **Rectifier and cold tap:** tank → 220 Ω → Schottky rectifier → `RECT`, with
   4.7 nF, 10 kΩ bleed, and 4.7 V shunt Zener to ground. Add the negative
   Schottky clamp at the rectifier input. **RECT remains separate from ASIC 5 V.**
   For the clock input, tank → 2.2 kΩ → FDV301N gate; Schottky clamps from gate to
   RECT and ground; 1 MΩ gate pulldown; source to ground; drain to the Schmitt
   `nfc_clk_in` pad; 470 Ω drain pullup to chip 5 V. This is an inverting common
   source detector. It avoids a conductive RF-to-chip-supply path; the deck still
   includes gate-drain displacement current and the body diode. A 2.2 kΩ resistor
   feeding the pad directly is retained as the unsafe comparison in the deck.
   Do not substitute a single pass FET with an uncontrolled body-diode path.
5. **ASK:** reserve footprints for a separate envelope detector/comparator and
   route its output through a second open-drain isolation stage, with its pullup
   powered from chip 5 V. The cold-tap deck characterizes the carrier input and
   rectifier; it does not establish ASK sensitivity, modulation-depth tolerance,
   or harvested-power operation. Leave ASK disconnected for the first powered
   carrier test. Populate and characterize it before claiming NFC protocol support.
6. **SPI:** keyed 2×5 header with SCK, MOSI, MISO, CS_N, reset monitor, chip-side
   5 V sense, and ground returns. Use partial-power-down capable translation for
   a 3.3 V host; never connect a powered host's push-pull output to an unpowered
   ASIC pad. Add 33 Ω source series resistors and a 10 kΩ CS_N pullup. Begin at
   1 MHz with a powered board. Expose the bypass-clock strap, defaulting to the
   internal-clock selection used by the RTL. Confirm pin polarity before wiring.
7. **FRAM:** FM25W256 on the anchor SPI bus, powered by chip 5 V, with 100 nF
   local bypass, 10 kΩ CS_N pullup, and WP_N/HOLD_N held high. It accepts
   2.7–5.5 V and up to 20 MHz SPI, but its listed industrial part also stops at
   +85 °C. Keep host SPI and the dedicated anchor bus separate.
   [Infineon FM25W256 datasheet](https://www.infineon.com/assets/row/public/documents/10/49/infineon-fm25w256-256-kbit-32k-x-8-serial-spi-f-ram-datasheet-en.pdf)
8. **Test points:** 5 V before/after the measurement jumper, ground at each supply
   pair, reset, tamper, internal clock monitor, SPI signals, RECT, tank, isolated
   clock drain, ASK, and FRAM CS_N. Use low-capacitance RF probing. Give rapid
   challenge/response their own short SMA/coax paths: the timing deck includes a
   50 Ω source and 15 pF response load, not the SPI level translator.

## Bring-up BOM

| Ref / quantity | Value or candidate | Purpose / qualification |
|---|---|---|
| U1 ×1 | Dregg-180 ASIC, package per bonding drawing | Footprint/pin numbers await package confirmation |
| U2 ×1 | TPS3839K50 | 4.38 V POR, 200 ms nominal, −40…85 °C |
| U3 ×1 | FM25W256-G | 5 V SPI FRAM, SOIC-8 |
| U4 optional | 5 V noninverting Schmitt buffer | Required if ASIC reset pad remains CMOS |
| U5 optional | Ioff-rated 3.3↔5 V SPI translation | Qualify direction, enable/reset, and unpowered behavior |
| Q1 ×1 (Q2 reserved) | FDV301N | RF gate isolation / optional ASK output isolation |
| D1–D4 | BAS70 family low-capacitance Schottky | Rectifier and gate clamps; pin topology must match schematic |
| DZ1 ×1 | BZT52C4V7 or selected 4.7 V shunt | Verify clamp curve, dissipation, and tolerance |
| L1 | Printed four-turn square coil | Geometry above; no ferrite/material assumptions |
| CT1, CT2 | 68 pF + 12 pF, C0G, 1%, ≥100 V | Initial tank tuning |
| CT3 | 3–15 pF RF trimmer, ≥100 V | Tune populated board |
| RD, RB | 4.7 Ω / 12 kΩ | Tank damping / bleed |
| RR | 220 Ω, ≥0.25 W | Rectifier current limiting; verify measured dissipation |
| RG | 2.2 kΩ, ≥0.25 W | Gate branch current limiting |
| RP, RGS | 470 Ω / 1 MΩ | Drain pullup / gate pulldown |
| CR, RRECT | 4.7 nF / 10 kΩ | Independent rectified node |
| CP ×4, CB ×1 | 100 nF X7R / 4.7 µF X7R, ≥10 V | Local / bulk supply bypass |
| Caux ×2 | 100 nF X7R, ≥10 V | Supervisor and FRAM bypass |
| RT, CT, RS | 10 kΩ / 10 nF / 1 kΩ | Tamper RC and exposed-contact series resistor |
| RRESET, RPD | 100 Ω / 100 kΩ | Reset drive series / pulldown |
| SPI resistors | 33 Ω source series; 10 kΩ CS_N pullups | Match number to fitted interfaces |
| Headers / jumpers | SPI 2×5, anchor test header, power shunt, clock strap | Key and label voltage domains |
| RF connectors | Two SMA plus probe pads | Rapid challenge/response, outside coil keepout |

The board device models in the NFC deck are explicit engineering approximations,
not vendor-qualified corner models. FDV301N's published typical Ciss/Crss are
9.5/1.3 pF at 10 V; the deck uses 20 pF gate-source and 2 pF gate-drain plus
an explicit body diode, without claiming those are guaranteed upper bounds.
[BAS70 specifications](https://www.diodes.com/part/view/BAS70),
[FDV301N datasheet](https://www.onsemi.com/pdf/datasheet/fdv301n-d.pdf).

Before attaching an NFC reader, test cold tap with the 5 V input disconnected,
monitoring chip supply current and voltage, reset, and the protected pad. The
SPICE limits are project screening targets (1 µA average / 100 µA peak ESD
injection, ±0.3 V rail excursion), not published foundry injection-current
ratings. Full PCB qualification needs vendor model tolerances, extracted
package/board parasitics, actual reader field strengths, and measurements.

Reproduce the calculator checks with:

```sh
python3 hardware/gf180mcu/pcb/planar_nfc_coil_calc.py --self-test
```
