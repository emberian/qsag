# eFuse characterisation block `dregg_efuse_tc` (first silicon, characterisation only)

Purpose: measure what simulation cannot give for the PDK fuse cell (final resistance and its tail,
programming window, retention), and calibrate the electro-thermal model
(`physics/efuse/fuse_thermal.py`). It holds no secret, feeds no decision in the chip, and may be left
unbonded. Basis: `scratch/lanes/fable-efuse-and-process-sim.last.md` sections A.5-A.7. Sizes marked [E]
are estimates.

## 1. Contents

64 fuse positions = 8 variants x 8 positions. Every position is one PDK fuse cell
(`gf180mcu_fd_pr` `efuse_cell`, unmodified, anode = pin `in`, cathode = pin `out`) with **its own**
programming transistor; position 7 of every variant has the fuse replaced by a Metal1 short (same
contacts and straps) as the series-resistance reference.

| Variant | Programming path (all 5 V devices, minimum L: PMOS 0.5 um, NMOS 0.6 um) | Why |
|---|---|---|
| V1 | PMOS 2 x 62 um from VPP to anode; cathode to VSS | copy of `efuse_async_mem_1x8` |
| V2 | PMOS 76.5 um to anode; NMOS 30.5 um cathode to VSS | copy of the `efuse_array` bit |
| V3 | anode to VPP; NMOS 20 um cathode to VSS | foundry arrangement (DRM 10.11), weak |
| V4 | as V3, NMOS 40 um | |
| V5 | as V3, NMOS 80 um | |
| V6 | as V3, NMOS 160 um | |
| V7 | PMOS 40 um to anode; cathode to VSS | weak PMOS |
| V8 | PMOS 250 um to anode; cathode to VSS | strong PMOS |

- Simulated drive of V1 and V2: `physics/efuse/drive.json` (15-42 mA and 8-22 mA into an intact fuse).
  The NMOS variants span roughly 3 to 25 mA [E]; simulate them with `run_prog_drive.py` once drawn.
- One copy of the macro sense amplifier (`efuse_senseamp` from
  `gf180mcu_re_efuse/spice/efuse_async_mem_1x8.spice`: precharge PMOS 2.44 um, pass NMOS 0.82/0.60 um, two
  `inv_1`) on the anode node of each V1 and V2 position: 14 amplifiers, supplied from VDD, read as 14 bits.
- Layout: fuse cells in two rows with the DRM keep-outs (EF.17 0.26 um between EFUSE_MK, EF.20 2.73 um
  from PLFUSE to COMP/Nplus/SAB/resistor), no metal over the links above Metal1 strap level, transistors
  beside their fuse. Guard ring around the block. Area about 33,000 um^2 [E: fuses with keep-out
  64 x 120, transistor width 6,600 um total x 2.4 um^2/um, logic 4,000, ring and spacing 5,000]. A half
  version (V1, V2, V4, V6; 32 positions) is about 17,000 um^2 [E].
- The block uses the PLFUSE and EFUSE_MK layers: it must pass the precheck DRC decks before it is
  allowed on the die. If it does not, drop it; nothing depends on it.

## 2. Pads and access

- **VPP**: one analog pad (`asig_5p0`), wired with wide Metal (>= 10 um, top metal) only to the sources of
  the PMOS variants and the anodes of the NMOS variants. No other connection. The pad's own diode to DVDD
  limits VPP to VDD + 0.2 V, so sweeps above 5 V raise VDD as well. With VPP at 0 V or open the block is
  inert.
- No other pad. Control and read-back go through the existing command link:
  - `TC_SEL[5:0]` position, `TC_WIDTH[15:0]` pulse length in clock periods (40 ns at 25 MHz) with a
    `TC_PRESCALE[3:0]` power-of-two multiplier (40 ns to about 85 ms), `TC_FIRE` (one pulse on the selected
    position's gate), `TC_HOLD` (gate on continuously, for resistance measurement), `TC_SENSE` (run the
    sense sequence of the macro: precharge low for one clock, then sense high for one clock, capture 14
    bits).
  - The gate of every unselected position is off; reset forces all gates off (same inhibit as the
    macro: gate = NAND(reset_n, select and fire)).
  - Commands are accepted under the same rule as the characterisation ring read-out (decision D13):
    owner-root signature over a fresh nonce. The block has no input from, and no output to, any key or
    lifecycle logic other than those registers.
- Gate drivers and the select decoder run from VDD; only the programming current comes from VPP.

## 3. Measurements (bench, per die)

1. **Initial resistance**, every position: `TC_HOLD`, VPP = 50 mV from a source-measure unit, read the
   current (about 0.8 mA into 60 ohm, 40 uW: no heating). Subtract the short position of the same
   variant. Expected 67 ohm (sheet-resistance value) or about 200 ohm (PDK model); this alone settles one
   open question.
2. **Programming**: one pulse per fuse. Matrix over VPP (3.0 to 5.5 V in 0.5 V steps), pulse length
   (1 us, 10 us, 50 us, 250 us, 1 ms, 10 ms) and temperature (-40, 25, 125 C), spread over dies so that
   every cell of the matrix gets at least a few hundred fuses per variant across the lot. Never a second
   pulse on the same fuse in this part.
3. **Current waveform**: VPP through a 1 ohm (or 10 ohm) sense resistor with a short ground return,
   oscilloscope across it, for at least 20 fuses per variant: time at which the current collapses or
   steps. Compare with the simulated melt times (7 ns to 0.9 us for V1; `results/corners.json`).
4. **Final resistance**: as step 1, with VPP = 50 mV, then 0.5 V if the current is below the instrument
   floor (range needed 50 ohm to above 100 Mohm). Record the full distribution; the result that matters is
   the count of fuses between 1 kohm and 100 kohm.
5. **Macro read**: `TC_SENSE` on V1 and V2 positions at VDD 4.5, 5.0, 5.5 V and -40, 25, 125 C, before and
   after programming. Expected read threshold 2 to 20 kohm depending on corner
   (`results/read_trip_20ns.json`); a fuse that changes its read value across these conditions is the
   failure a security bit cannot tolerate.
6. **Retry**: on fuses that ended between 500 ohm and 100 kohm, a second and third pulse; record
   resistance after each. (Prediction: no change above about 2 kohm.)
7. **Retention**: bake unbiased at 150 C (1000 h) and 250 C (24 h, bare die), 500 temperature cycles
   -55/125 C; re-measure steps 4 and 5 at intervals. Read disturb: 10^9 `TC_SENSE` cycles on a set of
   programmed and partly programmed fuses, then step 4.

## 4. What to report

Per variant and condition: histogram of log10(final resistance); fraction below 20 kohm and below
100 kohm; fraction changed by bake and cycling; current-collapse time. From these: the programming
window (variant, voltage, pulse) with no fuse below 100 kohm in the sample, the redundancy needed for a
lifecycle bit (per-fuse failure probability p, OR of n fuses fails with p^n), and whether the PDK macros
as they stand fall inside or outside that window.
