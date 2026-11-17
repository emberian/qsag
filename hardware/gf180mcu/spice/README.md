# Foundry SPICE electrical characterization

Run simulations on Linux only. `run_corners.py` rejects macOS. Each deck has
`.meas ... pass_*` results: **1 means PASS, 0 means FAIL, missing/failed means
ERROR**. The runner requires every expected flag, successful measurements,
normal simulator completion, and no transient abort. It never accepts ngspice's
exit status alone. A failed design limit is distinct from a solver error.

## Matrix and reproduction

The matrix is the Cartesian product TT/SS/FF × −40/27/125 °C. Supplies are
5.0/4.5/5.5 V respectively; diode, resistor and MOSCAP corners track the process.
PDN also runs both output slew selections. Default seed is 20261116.

The hbox container's ngspice 45 runs the rapid path and RO decks. Forward-biased
foundry diodes expose a simulator defect in both that version and the **47
release tarball**: sidewall depletion charge uses the bottom-junction integration
constant at FCS×PHP. This produces a charge discontinuity when PB/MJ differ from
PHP/MJSW. See [upstream report #870](https://sourceforge.net/p/ngspice/bugs/870/).
The lane-local `engine/diode-sidewall-continuity.patch` corrects that integration
constant, without changing diode I(V), C(V), any foundry coefficient, or tests.
The downloaded 47 archive is pinned by SHA-256 in `build_ngspice47.sh`.

```sh
# Local source sync; execute ngspice only on hbox/bb2.
rsync -az --exclude __pycache__ hardware/gf180mcu/spice/ \
  hbox:/var/tmp/dregg180-spice/astra-dregg180-spice-pcb/

# On hbox, in the lane directory (never install over the shared simulator):
sh build_ngspice47.sh
python3 engine/check_engine.py \
  --stock "$PWD/engine47/ngspice-stock" \
  --fixed "$PWD/engine47/install/bin/ngspice"
python3 run_corners.py --jobs 3 \
  --ngspice "$PWD/engine47/install/bin/ngspice" \
  --pdk /var/tmp/dregg180-spice/pdk --output results
```

The regression compares the unmodified release against the repaired engine at
three temperatures and two FCS values, including dQ/dV versus the simulator's
reported capacitance. The standalone mathematical check needs no simulator:

```sh
python3 hardware/gf180mcu/spice/check_analysis.py
python3 hardware/gf180mcu/pcb/planar_nfc_coil_calc.py --self-test
```

`--pdk` expects the existing flat PDK staging layout: `ngspice/` plus
`gf180mcu_fd_io.spice` and `gf180mcu_fd_sc_mcu7t5v0.spice`. Symlinks to the
provisioned foundry tree suffice. No foundry file is edited. The hbox staged
MOS and IO files were hash-compared with the read-only `/pdk` originals.
The runner saves generated decks, initialization files, logs, measurements,
and toolchain hashes. A time-limited/aborted run remains ERROR.

**Randomness:** `.spiceinit` `setseed` alone does not initialize the parser's
`agauss()` reproducibly in the tested executables. The RO deck explicitly uses
`.options seed=20261116`; the runner updates this option for `--seed`.
`engine/seed_probe.sp` is a small independently repeatable parser diagnostic.
Only runs with the explicit option can support paired PVT comparisons.

## Models and limits

| Deck | Physical scope | Pass criteria |
|---|---|---|
| `brands_chaum_and_vernier_tdc.sp` | Foundry `bi_24t` input/output, `latq_1`, four-inverter lock delay and reset-priority NOR lock, `mux2_4`; 50 Ω source, 1.8 nH/125 mΩ signal bonds, 15 pF output load; 14 loaded Vernier taps | All four turnaround polarities positive and <5 ns; output holds after hostile reversal in two rounds; lock gate closes; 0<differential stage delay<1 ns |
| `ro_puf_pelgrom_mc.sp` | 128 independent physical five-stage NAND rings matching current `dregg_puf_ro5`, plus two inverter-ring witnesses; foundry local mismatch on, global Monte Carlo off | All 130 rings oscillate, 1 MHz<f<2 GHz, full logic swing; BER/BCH qualification is reported separately |
| `nfc_13p56mhz_afe.sp` | Three independent 13.56 MHz coil/rectifier circuits for powered isolation, cold isolation, and unsafe direct-pad comparison; full foundry IO pads | Protected cold injection average<1 µA, peak<100 µA, pad within ±0.3 V; powered pad and logic swing valid, recovered frequency 13.4–13.7 MHz; rectified voltage<5.5 V, gate<10 V, rectifier peak<70 mA, each modeled resistor dissipation<0.25 W |
| `pdn_ssn_ground_bounce.sp` | Three DVDD/DVSS pairs plus core VDD/VSS pair; foundry rail clamps and eight output pads; 1.8 nF decap allocation, 20→120 mA core pulse, 15 pF/output, 33 Ω source termination | Positive/negative core bounce and positive bank bounce<0.5 V, droop<0.5 V, rail differential>90% nominal, quiet Schmitt victims retain logic levels |

These are project electrical screening budgets. The NFC injection targets are
not a published foundry injection-current guarantee. No unsupported electrical
rating is inferred from the IO cell's ESD qualification.

`moscap_with_esr.inc` is a deck-local implementation of the foundry 6 V NMOSCAP
C(V) coefficients and corner factors with 1 Ω/unit electrode ESR (scaled by
multiplicity). It integrates the positive C(V) into charge and uses a normalized
charge state. This avoids the native nonlinear-capacitor differentiator's very
small numerical state. The independent derivative check covers ten bias points,
including the transition and cold rail. Package resistance, inductance and pad
capacitance remain separate physical elements. ESR and package values are
engineering assumptions; final extracted/package data must replace them.

PDN uses a 1e-10 S junction gmin for operating-point convergence (0.5 nA
at 5 V per junction); all measurement limits remain unchanged.
The PDN's six ESD RC ladders receive **initial guesses**, using `.nodeset`, for
the powered settled state. These guesses do not clamp transient voltages.
The 1.8 nF on-die allocation is modeled as four finite-ESR 450 pF capacitors,
with four actual foundry fillcap witnesses. It is not a measured capacitance or
a claim that a particular count of `fillcap_16` cells supplies 1.8 nF.

The rapid-path latch demonstration uses two alternating public idle polarities
and explicit rearm. This characterizes both electrical transition directions;
arbitrary challenge data requires a valid strobe/encoding protocol. It does not
prove Brands–Chaum security, and it does not patch the RTL. The 14-tap TDC slice
measures the local slow-minus-fast delay; it does not establish full 32-bin DNL,
INL, metastability aperture, calibration drift, or distance accuracy.

## RO BER and BCH model

Frequency spread comes from `.meas` timing between the fifth and fifteenth
rising crossings. For each corner, `summary.json` reports the mean and sample
standard deviation across 128 rings. The first 126 rings form **63 disjoint
pairs**, so the BCH calculation does not reuse a ring in several bits.

For a ring with measured frequency f and counter window T, a uniform starting
phase gives count `floor(fT)` or `floor(fT)+1` with probabilities `1-frac(fT)`
and `frac(fT)`. An independent, equally likely −1/0/+1 stop-edge uncertainty is
added to each count. Equal counts have error probability 1/2. This is an explicit
conservative counter model, **not measured silicon noise or transient jitter**.
The reference bit is the sign of the underlying long-window frequency difference.

The calculation enumerates both count distributions exactly. It then convolves
the 63 unequal bit-error probabilities, reporting the Poisson-binomial tail
P(errors>5) for BCH(63,36,t=5). The selected engineering target is ≤10⁻⁶ block
failure per reconstruction. The first passing window is searched over 8, 16,
32, … core cycles at 50 MHz, and must fit a 14-bit counter with two counts of
headroom. No passing window is reported if that counter would overflow.

`puf_local` uses same-corner enrollment, isolating counter quantization effects.
`puf_vs_tt27` uses TT/27 °C enrollment with the same parser-seeded mismatch draws.
Temperature comparisons within a process corner describe a conditional model
of the same devices; cross-process-corner comparisons are **fixed-seed sensitivity
experiments**, not a claim that a physical chip changes process corner. A sign
reversal cannot be cured by a longer window. Unscreened near-tie pairs can prevent
a 14-bit solution even when most pairs are reliable.

The sample is not enough to certify a 10⁻⁶ physical failure rate. Supply noise,
spatial covariance, aging, asynchronous counter implementation, enrollment
selection/helper data, and silicon temperature drift require separate evidence.
