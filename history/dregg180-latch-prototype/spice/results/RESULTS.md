# Dregg-180 SPICE results — 2026-11-16

**45/45 final simulations completed; 34/45 electrical checks PASS.** The 11 FAIL results are design-budget failures, not simulator aborts. BCH results below are calculated under the stated counter-noise model.

Rapid-path results use ngspice 45. RO, NFC, and PDN use the isolated ngspice 47 build with the validated diode sidewall-charge repair. Foundry model files are unmodified. Full inputs, logs, hashes, and measurement vectors are in the adjacent JSON files and evidence archives.

## Corner × deck table

TT/SS/FF supplies are 5.0/4.5/5.5 V. Rapid delay is the worst of four PCB-pad-to-PCB-pad polarities; it excludes reader/air-path travel. PDN reports positive **south-bank** ground bounce for SL=0 / SL=1.

| Process | °C | Rapid status / ns / TDC ps | RO status / MHz mean ± σ | NFC status / cold avg–peak µA | PDN SL0 / SL1 status, peak mV |
|---|---:|---|---|---|---|
| TT | -40 | PASS / 3.047 / 95.08 | PASS / 850.222 ± 1.505 | PASS / 0.0467–39.20 | FAIL 781.3 / FAIL 742.3 |
| TT | 27 | PASS / 3.616 / 108.78 | PASS / 716.484 ± 1.306 | PASS / 0.0465–35.75 | FAIL 594.5 / FAIL 592.8 |
| TT | 125 | PASS / 4.411 / 127.28 | PASS / 579.917 ± 1.068 | PASS / 0.0067–35.76 | PASS 395.5 / PASS 442.9 |
| SS | -40 | PASS / 4.165 / 136.46 | PASS / 588.111 ± 1.241 | PASS / 0.0398–39.28 | PASS 436.6 / PASS 497.0 |
| SS | 27 | PASS / 4.972 / 157.20 | PASS / 493.664 ± 1.069 | PASS / 0.0390–35.82 | PASS 341.0 / PASS 390.2 |
| SS | 125 | FAIL / 6.159 / 184.37 | PASS / 398.984 ± 0.859 | PASS / 0.0058–35.73 | PASS 254.5 / PASS 286.2 |
| FF | -40 | PASS / 2.422 / 72.77 | PASS / 1120.261 ± 1.656 | PASS / 0.0405–39.02 | FAIL 1200.4 / FAIL 1021.3 |
| FF | 27 | PASS / 2.853 / 82.22 | PASS / 950.486 ± 1.484 | PASS / 0.0363–35.64 | FAIL 926.5 / FAIL 824.7 |
| FF | 125 | PASS / 3.469 / 95.78 | PASS / 773.247 ± 1.246 | PASS / 0.0066–35.87 | FAIL 648.4 / FAIL 617.5 |

All rapid latch-hold and TDC-step checks pass. SS/125 °C misses the 5 ns turnaround limit; SS/27 °C has only about 28 ps nominal margin. No RTL or extracted-layout timing closure is claimed.

## RO window and BCH(63,36,t=5)

128 physical NAND ROs were sampled with foundry local mismatch and parser seed 20261116. All 128 plus the two inverter witnesses oscillate at every corner. Frequencies feed an explicit model: uniform counter start phase, independent −1/0/+1 stop error per ring, and random tie decisions. The 63 BCH bits use disjoint pairs and ideal long-window TT/27 °C enrollment. The target is P(more than 5 errors) ≤10⁻⁶, computed by exact Poisson-binomial convolution; this is not a measured silicon BER.

| Process | °C | BER 160 ns | BER 10.24 µs | BER 20.48 µs | BCH failure at 10.24 µs | First passing local / TT27 window (µs, 14-bit) | Sign flips vs TT27 |
|---|---:|---:|---:|---:|---:|---|---:|
| TT | -40 | 0.42342 | 0.01798 | 0.01795 | 0 | 10.24 / 10.24 | 1 |
| TT | 27 | 0.43214 | 0.00986 | 0.00212 | 0 | 10.24 / 10.24 | 0 |
| TT | 125 | 0.44481 | 0.01408 | 0.00400 | 7.97e-06 | 20.48 / 20.48 | 0 |
| SS | -40 | 0.43695 | 0.02905 | 0.02999 | 0 | 10.24 / 10.24 | 2 |
| SS | 27 | 0.44535 | 0.02406 | 0.02030 | 3.77e-06 | 20.48 / 20.48 | 2 |
| SS | 125 | 0.45553 | 0.02221 | 0.01070 | 0.0001 | 20.48 / 20.48 | 0 |
| FF | -40 | 0.41543 | 0.00724 | 0.00439 | 0 | 10.24 / 10.24 | 0 |
| FF | 27 | 0.42451 | 0.00275 | 0.00000 | 2.92e-10 | 10.24 / 10.24 | 0 |
| FF | 125 | 0.43574 | 0.01647 | 0.00822 | 3.98e-06 | 20.48 / 20.48 | 0 |

The fastest measured ring is 1124.150 MHz. A fixed 20.48 µs window needs 23024.6 counts including two-count headroom: **15 counter bits**, or adaptive 10.24/20.48 µs windows with 14 bits. The 512-cycle window alone does not meet the model target at every corner. Cross-process comparisons are fixed-seed sensitivity experiments; a chip does not change process corner. Spatial covariance, noisy enrollment, aging, analog jitter, and real counter circuitry are outside this model. All 13 tested windows per corner are retained in `ro_summary.json`.

## NFC component and cold-tap measurements

Each case has an independent antenna. The applied series EMF is 7.5 Vpk at 13.56 MHz, corresponding to approximately 134 Vpk for the unloaded linear nominal tank. Cold VDD is held at 0 V to measure injection into a discharged supply; this does not predict the eventual voltage of a floating board. The protected gate path uses 2.2 kΩ, Schottky clamps and an isolated open-drain transistor; the rectifier uses 150 Ω. The unsafe comparison connects its tank directly to an unpowered foundry pad through 2.2 kΩ.

| Process | °C | RECT max V | Cold pad min / max V | Unsafe avg / peak mA | Rectifier peak mA | Rectifier R / gate R mW |
|---|---:|---:|---|---|---:|---|
| TT | -40 | 4.803 | -0.139 / 0.122 | 1.376 / 4.673 | 51.80 | 218.16 / 26.44 |
| TT | 27 | 4.807 | -0.127 / 0.107 | 1.351 / 4.593 | 51.50 | 218.02 / 25.44 |
| TT | 125 | 3.966 | -0.049 / 0.063 | 1.312 / 4.487 | 47.54 | 210.28 / 20.84 |
| SS | -40 | 4.803 | -0.139 / 0.122 | 1.355 / 4.652 | 51.80 | 218.19 / 26.42 |
| SS | 27 | 4.807 | -0.127 / 0.107 | 1.328 / 4.558 | 51.46 | 218.07 / 25.43 |
| SS | 125 | 3.970 | -0.049 / 0.063 | 1.288 / 4.426 | 47.57 | 210.32 / 20.83 |
| FF | -40 | 4.803 | -0.139 / 0.122 | 1.401 / 4.732 | 51.79 | 218.18 / 26.45 |
| FF | 27 | 4.807 | -0.127 / 0.107 | 1.377 / 4.650 | 51.47 | 218.02 / 25.46 |
| FF | 125 | 3.964 | -0.049 / 0.063 | 1.338 / 4.529 | 47.56 | 210.23 / 20.85 |

All nine cases satisfy the unchanged 1 µA average / 100 µA peak cold-injection targets, ±0.3 V pad excursion, 70 mA rectifier peak, and 0.25 W resistor budgets. The 150 Ω resistor replaces a measured 220 Ω trial that dissipated 0.268–0.272 W at TT. Use the ≥0.5 W part specified in the PCB BOM and check its temperature derating. These are project screening limits, not foundry injection-current ratings or vendor-model qualification. The reference board has 85 °C-rated POR/FRAM.

## PDN detail

Three DVDD/DVSS pairs plus one core pair, 125 mΩ / 1.8 nH per bond, 1.8 nF allocated on-die decap, eight simultaneous foundry outputs into 15 pF each through 33 Ω, and a 20→120 mA core-current pulse. All 18 rail-differential and quiet-victim checks pass. The bounce/droop budget passes 8/18; every electrical failure is retained.

| Process | °C | SL | Status | South peak mV | Core min / max mV | VDD droop mV | Min VDD−VSS V |
|---|---:|---:|---|---:|---|---:|---:|
| TT | -40 | 0 | FAIL | 781.35 | -252.35 / 767.17 | 625.28 | 4.7594 |
| TT | -40 | 1 | FAIL | 742.27 | -242.23 / 733.76 | 442.67 | 4.7781 |
| TT | 27 | 0 | FAIL | 594.47 | -204.31 / 581.97 | 377.94 | 4.7629 |
| TT | 27 | 1 | FAIL | 592.77 | -240.09 / 585.77 | 325.47 | 4.7886 |
| TT | 125 | 0 | PASS | 395.52 | -97.04 / 390.16 | 214.45 | 4.7776 |
| TT | 125 | 1 | PASS | 442.94 | -154.26 / 437.95 | 218.35 | 4.8090 |
| SS | -40 | 0 | PASS | 436.60 | -89.47 / 426.76 | 252.89 | 4.2847 |
| SS | -40 | 1 | PASS | 496.98 | -183.92 / 491.86 | 267.17 | 4.3124 |
| SS | 27 | 0 | PASS | 341.02 | -86.26 / 337.90 | 206.04 | 4.3006 |
| SS | 27 | 1 | PASS | 390.19 | -135.55 / 386.48 | 180.85 | 4.3309 |
| SS | 125 | 0 | PASS | 254.49 | -79.40 / 252.86 | 169.51 | 4.3325 |
| SS | 125 | 1 | PASS | 286.19 | -66.70 / 284.04 | 108.29 | 4.3593 |
| FF | -40 | 0 | FAIL | 1200.42 | -345.10 / 1183.47 | 945.43 | 5.2416 |
| FF | -40 | 1 | FAIL | 1021.27 | -235.53 / 1009.34 | 654.08 | 5.2534 |
| FF | 27 | 0 | FAIL | 926.53 | -343.48 / 910.71 | 700.74 | 5.2403 |
| FF | 27 | 1 | FAIL | 824.70 | -271.12 / 814.43 | 502.69 | 5.2583 |
| FF | 125 | 0 | FAIL | 648.43 | -242.62 / 635.12 | 400.68 | 5.2455 |
| FF | 125 | 1 | FAIL | 617.47 | -229.48 / 609.63 | 358.98 | 5.2717 |

The worst south-bank bounce is 1.20042 V at FF/−40 °C/SL=0, with 0.945429 V droop. The board/source terminations do not close the 0.5 V budget. Package extraction, extra return paths and/or a reduced simultaneous switching load need evaluation before signoff. The 1.8 nF is an allocation, not an extracted fillcap measurement.

Numerical control: changing PDN junction gmin from 1e-12 to 1e-10 S resolved the troublesome TT/27 °C/SL=1 operating point. The paired TT/27 °C/SL=0 control changed south/core bounce by only 22 µV and droop by 6 µV; the pass limits were unchanged. Six ESD RC ladders receive released `.nodeset` guesses, not forced transient voltages.

## Verification and remaining work

- Coil calculator: existing seven self-test assertions PASS; L=1.4662 µH, Rac=0.988 Ω, Ctotal=93.95 pF. Coupling/keepout formulas remain analytical estimates.
- Independent charge/counter analysis checks PASS. Stock ngspice diode regression aborts at 1.68687851999 µs; all six repaired cases reach 5 µs. Worst dQ/dV-versus-C relative discrepancy is 1.8263×10⁻⁷.
- `../../pcb/README.md` contains the stackup, reference schematic description, BOM, POR/reset, tamper RC, NFC isolation, SPI, FRAM and test points.
- Not delivered: a routed PCB/Gerbers, extracted package/decap data, vendor-qualified discrete PVT models, ASK protocol qualification, a physical BER certification, full TDC DNL/INL, or RTL integration/security proof.
- Explicit unresolved design limits: SS/hot rapid timing and TT/FF SSN. No tests were relaxed to mark these green.
