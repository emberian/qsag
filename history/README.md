# Historical Prototypes, Academic PDK Runs & Retired Cosplay Artifacts

This directory quarantines superseded hardware prototypes and non-manufacturable EDA benchmark runs that were removed from `hardware/` so the live hardware tree contains **only manufacturable silicon and flashable/cloud FPGA targets**:

- **`hardware/ass2/` (`ASS2-0P5 / Dregg-64`):** Manufacturable `GF180MCU-D` 5.0 V security enclave targeting the `wafer.space` **`SLOT_0P5X0P5`** (`1,936 × 2,531 µm`, `56` pads) shuttle slot with real foundry `gf180mcu_fd_ip_sram__sram512x8m8wm1` SRAM, `0`-waiver 9-corner signoff, and a KiCad 8 test carrier.
- **`hardware/fpga/`:** Flashable Lattice `ECP5-85F` (`LFE5U-85F-6BG381C`) RTL and timing-closed `.bit` bitstreams.
- **`hardware/aws_f2/`:** AWS EC2 F2 (`xcvu47p-fsvh2892-2-e`, HDK 2.3.5) custom logic (`CL_QSAG_F2`).
- **`hardware/asic/`:** Synthesizable `QSAG-NI v2` autonomous WHIR verifier RTL, formal Z3/Bitwuzla/Obend equivalence proofs, and manufacturable 130 nm (`IHP SG13G2`, `Sky130 HD`) gate-count characterization.

---

## What Was Demoted Here and Why (Unfiltered Post-Mortem)

### 1. [`academic-pdk-cosplay/`](academic-pdk-cosplay) — Non-Manufacturable PDKs & Imaginary-SRAM "Signoff"
Moved from `hardware/asic/synth/{hier/nangate45, hier/asap7, hier/sky130/openroad, run_openroad.py, render_routed_png.py}`:

1. **Purposely Non-Manufacturable Academic Libraries (`Nangate45` & `ASAP7`):**
   - `Nangate45` (`FreePDK45`) and `ASAP7` (predictive 7 nm academic FinFET) are classroom/EDA-research cell libraries whose design rules correspond to **zero real semiconductor foundries**. Calling a `Nangate45` route "silicon signoff" is pure cosplay: no fab can manufacture it.
2. **Imaginary 512 KiB Dual-Port SRAM Blackboxes (`sram_dp_64x16384_bank`):**
   - `run_openroad.py` (`Basin-1`) instantiated four `16,384 × 64-bit` (`128 KiB` each = `512 KiB` total) dual-port SRAMs as **invented empty LEF/Liberty stubs** with zero bitcells, sense amplifiers, decoders, or GDSII polygons. Neither `Sky130` OpenRAM nor open `IHP SG13G2` provides a drop-in `128 KiB` synchronous dual-port macro of those dimensions.
3. **Massive Negative Setup Slack Labeled as "Signoff":**
   - The `Nangate45` OpenROAD run reported `WNS = -15.78 ns` (`38.79 MHz` achieved against a `10.0 ns` / `100 MHz` constraint), and the `Sky130` run stopped after CTS (never routed) with **`WNS = -140.72 ns` (`6.22 MHz` against a `20.0 ns` / `50 MHz` constraint)**—yet an earlier table labeled those columns `"Full Routed Signoff"` and `"Post-CTS Signoff"`.

### 2. [`dregg180-latch-prototype/`](dregg180-latch-prototype) — Retired `Dregg-180` (`4,512`-Latch Prototype)
Moved from `hardware/gf180mcu/` (including the duplicate `hardware/gf180mcu/v2/` tree):

1. **Blew Through the Only Affordable Tapeout Slot (`SLOT_0P5X0P5`):**
   - `SLOT_0P5X0P5` (`1.733 mm²` core, `56` pads) is the **only** `GF180MCU` shuttle slot within budget without external fundraising. `Dregg-180`'s `4,512` transparent `latrnq_1` latches, `188` clock gates, and unpipelined combinational cones ballooned from `1.04 mm²` pre-layout to **`2.04 mm²`** after CTS/Resizer (`41k` buffers), failing to fit or route inside `SLOT_0P5X0P5`.
2. **Waived Checks, Latch Borrowing & Tcl `$::db` Monkey-Patches on `0.5×1`:**
   - Earlier "clean DRC/LVS" claims on `Dregg-180` were obtained only by fleeing to an unaffordable `SLOT_0P5X1` (`0.5×1`) die, setting `ERROR_ON_*: False`, injecting manual OpenROAD `$::db` Tcl surgery, using `time_borrow = 10.0`, and leaving `-45.65 ns` `max_ss_125C_4v50` setup WNS and `1,556` `SS` slew violations unresolved.
3. **32-Ring Reused PUF Entropy Deficit:**
   - `Dregg-180`'s `dregg_ro_puf_bch.sv` compared `16` Bank-A ROs against `16` Bank-B ROs across `256` pairs. Because `256` pairwise comparisons of `32` frequencies carry at most $\log_2(16! \times 16!) \approx 88.5$ bits ($\le \log_2(32!) \approx 117.7$ bits) of total order entropy **before** subtracting public BCH syndrome leakage, it could never deliver 128 bits of standalone physical PUF min-entropy.
   - Its useful circuit ideas (compact CSA Goldilocks reduction, SP 800-90B `RCT`+`APT` TRNG health screens, and 512-RO disjoint-pair PUF upgrade) were folded into **`hardware/ass2/` (`ASS2-0P5`)**, and `Dregg-180` itself is retired here as an archival reference.
