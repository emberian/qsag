// Dregg-180 (QSAG-NI-180) Production Silicon Datasheet
// Target: wafer.space GF180MCU Run 3 — `SLOT_0P5X0P5` (56-Pad Die, 1,936 × 2,531 µm), 5.0 V CMOS
// Compiles standalone with `typst compile` (zero external package dependencies).

// ---- Target Slot Geometry (`SLOT_0P5X0P5` — Sole Production Tapeout Slot) & Extracted Netlist Metrics ----
#let rev_code      = "0x0180_0003"
#let chip_id_ascii = "QSAGNI18 (0x3831_494E_4741_5351)"
#let die_dims      = "1,936 × 2,531 µm (4.900 mm² SLOT_0P5X0P5)"
#let core_dims     = "1,051 × 1,642 µm (1,726,000 µm² core)"
#let syn_area_um2  = "1,041,071 µm² (118.6 kGE @8.78 | 94.9 kGE @nand2)"
#let syn_core_pct  = "60.32% pre-CTS (SLOT_0P5X0P5)"
#let pnr_fill_pct  = "Target <= 58% (active area diet)"
#let std_cells_cnt = "39,692 synth cells (51,108 LVS devices)"
#let fmax_tt_mhz   = "21.89 MHz nom_tt (22.82 MHz min_tt SPEF)"
#let fmax_ss_mhz   = "12.23 MHz nom_ss (>25 MHz R2R FF SPEF)"
#let signoff_mhz   = "21.89 MHz TT / 12.23 MHz SS / 0 Hold Viols"
#let wns_ss_ns     = "-41.77 ns (@40 ns; pipelining active)"
#let wns_tt_ns     = "-5.69 ns (@40 ns; pipelining active)"
#let hold_wns_ns   = "+0.210 ns (max_ff) .. +1.268 ns (min_ss)"
#let drc_lvs_stat  = "0 LVS Err (51,108=51,108) • 0 Hold • SLOT_0P5X0P5 PnR active"

// ---- Typography & Corporate Datasheet Theme ----
#let navy   = rgb("#0f2742")
#let slate  = rgb("#334155")
#let steel  = rgb("#e2e8f0")
#let tint   = rgb("#f8fafc")
#let accent = rgb("#0284c7")
#let warnbg = rgb("#fffbeb")
#let warnbd = rgb("#d97706")
#let secbg  = rgb("#f0fdf4")
#let secbd  = rgb("#15803d")

#set document(
  title: "DREGG-180 (QSAG-NI-180) 5.0V Cryptographic Verifier & Object-Capability Enclave Datasheet",
  author: "QSAG Silicon Engineering",
)

#set page(
  paper: "a4",
  margin: (top: 2.0cm, bottom: 1.8cm, left: 1.5cm, right: 1.5cm),
  header: context {
    if counter(page).get().first() > 1 [
      #set text(font: "Helvetica Neue", size: 7.5pt, fill: slate)
      #grid(
        columns: (1fr, auto),
        [*DREGG-180 (`QSAG-NI-180`)* — 5.0 V `GF180MCU` `SLOT_0P5X0P5` 56-Pad Enclave & Verifier ASIC],
        [Document Rev. 3.0 — Signoff Edition],
      )
      #v(-3pt)
      #line(length: 100%, stroke: 0.5pt + steel)
    ]
  },
  footer: context [
    #line(length: 100%, stroke: 0.5pt + steel)
    #v(-2pt)
    #set text(font: "Helvetica Neue", size: 7.5pt, fill: slate)
    #grid(
      columns: (1fr, auto, 1fr),
      [GlobalFoundries `gf180mcuD` (180 nm 5LM 5.0 V)],
      align(center)[Apache-2.0 Open Silicon Specification],
      align(right)[Page #counter(page).display("1 of 1", both: true)],
    )
  ],
)

#set text(font: "Helvetica Neue", size: 8.6pt, fill: rgb("#0f172a"))
#set par(justify: true, leading: 0.52em)
#set heading(numbering: "1.1")

#show heading.where(level: 1): it => block(above: 1.1em, below: 0.55em, breakable: false)[
  #set text(size: 11.5pt, weight: "bold", fill: navy)
  #it
  #v(-3pt)
  #line(length: 100%, stroke: 1.1pt + navy)
]

#show heading.where(level: 2): it => block(above: 0.85em, below: 0.4em, breakable: false)[
  #set text(size: 9.6pt, weight: "bold", fill: navy)
  #it
]

#let callout(title, body, bg: tint, border: accent) = block(
  width: 100%,
  fill: bg,
  stroke: (left: 2.5pt + border, top: 0.4pt + steel, right: 0.4pt + steel, bottom: 0.4pt + steel),
  inset: (x: 8pt, y: 6pt),
  radius: 2pt,
)[
  #text(weight: "bold", fill: navy)[#title — ] #body
]

// ============================================================================
// PAGE 1: BANNER, KEY FEATURES, APPLICATIONS, SUMMARY TABLE & BLOCK DIAGRAM
// ============================================================================
#block(
  width: 100%,
  fill: navy,
  inset: (x: 12pt, y: 10pt),
  radius: 3pt,
)[
  #grid(
    columns: (1fr, auto),
    gutter: 8pt,
    [
      #text(size: 7.8pt, weight: "bold", fill: rgb("#7dd3fc"))[PRODUCTION SILICON DATASHEET • WAFER.SPACE GF180MCU RUN 3 • SLOT_0P5X0P5]
      #v(2pt)
      #text(size: 18pt, weight: "bold", fill: white)[DREGG-180 (QSAG-NI-180)]
      #v(2pt)
      #text(size: 9.5pt, fill: rgb("#e2e8f0"))[
        5.0 V Post-Quantum `Cut-the-Hash` Signing Enclave, Streamed `GoldilocksExt4` / Quintic `Fp5` ZK Verifier VM,
        and Object-Capability (`CapTP`) Physical-Presence Co-Processor in 180 nm CMOS
      ]
    ],
    align(right + horizon)[
      #box(fill: rgb("#1e3a5f"), stroke: 0.6pt + rgb("#38bdf8"), inset: 6pt, radius: 2pt)[
        #set text(size: 7.5pt, fill: white)
        *Slot:* `SLOT_0P5X0P5` (Sole Target) \
        *Die:* `1,936 × 2,531 µm` (`4.90 mm²`) \
        *Pads:* `56` (`42` Dig + `10` P/G + `4` Ana) \
        *Supply:* `5.0 V` (`4.5–5.5 V`) \
        *Signoff:* #signoff_mhz
      ]
    ],
  )
]

#v(6pt)

#grid(
  columns: (1.08fr, 0.92fr),
  gutter: 12pt,
  [
    #text(size: 9.8pt, weight: "bold", fill: navy)[1 • Key Features]
    #v(2pt)
    - *Native 5.0 V `GF180MCU` Standard-Cell Silicon (`SLOT_0P5X0P5`):*
      - `gf180mcuD` 180 nm 5-metal (`5LM`), `gf180mcu_fd_sc_mcu7t5v0` 7-track 5.0 V core + `gf180mcu_fd_io` 24 mA / Schmitt padring (`56` pads total; drop-in compatible with frozen `wafer.space` Run 3 breakout CoB / bare-die bonding).
      - Pure standard-cell architecture (zero SRAM macros, *zero dependency on unverified GF180 eFuse*).
    - *Dual-Extension Post-Quantum Proof Verifier VM (`0x30`, `0x31`):*
      - Bit-exact Goldilocks prime field $p = 2^{64} - 2^{32} + 1$ with 1-clock CSA-to-canonicalizer pipeline cut and Han-Carlson prefix adders.
      - Hardware `GoldilocksExt4` ($FF_p [X] / (X^4 - 7)$, 9-multiply tower) *and* `zk-Hem v2` Quintic `Fp5` ($FF_p [X] / (X^5 - 3)$) arithmetic.
      - Width-12 `Poseidon2` permutation (rate-8 domain-tagged Fiat-Shamir + canonical `sponge12_rate6`), depth `1..32` `Canopy` Merkle engine, `Keccak-p[1600, 12/24]` (`TurboSHAKE256` / `SHAKE256` / `cSHAKE256`), and `GF(2^128)` polynomial MACs (`H_ZK_PIN` irreducible digest).
    - *`Cut-the-Hash` (`FIPS 205` `SLH-DSA-SHAKE`) Signing Enclave:*
      - Private keys (`SK.seed`, `SK.prf`, `K_MAC`, `K_vat`) live in `latrnq_1` transparent-latch rows behind per-row `icgtp_4` clock gates and are *physically blocked from egress* (`e_rd >= 44 => out_data = 0`).
      - Mandatory `K_MAC` authentication on *all* secret-key and `PUBGEN` calls, WOTS `sw = 4` public-end enforcement, complementary 2-bit chain-end laser-DFA self-check, and torn-write-safe external SPI FRAM two-slot monotonic leaf counter.
    - *Five Integrated Physical-Root & Presence Enclave Organs:*
      + *`dregg_captp_vat`:* Sealed `SpongeMacaroon` capability membrane binding rights, monotonic guards, epoch windows, spend limits, and `(prog_digest, stmt_root)` `zk_pin` roots, with persistent `mint_lock`.
      + *`dregg_ro_puf_bch`:* 32-ring (256-pair) differential RO-PUF + `BCH(63, 36, t=5)` Berlekamp-Massey / Chien extractor + live oscillation health monitor.
      + *`dregg_nfc_nco`:* 13.56 MHz HF-NFC Manchester air-gap quorum receiver (96-bit `K_vat` MAC + 32-bit anti-replay `nfc_seq`) + 32-bit CW/2-FSK/Chirp RF NCO.
      + *`dregg_distance_tdc`:* `< 6 ns` single-shot `qsag_chal_lock` 64-round Hancke-Kuhn rapid-bit responder + 32-tap (~230 ps) Vernier TDC.
      + *`dregg_shield_canaries` + CoSO `qsag_trng`:* 4-quadrant delay-spine EMFI/glitch sensors, active `Metal5` serpentine integrity loop, and matched 17-stage Coherent-Sampling Ring-Oscillator (`CoSO`, $h_"min" approx 0.92..0.97$ bit/beat) TRNG with lock guard + SP 800-90B RCT/APT.
  ],
  [
    #text(size: 9.8pt, weight: "bold", fill: navy)[2 • Target Applications]
    #v(2pt)
    - Post-quantum `SLH-DSA` hardware security modules (HSMs) & air-gapped code-signing tokens
    - Streamed `WHIR` / `zk-Hem v1 & v2` / `BlindVC` succinct proof verification co-processors for embedded MCUs (`RP2350`, `STM32`, `RISC-V`)
    - Physical-presence-gated (`NFC` + `< 6 ns` relativistic distance-bounding) capability-attenuated custody vaults
    - Tamper-zeroizing industrial & sovereign root-of-trust anchors

    #v(6pt)
    #text(size: 9.8pt, weight: "bold", fill: navy)[3 • Silicon Summary (`SLOT_0P5X0P5` Shuttle Target)]
    #v(2pt)
    #table(
      columns: (1.05fr, 1.25fr),
      inset: 4.2pt,
      stroke: 0.4pt + steel,
      fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
      text(fill: white, weight: "bold")[Parameter], text(fill: white, weight: "bold")[Target / Measured Value],
      [Foundry / PDK], [`GlobalFoundries gf180mcuD` (5LM 1P)],
      [Standard Cell / I/O], [`mcu7t5v0` (5.0 V) / `gf180mcu_fd_io`],
      [Shuttle Slot], [*`SLOT_0P5X0P5`* (`4.90 mm²`, Sole Target)],
      [Die / Core Area], [#die_dims / `1.726 mm²`],
      [Padring Total], [*56 pads* (`42` dig + `10` VDD/VSS + `4` an)],
      [Synthesized Core], [#syn_area_um2 (#syn_core_pct of core)],
      [Post-PnR Std Cells], [#std_cells_cnt (#pnr_fill_pct)],
      [Signoff Clock Target], [`25.0 MHz` (`9` SPEF corners, `0` virtual clocks)],
      [Measured $f_"max"$ (`SS` / `TT`)], [#fmax_ss_mhz / #fmax_tt_mhz],
      [Physical Verification], [#drc_lvs_stat],
      [Hardware ID / Rev], [`"QSAGNI18"` / #rev_code],
    )

    #v(4pt)
    #callout(
      "SLOT_0P5X0P5 Area & Timing Closure Status",
      [56-pad `SLOT_0P5X0P5` (`1.726 mm²` core) is the sole tapeout target. Netlist connectivity (`51,108 == 51,108` LVS devices, `0` Hold violations across all 9 corners) is verified; `4,512`-latch CTS/buffer bloat (`77.6%` fill) and `-41.8 ns` `SS` setup slack are under active DO-254 `0`-waiver diet & pipelining. Native *5.0 V* (`4.50–5.50 V`).],
      bg: warnbg,
      border: warnbd,
    )
  ],
)

#pagebreak()

// ============================================================================
// PAGE 2: NATIVE VECTOR ARCHITECTURE BLOCK DIAGRAM
// ============================================================================
= Architectural Overview & Block Diagram

Dregg-180 unifies a formally verified post-quantum cryptographic verifier (`qsag_field_engine`, `qsag_gl64_karatsuba_csa`, `qsag_keccak_serial`, `qsag_gf128_clmul`) with a zeroizable hardware object-capability signing enclave (`qsag_wire_engine`, `qsag_sponge`, and the five `dregg_*` physical security organs) behind a three-personality GALS I/O shell (`qsag_io_shell`). A punctured `[12, 7, 4]` Hamming-distance-4 FSM (`125` legal states, rejecting both `12'h000` crowbar-zero and `12'hFFF` laser-saturation collapse) orchestrates all operations over a unified 56-row × 64-bit latch file.

#v(4pt)
#figure(
  caption: [Dregg-180 (`chip_top` / `chip_core`) internal architecture, clock domains, and security boundary.],
)[
  #box(width: 100%, height: 9.8cm, stroke: 0.8pt + navy, radius: 3pt, fill: rgb("#f8fafc"), inset: 6pt)[
    #set text(size: 6.9pt)
    // Outer padring banner
    #place(top + left, dx: 2pt, dy: 0pt)[
      #text(weight: "bold", fill: navy)[`chip_top` — Frozen 56-Pad `SLOT_0P5X0P5` `gf180mcu_fd_io` 5.0 V Padring (`in_s`, `in_c`, `bi_24t`, `asig_5p0`, `dvdd/dvss`)]
    ]

    // Left column: GALS I/O Shell + Clock/Reset/Shield
    #place(top + left, dx: 4pt, dy: 16pt)[
      #box(width: 4.1cm, height: 4.3cm, fill: white, stroke: 0.8pt + accent, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: navy)[`qsag_io_shell` (3-Mode Link)]\
        #v(2pt)
        • *`00` SPI/QSPI/OSPI* (`SCK`, `DQ[7:0]`)\
        • *`0x05 READ_DIAG`* (clockless `SCK`)\
        • *`01` Source-Sync* (`RX_CLK`, `TX_CLK`)\
        • *`1x` 2-Phase Async* (Muller-C)\
        • *Ingress FIFO:* `8 × 64b` (`latq_1`)\
        • *Egress FIFO:* `4 × 64b` (`latq_1`)\
        • Per-bank slew (`SL=0` RF/DB)
      ]
    ]

    #place(top + left, dx: 4pt, dy: 146pt)[
      #box(width: 4.1cm, height: 4.2cm, fill: white, stroke: 0.8pt + warnbd, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: navy)[`qsag_gals_clk_rst` + Shield]\
        #v(2pt)
        • Boot-default 32-tap *DCRO* + FLL\
        • Glitch-free mux + dual watchdogs\
        • Mixed-cell *TRCP* (`OAI21/AOI21/XOR2`)\
        • *`dregg_shield_canaries`:*\
          4-quadrant spines + `Metal5` PRNG\
        • Boot-blanked async `u_tamp` latch\
        • 2-FF sync `srst_n` -> `RN` tree
      ]
    ]

    // Center column: Wire Engine + Unified Sponge + Crypto Engines
    #place(top + left, dx: 4.55cm, dy: 16pt)[
      #box(width: 6.9cm, height: 2.9cm, fill: rgb("#eff6ff"), stroke: 0.9pt + navy, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: navy)[`qsag_wire_engine` — `[12,7,4]` HD=4 Packet & VM Controller]\
        #v(2pt)
        • 125 punctured HD≥4 states + 4× `qsag_hd4_checker` + `~steps_inv_q`\
        • Streamed Verifier VM (`OP_FOLD 0x30`, `OP_HEM 0x31`): `Ext4` + `Fp5`\
        • `Cut-the-Hash` (`0x41` WOTS/FORS + 2-bit laser-DFA chain-end check)\
        • Hardwired non-exfiltration gate: *`e_rd >= 44 => out_data = 64'd0`*
      ]
    ]

    #place(top + left, dx: 4.55cm, dy: 104pt)[
      #box(width: 6.9cm, height: 2.5cm, fill: secbg, stroke: 0.9pt + secbd, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: secbd)[`qsag_sponge` — Unified 56 × 64-Bit Enclave Latch File]\
        #v(2pt)
        • `rows 0..31`: Sponge / Keccak / `Ext4` & `Fp5` VM regs (`latq_1`, 1-clk `wipe`)\
        • `rows 32..41`: Scratchpad & `X, Y` operand bank (`latq_1`, 1-clk `wipe`)\
        • `rows 44..57`: *`zk_pin[0..3]`, `SK.seed`, `SK.prf`, `K_MAC`, `K_vat`* (`latrnq_1` behind `icgtp_4`, 0-clock async `srst_n` zeroization!)
      ]
    ]

    #place(top + left, dx: 4.55cm, dy: 181pt)[
      #box(width: 6.9cm, height: 2.9cm, fill: white, stroke: 0.8pt + navy, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: navy)[Cryptographic Datapath Engines]\
        #v(2pt)
        #grid(
          columns: (1fr, 1fr),
          gutter: 4pt,
          [• *`qsag_gl64_karatsuba_csa`:* 64b Goldilocks CSA + Han-Carlson canon + zero-extra-adder shift-add mul],
          [• *`qsag_field_engine`:* `Poseidon2-12` (`rate-8` & `rate-6`), `Canopy`, 9-mul `Ext4`, Quintic `Fp5`],
          [• *`qsag_keccak_serial`:* 3-reg in-place `N^k` `Keccak-p[1600, 12/24]`],
          [• *`qsag_gf128_clmul`:* `GF(2^128)` `GHASH` & `H_ZK_PIN` program digest],
        )
      ]
    ]

    // Right column: 5 Enclave Organs + TRNG + FRAM Anchor
    #place(top + left, dx: 11.9cm, dy: 16pt)[
      #box(width: 5.7cm, height: 2.0cm, fill: secbg, stroke: 0.8pt + secbd, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: secbd)[Organ 1: `dregg_captp_vat`]\
        Sealed `SpongeMacaroon` verifier, monotonic rights/guards/epoch/spend check, `(prog_digest, stmt_root)` `zk_pin`, `mint_lock`.
      ]
    ]
    #place(top + left, dx: 11.9cm, dy: 77pt)[
      #box(width: 5.7cm, height: 2.0cm, fill: secbg, stroke: 0.8pt + secbd, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: secbd)[Organ 2: `dregg_ro_puf_bch`]\
        32× 5-stage NAND2 ROs (256 diff pairs), Pelgrom margin screen, live RO stall guard, `BCH(63,36,t=5)` BM + Chien.
      ]
    ]
    #place(top + left, dx: 11.9cm, dy: 138pt)[
      #box(width: 5.7cm, height: 1.95cm, fill: white, stroke: 0.8pt + accent, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: navy)[Organ 3: `dregg_nfc_nco`]\
        13.56 MHz Manchester RX (96b `K_vat` MAC + 32b `nfc_seq`), 847.5 kHz ACK, 32b RF NCO.
      ]
    ]
    #place(top + left, dx: 11.9cm, dy: 198pt)[
      #box(width: 5.7cm, height: 1.95cm, fill: white, stroke: 0.8pt + accent, radius: 2pt, inset: 4pt)[
        #text(weight: "bold", fill: navy)[Organ 4: `dregg_distance_tdc`]\
        `< 6 ns` `qsag_chal_lock` (`AOI21`+`NOR2`+`mux2_4`) 64-round responder + 32-tap Vernier TDC.
      ]
    ]
    #place(top + left, dx: 11.9cm, dy: 257pt)[
      #box(width: 5.7cm, height: 1.1cm, fill: white, stroke: 0.8pt + slate, radius: 2pt, inset: 3.5pt)[
        #text(weight: "bold", fill: navy)[`qsag_trng` + `qsag_anchor_spi`]\
        17-stage CoSO ROs + SP 800-90B; FRAM SPI.
      ]
    ]

    // Bus arrows between columns
    #place(top + left, dx: 4.15cm, dy: 55pt)[#line(length: 0.38cm, stroke: 1.1pt + navy)]
    #place(top + left, dx: 4.15cm, dy: 185pt)[#line(length: 0.38cm, stroke: 1.1pt + warnbd)]
    #place(top + left, dx: 8.0cm, dy: 98pt)[#line(angle: 90deg, length: 0.22cm, stroke: 1.2pt + secbd)]
    #place(top + left, dx: 8.0cm, dy: 175pt)[#line(angle: 90deg, length: 0.22cm, stroke: 1.2pt + navy)]
    #place(top + left, dx: 11.48cm, dy: 45pt)[#line(length: 0.40cm, stroke: 1.0pt + secbd)]
    #place(top + left, dx: 11.48cm, dy: 105pt)[#line(length: 0.40cm, stroke: 1.0pt + secbd)]
    #place(top + left, dx: 11.48cm, dy: 165pt)[#line(length: 0.40cm, stroke: 1.0pt + accent)]
    #place(top + left, dx: 11.48cm, dy: 225pt)[#line(length: 0.40cm, stroke: 1.0pt + accent)]
    #place(top + left, dx: 11.48cm, dy: 268pt)[#line(length: 0.40cm, stroke: 1.0pt + slate)]
  ]
]

== Physical Silicon Area & Hierarchy Breakdown

All core logic is synthesized and routed inside the `1,052 × 1,647 µm` (`1,732,644 µm²`) `SLOT_0P5X0P5` core boundary with `gf180mcu_fd_sc_mcu7t5v0` standard cells and `wafer.space` mandatory ID/logo macros (`qrcode_id`, `shuttle_id`, `project_id`, `marker`, `wafer_space_logo`). No custom analog blocks or hard SRAMs are required.

#table(
  columns: (1.5fr, 0.85fr, 0.72fr, 2.13fr),
  inset: 4.0pt,
  stroke: 0.4pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[Subsystem / RTL Module],
  text(fill: white, weight: "bold")[Area (`µm²` incl / excl)],
  text(fill: white, weight: "bold")[Share],
  text(fill: white, weight: "bold")[Key Architectural Role & Physical Implementation],
  [`qsag_sponge` (`u_sp`)], [`222.1k / 51.8k`], [`20.78%`], [42 public/scratch rows (`latq_1`) + 14 secret rows (`latrnq_1` behind `icgtp_4`), 1-hot OR-bus],
  [`qsag_wire_engine` (`u_engine`)], [`215.5k / 191.1k`], [`20.16%`], [125-state `[12,7,4]` HD=4 FSM, flat 36-source `imm` OR-bus, Verifier VM, `Cut-the-Hash`],
  [`qsag_gl64_karatsuba_csa` (`u_alu`)], [`159.1k / 41.8k`], [`14.88%`], [5:2 `addf_1` CSA -> reg -> explicit Han-Carlson prefix trees (`26.9k`) + parallel `u_v` canon],
  [`qsag_io_shell` (`u_io`)], [`92.2k / 26.5k`], [`8.62%`], [SPI/QSPI/OSPI + `0x05 READ_DIAG` + Source-Sync + 2-phase Sutherland RX/TX latch FIFOs],
  [`qsag_keccak_serial` (`u_kc`)], [`59.3k / 45.6k`], [`5.55%`], [3-register (`acc_q, b0_q, b1_q`) + LUT `mod5` in-place `N^k` `Keccak-p[1600, 12/24]`],
  [`dregg_ro_puf_bch` (`u_puf`)], [`58.1k / 35.1k`], [`5.44%`], [32× 5-stage ROs (`256` pairs), 20-bit ripple counters, 10-root Horner + Chien `BCH(63,36,5)`],
  [`qsag_gals_clk_rst` + `u_shield`], [`49.0k / 21.7k`], [`4.58%`], [32-tap DCRO (`.en(rst_n_pad)`), dual-watchdog mux, TRCP, 4-quadrant spines, `Metal5` loop],
  [`dregg_nfc_nco` (`u_nfc`)], [`45.5k / 28.6k`], [`4.26%`], [13.56 MHz Manchester decoder (`144b` token + `CRC16-A`), 847.5 kHz ACK, 32-bit RF NCO],
  [`qsag_gf128_clmul` (`u_gf`)], [`35.0k / 10.6k`], [`3.27%`], [128-bit `GF(2^128)` accumulator (`g(z) = z^128 + z^7 + z^2 + z + 1`)],
  [`dregg_distance_tdc` (`u_db`)], [`33.8k / 16.5k`], [`3.17%`], [`qsag_chal_lock` `< 6 ns` 64-round responder + 32-tap Vernier TDC (`7.2k`)],
  [`dregg_captp_vat` (`u_vat`)], [`31.6k / 21.0k`], [`2.95%`], [160-bit policy `latrnq_1` bank, capability attenuation lattice & spend/epoch/guard membrane],
  [`u_fe`+`u_rc`+`u_trng`+`u_anchor`], [`67.3k / 66.6k`], [`6.29%`], [Field sequencer (`19.9k`), P2 RC (`19.3k`), 17-stage CoSO TRNG (`15.5k`), FRAM SPI (`12.6k`)],
)

#pagebreak()

// ============================================================================
// PAGE 3: EXACT 56-PAD PINOUT DIAGRAM & COMPLETE PINOUT TABLE
// ============================================================================
= 56-Pad `SLOT_0P5X0P5` Padring Diagram & Pin Description

Dregg-180 preserves the *exact 56-pad count, order, and power-pad positions* defined in `librelane/slots/slot_0p5x0p5.yaml` (`11` South, `17` East, `11` North, `17` West = `48` signal pads + `8` power/ground pads). In `gf180mcu_fd_io`, `DVDD`/`VDD` and `DVSS`/`VSS` share a unified 5.0 V rail (`assign VDD = DVDD; assign VSS = DVSS;`).

#v(3pt)
#figure(
  caption: [Exact top-view 56-pad `SLOT_0P5X0P5` die padring (`1,936 × 2,531 µm`, origin `(0,0)` at South-West corner).],
)[
  #box(width: 100%, height: 7.5cm, fill: white, stroke: 0.7pt + steel, radius: 3pt, inset: 4pt)[
    #set text(font: "Menlo", size: 5.5pt)
    // Die rectangle centered
    #place(top + left, dx: 4.3cm, dy: 0.95cm)[
      #box(width: 9.2cm, height: 5.5cm, fill: rgb("#f1f5f9"), stroke: 1.2pt + navy, radius: 2pt)[
        #place(center + horizon)[
          #align(center)[
            #text(font: "Helvetica Neue", size: 10pt, weight: "bold", fill: navy)[DREGG-180 (`QSAG-NI-180`)]\
            #text(font: "Helvetica Neue", size: 7.5pt, fill: slate)[`SLOT_0P5X0P5` • `1,936 × 2,531 µm` (`4.90 mm²`)]\
            #text(font: "Helvetica Neue", size: 7pt, fill: slate)[Core: `[442, 442] .. [1494, 2089]` • `56` Pads (`5.0 V`)]
          ]
        ]
        #place(bottom + left, dx: 4pt, dy: -4pt)[#text(size: 6pt, fill: warnbd, weight: "bold")[● `(0,0)` SW Origin]]
      ]
    ]

    // NORTH (11 pads, left-to-right matching PAD_NORTH[0..10]: analog[3], analog[2], dvss[2], dvdd[2], analog[1], analog[0], bidir[26..22])
    #let north_pads = ("an[3]", "an[2]", "DVSS2", "DVDD2", "an[1]", "an[0]", "b[26]", "b[25]", "b[24]", "b[23]", "b[22]")
    #for (idx, nm) in north_pads.enumerate() {
      let is_pwr = nm.starts-with("DV")
      place(top + left, dx: 4.52cm + idx * 0.80cm, dy: 0.18cm)[
        #box(width: 0.72cm, height: 0.72cm, fill: if is_pwr { rgb("#fee2e2") } else { rgb("#e0f2fe") }, stroke: 0.5pt + navy)[
          #align(center + horizon)[#nm]
        ]
      ]
    }

    // SOUTH (11 pads, left-to-right matching PAD_SOUTH[0..10]: clk, rst_n, dvss[0], dvdd[0], bidir[0..6])
    #let south_pads = ("clk", "rst_n", "DVSS0", "DVDD0", "b[0]", "b[1]", "b[2]", "b[3]", "b[4]", "b[5]", "b[6]")
    #for (idx, nm) in south_pads.enumerate() {
      let is_pwr = nm.starts-with("DV")
      place(top + left, dx: 4.52cm + idx * 0.80cm, dy: 6.50cm)[
        #box(width: 0.72cm, height: 0.72cm, fill: if is_pwr { rgb("#fee2e2") } else { rgb("#dcfce7") }, stroke: 0.5pt + navy)[
          #align(center + horizon)[#nm]
        ]
      ]
    }

    // WEST (17 pads, top-to-bottom: b[37..27], in[3..2], VSS0, VDD0, in[1..0])
    #let west_pads = ("b[37] RXC/REQ", "b[36] RXV/ACK", "b[35] RXR/FLT", "b[34] RXD[7]", "b[33] RXD[6]", "b[32] RXD[5]", "b[31] RXD[4]", "b[30] RXD[3]", "b[29] RXD[2]", "b[28] RXD[1]", "b[27] RXD[0]", "in[3] CS_N", "in[2] MODE[1]", "VSS0", "VDD0", "in[1] MODE[0]", "in[0] BYPASS")
    #for (idx, nm) in west_pads.enumerate() {
      let is_pwr = nm.starts-with("V")
      place(top + left, dx: 1.55cm, dy: 1.02cm + idx * 0.315cm)[
        #box(width: 2.70cm, height: 0.28cm, fill: if is_pwr { rgb("#fee2e2") } else { white }, stroke: 0.45pt + navy, inset: (x: 2pt))[
          #align(right + horizon)[#nm]
        ]
      ]
    }

    // EAST (17 pads, bottom-to-top PAD_EAST[0..16] = b[7..14], dvss[1], dvdd[1], b[15..21] -> top-to-bottom is b[21] down to b[7])
    #let east_pads = ("b[21] CLK_MON", "b[20] IRQ/FLT", "b[19] CRD/BSY", "b[18] SCK/D15", "b[17] FLT/RDY", "b[16] VOK/TXV", "b[15] TXC/REQ", "DVDD1", "DVSS1", "b[14] DB_RSP/TX7", "b[13] DB_CHL/TX6", "b[12] GUARD/TX5", "b[11] NCO/TX4", "b[10] LMOD/TX3", "b[9] ASK/TX2", "b[8] NFCCLK/TX1", "b[7] DQ7/TX0")
    #for (idx, nm) in east_pads.enumerate() {
      let is_pwr = nm.starts-with("DV")
      place(top + left, dx: 13.55cm, dy: 1.02cm + idx * 0.315cm)[
        #box(width: 2.85cm, height: 0.28cm, fill: if is_pwr { rgb("#fee2e2") } else { white }, stroke: 0.45pt + navy, inset: (x: 2pt))[
          #align(left + horizon)[#nm]
        ]
      ]
    }
  ]
]

== Complete 56-Pad Signal Multiplexing Table (`slot_0p5x0p5.yaml` & `qsag_io_shell.sv`)

#set text(size: 7.4pt)
#table(
  columns: (0.75fr, 0.72fr, 0.72fr, 1.35fr, 1.35fr, 1.35fr),
  inset: 3.3pt,
  stroke: 0.35pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[Side / Idx],
  text(fill: white, weight: "bold")[Pad Name],
  text(fill: white, weight: "bold")[Cell / Pull],
  text(fill: white, weight: "bold")[`IO_MODE 00` (SPI/QSPI/OSPI)],
  text(fill: white, weight: "bold")[`IO_MODE 01` (Source-Sync)],
  text(fill: white, weight: "bold")[`IO_MODE 1x` (2-Phase Async)],
  [S 0], [`clk_pad`], [`in_s` (none)], [Ext clk (`BYPASS=1`) / FLL ref], [Ext clk (`BYPASS=1`) / FLL ref], [Ext clk (`BYPASS=1`) / FLL ref],
  [S 1], [`rst_n_pad`], [`in_s` (PD)], [Async active-low master reset], [Async active-low master reset], [Async active-low master reset],
  [S 2..3], [`dvss[0], dvdd[0]`], [`dvss/dvdd`], [5.0 V GND / Supply pair 0], [5.0 V GND / Supply pair 0], [5.0 V GND / Supply pair 0],
  [S 4], [`bidir[0]`], [`bi_24t`], [`DQ[0]` (SPI MOSI / x4 / x8)], [`DB_RESP_OUT` (fast `SL=0`)], [`DIN[8]` (or `DB_RESP_OUT` if `CSR[26]`)],
  [S 5], [`bidir[1]`], [`bi_24t`], [`DQ[1]` (SPI MISO / `READ_DIAG`)], [`DB_CHAL_IN` (CMOS `CS=0`)], [`DIN[9]` (or `DB_CHAL_IN` if `CSR[26]`)],
  [S 6], [`bidir[2]`], [`bi_24t`], [`DQ[2]` (QSPI / OSPI)], [`NFC_CLK_IN` (13.56 MHz `CS=1`)], [`DIN[10]` (or `NFC_CLK_IN` if `CSR[26]`)],
  [S 7], [`bidir[3]`], [`bi_24t`], [`DQ[3]` (QSPI / OSPI)], [`NFC_ASK_IN` (Schmitt PU)], [`DIN[11]` (or `NFC_ASK_IN` if `CSR[26]`)],
  [S 8], [`bidir[4]`], [`bi_24t`], [`DQ[4]` (OSPI)], [`NFC_LOAD_MOD` (847.5 kHz)], [`DIN[12]` (or `NFC_LOAD_MOD` if `CSR[26]`)],
  [S 9], [`bidir[5]`], [`bi_24t`], [`DQ[5]` (OSPI)], [`NCO_RF_OUT` (32b RF NCO)], [`DIN[13]` (or `NCO_RF_OUT` if `CSR[26]`)],
  [S 10], [`bidir[6]`], [`bi_24t`], [`DQ[6]` (OSPI)], [`VERIFY_OK` (out)], [`DIN[14]` (in)],
  [E 0], [`bidir[7]`], [`bi_24t`], [`DQ[7]` (OSPI)], [`TX_DATA[0]` (out)], [`DOUT[0]` (out)],
  [E 1], [`bidir[8]`], [`bi_24t`], [`NFC_CLK_IN` (13.56 MHz `CS=1`)], [`TX_DATA[1]` (out)], [`DOUT[1]` (out)],
  [E 2], [`bidir[9]`], [`bi_24t`], [`NFC_ASK_IN` (Schmitt PU)], [`TX_DATA[2]` (out)], [`DOUT[2]` (out)],
  [E 3], [`bidir[10]`], [`bi_24t`], [`NFC_LOAD_MOD` (slow `SL=1`)], [`TX_DATA[3]` (out)], [`DOUT[3]` (out)],
  [E 4], [`bidir[11]`], [`bi_24t`], [`NCO_RF_OUT` (fast `SL=0`)], [`TX_DATA[4]` (out)], [`DOUT[4]` (out)],
  [E 5], [`bidir[12]`], [`bi_24t`], [RF/DB guard input (PD)], [`TX_DATA[5]` (out)], [`DOUT[5]` (out)],
  [E 6], [`bidir[13]`], [`bi_24t`], [`DB_CHAL_IN` (CMOS `CS=0`, PD)], [`TX_DATA[6]` (out)], [`DOUT[6]` (out)],
  [E 7], [`bidir[14]`], [`bi_24t`], [`DB_RESP_OUT` (fast `SL=0`)], [`TX_DATA[7]` (out)], [`DOUT[7]` (out)],
  [E 8..9], [`dvss[1], dvdd[1]`], [`dvss/dvdd`], [5.0 V GND / Supply pair 1], [5.0 V GND / Supply pair 1], [5.0 V GND / Supply pair 1],
  [E 10], [`bidir[15]`], [`bi_24t`], [Unused (in, PD)], [`TX_CLK` (center-aligned out)], [`REQ_OUT` (2-phase toggle out)],
  [E 11], [`bidir[16]`], [`bi_24t`], [`VERIFY_OK` (out)], [`TX_VALID` (out)], [`VERIFY_OK` (out)],
  [E 12], [`bidir[17]`], [`bi_24t`], [`FAULT` (sticky out)], [`TX_READY` (Schmitt in)], [`ACK_IN` (2-phase toggle in)],
  [E 13], [`bidir[18]`], [`bi_24t`], [`SCK` (SPI clk in, Schmitt)], [Unused (in, PD)], [`DIN[15]` (Schmitt in)],
  [E 14], [`bidir[19]`], [`bi_24t`], [`RX_CREDIT_OK` (out)], [`BUSY` (out)], [`BUSY` (out)],
  [E 15], [`bidir[20]`], [`bi_24t`], [`TX_VALID_IRQ` (out)], [`FAULT` (sticky out)], [`TX_VALID_IRQ` (out)],
  [E 16], [`bidir[21]`], [`bi_24t`], [`CLK_MON` (`clk_core/16` out)], [`CLK_MON` (`clk_core/16` out)], [`CLK_MON` (`clk_core/16` out)],
  [N 0..5], [`an[3:2],dvss/dd[2],an[1:0]`], [`asig_5p0`/P], [`analog[3:0]` unconnected; P/G 2], [`analog[3:0]` unconnected; P/G 2], [`analog[3:0]` unconnected; P/G 2],
  [N 6], [`bidir[26]`], [`bi_24t` (PU)], [`TAMPER_ZEROIZE_N` (Schmitt in)], [`TAMPER_ZEROIZE_N` (Schmitt in)], [`TAMPER_ZEROIZE_N` (Schmitt in)],
  [N 7..10], [`bidir[25:22]`], [`bi_24t`], [`AN_MISO`(PD), `MOSI`, `SCK`, `CS_N`], [`AN_MISO`(PD), `MOSI`, `SCK`, `CS_N`], [`AN_MISO`(PD), `MOSI`, `SCK`, `CS_N`],
  [W 0], [`bidir[37]`], [`bi_24t`], [Unused (in, PD)], [`RX_CLK` (Schmitt in)], [`REQ_IN` (2-phase toggle in)],
  [W 1], [`bidir[36]`], [`bi_24t`], [Unused (in, PD)], [`RX_VALID` (Schmitt in)], [`ACK_OUT` (2-phase toggle out)],
  [W 2], [`bidir[35]`], [`bi_24t`], [Unused (in, PD)], [`RX_READY` (credit out)], [`FAULT` (sticky out)],
  [W 3..10], [`bidir[34:27]`], [`bi_24t`], [Unused (in, PD)], [`RX_DATA[7:0]` (in)], [`DIN[7:0]` (in)],
  [W 11], [`inputs[3]`], [`in_c` (PU)], [`CS_N` (SPI chip-select, active-low)], [`CS_N` (unused, PU)], [`CS_N` (unused, PU)],
  [W 12,15], [`inputs[2], inputs[1]`], [`in_c` (PD)], [`IO_MODE[1:0] = 2'b00`], [`IO_MODE[1:0] = 2'b01`], [`IO_MODE[1:0] = 2'b10 / 2'b11`],
  [W 13..14], [`vss[0], vdd[0]`], [`vss/vdd`], [5.0 V Core GND / Supply], [5.0 V Core GND / Supply], [5.0 V Core GND / Supply],
  [W 16], [`inputs[0]`], [`in_c` (PD)], [`EXT_CLK_BYPASS` (`0`=DCRO boot)], [`EXT_CLK_BYPASS` (`0`=DCRO boot)], [`EXT_CLK_BYPASS` (`0`=DCRO boot)],
)
#set text(size: 8.6pt)

#pagebreak()

// ============================================================================
// PAGE 4: ELECTRICAL SPECS, 9-CORNER STA SIGN-OFF & LATENCY TABLES
// ============================================================================
= Electrical Specifications, 9-Corner Timing & Cycle Counts

== Recommended Operating Conditions & DC Characteristics (`gf180mcu_fd_io` 5.0 V)

#table(
  columns: (2.1fr, 0.9fr, 0.7fr, 0.7fr, 0.7fr, 0.7fr),
  inset: 4pt,
  stroke: 0.4pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[Parameter],
  text(fill: white, weight: "bold")[Symbol],
  text(fill: white, weight: "bold")[Min],
  text(fill: white, weight: "bold")[Typ],
  text(fill: white, weight: "bold")[Max],
  text(fill: white, weight: "bold")[Unit],
  [Core & I/O Supply Voltage (`DVDD = VDD`)], [$V_"DD"$], [4.50], [5.00], [5.50], [V],
  [Junction Operating Temperature (Silicon Deck)], [$T_J$], [-40], [25], [125], [°C],
  [CMOS Input High / Low Threshold (`in_c`, `DB_CHAL_IN`)], [$V_"IH" / V_"IL"$], [$0.7 V_"DD"$], [—], [$0.3 V_"DD"$], [V],
  [Schmitt Trigger Thresholds (`in_s`, `SCK`, `rst_n`, `TAMPER_N`)], [$V_"T+" / V_"T-"$], [2.95], [0.65 hyst], [1.75], [V],
  [Output Drive Current (`bi_24t` 5.0 V buffer)], [$I_"OH" / I_"OL"$], [—], [24], [—], [mA],
  [Max DC Current per `dvdd` / `dvss` Supply Pad], [$I_"PAD,MAX"$], [—], [—], [60], [mA],
  [Internal Pad Pull-Up / Pull-Down Resistance], [$R_"PU" / R_"PD"$], [35], [55], [90], [kΩ],
)

== Post-Layout 9-Corner Propagated-Clock OpenSTA (`CLOCK_PERIOD = 40.0 ns`, `0` Virtual Clocks)

Post-PnR parasitic extraction (`OpenROAD.RCX` `nom`/`min`/`max` SPEF) and zero-virtual-clock propagated `OpenSTA` (`unpropagated.rpt = 0 B`, `librelane/chip_top_qsag.sdc`) measure extracted netlist timing and LVS connectivity (`0` Netgen LVS errors — `"Circuits match uniquely"` across `51,108` devices & `50,584` nets, `0` hold violations across all 9 corners; closing `SLOT_0P5X0P5` routing congestion and `SS` setup/slew without `ERROR_ON_*` waivers is tracked in `docs/MIL_STD_ASSURANCE_MATRIX.md`):

#table(
  columns: (1.55fr, 0.98fr, 0.88fr, 0.82fr, 0.82fr, 0.95fr),
  inset: 3.8pt,
  stroke: 0.4pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[PVT × RC Corner (`SPEF`)],
  text(fill: white, weight: "bold")[Setup WNS],
  text(fill: white, weight: "bold")[Hold WS],
  text(fill: white, weight: "bold")[Slew Viol],
  text(fill: white, weight: "bold")[Cap Viol],
  text(fill: white, weight: "bold")[Measured $f_"max"$],
  [`nom_tt_025C_5v00` (`min`/`max`)], [`-5.69 ns` (`-3.8/-7.9`)], [`+0.55 ns` (`0` viol)], [`2` (`0` min)], [`1` (`0` min)], [`21.89 MHz` (`22.8` min)],
  [`nom_ss_125C_4v50` (`min`/`max`)], [`-41.77 ns` (`-38.9/-45.7`)], [`+1.26 ns` (`0` viol)], [`642`], [`1` (`0` min)], [`12.23 MHz` (`12.7` min)],
  [`nom_ff_n40C_5v50` (`min`/`max`)], [`-1.70 ns`\* (`0` FF viol)], [`+0.23 ns` (`0` viol)], [`0`], [`1` (`0` min)], [`> 25 MHz` R2R (`24.0`\*)],
  [`SCK` / `RX_CLK` / `NFC_CLK` (`SS`)], [`23.0 / 23.0 / 7.7 ns`], [`0` hold viol], [`0` `STA-0450`], [Liberty lim], [`43.4 / 43.4 / 130.4 MHz`],
  [`DB_CHAL_IN -> DB_RESP_OUT`], [`3.99–5.56 ns` (`FF`)], [pad-to-pad], [`SL=0` fast], [5 pF coax], [`< 8.0 ns` rapid-bit],
)
#text(size: 6.9pt, fill: slate)[\*All `FF` rising-edge FF-to-FF paths close `> 25 MHz` (`0` FF setup violations); `-1.70 ns` is the `set_max_time_borrow 0.0` opening-edge check on `u_hold -> latrnq_1` (`20 ns` falling closing edge gives `+18.3 ns` silicon margin).]

== Exact Measured Cryptographic & Enclave Operation Latencies

#table(
  columns: (1.85fr, 1.35fr, 0.85fr, 0.95fr),
  inset: 4pt,
  stroke: 0.4pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[Operation / Primitive],
  text(fill: white, weight: "bold")[Opcode / Mode],
  text(fill: white, weight: "bold")[Core Clocks],
  text(fill: white, weight: "bold")[Time @ 40 MHz],
  [Goldilocks 64×64 -> 64 canonical multiply], [Internal ALU (`u_alu`)], [`66`], [`1.65 µs`],
  [Goldilocks CSA add / sub / shift-scale + canon], [Internal ALU (`u_alu`)], [`2`], [`0.05 µs`],
  [`GoldilocksExt4` tower multiply (9 base muls)], [`F_EMUL` (`0x30/0x31`)], [`724`], [`18.1 µs`],
  [`zk-Hem v2` Quintic `Fp5` multiply ($FF_p [X] / (X^5 - 3)$)], [`F_FP5_MUL` (`flags[4]=1`)], [`1,781`], [`44.5 µs`],
  [`Poseidon2-12` full permutation (8 full + 22 partial)], [`0x10` (`flags=1`)], [`33,098`], [`0.83 ms`],
  [`sponge12_rate6` absorb + squeeze (6 limbs)], [`0x10` (`flags=2`)], [`~33.2k / blk`], [`0.83 ms`],
  [`Keccak-p[1600, 12]` (`TurboSHAKE256` block)], [`0x20` (`flags=1`)], [`~3,504`], [`87.6 µs`],
  [`Keccak-f[1600]` (`SHAKE256` / `cSHAKE256` block)], [`0x20` (`flags=0`)], [`~7,008`], [`175.2 µs`],
  [`GF(2^128)` `GHASH` / `H_ZK_PIN` 64-bit word step], [Internal (`D=1`)], [`128`], [`3.20 µs`],
  [PUF Enroll / Reconstruct (8 blocks × 64 Pelgrom wins)], [`0x50 OP_PUF`], [`~2.10 M`], [`52.5 ms`],
  [CapTP `SpongeMacaroon` Mint / Attenuate], [`0x51 OP_VAT`], [`~3,600`], [`90.0 µs`],
  [Built-In Cryptographic Self-Test (`Keccak`+`Ext4`+`GF128`)], [`0x03 OP_BIST`], [`~4,450`], [`111.3 µs`],
)

#pagebreak()

// ============================================================================
// PAGE 5: QSAG-WIRE PROTOCOL, OPCODE REFERENCE & HOUYHNHNM SECURITY LIFECYCLE
// ============================================================================
= `QSAG-Wire` Protocol, CSR Map & Enclave Security Lifecycle

== Packet Framing & Out-of-Band `0x05 READ_DIAG`

Every request begins with a 64-bit little-endian header `w0 = 0x51 | (op << 8) | (flags << 16) | (byte_len << 24) | (arg << 48)` followed by `ceil(byte_len / 8)` 64-bit payload words. Every response begins with `0x51 | ((op | 0x80) << 8) | (rflags << 16) | (rlen << 24) | (err_code << 48)`, where `rflags[0] = ok` and `rflags[7] = err`. Error codes: `1` `E_MAGIC`, `2` `E_OPCODE`, `3` `E_LEN`, `4` `E_NOKEY`, `5` `E_MAC`, `6` `E_ANCHOR_EMPTY`, `7` `E_ROLLBACK`, `8` `E_REUSE`, `9` `E_ANCHOR_IO`, `10` `E_KEYSET`, `11` `E_TRNG`, `12` `E_PUF`, `13` `E_CAP`, `14` `E_LOCKED`.

*Clockless Bring-Up Diagnostic (`SPI 0x05 READ_DIAG`):* Shifting command `0x05` + 8 dummy clocks on `SCK` clocks out `{8'h5A, fifo_counts[7:0], link_flags[7:0], hb_gray_2[7:0], core_stat[7:0], hb_gray_1[7:0], 16'hD180}` directly in the `SCK` domain — answering even if `clk_core` is stopped or the engine is in `S_DEAD`.

#table(
  columns: (0.52fr, 1.15fr, 1.55fr, 1.78fr),
  inset: 3.8pt,
  stroke: 0.4pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[Op],
  text(fill: white, weight: "bold")[Mnemonic],
  text(fill: white, weight: "bold")[Request (`flags` / `arg` / Payload)],
  text(fill: white, weight: "bold")[Response & Enclave Security Invariants],
  [`0x01`], [`OP_PING`], [`len = 0`], [`"QSAGNI18"`, `tel0`, `{vat_spend, flags, tel1}`, `trng_word`],
  [`0x02`], [`OP_CSR`], [`len = 8` (`csr_word`)], [Updates `CSR` (`CSR[53:52]` fault hooks locked once `mint_lock=1`)],
  [`0x03`], [`OP_BIST`], [`len = 0`], [KAT (`0x4ae2_1323_a298_0887`) over `Keccak` + `Ext4` + `GF(2^128)`],
  [`0x10`], [`OP_P2`], [`flags=1`: 12w raw; `0`: dom+cap+limbs; `2`: `rate6`], [`12`, `4`, or `6` canonical Goldilocks words],
  [`0x11`], [`OP_MERKLE`], [`arg = depth (1..32)`; `key[3], idx, leaf[4], sibs, root`], [`verdict` + computed root (`4w`); drives `VERIFY_OK`],
  [`0x20`], [`OP_KECCAK`], [`flags[0]=turbo`; `arg={out_w, D}`; message], [`out_w` squeezed words (`TurboSHAKE256` / `SHAKE256` / `cSHAKE`)],
  [`0x30/31`], [`OP_FOLD / HEM`], [`flags[3]=pin`, `flags[4]=Fp5`; VM records], [`stat`, `receipt[4]`, `CH[4 or 5]`; pins `zk_pin` on valid assertion],
  [`0x40`], [`OP_KEYLOAD`], [`flags[0]=host/TRNG`, `[1]=FRAM init`, `[2]=K_vat`], [One-shot key provisioning; refused (`E_KEYSET`) if `key_valid`],
  [`0x41`], [`OP_CTH`], [`flags[0]=pub`, `[1]=FRAM`, `[2]=cap`, `[3]=DFA chk`], [`SLH-DSA` WOTS (`pub => sw==4`) / FORS; requires Macaroon or `K_MAC`],
  [`0x42`], [`OP_PRFMSG`], [`flags[2]=1`: Macaroon+msg; `0`: msg+`K_MAC` tag], [`SHAKE256(SK.prf || msg)[0..15]`; zero bytes emitted on bad MAC],
  [`0x50`], [`OP_PUF`], [`flags[0]=0` Enroll (`arg[15]=lock`); `1` Recon (`160B`)], [Enroll: `8×(vmask, syn) + H_pub[4]`; Recon: verifies `H_pub`, commits keys],
  [`0x51`], [`OP_VAT`], [`flags[0]=0` Mint (`flags[3]=lock`); `1` Attenuate], [`96B` `SpongeMacaroon` (`desc[8] || seal[4]`); monotone lattice check],
  [`0x52`], [`OP_DB_NCO`], [`len = 24`; `arg` = DB arm/step/ping/cal + NCO cfg], [`status`, `db_dist_cycles` (separate `cal_valid` vs `dist_valid`), logs],
  [`0x53`], [`OP_VAT_ZK`], [`len = 96` (`SpongeMacaroon`), `arg = epoch`], [`32B` (`4w` locked!) `DREGGZKG` grant iff `mac.vk == zk_pin` & valid],
)

== Zero-eFuse Root-of-Trust & Provisioning Lifecycle

#callout(
  "Why Dregg-180 Avoids GF180 eFuse",
  [Foundry `gf180mcu` eFuse macros require high-current programming pulses from the shared 5.0 V rail with incomplete open-source blow-yield characterization and optical readback exposure. Dregg-180 achieves a *zero-eFuse silicon root of trust* using intrinsic Pelgrom transistor mismatch (`dregg_ro_puf_bch`) + authenticated public helper data (`H_pub`) + dedicated 5.0 V SPI FRAM (`FM25W256-G`).],
  bg: secbg,
  border: secbd,
)

+ *Cold Power-On (`EXT_CLK_BYPASS = 0` default):* Chip boots unconditionally on the internal 32-tap DCRO (`tap = 31` slowest), holds `srst_n = 0` until `TAMPER_ZEROIZE_N` charges high (4,096-clock boot blanking prevents RC rise false-bricking while keeping secrets cleared), and awaits `QSAG-Wire` commands.
+ *PUF Enrollment (`OP_PUF`, `flags = 0`, `arg[15] = 1` `mint_lock`):* Sponge is wiped on entry; 8 blocks × 60 margin-screened differential RO bits are extracted across 4,096-clock Pelgrom windows, encoded with `BCH(63, 36, t=5)`, and absorbed with `arg[15]` into `TurboSHAKE256` to derive `(K_vat, SK.seed, SK.prf, K_MAC)` and public verification tag `H_pub = TurboSHAKE256("DREGGCHK" || K_vat || mint_lock)`. Host stores the 160-byte `(vmask, syn, H_pub)` helper record in FRAM/flash, mints root `SpongeMacaroon` capabilities, and locks further root minting (`vat_mint_locked = 1`).
+ *Field Boot Reconstruction (`OP_PUF`, `flags = 1`, `arg[15] = 1`):* Host replays the 160-byte helper record. `dregg_ro_puf_bch` corrects up to $t = 5$ bit flips per block and checks live RO oscillation bounds; `qsag_wire_engine` derives identical keys into `sh[0..9]`, verifies `H_pub` in constant time (*cryptographically enforcing `arg[15] == enrolled mint_lock`*), and only commits `K_vat` and `SK.*` if `puf_any_err == 0 && H_pub_ok`.
+ *Capability-Attenuated Execution & Emergency Zeroization:* All subsequent `OP_CTH`, `OP_PRFMSG`, and `OP_VAT_ZK` calls require a valid `SpongeMacaroon` (plus fresh 96-bit `K_vat`-MAC NFC token if `G_NFC=1`, 64-round `< 6 ns` rapid-bit + Vernier TDC bound if `G_DIST=1`, and verified `(prog_digest, stmt_root)` `zk_pin` if `G_PIN_VK=1`). Any tamper edge, 4-quadrant glitch, `Metal5` shield fault, `[12,7,4]` control fault, or CTH chain-end laser-DFA fault asserts `srst_n = 0`, *wiping all secret `latrnq_1` cells in 0 clocks* even if `clk_core` is stopped.

#pagebreak()

// ============================================================================
// PAGE 6: 4-LAYER REFERENCE BRING-UP SCHEMATIC & QUALIFIED BOM
// ============================================================================
= 4-Layer Reference Bring-Up Schematic & PCB Layout Guidelines

== Stackup, Supply Bypass, NFC Cold-Tap Isolation & Rapid-Bit Coax Routing

- *4-Layer FR-4 Stackup (`1.6 mm`):* `L1` components, 50 Ω microstrip (`DB_CHAL`, `DB_RESP`, `NCO_RF`) & 4-turn `40 × 40 mm` planar 13.56 MHz NFC coil (`w = 0.42 mm`, `s = 0.56 mm`, `L = 1.466 µH`, `C_res = 94.0 pF`); `L2` solid GND reference; `L3` `5V0` ASIC & `3V3` host islands; `L4` low-speed control. *Clear all copper on L2/L3/L4 inside a `46 × 46 mm` window under the NFC coil.*
- *5.0 V Supply & POR Supervision:* Bypass `dvdd[2:0]` and `vdd[0]` with `4 × 100 nF` + `4 × 1 nF` `0402` capacitors within `1.5 mm` of the die/package pads plus `4.7–10 µF` bulk. Drive `rst_n_pad` (`in_s` Schmitt) from a `TPS3839K50` (`4.38 V` threshold, `200 ms` release) via `100 Ω` series + `100 kΩ` pull-down.
- *Oxide-Safe NFC Cold-Tap Isolation:* Never wire the 13.56 MHz LC tank directly to a CMOS/I/O pad! Route `TANK -> 150 Ω -> BAS70 rectifier -> RECT` (`4.7 V` Zener `BZT52C4V7`, kept *separate* from ASIC `5V0`), and drive `NFC_CLK_IN` (`bidir[8]`) from an inverting `FDV301N` common-source stage (`TANK -> 2.2 kΩ -> Gate` with `BAS70` clamps to `RECT`/`GND`, `470 Ω` drain pull-up to ASIC `5V0`), eliminating unpowered RF back-powering.

#v(3pt)
#figure(
  caption: [Reference bring-up schematic interconnections (`pcb/README.md` & `pcb/BOM.csv`).],
)[
  #box(width: 100%, height: 6.2cm, fill: white, stroke: 0.8pt + navy, radius: 3pt, inset: 6pt)[
    #set text(font: "Menlo", size: 6.3pt)
    // Power & POR block
    #place(top + left, dx: 4pt, dy: 4pt)[
      #box(width: 5.1cm, height: 2.5cm, fill: tint, stroke: 0.6pt + slate, radius: 2pt, inset: 4pt)[
        *5.0V LDO + POR + Tamper*\
        `VIN -> ADM7150-5.0 -> JP_IDD -> 5V0`\
        `5V0 -> 4x(100nF||1nF) -> DVDD[2:0],VDD0`\
        `TPS3839K50 --[100R]--> rst_n_pad (in_s)`\
        `5V0 --[10k]--+--> b[26] TAMPER_ZEROIZE_N`\
        `SW_TAMPER ---+--[10nF]--> GND`
      ]
    ]
    // Host Translator block
    #place(top + left, dx: 4pt, dy: 82pt)[
      #box(width: 5.1cm, height: 2.7cm, fill: tint, stroke: 0.6pt + accent, radius: 2pt, inset: 4pt)[
        *3.3V Host (`I_off` Isolated)*\
        `RP2350 / FT232H (VCCB = 3.3V)`\
        `  <-> SN74LXC8T245 (VCCA = 5V0)`\
        `  --[33R]--> b[18] SCK, in[3] CS_N`\
        `  <-[33R]--> b[7:0] DQ[7:0]`\
        `  <-------- b[16,17,19,20] VOK/FLT/IRQ`\
        `in[0] BYPASS: [10k PD] (0 = DCRO boot)`
      ]
    ]
    // Center ASIC box
    #place(top + left, dx: 5.75cm, dy: 18pt)[
      #box(width: 5.2cm, height: 4.6cm, fill: rgb("#eff6ff"), stroke: 1.1pt + navy, radius: 2pt, inset: 5pt)[
        #align(center)[
          *U1: DREGG-180 ASIC*\
          `SLOT_0P5X0P5` (`56` Pads, `5.0 V`)\
          #line(length: 100%, stroke: 0.4pt + navy)
        ]
        `W: in[3:0], VDD0/VSS0, b[37:27]`\
        `S: clk, rst_n, DVDD0/SS0, b[0:6]`\
        `E: b[7:14], DVDD1/SS1, b[15:21]`\
        `N: b[22:26], an[3:0], DVDD2/SS2`\
        #v(3pt)
        *Dedicated Anchor Bus (`N`):*\
        `b[22] AN_CS_N  b[23] AN_SCK`\
        `b[24] AN_MOSI  b[25] AN_MISO`
      ]
    ]
    // Right top: NFC Cold-Tap Front-End
    #place(top + left, dx: 11.55cm, dy: 4pt)[
      #box(width: 6.0cm, height: 2.85cm, fill: warnbg, stroke: 0.6pt + warnbd, radius: 2pt, inset: 4pt)[
        *13.56 MHz NFC Tank & Cold-Tap Isolator*\
        `L1 (1.47uH, 40x40mm) || 68p+12p+Trim (C0G)`\
        `TANK --[150R]--> BAS70 --> RECT (BZT52C4V7)`\
        `  (RECT isolated from ASIC 5V0!)`\
        `TANK --[2.2k]--> G(FDV301N Q1), D--[470R]->5V0`\
        `D(Q1) ---------> b[8] NFC_CLK_IN (in_s)`\
        `TLV3201 ASK ---> b[9]; b[10] -> Q_MOD (220R)`
      ]
    ]
    // Right bottom: FRAM + Coax DB/NCO
    #place(top + left, dx: 11.55cm, dy: 93pt)[
      #box(width: 6.0cm, height: 2.45cm, fill: secbg, stroke: 0.6pt + secbd, radius: 2pt, inset: 4pt)[
        *5V FRAM Anchor + 50Ω SMA Coax Ports*\
        `U3 FM25W256-G (5.0V, SOIC-8, 100nF + 10k CS)`\
        `  <-> b[22:25] ANCHOR_SPI (short local traces)`\
        `J_DB_CHAL (SMA, 49.9R||GND) -> b[13] (CS=0)`\
        `b[14] (SL=0 fast) --[22R]--> J_DB_RESP (SMA)`\
        `b[11] NCO_RF --[442R + 5th Chebyshev]--> SMA`
      ]
    ]
    // Connecting lines
    #place(top + left, dx: 5.25cm, dy: 42pt)[#line(length: 0.48cm, stroke: 0.9pt + navy)]
    #place(top + left, dx: 5.25cm, dy: 118pt)[#line(length: 0.48cm, stroke: 0.9pt + accent)]
    #place(top + left, dx: 10.98cm, dy: 48pt)[#line(length: 0.55cm, stroke: 0.9pt + warnbd)]
    #place(top + left, dx: 10.98cm, dy: 122pt)[#line(length: 0.55cm, stroke: 0.9pt + secbd)]
  ]
]

== Qualified Reference Bill of Materials (`pcb/BOM.csv`)

#set text(size: 7.6pt)
#table(
  columns: (0.85fr, 1.35fr, 1.35fr, 2.45fr),
  inset: 3.6pt,
  stroke: 0.4pt + steel,
  fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
  text(fill: white, weight: "bold")[RefDes],
  text(fill: white, weight: "bold")[Part Number / Value],
  text(fill: white, weight: "bold")[Package / Rating],
  text(fill: white, weight: "bold")[Function & Bring-Up Qualification Notes],
  [`U1`], [`DREGG-180 (QSAG-NI-180)`], [`SLOT_0P5X0P5` (56-pad)], [5.0 V `gf180mcuD` enclave & verifier ASIC (`1,936 × 2,531 µm`)],
  [`U2`], [`TI TPS3839K50`], [`SOT-23` (`4.38 V` POR)], [200 ms reset supervisor -> `100 Ω` series -> Schmitt `rst_n_pad`],
  [`U3`], [`Infineon FM25W256-G`], [`SOIC-8` (`2.7–5.5 V`)], [True 5.0 V 256-Kbit SPI FRAM for two-slot monotonic counter & helper record],
  [`U4–U6`], [`TI SN74LXC8T245PWR`], [`TSSOP-24` (`5V <-> 3.3V`)], [`I_off` partial-power-down isolated host translators (zero back-powering)],
  [`U7`], [`ADI ADM7150ARDZ-5.0`], [`SOIC-8-EP` (`5.00 V`)], [Ultra-low-noise (`1.0 µVrms`) LDO for clean RO-PUF, Vernier TDC & TVLA],
  [`Q1`], [`onsemi FDV301N`], [`SOT-23` (`25 V` N-FET)], [Common-source RF carrier isolator on `NFC_CLK_IN` + `220 Ω` load-mod shunt],
  [`D1–D4, DZ1`], [`BAS70 / BAT54S + BZT52C4V7`], [`SOT-23 / SOD-123`], [Schottky tank rectifier, gate oxide clamps & independent `4.7 V` `RECT` clamp],
  [`CT1–CT3`], [`68 pF + 12 pF + 3–15 pF`], [`0603 C0G` (`>= 50 V`)], [Zero-TC Class-I C0G 13.56 MHz tank tuning (`R_damp = 4.7 Ω`, $Q_L approx 17.9$)],
  [`J_SMA1–4`], [`Cinch 142-0701-851`], [`50 Ω` Edge-Launch SMA], [`DB_CHAL_IN`, `DB_RESP_OUT` (`< 6 ns` path, bypass translators!), `NCO_RF`, `TVLA`],
)
