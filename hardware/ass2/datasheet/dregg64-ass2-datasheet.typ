// Dregg-64 (ASS2) architecture datasheet and programmer's reference.
// Standalone Typst, no packages. Build from the directory that holds `hardware/` and `build/`:
//
//   typst compile --root . --font-path build/fonts --ignore-system-fonts \
//       hardware/ass2/datasheet/dregg64-ass2-datasheet.typ
//
// Fonts: Liberation Sans (build/fonts) for text, DejaVu Sans Mono (embedded in Typst) for code.
// The listing blocks between `@listing` / `@rust` and `@end` are written by
// hardware/ass2/tools/sync_listings.py from build/listings/*.lst; do not edit them by hand.

#let doc_rev  = "Rev. 2.3"
#let doc_date = "2026-11-23"

// ---- theme ---------------------------------------------------------------------------------
#let navy   = rgb("#0f2742")
#let slate  = rgb("#334155")
#let steel  = rgb("#cbd5e1")
#let tint   = rgb("#f8fafc")
#let accent = rgb("#0369a1")
#let warnbg = rgb("#fffbeb")
#let warnbd = rgb("#b45309")
#let secbg  = rgb("#f0fdf4")
#let secbd  = rgb("#15803d")
#let redbd  = rgb("#b91c1c")
#let sans   = "Liberation Sans"
#let mono   = "DejaVu Sans Mono"

#set document(
  title: "Dregg-64 (ASS2) 5.0 V Enclave Crypto-RISC: Architecture Datasheet and Programmer's Reference",
  author: "QSAG Silicon Engineering",
)

#set page(
  paper: "a4",
  margin: (top: 1.9cm, bottom: 1.7cm, left: 1.5cm, right: 1.5cm),
  header: context {
    if counter(page).get().first() > 1 [
      #set text(font: sans, size: 7.5pt, fill: slate)
      #grid(
        columns: (1fr, auto),
        [*DREGG-64 (`ASS2-0P5`)* · 5.0 V enclave crypto-RISC · 56-pad `SLOT_0P5X0P5`],
        [#doc_rev · silicon specification · #doc_date],
      )
      #v(-3pt)
      #line(length: 100%, stroke: 0.5pt + steel)
    ]
  },
  footer: context [
    #line(length: 100%, stroke: 0.5pt + steel)
    #v(-2pt)
    #set text(font: sans, size: 7.5pt, fill: slate)
    #grid(
      columns: (1fr, auto, 1fr),
      [`gf180mcuD` 5LM · 5.0 V · architecture specification],
      align(center)[QSAG Silicon Engineering],
      align(right)[Page #counter(page).display("1 of 1", both: true)],
    )
  ],
)

#set text(font: sans, size: 8.4pt, fill: rgb("#0f172a"), lang: "en")
#set par(justify: true, leading: 0.5em, spacing: 0.75em)
#show raw: set text(font: mono)
#show raw.where(block: false): set text(size: 0.86em / 0.8)
#set heading(numbering: "1.1")
#set list(indent: 2pt, body-indent: 4pt, spacing: 0.5em)
#set enum(indent: 2pt, body-indent: 4pt, spacing: 0.5em)
#set figure(kind: image, gap: 5pt)
#show figure.caption: set text(size: 7.4pt, fill: slate)

#show heading.where(level: 1): it => block(above: 0.2em, below: 0.6em, breakable: false)[
  #set text(size: 11.5pt, weight: "bold", fill: navy)
  #it
  #v(-4pt)
  #line(length: 100%, stroke: 1.1pt + navy)
]
#show heading.where(level: 2): it => block(above: 0.9em, below: 0.45em, breakable: false)[
  #set text(size: 9.3pt, weight: "bold", fill: navy)
  #it
]

#show raw.where(block: true): set text(size: 5.25pt)
#show raw.where(block: true): it => block(
  width: 100%, fill: tint, stroke: 0.4pt + steel, inset: (x: 4pt, y: 3.5pt), radius: 2pt,
)[
  #set par(leading: 0.36em, justify: false)
  #it
]

// ---- helpers -------------------------------------------------------------------------------
#let tag(t, c) = box(
  fill: c.lighten(86%), stroke: 0.4pt + c, radius: 1.5pt,
  inset: (x: 2.2pt, y: 0pt), outset: (y: 1.7pt),
  text(size: 0.76em, weight: "bold", fill: c.darken(15%), t),
)
#let SPEC = tag("SPEC", accent)
#let TGT  = tag("TARGET", warnbd)
#let MEAS = tag("MEASURED", secbd)
#let PDK  = tag("PDK", slate)

#let th(..c) = c.pos().map(x => text(fill: white, weight: "bold", x))
#let dtable(cols, size: 7.3pt, inset: 3.3pt, ..cells) = {
  set text(size: size)
  set par(justify: false, leading: 0.42em)
  table(
    columns: cols, inset: inset, stroke: 0.4pt + steel,
    fill: (x, y) => if y == 0 { navy } else if calc.odd(y) { tint } else { white },
    ..cells,
  )
}
#let fam(n, body) = table.cell(colspan: n, fill: rgb("#dbeafe"), text(weight: "bold", fill: navy, body))

#let callout(title, body, bg: tint, border: accent) = block(
  width: 100%, fill: bg,
  stroke: (left: 2.5pt + border, top: 0.4pt + steel, right: 0.4pt + steel, bottom: 0.4pt + steel),
  inset: (x: 8pt, y: 6pt), radius: 2pt,
)[#text(weight: "bold", fill: navy)[#title.] #body]

// absolute placement inside a diagram box
#let at(x, y, body) = place(top + left, dx: x, dy: y, body)
#let node(x, y, w, h, title, body, fill: white, bd: navy) = at(x, y, box(
  width: w, height: h, fill: fill, stroke: 0.8pt + bd, radius: 2pt, inset: (x: 4pt, y: 3.5pt),
)[#set par(justify: false, leading: 0.4em)
  #text(weight: "bold", fill: navy, title)\ #body])
#let harrow(x, y, len, c: navy, both: false) = {
  at(x, y, line(length: len, stroke: 0.9pt + c))
  at(x + len - 4pt, y - 2.2pt, polygon(fill: c, (0pt, 0pt), (4.4pt, 2.2pt), (0pt, 4.4pt)))
  if both { at(x - 0.4pt, y - 2.2pt, polygon(fill: c, (4.4pt, 0pt), (0pt, 2.2pt), (4.4pt, 4.4pt))) }
}
#let varrow(x, y, len, c: navy, both: false) = {
  at(x, y, line(start: (0pt, 0pt), end: (0pt, len), stroke: 0.9pt + c))
  at(x - 2.2pt, y + len - 4pt, polygon(fill: c, (0pt, 0pt), (4.4pt, 0pt), (2.2pt, 4.4pt)))
  if both { at(x - 2.2pt, y - 0.4pt, polygon(fill: c, (0pt, 4.4pt), (4.4pt, 4.4pt), (2.2pt, 0pt))) }
}

// one row of a 32-bit encoding figure: fields are (width in bits, label, kind)
#let bfcell(f, h: 11.5pt) = {
  let kind = f.at(2, default: "r")
  let (bg, fg) = if kind == "op" { (navy, white) } else if kind == "z" { (rgb("#e5e7eb"), slate) } else if kind == "i" { (rgb("#fef3c7"), black) } else if kind == "s" { (rgb("#dcfce7"), black) } else { (rgb("#e0f2fe"), black) }
  box(width: 100%, height: h, fill: bg, stroke: 0.5pt + navy,
    align(center + horizon, text(font: mono, size: 5.5pt, fill: fg, f.at(1))))
}
#let bfrow(name, fields, note) = (
  align(right + horizon, text(size: 6.6pt, weight: "bold", fill: navy, name)),
  grid(columns: fields.map(f => f.at(0) * 1fr), ..fields.map(f => bfcell(f))),
  align(left + horizon, text(size: 6.3pt, note)),
)

// ============================================================================================

#set heading(numbering: none)
#set text(size: 9.4pt)
#block(width: 100%, fill: navy, inset: 13pt, radius: 3pt)[
  #text(size: 8.5pt, weight: "bold", fill: rgb("#7dd3fc"))[SILICON ARCHITECTURE & PHYSICAL SIGNOFF SPECIFICATION  /  REV. 2.3]
  #v(6pt)
  #text(size: 28pt, weight: "bold", fill: white)[Dregg-64]
  #v(3pt)
  #text(size: 12pt, fill: white)[ASS2-0P5  ·  64-bit Zero-Factory-Trust post-quantum enclave crypto-RISC]
]
#v(5pt)
The `ASS2-0P5` integrates a 64-bit `DIT = 1` crypto-RISC core, an immutable `4,096 B` (`1,024`-word) post-quantum `WOTS+C` resident mask `I-ROM`, a Two-Ring Hardware `W^X` MPU (`applet_exec_q`), `3,008` asynchronous-clear `latrnq_1` secret latches (`2,560` core + `448` Vault), `514` physical ring oscillators (`512` PUF + `2` coprime CoSO TRNG), and a single 5.0 V byte-wide `512 B` foundry SRAM macro (`D-SRAM`) in the 56-pad GF180MCU `SLOT_0P5X0P5` (`1,936 × 2,531 µm`). A host exchanges little-endian `QSAG-Wire` frames over 1, 4 or 8 data lines while a dedicated SPI master manages dual-slot torn-write-safe FRAM records.

== Device at a glance
#dtable((1.1fr, 3fr), size: 8.8pt, inset: 3.4pt,
  table.header(..th([Parameter], [ASS2-0P5 (Rev. 2.3 · Two-Ring Single-SRAM W^X Signoff)])),
  [Architecture ID], [`0x4153_5332_0000_0001`. Sixteen instruction families, 32-bit little-endian encodings, independent 64-bit PC, formally proven (`UNSAT`) `DIT = 1`.],
  [Memory (2-Ring W^X)], [Ring 0: 4 KiB `I-ROM` (`1,020 / 1,024` words) `R+X,!W` + 512 B `D-SRAM` `R+W,!X` + `SYS_MMIO`. Ring 3 (`applet_exec_q=1`): `0x10000..0x100FF` `R+X,!W` (`<= 64` insns), `0x10100..0x101FF` `R+W,!X`, `I-ROM` & `SYS_MMIO` fenced (`MemFault`).],
  [Clock and supply], [20 MHz (`50.0 ns`) 9-corner SPEF signoff over 4.5–5.5 V (`−40..+125 °C`). Zero-waiver STA (`set_max_time_borrow 0.0`, all 45 clocks constrained, `ERROR_ON_* = true`).],
  [Die and core], [`1,936 × 2,531 µm` (`4.900 mm²`) `SLOT_0P5X0P5` die, 56 pads (`48` signal/analog + `8` supply). Core `(442, 442)..(1,494, 2,089) µm` (`1,732,644 µm²`).],
  [Secret storage & PUF], [`2,560`-bit core + `448`-bit Vault `latrnq_1` latches (`0`-clock stopped-`CLK` wipe) + `512` 5-stage PUF ROs (`252` pairs, `4 × BCH(63,36,5)` = `144`b entropy) + `33/35`-stage CoSO TRNG.],
  [Arithmetic & POST], [Full cold-boot FIPS 140-3 §10.3.A KAT over ALU, Shifter, `GL.MAC`, 128-step $"GF"(2^128)$, $FF_(p^5)$, 30r `Poseidon2-GL12`, and 24r/12r `Keccak-f[1600]` (`0` fast-bypass wires).],
  [Owner authority & I/O], [Zero-Factory-Trust 16-chain base-256 `WOTS+C` (`TurboSHAKE256`) owner bootstrap, signed Ring-3 applets (`cSHAKE256` key in `R1..R2`), & dual-slot FRAM journal. SPI/QSPI/OSPI, `UART`, `GPIO[7:0]`, `SafeRecovery` & `TAMPER_ZEROIZE_N`.],
  [Signoff & Verification], [182 `UNSAT` ISA checks, 5/5 `UNSAT` inductive `DIT=1` proofs, `98,824`-step cosim, `46/46` Rust tests, 83-step `0`-DRC/`0`-LVS LibreLane signoff, post-route `chip_top.nl.v` LEC & 4-state specify sim.],
)

== Programming model

Fixed instruction costs make the architectural CYCLES count predictable for a public instruction trace. Fetches and byte-serial SRAM transfers consume additional core clocks. Use the EXEC watchdog to bound elapsed clocks. Use INSTRET and CYCLES to compare firmware paths.

Keccak uses all 25 lanes. Poseidon2 uses the low 24 or 12. The same latches hold five quintic field elements or twelve 128-bit binary polynomials. An instruction that writes a lane changes every overlapping view.

== Lifecycle and tamper

A low TAMPER_ZEROIZE_N immediately clears the 2,560-bit bank, deasserts VERIFY_OK and asserts FAULT, including with CLK_IN stopped. SRAM erasure needs a running clock after release. A local MAC authenticates an external FRAM record. Fresh authority leases bind the next counter interval to the authority ledger, so replaying an earlier valid record cannot restore spent signing capacity under the leased policy.

#figure(caption: [Power-session transitions. See page 5 for the command allowed in each state.])[
  #box(width: 100%, height: 2.75cm, stroke: 0.6pt + steel, radius: 2pt, fill: white, inset: 4pt)[
    #set text(size: 6.3pt)
    #set align(left)
    #let st(x, y, w, t, f) = at(x, y, box(width: w, height: 0.52cm, fill: f, stroke: 0.7pt + navy, radius: 6pt, align(center + horizon, text(font: mono, size: 5.8pt, weight: "bold", t))))
    #st(0.1cm, 1.0cm, 1.35cm, "RESET", white)
    #harrow(1.45cm, 1.26cm, 0.95cm)
    #at(1.5cm, 0.92cm)[`BOOT`]
    #st(2.4cm, 1.0cm, 1.35cm, "BOOT", rgb("#eff6ff"))
    // fan-out
    #at(3.75cm, 1.26cm, line(length: 0.45cm, stroke: 0.9pt + navy))
    #at(4.2cm, 0.3cm, line(start: (0pt, 0pt), end: (0pt, 1.95cm), stroke: 0.9pt + navy))
    #harrow(4.2cm, 0.3cm, 0.6cm)
    #harrow(4.2cm, 0.95cm, 0.6cm)
    #harrow(4.2cm, 1.6cm, 0.6cm)
    #harrow(4.2cm, 2.25cm, 0.6cm)
    #st(4.8cm, 0.04cm, 2.2cm, "LEASE_PENDING", warnbg)
    #st(4.8cm, 0.69cm, 2.2cm, "ORPHAN", warnbg)
    #st(4.8cm, 1.34cm, 2.2cm, "BLANK", warnbg)
    #st(4.8cm, 1.99cm, 2.2cm, "LOCKED_OUT", rgb("#fee2e2"))
    #harrow(7.0cm, 0.3cm, 4.6cm, c: secbd)
    #at(7.25cm, -0.04cm)[`LEASE` (nonce-bound grant)]
    #st(11.6cm, 0.04cm, 1.6cm, "READY", secbg)
    #at(13.3cm, 0.0cm, box(width: 4.2cm)[#set par(justify: false, leading: 0.4em)
      unleased policy: `BOOT` goes straight to `READY`. `GATE`, signing, resident `EXEC`])
    #harrow(7.0cm, 0.95cm, 3.15cm)
    #at(7.25cm, 0.61cm)[`NONCE`, `REINIT` (owner root)]
    #harrow(7.0cm, 1.6cm, 3.15cm)
    #at(7.25cm, 1.26cm)[`ENROL`, `COMMIT` (owner root)]
    #at(10.15cm, 0.95cm, line(start: (0pt, 0pt), end: (0pt, 0.65cm), stroke: 0.9pt + navy))
    #harrow(10.15cm, 1.28cm, 0.5cm)
    #st(10.65cm, 1.02cm, 2.2cm, "PROVISIONED", secbg)
    #at(13.05cm, 1.0cm, box(width: 4.55cm)[#set par(justify: false, leading: 0.4em)
      diagnostics only until the next reset; the next `BOOT` finds an authentic record])
    #at(7.25cm, 2.02cm, box(width: 10.2cm)[#set par(justify: false, leading: 0.4em)
      owner signature, check tag or retired flag fails. Nothing is written or erased: a transient fault cannot brick the part])
  ]
]


#callout("Reading this specification", [Pages 2–5 define the memory, 16-register `SYS_MMIO`, 56-pad `SLOT_0P5X0P5` ring, and Zero-Factory-Trust `WOTS+C` host contracts, together with GF180MCU synthesis and 3-corner OpenSTA timing. Pages 6–10 cover instruction encodings and KAT-verified callable examples. Pages 11–12 give the 9-corner BSIM3v3 electrical envelope and reference carrier.])
#pagebreak()
#set heading(numbering: "1.1")
= Architecture

One fetch-and-decode sequencer drives one shared datapath over one register bank. The six
hardwired engines of the prototype latch enclave and their private state registers are replaced by
instructions that operate in place on `S0..S24`.

#figure(
  caption: [Dregg-64 internal organisation. The dashed line is the asynchronous clear of the secret bank.],
)[
  #box(width: 100%, height: 8.25cm, stroke: 0.8pt + navy, radius: 3pt, fill: tint, inset: 5pt)[
    #set text(size: 6.5pt)
    #set align(left)
    // column titles
    #at(0.1cm, 0pt, text(weight: "bold", fill: slate)[PAD SHELL · 56-pad `SLOT_0P5X0P5`])
    #at(5.0cm, 0pt, text(weight: "bold", fill: slate)[CORE · `DIT = 1`])
    #at(11.25cm, 0pt, text(weight: "bold", fill: slate)[SHARED CONSTANT-TIME DATAPATH])

    // left column
    #node(0.1cm, 0.42cm, 4.2cm, 2.25cm, [Host link], [
      SPI ×1, quad ×4 and octal ×8\
      `HOST_CS_N`, `SCK`, `DQ[7:0]`, `RDY`, `IRQ`\
      `QSAG-Wire` frames, 64-bit LE words\
      `0x05 CMD_DIAG_RAW` in the `SCK` domain:\
      answers with the core clock stopped
    ], bd: accent)
    #node(0.1cm, 2.85cm, 4.2cm, 1.15cm, [Private FRAM master], [
      `FRAM_CS_N`, `SCK`, `MOSI`, `MISO`\
      Dual-slot torn-write-safe journal (`FM25W256-G`)
    ], fill: secbg, bd: secbd)
    #node(0.1cm, 4.18cm, 4.2cm, 1.15cm, [Debug & SafeRecovery], [
      UART TX ← `CSR 0x0A`, RX → `CSR 0x0B`\
      `BOOT_MODE[1:0]` (`01` → `E_LOCKED`)
    ], bd: slate)
    #node(0.1cm, 5.51cm, 4.2cm, 2.3cm, [Physical roots (`514` ROs)], [
      `512` 5-stage ROs (`4 × BCH(63,36,5)` = 144b)\
      `33/35`-stage CoSO TRNG + NIST RCT/APT\
      `TAMPER_ZEROIZE_N`: 0-clk `3,008`-latch wipe,\
      `VERIFY_OK = 0`, `FAULT = 1` combinational
    ], fill: warnbg, bd: warnbd)

    // centre column
    #node(5.0cm, 0.42cm, 5.55cm, 1.55cm, [Fetch, decode, sequence], [
      32-bit LE instruction, dedicated `PC`, `PC[1:0] = 0`\
      pipelined `CAP_A..D` decode · CSRs, trap unit\
      `INSTRET`, `CYCLES`, `EVEC`, `EPC`, `ECAUSE`
    ], fill: rgb("#eff6ff"))
    #node(5.0cm, 2.2cm, 5.55cm, 1.2cm, [GPR bank `R0..R15` (5-octet)], [
      `R0 = 0`; `R1..R15` 15 × 64 = 960 bits `latrnq_1`\
      local `buf_4` + `aoi22`/`nand4` octet reduction
    ], fill: secbg, bd: secbd)
    #node(5.0cm, 3.63cm, 5.55cm, 1.7cm, [Sponge and field bank `S0..S24`], [
      25 × 64 = 1,600 bits `latrnq_1`\
      views: Keccak lanes · Poseidon2 limbs ·\
      `E0..E4` (5 lanes each) · `P0..P11` (2 lanes each)
    ], fill: secbg, bd: secbd)
    #node(5.0cm, 5.56cm, 5.55cm, 2.25cm, [Memory (Single-SRAM W^X)], [
      `0x0000_0000` `I-ROM` 4 KiB (`WOTS+C` + POST)\
      `0x0000_1000` *(retired / unmapped `MemFault`)*\
      `0x0001_0000` `D-SRAM` 512 B: scratch, `RX_MBOX`,\
      `TX_MBOX` · zero CSPs · byte-serial zeroizer\
      `0xFFFF_0000` `SYS_MMIO` + `448`b `latrnq_1` Vault
    ])

    // right column
    #node(11.25cm, 0.42cm, 6.3cm, 1.55cm, [Word unit · 1 arch cycle], [
      `LUT4` 16 bitwise functions · Kogge-Stone64 add/sub\
      `CMP` 16 predicates → 0 or 1 · `SEL` 4-operand select\
      log/arith/rot barrel shifter, byte extract, `BSWAP64`
    ])
    #node(11.25cm, 2.2cm, 6.3cm, 1.55cm, [Goldilocks multiplier · 4 arch cyc], [
      64-step iterative shift-add sharing `qsag_ass2_add64`\
      `GL.MAC`, `GL.SBOX7` (12), `FP5.MUL` (104), `MUL64`\
      formally proven `UNSAT` over all $2^192$ inputs
    ])
    #node(11.25cm, 3.98cm, 6.3cm, 1.35cm, [$"GF"(2^128)$ multiplier · 4 arch cyc], [
      $x^128 + x^7 + x^2 + x + 1$, 128-step bit-serial Horner\
      `GF128.MUL`, `GF128.XOR` on `P0..P11`
    ])
    #node(11.25cm, 5.56cm, 6.3cm, 2.25cm, [Round network · in place on the bank], [
      `KECCAK.F1600 12 | 24`: 1-clk barrel Rho rotator\
      `POSEIDON2.GL24`: 52 rounds, 216 arch cycles\
      `POSEIDON2.GL12`: 30 rounds, 120 arch cycles\
      no private copy of the 1,600-bit state
    ])

    // arrows: shell <-> core
    #harrow(4.3cm, 1.2cm, 0.7cm, both: true, c: accent)
    #harrow(4.3cm, 3.42cm, 0.35cm, c: secbd)
    #at(4.65cm, 3.42cm, line(start: (0pt, 0pt), end: (0pt, 3.1cm), stroke: 0.9pt + secbd))
    #harrow(4.65cm, 6.52cm, 0.35cm, both: false, c: secbd)
    #harrow(4.3cm, 4.75cm, 0.2cm, c: slate)
    // tamper wipe (dashed) to both banks
    #at(4.3cm, 7.3cm, line(length: 0.5cm, stroke: (paint: redbd, thickness: 1pt, dash: "dashed")))
    #at(4.8cm, 2.8cm, line(start: (0pt, 0pt), end: (0pt, 4.5cm), stroke: (paint: redbd, thickness: 1pt, dash: "dashed")))
    #harrow(4.8cm, 2.8cm, 0.2cm, c: redbd)
    #harrow(4.8cm, 4.2cm, 0.2cm, c: redbd)
    // core internal
    #varrow(7.77cm, 1.97cm, 0.23cm)
    #varrow(7.77cm, 3.4cm, 0.23cm, both: true)
    #varrow(7.77cm, 5.33cm, 0.23cm, both: true)
    // core <-> datapath
    #harrow(10.55cm, 1.2cm, 0.7cm)
    #harrow(10.55cm, 2.8cm, 0.7cm, both: true, c: secbd)
    #harrow(10.55cm, 4.5cm, 0.7cm, both: true, c: secbd)
    #at(10.9cm, 2.8cm, line(start: (0pt, 0pt), end: (0pt, 3.9cm), stroke: 0.9pt + secbd))
    #harrow(10.9cm, 6.7cm, 0.35cm, c: secbd)
  ]
]

== Memory map (Two-Ring Hardware `W^X`: Ring 0 vs Ring 3)
#dtable((1.45fr, .68fr, .42fr, .42fr, .42fr, 1.85fr), size: 7.7pt, inset: 3.1pt,
  table.header(..th([Inclusive byte addresses], [Region], [R0], [R3], [Size], [Function])),
  [`0x0000_0000..0x0000_0FFF`], [`I-ROM`], [X R], [—], [4 KiB], [1,024 × 32-bit insns (`1,020` used). Ring-0 boot, POST KAT, `WOTS+C` & `CTH_SIGN`.],
  [`0x0000_1000..0x0000_11FF`], [*(retired)*], [—], [—], [—], [Unmapped former `I-SRAM` (`MemFault` in both rings).],
  [`0x0001_0000..0x0001_00FF`], [`APPLET / D`], [R W], [X R], [256 B], [`sram512x8m8wm1` words 0–31: Ring-0 scratch/stack or Ring-3 `<= 64`-insn code (`!W`).],
  [`0x0001_0100..0x0001_017F`], [`RX_MBOX`], [R W], [R W], [128 B], [`D-SRAM` words 32–47. Request bytes / Ring-3 data (`!X`).],
  [`0x0001_0180..0x0001_01FF`], [`TX_MBOX`], [R W], [R W], [128 B], [`D-SRAM` words 48–63. Application response bytes (`!X`).],
  [`0xFFFF_0000..0xFFFF_007F`], [`SYS_MMIO`], [R W], [—], [128 B], [Ring-0 peripherals + `448`b `latrnq_1` Vault (`MemFault` in Ring 3 & POST KAT).],
)

The full `D-SRAM` window spans `0x0001_0000..0x0001_01FF` inside the single 5.0 V `sram512x8m8wm1` macro (`64` little-endian 64-bit words). All CSPs (`root_secret`, per-applet key in `R1..R2`, `cap_commit`, `nonce`, raw PUF words, private `WOTS+C` chain pre-images) reside strictly in `latrnq_1` latches (`3,008` bits) and never touch `D-SRAM`.

== Erasure and Two-Ring `W^X` isolation
Core `ZEROIZE` (`0x00040000`) or a `CSRW` to `0x41` with bit 0 set clears `R1..R15` and `S0..S24` in one architectural cycle, clears the 448-bit Vault & PUF buffers (`vault_clr_q`), scrubs `buf64_q`, and starts the full 512-byte D-SRAM scrub (512 clocks = 25.60 µs at 20 MHz). Reset, tamper release, TRNG health fault and budget expiry also select a full scrub. Ring-0 halt scrubs bytes 0–383; Ring-3 halt wipes `R1..R2` (`applet_key`) before `HOST_RDY` rises and scrubs `RX_MBOX` (`256..383`). `HOST_RDY` stays low throughout cold-boot FIPS 140-3 §10.3.A `POST KAT` (`284` arch cycles against `0x17e8_2cb8_0830_751d`) and every sweep.

Hardware `applet_exec_q` enforces Two-Ring `W^X` in ~18 gates: Ring 0 fetches strictly from `I-ROM` (`D-SRAM` is `!X`); Ring 3 flips `0x10000..0x100FF` to `R+X, !W`, keeps `0x10100..0x101FF` `R+W, !X`, fences `I-ROM` & `SYS_MMIO` (`MemFault` over `MisalignedMem`), and traps `CSRW EVEC/EXC_EN` (`IllegalInsn`).

#pagebreak()
= Peripherals, verification and silicon signoff
Access `SYS_MMIO` at base `0xFFFF_0000` (aligned LE64, `I-ROM` + `!post_running` only). All 16 word offsets are decoded below.
#dtable((.82fr, 1.25fr, .38fr, 3.4fr), size: 7.1pt, inset: 2.5pt,
  table.header(..th([Offset], [Register], [Acc.], [Fields and operation])),
  [`+0x00`], [`FRAM_XFER`], [RW], [Read: `[7:0]` RX byte. Write: `[7:0]` TX byte, `[8]` `FRAM_CS_N`, `[9]` start 1-byte transfer (`FRAM_SCK = CLK_IN / 8`).],
  [`+0x08`], [`FRAM_STATUS / CAP_LO`], [R/W], [Read: `[0]` busy, `[1]` sync `MISO`. Write (64b): enclave-private `cap_commit[63:0]`.],
  [`+0x10`], [`CMD_CTX / PUF_CTRL`], [RW], [Read: `{record.state, 4'd0, flags[1:0], len[9:0], 8'd0, op[7:0]}`. Write: `{bist[3:0], 2'd0, margin[5:0], 4'd0, recon, blk[2:0]}` starts PUF.],
  [`+0x18, +0x78`], [`VAULT_NONCE_LO/HI`], [RW], [Enclave-private 128-bit session `nonce`, cleared asynchronously on `srst_n`.],
  [`+0x20, +0x28`], [`PUF_VMASK`, `PUF_SYN`], [RW], [63-bit valid-pair mask and 27-bit `BCH(63,36,5)` helper syndrome (`dregg_ro_puf_bch`).],
  [`+0x30`], [`PUF_WORD / CAP_HI`], [R/W], [Read: `[35:0]` 36-bit BCH word when `puf_complete && !puf_err`. Write (64b): `cap_commit[127:64]`.],
  [`+0x38`], [`PUF_STAT / RECORD`], [RW], [Read: `{record.gen, 19'd0, corrected[3:0], accepted[5:0], err, done, busy}`. Write (64b): `record_q`.],
  [`+0x40, +0x48`], [`TRNG_DATA / HEALTH`], [R], [`+0x40`: conditioned 64b word. `+0x48`: `{rct_fail, apt_fail, !uart_ovf, ok, valid, cnt[29:0]}`.],
  [`+0x50, +0x58`], [`VAULT_LO / HI`], [RW], [Reads `root_secret` (`VERDICT_CTRL[16]=0`) or `cap_commit` (`=1`); 64b writes update `key_lo/hi`.],
  [`+0x60`], [`VERDICT_CTRL`], [RW], [`[0]` `VERIFY_OK`, `[1]` sticky `FAULT`, `[10:8]` `lc_state`, `[16]` `vault_cap_sel`. Tamper forces `0` / `1`.],
  [`+0x68, +0x70`], [`GPIO_IO`, `UART_DIV`], [RW], [`+0x68`: `{in[7:0], oe[7:0], out[7:0]}` (PD reset). `+0x70`: `[11:0]` clocks/bit (reset `25` = `800 kbaud` @ 20M).],
)

== Debug and physical entropy roots
Only `BOOT_MODE = 10` with `lc_state == BLANK` enables the 8N1 UART (`CSR 0x0A` 2-byte shift+hold non-stalling TX, `CSR 0x0B` RX). Outside `BLANK && 10`, TX idles high and `DBG_IN` reads zero. `dregg_ro_puf_bch` instantiates *512 physical 5-stage `gf180mcu_fd_sc_mcu7t5v0` ring oscillators* (`256` strictly disjoint differential pairs, `252` active across 4 disjoint `BCH(63,36,5)` blocks -> `4 × 36 = 144` bits of independent post-helper min-entropy, `t = 5` error correction per block). `qsag_trng` instantiates *coprime 33-stage and 35-stage physical CoSO ring oscillators* (`16.5`-cycle nominal half-integer beat) with continuous NIST SP 800-90B `RCT`, `APT`, and lock-detector health gates.

== Formal, lockstep, coverage and 4-state gate-level verification
All formal proofs passed `UNSAT`: Z3 182-case ALU proof (`lec_ass2.py`), Z3 5-check relational inductive `DIT = 1` constant-time proof across Ring 0 & Ring 3 (`lec_timing.py`), Yosys SAT `add64`/`u8add64` exactness, and all 6 SBY/Bitwuzla theorems (`gl_helpers`, `gf_step`, `alu_equiv`, `seq_mul_inductive`, `seq_mul_bmc`). Rust `qsag-ass2` passed `46/46` tests; RTL lockstep cosim matched over `1,028` programs (`98,824` steps); merged 5-suite DO-254 production RTL line coverage achieved *`96.45%` (`1,467 / 1,521`)*; pre-route & post-route (`final/nl/chip_top.nl.v`) Yosys formal LEC (`equiv_status -assert`) and 4-state `GF180MCU` specify sim (`iverilog -gspecify -Ttyp`) verified cold-boot FIPS POST KAT, clockless `DIAG`, `IDENT`, resident `EXEC`, and `0.600 ns` clockless tamper wipe of all `3,008` (`2,560` bank + `448` Vault) `.Q` latch nodes.

== GF180MCU synthesis and 9-corner SPEF signoff (`SLOT_0P5X0P5`)
`qsag_ass2_enclave_top` maps to *38,742 cells* (`38,741` stdcells = `831,919.33 µm²` + `1 × sram512x8m8wm1` = `209,400.28 µm²` -> *1,041,319.61 µm²*, `-27.0%` vs 2-SRAM) inside the `SLOT_0P5X0P5` `1,732,644 µm²` core (`[442, 442]..[1494, 2089] µm`).

#dtable((1.45fr, 1.05fr, 1.05fr, .85fr, .8fr, .75fr, .75fr), size: 7.1pt, inset: 2.3pt,
  table.header(..th([Pre-Layout Corner], [Core min. (ns)], [Core Fmax (MHz)], [`HOST_SCK`], [`trng_sclk`], [TNS @ 20M], [Min hold])),
  [TT · 25 °C · 5.00 V], [20.16], [49.60], [64.81 (101.9 reg)], [223.18 MHz], [0.00 ns], [+0.27 ns],
  [FF · −40 °C · 5.50 V], [14.65 (12.74 reg)], [68.27 (78.52 reg)], [87.25 (156.3 reg)], [351.09 MHz], [0.00 ns], [+0.16 ns],
  [SS · 125 °C · 4.50 V], [*37.15*], [*26.92*], [41.73 (56.4 reg)], [122.41 MHz], [*0.00 ns*], [+0.30 ns],
)
*83-Step 9-Corner SPEF Signoff (`SLOT_0P5X0P5`).* Single-SRAM floorplan (`[465, 465]` `FS`), `set_max_time_borrow 0.0` across all 46 clocks, and full `ERROR_ON_* = true` signoff close all 9 SPEF corners at 20 MHz (`Setup WNS = 0.00 ns`, `Setup TNS = 0.00 ns`, `Hold WNS = 0.00 ns`, `Hold TNS = 0.00 ns`, `0` slew/cap/fanout, `0` DRC/Antenna/Density/XOR/PDN/LVS).

== Supply, pad controls and reset
#dtable((1.0fr, 1.1fr, 2.7fr), size: 7.6pt, inset: 2.6pt,
  table.header(..th([Interface], [Operating value], [Board connection])),
  [Chip supplies], [4.5–5.5 V, nominal 5 V], [Feed three `DVDD/DVSS` pairs and one `VDD/VSS` pair (`8` supply pads, `60 mA` DC rating per pad).],
  [Host DQ0–7], [8 mA, fast slew], [Fit a 33 Ω series resistor per line (`pads 5–12`). Switch direction during the 8-clock dummy turnaround.],
  [Clock and reset], [5 V Schmitt inputs], [`RST_N` low disables bidirectional output drivers. Drive `CLK_IN` (`pad 1`) externally on the reference carrier.],
  [Operating temp.], [−40 to +125 °C silicon], [`TPS3839K50` and `FM25W256-G` limit the populated reference carrier to −40 to +85 °C.],
)
#text(size: 7.4pt)[Pad cell controls follow the #link("https://gf180mcu-pdk.readthedocs.io/en/latest/IPs/IO/gf180mcu_fd_io/digital.html")[GF180MCU digital I/O table]. Reset enters `LC_RESET` (`0`) and scrubs all 512 `D-SRAM` bytes. Hardware `SafeRecovery` (`BOOT_MODE = 01`) rejects `0x20`, `0x30` and applet `0x31` with `E_LOCKED = 14`. JTAG test (`11`) holds `srst_n = 0` (`2,560`-bit secret bank wiped) and locks out `JTAG_TDO` outside `RESET`/`BLANK`.]
#pagebreak()
#set text(size: 8.4pt)
= Pad ring and signal description

The ring is the 56-pad ring of `librelane/slot_0p5x0p5.yaml`: 11 pads south, 17 east,
11 north, 17 west; 48 signal pads and 8 supply pads at fixed positions. Every signal has one
pad and one function. Indices run west to east on the south and north sides and south to
north on the east and west sides.

#let padcol(g) = (
  host: rgb("#dbeafe"), dbg: rgb("#fef9c3"), fram: rgb("#dcfce7"), sec: rgb("#fee2e2"),
  gpio: rgb("#ede9fe"), pres: rgb("#ffedd5"), test: rgb("#e5e7eb"), pwr: rgb("#334155"),
  nc: white, clk: rgb("#cffafe"),
).at(g)
#let south = (("clk", "CLK_IN", "clk"), ("rst_n", "RST_N", "clk"), ("dvss0", "DVSS", "pwr"), ("dvdd0", "DVDD", "pwr"),
  ("b[0]", "HOST_DQ0", "host"), ("b[1]", "HOST_DQ1", "host"), ("b[2]", "HOST_DQ2", "host"), ("b[3]", "HOST_DQ3", "host"),
  ("b[4]", "HOST_DQ4", "host"), ("b[5]", "HOST_DQ5", "host"), ("b[6]", "HOST_DQ6", "host"))
#let north = (("an[3]", "n/c", "nc"), ("an[2]", "n/c", "nc"), ("dvss2", "DVSS", "pwr"), ("dvdd2", "DVDD", "pwr"),
  ("an[1]", "n/c", "nc"), ("an[0]", "n/c", "nc"), ("b[26]", "TAMPER_ZEROIZE_N", "sec"), ("b[25]", "FRAM_MISO", "fram"),
  ("b[24]", "FRAM_MOSI", "fram"), ("b[23]", "FRAM_SCK", "fram"), ("b[22]", "FRAM_CS_N", "fram"))
// east and west, top to bottom
#let east = (("b[21]", "CLK_MON", "dbg"), ("b[20]", "HOST_IRQ", "host"), ("b[19]", "HOST_RDY", "host"), ("b[18]", "HOST_SCK", "host"),
  ("b[17]", "FAULT", "sec"), ("b[16]", "VERIFY_OK", "sec"), ("b[15]", "GPIO7", "gpio"), ("dvdd1", "DVDD", "pwr"), ("dvss1", "DVSS", "pwr"),
  ("b[14]", "GPIO6", "gpio"), ("b[13]", "GPIO5", "gpio"), ("b[12]", "GPIO4", "gpio"), ("b[11]", "GPIO3", "gpio"),
  ("b[10]", "GPIO2", "gpio"), ("b[9]", "GPIO1", "gpio"), ("b[8]", "GPIO0", "gpio"), ("b[7]", "HOST_DQ7", "host"))
#let west = (("in[0]", "CLK_EXT_EN", "clk"), ("in[1]", "BOOT_MODE0", "dbg"), ("vdd0", "VDD", "pwr"), ("vss0", "VSS", "pwr"),
  ("in[2]", "BOOT_MODE1", "dbg"), ("in[3]", "HOST_CS_N", "host"), ("b[27]", "DBG_UART_RX", "dbg"), ("b[28]", "DBG_UART_TX", "dbg"),
  ("b[29]", "DB_RESP_OUT", "pres"), ("b[30]", "DB_CHAL_IN", "pres"), ("b[31]", "NFC_LOAD_MOD", "pres"), ("b[32]", "NFC_ASK_IN", "pres"),
  ("b[33]", "NFC_CLK_IN", "pres"), ("b[34]", "JTAG_TDO", "test"), ("b[35]", "JTAG_TDI", "test"), ("b[36]", "JTAG_TMS", "test"),
  ("b[37]", "JTAG_TCK", "test"))

#figure(
  caption: [Top view, die 1,936 × 2,531 µm, origin at the south-west corner. Side indices follow the slot YAML order. Numbers 1–56 identify die pads.],
)[
  #box(width: 100%, height: 9.15cm, fill: white, stroke: 0.7pt + steel, radius: 3pt, inset: 4pt)[
    #set text(font: mono, size: 5.3pt)
    #set align(left)
    #let dx0 = 6.3cm
    #let dy0 = 2.66cm
    #let dw = 4.3cm
    #let dh = 4.55cm
    // die
    #at(dx0, dy0, box(width: dw, height: dh, fill: rgb("#f1f5f9"), stroke: 1.2pt + navy, radius: 1.5pt)[
      #place(center + horizon)[
        #align(center)[
          #text(font: sans, size: 10pt, weight: "bold", fill: navy)[DREGG-64]\
          #text(font: sans, size: 7pt, fill: slate)[`ASS2-0P5` · `SLOT_0P5X0P5`]\
          #text(font: sans, size: 6.4pt, fill: slate)[core `[442,442]..[1494,2089]`]\
          #v(2pt)
          #text(font: sans, size: 6.4pt, fill: slate)[top view · north up]
        ]
      ]
      #place(bottom + left, dx: 3pt, dy: -3pt)[#text(size: 5.4pt, fill: warnbd, weight: "bold")[● (0,0)]]
    ])
    // north and south pads, labels rotated
    #let px = (dw - 0.5cm) / 11
    #for (i, p) in north.enumerate() {
      let x = dx0 + 0.25cm + i * px
      at(x + 0.03cm, dy0 + 0.04cm, box(width: px - 0.06cm, height: 0.24cm, fill: padcol(p.at(2)), stroke: 0.45pt + navy))
      at(x + px / 2 - 2.6pt, dy0 - 0.08cm, place(bottom + left, rotate(-90deg, reflow: true, text(fill: if p.at(2) == "pwr" { slate } else { black })[#p.at(0) #text(weight: "bold", p.at(1))])))
    }
    #for (i, p) in south.enumerate() {
      let x = dx0 + 0.25cm + i * px
      at(x + 0.03cm, dy0 + dh - 0.28cm, box(width: px - 0.06cm, height: 0.24cm, fill: padcol(p.at(2)), stroke: 0.45pt + navy))
      at(x + px / 2 - 2.6pt, dy0 + dh + 0.08cm, rotate(90deg, reflow: true, text(fill: if p.at(2) == "pwr" { slate } else { black })[#p.at(0) #text(weight: "bold", p.at(1))]))
    }
    // east and west pads
    #let py = (dh - 0.5cm) / 17
    #for (i, p) in west.enumerate() {
      let y = dy0 + 0.25cm + i * py
      at(dx0 + 0.04cm, y + 0.025cm, box(width: 0.24cm, height: py - 0.05cm, fill: padcol(p.at(2)), stroke: 0.45pt + navy))
      at(dx0 - 3.08cm, y + 0.035cm, box(width: 3.0cm, height: py - 0.07cm, align(right + horizon)[#text(weight: "bold", p.at(1)) #p.at(0)]))
    }
    #for (i, p) in east.enumerate() {
      let y = dy0 + 0.25cm + i * py
      at(dx0 + dw - 0.28cm, y + 0.025cm, box(width: 0.24cm, height: py - 0.05cm, fill: padcol(p.at(2)), stroke: 0.45pt + navy))
      at(dx0 + dw + 0.08cm, y + 0.035cm, box(width: 3.0cm, height: py - 0.07cm, align(left + horizon)[#p.at(0) #text(weight: "bold", p.at(1))]))
    }
    // legend, left
    #at(0.1cm, 0.1cm, box(width: 2.95cm)[
      #set text(font: sans, size: 6.5pt)
      #set par(justify: false, leading: 0.45em)
      #text(weight: "bold", fill: navy)[Pad groups]\
      #for (g, t) in (("host", "Host SPI ×1 / ×4 / ×8 (12)"), ("fram", "Private FRAM master (4)"), ("sec", "Tamper and verdict (3)"), ("dbg", "UART, boot, monitor (5)"), ("gpio", "GPIO[7:0] (8)"), ("pres", "Presence front end (5)"), ("test", "JTAG, test mode only (4)"), ("clk", "Clock and reset (3)"), ("pwr", "Supply (8)"), ("nc", "Analog, not connected (4)")) [
        #box(width: 7pt, height: 5.5pt, fill: padcol(g), stroke: 0.4pt + navy, baseline: 0.5pt) #t\
      ]
    ])
    // notes, right
    #at(14.0cm, 0.1cm, box(width: 3.55cm)[
      #set text(font: sans, size: 6.5pt)
      #set par(justify: false, leading: 0.45em)
      #text(weight: "bold", fill: navy)[`BOOT_MODE[1:0]`]\
      `00` mission\
      `01` safe recovery (`E_LOCKED`)\
      `10` blank bring-up, UART live\
      `11` JTAG test, secret bank held 0\
      Hold stable during use.
    ])
    #at(14.0cm, 7.35cm, box(width: 3.55cm)[
      #set text(font: sans, size: 6.5pt)
      #set par(justify: false, leading: 0.45em)
      #text(weight: "bold", fill: navy)[Supply]\
      `DVDD = VDD`, `DVSS = VSS` inside the pad library: one 5.0 V rail, four pad pairs.
    ])
  ]
]

#v(-2pt)
#dtable(
  (0.42fr, 0.5fr, 0.62fr, 0.72fr, 1.05fr, 0.34fr, 3.1fr),
  size: 6.8pt, inset: 2.5pt,
  table.header(..th([Pad no.], [Side · index], [Slot pad], [Cell · pull], [Signal], [Dir], [Function])),
  [1], [S 0], [`clk`], [`in_s`], [`CLK_IN`], [I], [External core clock input],
  [2], [S 1], [`rst_n`], [`in_s` · PD], [`RST_N`], [I], [Active-low Schmitt reset. Every bidirectional pad is high-impedance while it is low],
  [3, 4], [S 2, 3], [`dvss[0]`, `dvdd[0]`], [supply], [`DVSS`, `DVDD`], [—], [5.0 V pair 0],
  [5–11], [S 4..10], [`bidir[0..6]`], [`bi_t` 8 mA], [`HOST_DQ[0..6]`], [I/O], [Host data. ×1: `DQ0` in, `DQ1` out. ×4: `DQ[3:0]`. ×8: all eight. 33 Ω series resistor on the board],
  [12], [E 0], [`bidir[7]`], [`bi_t` 8 mA], [`HOST_DQ7`], [I/O], [Host data bit 7 (×8 only). 33 Ω series resistor on the board],
  [13–19], [E 1..7], [`bidir[8..14]`], [`bi_t` · PD], [`GPIO[0..6]`], [I/O], [General-purpose pins under `GPIO_IO`; inputs with pull-down after reset],
  [20, 21], [E 8, 9], [`dvss[1]`, `dvdd[1]`], [supply], [`DVSS`, `DVDD`], [—], [5.0 V pair 1],
  [22], [E 10], [`bidir[15]`], [`bi_t` · PD], [`GPIO7`], [I/O], [As `GPIO[0..6]`],
  [23], [E 11], [`bidir[16]`], [`bi_t`], [`VERIFY_OK`], [O], [`VERDICT_CTRL[0]`. Forced 0 by tamper, combinationally],
  [24], [E 12], [`bidir[17]`], [`bi_t`], [`FAULT`], [O], [`VERDICT_CTRL[1]`, sticky. Forced 1 by tamper, combinationally],
  [25], [E 13], [`bidir[18]`], [`bi_t` Schmitt], [`HOST_SCK`], [I], [Host serial clock, SPI mode 0],
  [26], [E 14], [`bidir[19]`], [`bi_t`], [`HOST_RDY`], [O], [High when a request frame can be accepted],
  [27], [E 15], [`bidir[20]`], [`bi_t`], [`HOST_IRQ`], [O], [High while a response frame is waiting],
  [28], [E 16], [`bidir[21]`], [`bi_t`], [`CLK_MON`], [O], [Core clock divided by 16],
  [29, 30, 33, 34], [N 0, 1, 4, 5], [`analog[3..0]`], [`asig_5p0`], [not connected], [—], [Leave open],
  [31, 32], [N 2, 3], [`dvss[2]`, `dvdd[2]`], [supply], [`DVSS`, `DVDD`], [—], [5.0 V pair 2],
  [35], [N 6], [`bidir[26]`], [`bi_t` Schmitt · PU], [`TAMPER_ZEROIZE_N`], [I], [Low clears `R1..R15` and `S0..S24` in `0.600 ns` with no clock and forces `VERIFY_OK = 0`, `FAULT = 1`],
  [36–39], [N 7..10], [`bidir[25..22]`], [`bi_t`], [`FRAM_MISO`, `FRAM_MOSI`, `FRAM_SCK`, `FRAM_CS_N`], [I, O, O, O], [Private SPI master to `FM25W256-G` (`CLK_IN / 8`). `MISO` PD; `CS_N` released high in reset],
  [40–43], [W 0..3], [`bidir[37..34]`], [`bi_t` · PD], [`JTAG_TCK`, `TMS`, `TDI`, `TDO`], [I, I, I, O], [Test signals; `TDO` output enabled only in `BOOT_MODE=11 && (RESET || BLANK) && !tampered`],
  [44–46], [W 4..6], [`bidir[33..31]`], [`bi_t`], [`NFC_CLK_IN`, `NFC_ASK_IN`, `NFC_LOAD_MOD`], [I, I, O], [13.56 MHz presence front end, through the carrier detector on page 11],
  [47, 48], [W 7, 8], [`bidir[30]`, `[29]`], [`bi_t`], [`DB_CHAL_IN`, `DB_RESP_OUT`], [I, O], [Rapid-bit distance bounding: challenge in, response out],
  [49, 50], [W 9, 10], [`bidir[28]`, `[27]`], [`bi_t`], [`DBG_UART_TX`, `DBG_UART_RX`], [O, I], [Debug UART, 8N1. `TX` idles high and is muted outside blank bring-up],
  [51], [W 11], [`inputs[3]`], [`in_c` · PU], [`HOST_CS_N`], [I], [Host chip select, active low. One low period is one link transaction],
  [52, 55], [W 12, 15], [`inputs[2]`, `[1]`], [`in_c` · PD], [`BOOT_MODE[1:0]`], [I], [`00` mission · `01` safe recovery (`E_LOCKED`) · `10` blank bring-up · `11` JTAG test],
  [53, 54], [W 13, 14], [`vss[0]`, `vdd[0]`], [supply], [`VSS`, `VDD`], [—], [Core pair, same rail],
  [56], [W 16], [`inputs[0]`], [`in_c` · PD], [`CLK_EXT_EN`], [I], [External clock select strap. Supply CLK_IN on the reference board],
)
#v(1pt)

The eight HOST_DQ pads use `gf180mcu_fd_io__bi_t` at 8 mA (`PDRV=2'b01`, `SL=0`, fast slew for 20 MHz 50 pF `max_ss` margin). Fit 33 Ω in series on each DQ trace. See page 11 for south-bank bounce notes.
#pagebreak()
= Host interface and `QSAG-Wire` protocol

== Synchronous serial link

The host is the SPI controller, mode 0: data are sampled on the rising edge of `HOST_SCK` and
change on the falling edge, most significant bit of each byte first. `HOST_CS_N` low frames
one transaction. Its first byte, the prefix, is always sent one bit wide on `DQ0` and selects
the direction and the width of everything that follows.

#grid(
  columns: (1.05fr, 0.95fr),
  gutter: 10pt,
  [
    #figure(caption: [One write and one read transaction on the 1-bit link. Words are 64-bit little-endian.])[
      #box(width: 100%, height: 2.65cm, stroke: 0.6pt + steel, radius: 2pt, fill: white, inset: 4pt)[
        #set text(font: mono, size: 5.6pt)
        #set align(left)
        #let cell(x, y, w, t, f) = at(x, y, box(width: w, height: 0.42cm, fill: f, stroke: 0.5pt + navy, align(center + horizon, t)))
        #at(0cm, 0.02cm)[write CS]
        #at(8.65cm, 0.02cm, line(start: (0pt, 0.18cm), end: (0.2cm, 0pt), stroke: 0.8pt + navy))
        #at(1.55cm, 0.2cm, line(length: 7.1cm, stroke: 0.8pt + navy))
        #at(1.3cm, 0.02cm, line(start: (0pt, 0pt), end: (0.25cm, 0.18cm), stroke: 0.8pt + navy))
        #at(0cm, 0.52cm)[`DQ0` in]
        #cell(1.55cm, 0.42cm, 0.95cm, [`0x00`], rgb("#e0f2fe"))
        #cell(2.5cm, 0.42cm, 2.5cm, [`w0` header, 8 bytes], rgb("#fef3c7"))
        #cell(5.0cm, 0.42cm, 3.85cm, [payload, ⌈len / 8⌉ words], rgb("#dcfce7"))
        #at(0cm, 1.02cm)[read CS]
        #at(1.3cm, 1.02cm, line(start: (0pt, 0pt), end: (0.25cm, 0.18cm), stroke: 0.8pt + navy))
        #at(1.55cm, 1.2cm, line(length: 7.1cm, stroke: 0.8pt + navy))
        #at(8.65cm, 1.02cm, line(start: (0pt, 0.18cm), end: (0.2cm, 0pt), stroke: 0.8pt + navy))
        #at(0cm, 1.62cm)[`DQ0` in]
        #cell(1.55cm, 1.52cm, 0.95cm, [`0x02`], rgb("#e0f2fe"))
        #cell(2.5cm, 1.52cm, 1.1cm, [8 dummy], rgb("#e5e7eb"))
        #at(0cm, 2.08cm)[`DQ1` out]
        #cell(3.6cm, 1.98cm, 2.2cm, [`w0'` header], rgb("#fef3c7"))
        #cell(5.8cm, 1.98cm, 3.05cm, [payload words], rgb("#dcfce7"))
      ]
    ]
  ],
  [
    #dtable(
      (0.62fr, 1.9fr),
      table.header(..th([Prefix], [Transaction])),
      [`0x00`], [Write, ×1: `DQ0`, 8 clocks per byte],
      [`0x02`], [Read, ×1: 8 dummy clocks, then `DQ1`],
      [`0x40`], [Write, ×4: `DQ[3:0]`, 2 clocks per byte, high nibble first],
      [`0x42`], [Read, ×4: 8 dummy clocks, then `DQ[3:0]`],
      [`0x80`], [Write, ×8: `DQ[7:0]`, 1 clock per byte],
      [`0x82`], [Read, ×8: 8 dummy clocks, then `DQ[7:0]`],
      [`0x05`], [`CMD_DIAG_RAW`: 8 dummy clocks, then 64 bits on `DQ1`, bit 63 first, clocked by `HOST_SCK` alone],
    )
    #v(1pt)
    #set par(justify: false)
    #text(size: 7.3pt)[`HOST_RDY` high: a request frame can be written. `HOST_IRQ` high: a
    response frame is waiting; read its header and padded body under one chip select. The host
    releases `DQ` during the dummy clocks; the chip drives from the falling edge of the eighth.
    End the transaction by releasing chip select.]
  ],
)

== Frames

Requests and responses are sequences of 64-bit little-endian words. The first word is the header;
`⌈byte_len / 8⌉` payload words follow. In a response the opcode has bit 7 set, `rflags[0]` is `ok`
and `rflags[7]` is `err`.

#let wf(fields) = grid(columns: fields.map(f => f.at(0) * 1fr), ..fields.map(f => bfcell(f, h: 12.5pt)))
#grid(
  columns: (1.5cm, 1fr),
  row-gutter: 2.5pt, column-gutter: 5pt,
  [], grid(columns: (16fr, 24fr, 8fr, 8fr, 8fr), ..("63 … 48", "47 … 24", "23 … 16", "15 … 8", "7 … 0").map(t => align(center, text(font: mono, size: 5.2pt, fill: slate, t)))),
  align(right + horizon, text(size: 6.6pt, weight: "bold", fill: navy)[request `w0`]),
  wf(((16, "arg", "i"), (24, "byte_len", "i"), (8, "flags", "s"), (8, "op", "r"), (8, "0x51", "op"))),
  align(right + horizon, text(size: 6.6pt, weight: "bold", fill: navy)[response `w0'`]),
  wf(((16, "err_code", "i"), (24, "rlen", "i"), (8, "rflags", "s"), (8, "op | 0x80", "r"), (8, "0x51", "op"))),
  align(right + horizon, text(size: 6.6pt, weight: "bold", fill: navy)[`DIAG_RAW`]),
  wf(((8, "0x5A", "op"), (8, "link_stat", "s"), (16, "pc[15:0]", "i"), (8, "lc_state", "r"), (8, "ecause", "r"), (16, "0xA552", "op"))),
)
#v(-1pt)
#text(size: 7.7pt)[Bits 63–56 = 0x5A, 55–48 = link_stat, 47–32 = `PC[15:0]`, 31–24 = lc_state, 23–16 = `ECAUSE[7:0]`, 15–0 = 0xA552. From bit 7 to bit 0, link_stat carries FAULT, VERIFY_OK, tampered, running, scrub active, IRQ, RDY and halted. Lifecycle codes are 0 RESET, 1 BLANK, 2 PROVISIONED, 3 LEASE_PENDING, 4 ORPHAN, 5 READY and 6 LOCKED_OUT.]
== Host command set (`1,020 / 1,024`-word Zero-Factory-Trust `WOTS+C` resident `I-ROM`)
#dtable((.62fr, 1.18fr, .98fr, 2.75fr), size: 6.8pt, inset: 2.9pt,
  table.header(..th([Opcode], [Command], [State], [Operation])),
  [`0x01`], [`CMD_IDENT`], [Any], [Hardware fast-path: four LE64 words (`ASS2D180`, `ARCH_ID`, `{lc_state, trng_ok, trng_valid, cnt}`, `CYCLES`).],
  [`0x10`], [`CMD_BOOT`], [`RESET`], [Inspects dual 64B FRAM slots (`0x0000`/`0x0040`), recovers torn writes by highest MAC-valid `gen`, reconstructs 144b PUF `root_secret` into `VAULT` (`S0..S3` staging only), emits `(nonce, record, enclave_id)` and enters `BLANK` or `LEASE_PENDING`.],
  [`0x11`], [`CMD_ENROL`], [`BLANK`], [Binds Owner's 32B post-quantum `WOTS+C` root `pk_0`, enrolls 4 `BCH(63,36,5)` PUF blocks, seals `(helpers, pk_0)` to FRAM (`0x0100`), and returns `(16B nonce || 32B public enclave_id)` — zero factory secret export.],
  [`0x12`], [`CMD_COMMIT`], [`BLANK`], [Verifies 320B Owner `WOTS+C` frame (`24B` header + `296B` 16-chain base-256 `sum=2040` `TurboSHAKE256` proof), persists `gen=1` journal record with `next_wots_root`, and enters `PROVISIONED`.],
  [`0x15 / 0x16`], [`CMD_LEASE / GATE`], [`LEASE_PENDING` / `READY`], [Verifies 320B Owner `WOTS+C` proof bound to `(enclave_id, nonce, record)`, caches `cap_commit` in `VAULT_CAP`, rolls `(gen+1, state, next_wots_root)` into the alternate FRAM slot, and enters/updates `READY`.],
  [`0x20`], [`CMD_CTH_SIGN`], [`READY`], [Verifies 16B `cap_token` (`120B` payload), runs constant-time `GF(2^128)` `cth_dualmac`, derives base-4 `Poseidon2-GL-w12` Jive chains strictly in `S0..S24` (zero CSP SRAM spill), and rolls `gen+1`.],
  [`0x30`], [`CMD_LOAD_CODE`], [`BLANK / PROV / READY`], [Two-Ring `W^X` `<= 64`-word Ring-3 loader: `flags=0` (`4+4n` B) open in `BLANK`; `flags=2` (`300+4n` B) Owner `WOTS+C` signed over `cSHAKE256("ASS2.CODE", words)` when `!rom_lock`, rolling `gen+1`, injecting `cSHAKE256("ASS2.APPLET", K_root || "ASS2.APPLET" || code_hash)` into `R1..R2` and scrubbing `R3..R15`/`S0..S24`; `E_LOCKED = 14` if `rom_lock`.],
  [`0x31`], [`CMD_EXEC`], [`READY` / Any (`f[0]=1`)], [Executes installed Ring-3 applet (`f[0]=0`) or resident Ring-0 `I-ROM` service (`f[0]=1`: `IDENT`, `BIST` in `BLANK`, `LIFECYCLE`, `CTH_SIGN`) under exact-edge clock watchdog `arg` (`0` = `65,535`).],
)

#text(size: 7.3pt)[*Execute and Two-Ring W^X.* `CMD_LOAD_CODE` (`0x30`) enforces three hardware-backed lifecycle policies (`BLANK` open devkit, `PROVISIONED/READY` `!rom_lock` `WOTS+C` signed code with domain-separated `applet_key` in `R1..R2`, and `rom_lock` / `SafeRecovery` `E_LOCKED = 14`). `CMD_EXEC` (`0x31`) accepts up to 128 bytes in `RX_MBOX`; registered 1-bit lookahead `budget_last_q` halts execution on the *exact* requested physical core-clock edge (`arg`, `0` = `65,535`). A successful response is 160 bytes: `128B TX_MBOX` + four LE64 words (`A0`, `ECAUSE`, `INSTRET`, `CYCLES`).]

#text(size: 7.2pt)[*Wire errors.* 1 `E_MAGIC` · 2 `E_OPCODE` · 3 `E_LEN` · 4 `E_NOKEY` · 5 `E_MAC` · 6 `E_ANCHOR_EMPTY` · 7 `E_ROLLBACK` · 8 `E_REUSE` · 9 `E_ANCHOR_IO` · 10 `E_KEYSET` · 11 `E_TRNG` · 12 `E_PUF` · 13 `E_CAP` · 14 `E_LOCKED` · 15 `E_BUDGET` · 16 `E_TRAP`]

#callout("Zero-Factory-Trust security & dual-slot power-loss resilience", [`root_secret` is reconstructed strictly inside `SYS_MMIO` `VAULT_LO/HI` from 4 disjoint `BCH(63,36,5)` RO-PUF blocks and never touches `TX_MBOX` or `D-SRAM`. `CMD_ENROL` exports only the public `enclave_id` and binds the Owner's post-quantum `WOTS+C` public root `pk_0`. Every FRAM mutation writes the inactive slot `(gen + 1) & 1` so power loss mid-write leaves the previous generation intact.])
#pagebreak()
= Instruction set: programmer's model and encodings

The ISA tables follow sections 1 and 2 of the canonical specification. Architectural cycles depend only on instruction encoding, including the round count in `KECCAK.F1600`.

== Encoding formats

Every instruction is one 32-bit little-endian word at a `PC` that is a multiple of 4. The major
opcode is bits 31..28. Grey fields and unused operands must be zero. Reserved functions and nonzero reserved bits trap with `IllegalInsn`.

#let R = "r"
#let fmt = (
  ("0x0  SYS", ((4, "0000", "op"), (8, "csr8 / 0", "i"), (4, "sub", "s"), (4, "0", "z"), (4, "0", "z"), (4, "ra", R), (4, "rd", R)), [`EXC` `ERET` `CSRR` `CSRW` `ZEROIZE` `HALT` `NOP`]),
  ("0x1  LUT4", ((4, "0001", "op"), (8, "0", "z"), (4, "M", "s"), (4, "0", "z"), (4, "rb", R), (4, "ra", R), (4, "rd", R)), [truth table `M`, index `(ra_k << 1) | rb_k`]),
  ("0x2  ALU", ((4, "0010", "op"), (8, "0", "z"), (4, "sub", "s"), (4, "0", "z"), (4, "rb", R), (4, "ra", R), (4, "rd", R)), [`ADD` … `ROR`, `MUL64`, `MULHU64`]),
  ("0x3  ALUI", ((4, "0011", "op"), (16, "imm16", "i"), (4, "fn4", "s"), (4, "ra", R), (4, "rd", R)), [`ADDI` … `ROLI`, `SLK16`]),
  ("0x4  IMM20", ((4, "0100", "op"), (20, "imm20", "i"), (4, "mode4", "s"), (4, "rd", R)), [`MOVZ20` `MOVS20` `AUIPC`]),
  ("0x5  CMP", ((4, "0101", "op"), (8, "0", "z"), (4, "0", "z"), (4, "flags4", "s"), (4, "rb", R), (4, "ra", R), (4, "rd", R)), [`flags4` = `IV SN GT EQ`]),
  ("0x6  SEL / byte", ((4, "0110", "op"), (8, "0", "z"), (4, "sub", "s"), (4, "rc", R), (4, "rb", R), (4, "ra", R), (4, "rd", R)), [`SEL` `BEXTU` `BEXTS` `BSWAP64`]),
  ("0x7  LOAD", ((4, "0111", "op"), (16, "simm16", "i"), (4, "mode4", "s"), (4, "ra", R), (4, "rd", R)), [`LD64` (offset × 8), `LDBU`]),
  ("0x8  STORE", ((4, "1000", "op"), (16, "simm16", "i"), (4, "mode4", "s"), (4, "ra", R), (4, "rs", R)), [`ST64` (offset × 8), `STB`]),
  ("0x9  BR", ((4, "1001", "op"), (20, "off20", "i"), (4, "bop4", "s"), (4, "cond", R)), [target `PC + 4 + (sext(off20) << 2)`]),
  ("0xA  JAL", ((4, "1010", "op"), (24, "off24", "i"), (4, "rd", R)), [target `PC + 4 + (sext(off24) << 2)`]),
  ("0xB  JALR", ((4, "1011", "op"), (16, "simm16", "i"), (4, "0", "z"), (4, "ra", R), (4, "rd", R)), [target `R[ra] + (simm16 << 2)`]),
  ("0xC  SPG", ((4, "1100", "op"), (8, "off8", "i"), (8, "sidx", "i"), (4, "sub", "s"), (4, "ra", R), (4, "rd", R)), [lane `S[sidx]`, `sidx < 25`]),
  ("0xD  GL64 / FP5", ((4, "1101", "op"), (8, "0", "z"), (4, "sub", "s"), (4, "rc", R), (4, "rb | eb", R), (4, "ra | ea", R), (4, "rd | ed", R)), [`E` indices `< 5`]),
  ("0xE  GF128", ((4, "1110", "op"), (8, "0", "z"), (4, "sub", "s"), (4, "0", "z"), (4, "pb", R), (4, "pa", R), (4, "pd", R)), [`P` indices `< 12`]),
  ("0xF  PERM", ((4, "1111", "op"), (8, "rounds / 0", "i"), (4, "sub", "s"), (4, "0", "z"), (4, "0", "z"), (4, "0", "z"), (4, "0", "z")), [`rounds` = 12 or 24]),
)
#figure(caption: [The sixteen opcode families. Dark: opcode. Green: sub-opcode or function. Amber: immediate. Blue: register or register-view index. Grey: must be zero.])[
  #grid(
    columns: (2.25cm, 1fr, 4.75cm),
    row-gutter: 2.2pt, column-gutter: 5pt,
    [], grid(columns: (1fr,) * 32, ..range(32).map(i => align(center, text(font: mono, size: 4.6pt, fill: slate, str(31 - i))))), [],
    ..fmt.map(r => bfrow(r.at(0), r.at(1), r.at(2))).flatten(),
  )
]

== Registers and control registers

#grid(
  columns: (0.72fr, 1.28fr),
  gutter: 10pt,
  [
    #dtable(
      (0.6fr, 0.55fr, 1.6fr),
      table.header(..th([Register], [ABI], [Role])),
      [`R0`], [`ZERO`], [reads 0; a write is discarded],
      [`R1`], [`SP`], [stack pointer, 8-byte aligned, grows down],
      [`R2`], [`FP`], [frame pointer],
      [`R3`], [`RA`], [return address; `RET` = `JALR R0, RA, 0`],
      [`R4..R9`], [`A0..A5`], [arguments and results, caller-saved],
      [`R10..R15`], [`T0..T5`], [temporaries, callee-saved],
      [`S0..S24`], [—], [lanes; views `E0..E4`, `P0..P11`],
      [`PC`], [—], [64 bits, not a general register],
    )
    #v(2pt)
    #set par(justify: false)
    #text(size: 7.3pt)[*Traps.* Causes: 1 `IllegalInsn`, 2 `EnvCall` (`EXC`), 3 `MisalignedPc`,
    4 `MisalignedMem`, 5 `MemFault`. With `EXC_EN = 1`: `EPC := PC` (`PC + 4` for `EXC`),
    `ECAUSE := cause`, `EXC_EN := 0`, `PC := EVEC`. With `EXC_EN = 0` a fault halts the core
    with `ECAUSE` set (fail closed) and `EXC` falls through to `PC + 4`. `ERET` restores
    `PC := EPC & ~3` and sets `EXC_EN`.]
  ],
  [
    #dtable(
      (0.42fr, 0.72fr, 0.3fr, 2.6fr),
      table.header(..th([CSR], [Name], [Acc.], [Meaning])),
      [`0x00`], [`ARCH_ID`], [R], [`0x4153_5332_0000_0001`],
      [`0x01`], [`WORD_BITS`], [R], [64],
      [`0x02`], [`EVEC`], [RW], [trap handler base, stored as `val & ~3`],
      [`0x03`], [`POWER`], [W], [`val[0] = 1` halts the core],
      [`0x04`], [`INSTRET`], [RW], [+1 per retired instruction that does not trap; a `CSRW` to it takes effect directly],
      [`0x05`], [`CYCLES`], [RW], [+ the fixed cycle cost of each instruction; a `CSRW` to it takes effect directly],
      [`0x06`], [`FEATURES`], [R], [`0x0000_000F`: `LUT4`, `GL64_FP5`, `GF128`, `KECCAK_POSEIDON2`],
      [`0x08`], [`EPC`], [RW], [continuation `PC` of the last trap],
      [`0x09`], [`ECAUSE`], [RW], [cause of the last trap, 1 to 5],
      [`0x0A`], [`DBG_OUT`], [W], [enqueue bits 7–0, drop on full],
      [`0x0B`], [`DBG_IN`], [R], [bit 8 valid, bits 7–0 byte. Read acknowledges],
      [`0x3F`], [`EXC_EN`], [RW], [bit 0: traps enabled. Cleared on trap entry, set by `ERET`],
      [`0x40`], [`DIT`], [R], [hardwired 1],
      [`0x41`], [`ZEROIZE`], [W], [Write bit 0 = 1 to clear both banks and start the full D-SRAM scrub],
    )
  ],
)

#v(5pt)
#callout("Unassigned addresses", [`0x07`, `0x0C..0x3E` and `0x42..0xFF` have no architectural CSR definition. The reference VM raises `IllegalInsn` for an unassigned CSR or access in the wrong direction.])


#pagebreak()

// ============================================================================================
// PAGE 6
// ============================================================================================
= Instruction reference, families `0x0` to `0x6`

`R[x]` is a general register, all arithmetic is on 64-bit words, `zext` and `sext` extend to 64
bits. Every instruction advances `PC` by 4 unless stated. Hex words in the last column were
assembled by the reference assembler and are checked by `check_examples.py`.

#let itab(..cells) = dtable(
  (1.25fr, 0.4fr, 3.3fr, 0.32fr, 0.95fr),
  size: 6.8pt, inset: 2.5pt,
  table.header(..th([Mnemonic and operands], [Sub], [Operation], [Cyc], [Example word])),
  ..cells,
)
#itab(
  fam(5)[`0x0` SYS · `sub` = bits 19..16; `ERET`, `ZEROIZE`, `HALT`, `NOP` require every other field zero],
  [`EXC`], [`0`], [the all-zero word. `EXC_EN = 1`: `EPC := PC + 4`, `ECAUSE := 2`, `EXC_EN := 0`, `PC := EVEC`. With traps disabled, `PC := PC + 4`], [1], [`00000000`],
  [`ERET`], [`1`], [`PC := EPC & ~3`, `EXC_EN := 1`], [1], [`00010000`],
  [`CSRR rd, csr8`], [`2`], [`R[rd] := csr_read(csr8)`; `ra = rb = rc = 0`], [1], [`00520004` · `CSRR A0, CYCLES`],
  [`CSRW ra, csr8`], [`3`], [`csr_write(csr8, R[ra])`; `rd = rb = rc = 0`], [1], [`002300a0` · `CSRW T0, EVEC`],
  [`ZEROIZE`], [`4`], [Clear both banks, start full D-SRAM scrub], [1], [`00040000`],
  [`HALT`], [`5`], [`halted := true`], [1], [`00050000`],
  [`NOP`], [`6`], [no effect], [1], [`00060000`],
  fam(5)[`0x1` LUT4 · `M` = bits 19..16; `rc` and `imm8` zero],
  [`LUT4 rd, ra, rb, M`], [`M`], [for each bit `k`: `out[k] := (M >> ((ra[k] << 1) | rb[k])) & 1`. Aliases: `XOR` 6, `AND` 8, `OR` 14, `XNOR` 9, `ANDN` 4, `NOR` 1, `NAND` 7, `ORN` 13, `MOV rd, ra` 12, `NOT rd, ra` 3], [1], [`10060654` · `XOR A0, A1, A2`],
  fam(5)[`0x2` ALU · `rc` and `imm8` zero],
  [`ADD rd, ra, rb`], [`0`], [`(R[ra] + R[rb]) mod 2^64`], [1], [`20000654`],
  [`SUB rd, ra, rb`], [`1`], [`(R[ra] − R[rb]) mod 2^64`], [1], [],
  [`SHL rd, ra, rb`], [`2`], [`R[rb] >= 64 ? 0 : R[ra] << R[rb]`], [1], [],
  [`SHR rd, ra, rb`], [`3`], [`R[rb] >= 64 ? 0 : R[ra] >> R[rb]` (logical)], [1], [],
  [`ASR rd, ra, rb`], [`4`], [arithmetic shift; a count of 64 or more gives 64 copies of the sign bit], [1], [],
  [`ROL rd, ra, rb`], [`5`], [rotate left by `R[rb] & 63`], [1], [],
  [`ROR rd, ra, rb`], [`6`], [rotate right by `R[rb] & 63`], [1], [],
  [`MUL64 rd, ra, rb`], [`7`], [low 64 bits of `R[ra] × R[rb]`], [4], [`2007054a` · `MUL64 T0, A0, A1`],
  [`MULHU64 rd, ra, rb`], [`8`], [high 64 bits of the unsigned 128-bit product], [4], [],
  fam(5)[`0x3` ALUI · `fn4` = bits 11..8, `imm16` = bits 27..12],
  [`ADDI rd, ra, s16`], [`0`], [`R[ra] + sext(imm16)`], [1], [`3fff0011` · `ADDI SP, SP, -16`],
  [`ADDIU rd, ra, u16`], [`1`], [`R[ra] + zext(imm16)`], [1], [],
  [`XORI` · `ANDI` · `ORI`], [`2` `3` `4`], [bitwise with `zext(imm16)`], [1], [],
  [`SHLI` · `SHRI` · `ASRI`], [`5` `6` `7`], [shift by `imm16 & 63`; `imm16 >> 6` must be zero], [1], [],
  [`ROLI rd, ra, n`], [`8`], [rotate left by `imm16 & 63`; `imm16 >> 6` must be zero], [1], [],
  [`SLK16 rd, ra, u16`], [`9`], [`(R[ra] << 16) | zext(imm16)`: shift in 16 constant bits], [1], [`3beef9aa` · `SLK16 T0, T0, 0xBEEF`],
  fam(5)[`0x4` IMM20 · `mode4` = bits 7..4, `imm20` = bits 27..8],
  [`MOVZ20 rd, u20`], [`0`], [`R[rd] := zext(imm20)`], [1], [`4123450a` · `MOVZ20 T0, 0x12345`],
  [`MOVS20 rd, s20`], [`1`], [`R[rd] := sext(imm20)`], [1], [],
  [`AUIPC rd, s20`], [`2`], [`R[rd] := PC + (sext(imm20) << 2)`], [1], [],
  fam(5)[`0x5` CMP · `flags4` = bits 15..12 = `IV SN GT EQ`; `sub` and `imm8` zero],
  [`CMP rd, ra, rb, pred`], [—], [`e := EQ and R[ra] = R[rb]`; `g := GT and R[ra] > R[rb]` (signed if `SN`); `R[rd] := (IV ? not (e or g) : (e or g)) ? 1 : 0`], [1], [`5000b54a` · `CMP T0, A0, A1, LTU`],
  fam(5)[`0x6` SEL and bytes · `imm8` zero],
  [`SEL rd, ra, rb, rc`], [`0`], [`R[rd] := (R[rc] = 0) ? R[ra] : R[rb]`. The constant-time select], [1], [`6000a654` · `SEL A0, A1, A2, T0`],
  [`BEXTU rd, ra, i, n`], [`1`], [`n` bytes of `R[ra]` from byte `i`, zero-extended. `i` = `rb` 0..7, `n` = 1..8 (`rc` = `n & 7`)], [1], [],
  [`BEXTS rd, ra, i, n`], [`2`], [shift right logically, mask to `8n` bits, then sign-extend from bit `8n − 1` for `n < 8`], [1], [],
  [`BSWAP64 rd, ra`], [`3`], [reverse the 8 bytes of `R[ra]`; `rb`, `rc` zero], [1], [],
)

#v(2pt)
#grid(
  columns: (1fr, 1fr),
  gutter: 10pt,
  [
    #dtable(
      (0.55fr, 0.38fr, 0.55fr, 0.38fr, 0.55fr, 0.38fr, 0.55fr, 0.38fr),
      size: 6.8pt, inset: 2.5pt,
      table.header(..th([`LUT4`], [`M`], [`LUT4`], [`M`], [`LUT4`], [`M`], [`LUT4`], [`M`])),
      [`ZERO`], [0], [`ANDN a,b`], [4], [`AND`], [8], [`MOV a`], [12],
      [`NOR`], [1], [`NOT b`], [5], [`XNOR`], [9], [`ORN a,b`], [13],
      [`ANDN b,a`], [2], [`XOR`], [6], [`MOV b`], [10], [`OR`], [14],
      [`NOT a`], [3], [`NAND`], [7], [`ORN b,a`], [11], [`ONES`], [15],
    )
    #text(size: 6.8pt)[`ANDN a,b` is `a and not b`; `ORN a,b` is `a or not b`. Bit 3 of `M` is the output for `a = b = 1`, bit 0 for `a = b = 0`.]
  ],
  [
    #dtable(
      (0.5fr, 0.4fr, 0.5fr, 0.4fr, 0.5fr, 0.4fr, 0.5fr, 0.4fr),
      size: 6.8pt, inset: 2.5pt,
      table.header(..th([`CMP`], [`flags4`], [`CMP`], [`flags4`], [`CMP`], [`flags4`], [`CMP`], [`flags4`])),
      [`F`], [0], [`GEU`], [3], [`T`], [8], [`LTU`], [11],
      [`EQ`], [1], [`GTS`], [6], [`NE`], [9], [`LES`], [14],
      [`GTU`], [2], [`GES`], [7], [`LEU`], [10], [`LTS`], [15],
    )
    #text(size: 6.8pt)[Predicate names of the reference assembler. `U` unsigned, `S` signed. `F` and `T` write the constants 0 and 1. The remaining four codes (4, 5, 12, 13) repeat `F`, `EQ`, `T`, `NE`.]
  ],
)

#pagebreak()

// ============================================================================================
// PAGE 7
// ============================================================================================
= Instruction reference, families `0x7` to `0xF`

#itab(
  fam(5)[`0x7` LOAD · `0x8` STORE · `mode4` = bits 11..8, `simm16` = bits 27..12; the store source is bits 3..0],
  [`LD64 rd, [ra + off]`], [`0`], [`ea := R[ra] + (simm16 << 3)`; `ea & 7 != 0` traps `MisalignedMem`; `R[rd] := mem64[ea]`. `off` is a multiple of 8], [2], [`7000201a` · `LD64 T0, [SP+16]`],
  [`LDBU rd, [ra + off]`], [`1`], [`R[rd] := zext(mem8[R[ra] + simm16])`], [2], [],
  [`ST64 [ra + off], rs`], [`0`], [`mem64[R[ra] + (simm16 << 3)] := R[rs]`; alignment as `LD64`], [2], [`8000201a` · `ST64 [SP+16], T0`],
  [`STB [ra + off], rs`], [`1`], [`mem8[R[ra] + simm16] := R[rs][7:0]`], [2], [],
  fam(5)[`0x9` BR · `bop4` = bits 7..4, register in bits 3..0. One cycle whether taken or not. Public conditions only],
  [`BEQZ` · `BNEZ r, label`], [`0` `1`], [taken if `R[r] = 0` · `R[r] != 0`: `PC := PC + 4 + (off20 << 2)`], [1], [`9ffff315` · `BNEZ A1, −13`],
  [`BLTZ` · `BGEZ r, label`], [`2` `3`], [taken if `R[r]` as a signed word is `< 0` · `>= 0`], [1], [],
  fam(5)[`0xA` JAL · `0xB` JALR],
  [`JAL rd, label`], [—], [`R[rd] := PC + 4`; `PC := PC + 4 + (off24 << 2)`. `CALL f` = `JAL RA, f`; `J l` = `JAL R0, l`], [1], [],
  [`JALR rd, ra, s16`], [—], [`t := R[ra] + (simm16 << 2)`; `t & 3 != 0` traps `MisalignedPc`; `R[rd] := PC + 4`; `PC := t`. Safe when `rd = ra`], [1], [`b0000030` · `RET`],
  fam(5)[`0xC` SPG · `sub` = bits 11..8, `sidx` = bits 19..12 (lane ≥25 traps), `off8` = bits 27..20],
  [`SGET rd, S[i]`], [`0`], [`R[rd] := S[i]`; `ra = off8 = 0`], [1], [`c000600a` · `SGET T0, S[6]`],
  [`SPUT S[i], ra`], [`1`], [`S[i] := R[ra]`; `rd = off8 = 0`], [1], [],
  [`SXOR S[i], ra`], [`2`], [`S[i] := S[i] xor R[ra]`; `rd = off8 = 0`], [1], [`c000d2a0` · `SXOR S[13], T0`],
  [`SZERO`], [`3`], [`S[0..24] := 0`; all operands zero], [1], [`c0000300`],
  [`SLD64 S[i], [ra + off]`], [`4`], [`S[i] := mem64[R[ra] + (sext(off8) << 3)]`; `rd = 0`; alignment as `LD64`], [2], [`c1818480` · `SLD64 S[24], [A4+192]`],
  [`SST64 [ra + off], S[i]`], [`5`], [`mem64[R[ra] + (sext(off8) << 3)] := S[i]`; `rd = 0`, aligned], [2], [],
  fam(5)[`0xD` GL64 and FP5 · $p = 2^64 - 2^32 + 1$; inputs are reduced mod $p$, results are canonical (`< p`); `imm8 = 0`, `rc = 0` except on MAC, `rb = 0` on SBOX7],
  [`GL.MAC rd, ra, rb, rc`], [`0`], [`R[rd] := (R[ra] × R[rb] + R[rc]) mod p`], [4], [`d0007654` · `GL.MAC A0, A1, A2, A3`],
  [`GL.ADD` · `GL.SUB rd, ra, rb`], [`1` `2`], [`(R[ra] ± R[rb]) mod p`], [1], [],
  [`GL.SBOX7 rd, ra`], [`3`], [`R[ra]^7 mod p`], [12], [],
  [`FP5.MUL ed, ea, eb`], [`4`], [`E[ed] := E[ea] × E[eb]` in $FF_p [u] \/ (u^5 - 3)$. Both operands are read before the write, so `ed` may equal `ea` or `eb`], [104], [`d0040100` · `FP5.MUL E0, E0, E1`],
  [`FP5.ADD` · `FP5.SUB ed, ea, eb`], [`5` `6`], [limb-wise `E[ea] ± E[eb]` mod $p$], [5], [`d0050200` · `FP5.ADD E0, E0, E2`],
  fam(5)[`0xE` GF128 · $FF_2 [x] \/ (x^128 + x^7 + x^2 + x + 1)$, bit $i$ of a register is the coefficient of $x^i$; `rc`, `imm8` zero],
  [`GF128.MUL pd, pa, pb`], [`0`], [`P[pd] := P[pa] × P[pb]`, operands read before the write], [4], [`e0000404` · `GF128.MUL P4, P0, P4`],
  [`GF128.XOR pd, pa, pb`], [`1`], [`P[pd] := P[pa] xor P[pb]`], [1], [`e0010444`],
  fam(5)[`0xF` PERM · in place; register fields zero, `imm8 = 0` for Poseidon2],
  [`KECCAK.F1600 n`], [`0`], [the last `n` rounds of `Keccak-f[1600]` on `S[0..24]`; `n` = 12 (`TurboSHAKE256`, RFC 9861) or 24 (full-round permutation for SHAKE256 and cSHAKE256)], [`n`], [`f0c00000` · `f1800000`],
  [`POSEIDON2.GL24`], [`1`], [`Poseidon2-GL-w24` on `S[0..23]`: 52 rounds, $R_F = 8$, $R_P = 44$, external matrix $M_4 times.o P_6$, shift-only internal matrix], [216], [`f0010000`],
  [`POSEIDON2.GL12`], [`2`], [width-12 `Poseidon2` on `S[0..11]`: 30 rounds], [120], [`f0020000`],
)

== Views of the bank `S0..S24`

#let ov(n, t, f, fg: black) = grid.cell(colspan: n, box(width: 100%, height: 11pt, fill: f, stroke: 0.5pt + navy, align(center + horizon, text(size: 5.9pt, fill: fg, t))))
#let lab(t) = align(right + horizon, text(size: 6.5pt, weight: "bold", fill: navy, t))
#figure(caption: [One 1,600-bit bank, four overlaid views. `E_k` = `S[5k..5k+4]`, limb 0 first. `P_k` = (`lo`: `S[2k]`, `hi`: `S[2k+1]`). `S24` is Keccak lane 24 and the fifth limb of `E4`.])[
  #grid(
    columns: (2.6cm,) + (1fr,) * 25,
    row-gutter: 2pt, column-gutter: 0pt,
    lab[lane],
    ..range(25).map(i => box(width: 100%, height: 11pt, fill: secbg, stroke: 0.5pt + secbd, align(center + horizon, text(font: mono, size: 5.2pt, "S" + str(i))))),
    lab[`Keccak-f[1600]`], ov(17, [rate: 17 lanes = 136 bytes (`TurboSHAKE256`, `SHAKE256`)], rgb("#dbeafe")), ov(8, [capacity 512 bits], rgb("#bfdbfe")),
    lab[`Poseidon2-GL-w24`], ov(7, [digest `S[0..6]`], rgb("#fde68a")), ov(9, [rate, 16 limbs in all], rgb("#fef3c7")), ov(8, [capacity, 8 limbs], rgb("#fde68a")), ov(1, [], white),
    lab[`Poseidon2-GL-w12`], ov(12, [state `S[0..11]`], rgb("#fef3c7")), ov(13, [not touched], white),
    lab[`E0..E4`  quintic], ov(5, [`E0`], rgb("#dcfce7")), ov(5, [`E1`], rgb("#bbf7d0")), ov(5, [`E2`], rgb("#dcfce7")), ov(5, [`E3`], rgb("#bbf7d0")), ov(5, [`E4`], rgb("#dcfce7")),
    lab[`P0..P11`  $"GF"(2^128)$], ..range(12).map(i => ov(2, [`P` #str(i)], if calc.even(i) { rgb("#ede9fe") } else { rgb("#ddd6fe") })), ov(1, [], white),
  )
]

#grid(
  columns: (1fr, 1fr),
  gutter: 10pt,
  [
    #set par(justify: false)
    #text(size: 7.4pt)[*Overlap is the programmer's responsibility.* The views are names for
    the same latches: `FP5.MUL E0, …` overwrites `P0`, `P1` and half of `P2`; a permutation
    overwrites every view it covers. A routine keeps its values in lanes that the next
    instruction does not write, as the Jive listing on page 9 does when it reloads `E2`, `E3`
    over lanes that hold spent permutation output.]
  ],
  [
    #dtable(
      (1.6fr, 0.5fr, 0.9fr),
      size: 6.8pt, inset: 2.5pt,
      table.header(..th([Architectural cost], [Cycles], [Cost × 50 ns¹])),
      [word unit, branch, jump, CSR, lane move], [1], [50 ns],
      [memory and lane load or store], [2], [100 ns],
      [`MUL64`, `MULHU64`, `GL.MAC`, `GF128.MUL`], [4], [200 ns],
      [`FP5.ADD`, `FP5.SUB` · `GL.SBOX7`], [5 · 12], [250 ns · 600 ns],
      [`KECCAK.F1600 12` · `24`], [12 · 24], [0.60 µs · 1.20 µs],
      [`FP5.MUL` · `POSEIDON2.GL12` · `GL24`], [104 · 120 · 216], [5.20 · 6.00 · 10.80 µs],
    )
  ],
)

¹ Architectural cost at 50 ns per cycle (20 MHz 9-corner SPEF signoff). Fetch and memory waits add elapsed time.

#pagebreak()

// ============================================================================================
// PAGE 8
// ============================================================================================
= Programming guide · field arithmetic

#text(size: 8pt)[Each line gives the byte PC, the 32-bit word in numeric order and the source instruction.
Listing PCs are offsets from the routine base. All memory displacements in assembly are in bytes. Timing includes the final `RET`.]

#let listtext = 6.9pt
#show raw.where(block: true): set text(size: listtext)
#grid(columns: (1fr, 1fr), gutter: 12pt, [
  == Quintic Horner evaluation
  #text(size: 7.6pt)[`A0` points to the leading coefficient in an ascending array of five-limb coefficients, `A1` holds public degree $d$, and `E1` holds the evaluation point. `E0` returns the result after *12 + 122d cycles*. `horner_step` is at `0x18`, `horner_done` at `0x40`.]
  // @listing fp5_horner print
```text
0000  c0000440  SLD64   S[0], [A0+0]
0004  c0101440  SLD64   S[1], [A0+8]
0008  c0202440  SLD64   S[2], [A0+16]
000c  c0303440  SLD64   S[3], [A0+24]
0010  c0404440  SLD64   S[4], [A0+32]
0014  90000a05  BEQZ    A1, horner_done
0018  3ffd8044  ADDI    A0, A0, -40
001c  c000a440  SLD64   S[10], [A0+0]
0020  c010b440  SLD64   S[11], [A0+8]
0024  c020c440  SLD64   S[12], [A0+16]
0028  c030d440  SLD64   S[13], [A0+24]
002c  c040e440  SLD64   S[14], [A0+32]
0030  d0040100  FP5.MUL E0, E0, E1
0034  d0050200  FP5.ADD E0, E0, E2
0038  3ffff055  ADDI    A1, A1, -1
003c  9ffff615  BNEZ    A1, horner_step
0040  b0000030  RET
```
  // @end

  == Binary-field MAC check
  #text(size: 7.6pt)[`P0` holds the key $r$. `A0` points to $n$ records of three LE128 elements $(a,z,m)$, `A1` holds public $n ≥ 1$. The routine reduces both 64-bit halves of $sum a m + r sum a z$ to a single verdict in `A0`. *13 + 25n cycles*. `mac_loop` is at `0x08`.]
  // @listing cth_dualmac print
```text
0000  e0010444  GF128.XOR P4, P4, P4
0004  e0010555  GF128.XOR P5, P5, P5
0008  c0002440  SLD64   S[2], [A0+0]
000c  c0103440  SLD64   S[3], [A0+8]
0010  c0204440  SLD64   S[4], [A0+16]
0014  c0305440  SLD64   S[5], [A0+24]
0018  c0406440  SLD64   S[6], [A0+32]
001c  c0507440  SLD64   S[7], [A0+40]
0020  e0000212  GF128.MUL P2, P1, P2
0024  e0000313  GF128.MUL P3, P1, P3
0028  e0010244  GF128.XOR P4, P4, P2
002c  e0010355  GF128.XOR P5, P5, P3
0030  30030044  ADDI    A0, A0, 48
0034  3ffff055  ADDI    A1, A1, -1
0038  9ffff315  BNEZ    A1, mac_loop
003c  e0000404  GF128.MUL P4, P0, P4
0040  e0010455  GF128.XOR P5, P5, P4
0044  c000a005  SGET    A1, S[10]
0048  c000b006  SGET    A2, S[11]
004c  100e0655  OR      A1, A1, A2
0050  50001054  CMP     A0, A1, ZERO, EQ
0054  c0000300  SZERO
0058  b0000030  RET
```
  // @end

  == Constant-time idioms
  #text(size: 7.6pt)[Only public values may select a branch, indirect jump or memory address. For a secret condition, load both candidates at fixed public addresses and select their values. `LI64` emits four instructions and performs no data read.]
  ```text
  ; A0 = (A2 < A3 unsigned) ? A1 : A0
  CMP  T0, A2, A3, LTU
  SEL  A0, A0, A1, T0

  ; LI64 T0, 0x0123456789abcdef
  0000  4001230a  MOVZ20 T0, 0x0123
  0004  345679aa  SLK16  T0, T0, 0x4567
  0008  389ab9aa  SLK16  T0, T0, 0x89ab
  000c  3cdef9aa  SLK16  T0, T0, 0xcdef
  ```
  #text(size: 7.6pt)[`T0..T5` are callee-saved. `SZERO` clears the lanes. For a mailbox reply, write the permitted result to TX and halt. `ZEROIZE` erases TX, `RA` and `SP`.]
], [
  == Seven-limb Jive compression
  #text(size: 7.6pt)[`A0/A1/A2` point to left/right/output (56 bytes each). `A3/A4` hold the two tweaks. After one permutation, add $L_i + 2 R_i$ to each of seven output limbs and $4 t_i$ to the first two. *347 cycles*.]
  // @listing p2gl24_jive print
```text
0000  c0000300  SZERO
0004  c0000440  SLD64   S[0], [A0+0]
0008  c0101440  SLD64   S[1], [A0+8]
000c  c0202440  SLD64   S[2], [A0+16]
0010  c0303440  SLD64   S[3], [A0+24]
0014  c0404440  SLD64   S[4], [A0+32]
0018  c0505440  SLD64   S[5], [A0+40]
001c  c0606440  SLD64   S[6], [A0+48]
0020  c0007450  SLD64   S[7], [A1+0]
0024  c0108450  SLD64   S[8], [A1+8]
0028  c0209450  SLD64   S[9], [A1+16]
002c  c030a450  SLD64   S[10], [A1+24]
0030  c040b450  SLD64   S[11], [A1+32]
0034  c050c450  SLD64   S[12], [A1+40]
0038  c060d450  SLD64   S[13], [A1+48]
003c  c000e170  SPUT    S[14], A3
0040  c000f180  SPUT    S[15], A4
0044  40001009  MOVZ20  A5, 16
0048  c0010190  SPUT    S[16], A5
004c  40000809  MOVZ20  A5, 8
0050  c0011190  SPUT    S[17], A5
0054  40000709  MOVZ20  A5, 7
0058  c0012190  SPUT    S[18], A5
005c  404d5209  MOVZ20  A5, 0x4d52
0060  34b4c999  SLK16   A5, A5, 0x4b4c
0064  3474c999  SLK16   A5, A5, 0x474c
0068  33234999  SLK16   A5, A5, 0x3234
006c  c0013190  SPUT    S[19], A5
0070  40504f09  MOVZ20  A5, 0x504f
0074  35332999  SLK16   A5, A5, 0x5332
0078  3474c999  SLK16   A5, A5, 0x474c
007c  33234999  SLK16   A5, A5, 0x3234
0080  c0017190  SPUT    S[23], A5
0084  f0010000  POSEIDON2.GL24
0088  c000a440  SLD64   S[10], [A0+0]
008c  c010b440  SLD64   S[11], [A0+8]
0090  c020c440  SLD64   S[12], [A0+16]
0094  c030d440  SLD64   S[13], [A0+24]
0098  c040e440  SLD64   S[14], [A0+32]
009c  c050f440  SLD64   S[15], [A0+40]
00a0  c0610440  SLD64   S[16], [A0+48]
00a4  d0050200  FP5.ADD E0, E0, E2
00a8  d0050311  FP5.ADD E1, E1, E3
00ac  c000a450  SLD64   S[10], [A1+0]
00b0  c010b450  SLD64   S[11], [A1+8]
00b4  c020c450  SLD64   S[12], [A1+16]
00b8  c030d450  SLD64   S[13], [A1+24]
00bc  c040e450  SLD64   S[14], [A1+32]
00c0  c050f450  SLD64   S[15], [A1+40]
00c4  c0610450  SLD64   S[16], [A1+48]
00c8  d0050222  FP5.ADD E2, E2, E2
00cc  d0050333  FP5.ADD E3, E3, E3
00d0  d0050200  FP5.ADD E0, E0, E2
00d4  d0050311  FP5.ADD E1, E1, E3
00d8  d0010777  GL.ADD  A3, A3, A3
00dc  d0010777  GL.ADD  A3, A3, A3
00e0  c0000009  SGET    A5, S[0]
00e4  d0010799  GL.ADD  A5, A5, A3
00e8  c0000190  SPUT    S[0], A5
00ec  d0010888  GL.ADD  A4, A4, A4
00f0  d0010888  GL.ADD  A4, A4, A4
00f4  c0001009  SGET    A5, S[1]
00f8  d0010899  GL.ADD  A5, A5, A4
00fc  c0001190  SPUT    S[1], A5
0100  c0000560  SST64   [A2+0], S[0]
0104  c0101560  SST64   [A2+8], S[1]
0108  c0202560  SST64   [A2+16], S[2]
010c  c0303560  SST64   [A2+24], S[3]
0110  c0404560  SST64   [A2+32], S[4]
0114  c0505560  SST64   [A2+40], S[5]
0118  c0606560  SST64   [A2+48], S[6]
011c  c0000300  SZERO
0120  b0000030  RET
```
  // @end
])

#pagebreak()

= Programming guide · 50-byte Canopy node and SPI host

#text(size: 8pt)[`A0/A1` point to padded current/sibling digests (50 bytes + six zero bytes each). `A2` is the possibly secret direction. `A3` holds the public 32-bit heap parent index, `A4` points to the 25-lane tree midstate, and `A5` points to 56 writable bytes. `SP` has one disjoint stack word below it. The routine absorbs tag 0, LE32 parent index, then 50 bytes per child, with suffix `0x07` at byte 105 and final bit at byte 135. *130 instructions, 190 cycles; 520 bytes in immutable resident `I-ROM`*. Read down the left column, then the right.]
#show raw.where(block: true): set text(size: listtext)
#grid(columns: (1fr, 1fr), gutter: 12pt, [
  // @listing canopy50_node print 0-64
```text
0000  3fff8011  ADDI    SP, SP, -8
0004  8000001a  ST64    [SP], T0
0008  c0000480  SLD64   S[0], [A4+0]
000c  c0101480  SLD64   S[1], [A4+8]
0010  c0202480  SLD64   S[2], [A4+16]
0014  c0303480  SLD64   S[3], [A4+24]
0018  c0404480  SLD64   S[4], [A4+32]
001c  c0505480  SLD64   S[5], [A4+40]
0020  c0606480  SLD64   S[6], [A4+48]
0024  c0707480  SLD64   S[7], [A4+56]
0028  c0808480  SLD64   S[8], [A4+64]
002c  c0909480  SLD64   S[9], [A4+72]
0030  c0a0a480  SLD64   S[10], [A4+80]
0034  c0b0b480  SLD64   S[11], [A4+88]
0038  c0c0c480  SLD64   S[12], [A4+96]
003c  c0d0d480  SLD64   S[13], [A4+104]
0040  c0e0e480  SLD64   S[14], [A4+112]
0044  c0f0f480  SLD64   S[15], [A4+120]
0048  c1010480  SLD64   S[16], [A4+128]
004c  c1111480  SLD64   S[17], [A4+136]
0050  c1212480  SLD64   S[18], [A4+144]
0054  c1313480  SLD64   S[19], [A4+152]
0058  c1414480  SLD64   S[20], [A4+160]
005c  c1515480  SLD64   S[21], [A4+168]
0060  c1616480  SLD64   S[22], [A4+176]
0064  c1717480  SLD64   S[23], [A4+184]
0068  c1818480  SLD64   S[24], [A4+192]
006c  3000857a  SHLI    T0, A3, 8
0070  c00002a0  SXOR    S[0], T0
0074  70000047  LD64    A3, [A0+0]
0078  70000058  LD64    A4, [A1+0]
007c  6000687a  SEL     T0, A3, A4, A2
0080  60006788  SEL     A4, A4, A3, A2
0084  300285a7  SHLI    A3, T0, 40
0088  c0000270  SXOR    S[0], A3
008c  300186a7  SHRI    A3, T0, 24
0090  c0001270  SXOR    S[1], A3
0094  30038587  SHLI    A3, A4, 56
0098  c0006270  SXOR    S[6], A3
009c  30008687  SHRI    A3, A4, 8
00a0  c0007270  SXOR    S[7], A3
00a4  70001047  LD64    A3, [A0+8]
00a8  70001058  LD64    A4, [A1+8]
00ac  6000687a  SEL     T0, A3, A4, A2
00b0  60006788  SEL     A4, A4, A3, A2
00b4  300285a7  SHLI    A3, T0, 40
00b8  c0001270  SXOR    S[1], A3
00bc  300186a7  SHRI    A3, T0, 24
00c0  c0002270  SXOR    S[2], A3
00c4  30038587  SHLI    A3, A4, 56
00c8  c0007270  SXOR    S[7], A3
00cc  30008687  SHRI    A3, A4, 8
00d0  c0008270  SXOR    S[8], A3
00d4  70002047  LD64    A3, [A0+16]
00d8  70002058  LD64    A4, [A1+16]
00dc  6000687a  SEL     T0, A3, A4, A2
00e0  60006788  SEL     A4, A4, A3, A2
00e4  300285a7  SHLI    A3, T0, 40
00e8  c0002270  SXOR    S[2], A3
00ec  300186a7  SHRI    A3, T0, 24
00f0  c0003270  SXOR    S[3], A3
00f4  30038587  SHLI    A3, A4, 56
00f8  c0008270  SXOR    S[8], A3
00fc  30008687  SHRI    A3, A4, 8
0100  c0009270  SXOR    S[9], A3
```
  // @end
], [
  // @listing canopy50_node print 65-129
```text
0104  70003047  LD64    A3, [A0+24]
0108  70003058  LD64    A4, [A1+24]
010c  6000687a  SEL     T0, A3, A4, A2
0110  60006788  SEL     A4, A4, A3, A2
0114  300285a7  SHLI    A3, T0, 40
0118  c0003270  SXOR    S[3], A3
011c  300186a7  SHRI    A3, T0, 24
0120  c0004270  SXOR    S[4], A3
0124  30038587  SHLI    A3, A4, 56
0128  c0009270  SXOR    S[9], A3
012c  30008687  SHRI    A3, A4, 8
0130  c000a270  SXOR    S[10], A3
0134  70004047  LD64    A3, [A0+32]
0138  70004058  LD64    A4, [A1+32]
013c  6000687a  SEL     T0, A3, A4, A2
0140  60006788  SEL     A4, A4, A3, A2
0144  300285a7  SHLI    A3, T0, 40
0148  c0004270  SXOR    S[4], A3
014c  300186a7  SHRI    A3, T0, 24
0150  c0005270  SXOR    S[5], A3
0154  30038587  SHLI    A3, A4, 56
0158  c000a270  SXOR    S[10], A3
015c  30008687  SHRI    A3, A4, 8
0160  c000b270  SXOR    S[11], A3
0164  70005047  LD64    A3, [A0+40]
0168  70005058  LD64    A4, [A1+40]
016c  6000687a  SEL     T0, A3, A4, A2
0170  60006788  SEL     A4, A4, A3, A2
0174  300285a7  SHLI    A3, T0, 40
0178  c0005270  SXOR    S[5], A3
017c  300186a7  SHRI    A3, T0, 24
0180  c0006270  SXOR    S[6], A3
0184  30038587  SHLI    A3, A4, 56
0188  c000b270  SXOR    S[11], A3
018c  30008687  SHRI    A3, A4, 8
0190  c000c270  SXOR    S[12], A3
0194  70006047  LD64    A3, [A0+48]
0198  70006058  LD64    A4, [A1+48]
019c  6000687a  SEL     T0, A3, A4, A2
01a0  60006788  SEL     A4, A4, A3, A2
01a4  300285a7  SHLI    A3, T0, 40
01a8  c0006270  SXOR    S[6], A3
01ac  30038587  SHLI    A3, A4, 56
01b0  c000c270  SXOR    S[12], A3
01b4  30008687  SHRI    A3, A4, 8
01b8  c000d270  SXOR    S[13], A3
01bc  40070007  MOVZ20  A3, 0x700
01c0  c000d270  SXOR    S[13], A3
01c4  40008007  MOVZ20  A3, 0x80
01c8  30038577  SHLI    A3, A3, 56
01cc  c0010270  SXOR    S[16], A3
01d0  f0c00000  KECCAK.F1600 12
01d4  c0000590  SST64   [A5+0], S[0]
01d8  c0101590  SST64   [A5+8], S[1]
01dc  c0202590  SST64   [A5+16], S[2]
01e0  c0303590  SST64   [A5+24], S[3]
01e4  c0404590  SST64   [A5+32], S[4]
01e8  c0505590  SST64   [A5+40], S[5]
01ec  c0006007  SGET    A3, S[6]
01f0  3ffff377  ANDI    A3, A3, 0xFFFF
01f4  80006097  ST64    [A5+48], A3
01f8  7000001a  LD64    T0, [SP]
01fc  80000010  ST64    [SP], ZERO
0200  30008011  ADDI    SP, SP, 8
0204  b0000030  RET
```
  // @end
])
== Reading a QSAG-Wire response
#text(size: 7.6pt)[After `HOST_IRQ` rises, the driver keeps `HOST_CS_N` low across the header and padded body. The prefix supplies the single-bit read command and eight dummy clocks. The full Rust example and error paths appear in the programming guide.]
 // @rust 86-95
```rust
    let mut rx = bus.begin_read(&[0x02, 0x00])?; // read prefix and eight dummy clocks
    let mut hdr = [0; 8];
    rx.read_exact(&mut hdr)?;
    if hdr[0] != 0x51 {
        return Err(WireError::BadMagic);
    }
    if hdr[1] != (op | 0x80) {
        return Err(WireError::BadOpcode);
    }
    let len = u32::from_le_bytes([hdr[3], hdr[4], hdr[5], 0]) as usize;
```
 // @end

#pagebreak()

#set text(size: 9.1pt)
= Nine-corner electrical characterization
GF180MCU BSIM3v3 transistor models at TT (5.0 V), SS (4.5 V) and FF (5.5 V). RO-PUF, cold-rail isolation and PDN used ngspice 47. The rapid-response and Vernier decks used ngspice 45. Temperature is junction temperature in the chip decks.

#dtable((.83fr, 1.23fr, .77fr, 1.11fr, .6fr, .62fr, 1.12fr), size: 7.8pt, inset: 3.5pt,
  table.header(..th([PVT], [RO mean ± σ (MHz)], [BCH window (µs)], [Cold avg / peak (nA / µA)], [Rapid (ns)], [TDC (ps)], [South bounce (mV) baseline / carrier])),
  [TT / -40 °C], [850.222 ± 1.505], [10.24], [46.7 / 39.20], [3.047], [95.08], [376.2 / 328.2],
  [TT / 27 °C], [716.484 ± 1.306], [10.24], [46.5 / 35.75], [3.616], [108.78], [283.7 / 243.9],
  [TT / 125 °C], [579.917 ± 1.068], [20.48], [6.7 / 35.76], [4.411], [127.28], [202.5 / 171.8],
  [SS / -40 °C], [588.111 ± 1.241], [10.24], [39.8 / 39.28], [4.165], [136.46], [255.0 / 218.1],
  [SS / 27 °C], [493.664 ± 1.069], [20.48], [39.0 / 35.82], [4.972], [157.20], [191.1 / 160.9],
  [SS / 125 °C], [398.984 ± 0.859], [20.48], [5.8 / 35.73], [6.159], [184.37], [134.6 / 111.5],
  [FF / -40 °C], [1120.261 ± 1.656], [10.24], [40.5 / 39.02], [2.422], [72.77], [516.1 / 453.9],
  [FF / 27 °C], [950.486 ± 1.484], [10.24], [36.3 / 35.64], [2.853], [82.22], [388.8 / 338.0],
  [FF / 125 °C], [773.247 ± 1.246], [20.48], [6.6 / 35.87], [3.469], [95.78], [274.9 / 234.9],
)

== Ring pairs and helper data

All characterized 5-stage `gf180mcu_fd_sc_mcu7t5v0` rings oscillated across all nine BSIM3v3 corners, spanning 399–1,120 MHz. Rev. 2.0 instantiates *512 physical 5-stage rings* (`256` strictly disjoint differential pairs, `252` active across 4 disjoint `BCH(63,36,5)` blocks with 20-bit ripple counters), delivering `4 × 36 = 144` bits of independent post-helper min-entropy after disclosing `4 × 27 = 108` syndrome bits and correcting up to `t = 5` flips per block ($\le 10^{-6}$ block failure at 10.24–20.48 µs windows).

== Pad and rapid-path budgets

With eight simultaneously switching 15 pF loads, 33 Ω source resistors, three I/O return pairs, 1.8 nH and 125 mΩ per bond, and 1.8 nF die decoupling, 8 mA slow slew meets the 500 mV bounce budget at eight corners. FF/−40 °C reaches 516.1 mV, compared with 1,021.3 mV for the original 24 mA slow-slew deck. The reference carrier keeps 8 mA drive and uses 0.9 nH each for the south DVDD and DVSS bonds. At 125 mΩ per bond with the same loads, all nine corners pass bounce/droop, rail-differential and quiet-victim checks. Worst south bounce is 453.9 mV at FF/−40 °C. These are package-model results. Verify the effective bond inductance from the assembly extraction.

The 14-tap Vernier step spans 72.77–184.37 ps. Pad-to-pad turnaround meets 5 ns at eight corners. SS/125 °C takes 6.159 ns. These values exclude reader and air-path delay.

== Reference RF circuit · 13.56 MHz

#image("reference-rf.svg",width:100%)
With 7.5 V peak series excitation and cold VDD held at 0 V, all nine corners meet the 1 µA average and 100 µA peak injection screens. The protected branch gives 5.8–46.7 nA average and at most 39.28 µA peak. RECT supplies the shunt and gate clamp. The drain pull-up runs from chip 5 V. With the chip unpowered, the two rails stay isolated.

#pagebreak()
= Reference carrier and population schedule

#image("reference-carrier.svg",width:100%)
#v(-2pt)
Four layers, 1.6 mm FR-4. L1 carries the four-turn 40 × 40 mm square spiral. Use 0.42 mm tracks, 0.56 mm gaps and 35 µm copper. Keep a 46 × 46 mm window free of copper on L2–L4 except the short insulated inner-turn crossover. Outside the coil, L2 is ground, L3 power and L4 signals/ground. Route the supply fingers close to south die pads 3 (DVSS) and 4 (DVDD). Budget 0.9 nH and 125 mΩ per south bond. The modeled remaining bonds are 1.8 nH each. Provide short supply-pair return paths and one ground via at each bypass.

== Assembly schedule
#dtable((1.0fr, 1.36fr, 2.95fr), size: 7.15pt, inset: 3.5pt,
  table.header(..th([Ref.], [Fit], [Connections and placement])),
  [U1 / U2 / U3], [ASS2-0P5 / TPS3839K50 / FM25W256-G], [Schmitt reset. Supervisor trips at 4.38 V, releases after 200 ms nominal. Strap FRAM WP_N and HOLD_N high. POR and FRAM limit the populated board to +85 °C.],
  [U4 / U5], [U4 DNP / host translator as fitted], [U1 provides Schmitt reset. Use Ioff-rated 3.3 ↔ 5 V translation on 3.3 V hosts, with separate TX/RX directions for ×1 and turnaround control for wide DQ.],
  [Q1 / Q2], [FDV301N / FDV301N DNP], [Carrier isolation. Reserve Q2 and detector/comparator for ASK, pulled up only from chip 5 V. Leave ASK disconnected for first carrier test.],
  [D1–D4 / DZ1], [4 × BAS70 / BZT52C4V7], [Schottky rectifier and negative clamp, upper/lower gate clamps. 4.7 V shunt cathode at RECT.],
  [L1 / CT1–3], [Printed spiral / 68 pF + 12 pF + 3–15 pF], [C0G 1% and RF trimmer, all ≥100 V. L = 1.466 µH, Rac = 0.988 Ω at 25 °C. Target total 93.95 pF including parasitics.],
  [RD, RB / RR / RG], [4.7 Ω, 12 kΩ / 150 Ω / 2.2 kΩ], [Series damping and tank bleed. Rectifier resistor ≥0.5 W. Gate series resistor ≥0.25 W.],
  [RP, RGS / CR, RRECT], [470 Ω, 1 MΩ / 4.7 nF, 10 kΩ], [Drain pull-up, gate pull-down, rectified-rail storage and bleed.],
  [CP1–4, CB, CA1–2], [4 × 100 nF, 4.7 µF, 2 × 100 nF], [X7R ≥10 V. Local bypass for each supply pair, bulk at the power entry, one bypass each at U2 and U3.],
  [RT, CT, RS / reset], [10 kΩ, 10 nF, 1 kΩ / 100 Ω, 100 kΩ], [Normally open grounded tamper contact. 100 µs charging time. Reset series resistor and chip-side pull-down.],
  [Bus resistors / straps], [8 × 33 Ω DQ, 33 Ω SCK, 10 kΩ select and strap pulls], [Fit source damping at the driver. Pull up host and FRAM selects. Expose BOOT_MODE and clock select. Pull BOOT_MODE low for mission. Select external CLK_IN on the carrier.],
  [Headers, probes, clock], [Power jumper, keyed 2×5 SPI, expansion, anchor header, two SMA], [Route rapid challenge/response on short coax. Provide a 5 V-level bench clock. Expansion carries DQ2–7, RDY, IRQ and debug.],
)

== Connector and strap wiring

#dtable((.9fr, 3.8fr),size: 7.4pt, inset: 2.8pt,
  table.header(..th([Carrier connection], [Net assignment])),
  [J1 / JP1], [Bench 5 V and GND. JP1 joins the input to V5_CHIP for current measurement. Tie supply returns to the L2 plane outside the coil keepout.],
  [J2 keyed 2×5], [1 SCK, 2 GND, 3 DQ0, 4 GND, 5 DQ1, 6 GND, 7 CS_N, 8 reset monitor, 9 V5_CHIP sense, 10 GND. Chip-side levels are 5 V. U4 and U5 are DNP for a 5 V host.],
  [Expansion and test], [Expose DQ2–7, RDY, IRQ, UART TX/RX, GPIO, verdict, JTAG and NFC signals at labeled pads. FRAM test points connect to U3 CS, SCK, SI and SO.],
  [CLK / mode / rapid], [External clock header to pad 1 and GND. Jumper CLK_EXT_EN to V5_CHIP. Strap pads 52 and 55 individually to 5 V or GND. Challenge SMA to pad 47, response SMA to pad 48, both shields to GND.],
)
== First power and carrier test

Power from a current-limited 5.0 V supply. Probe both sides of JP1, ground at each supply pair, RST_N, tamper and CLK_MON (CLK_IN / 16). Begin SPI at 1 MHz. Observe SCK, CS_N, MOSI, MISO, RDY and IRQ. Check the raw diagnostic sentinels before issuing IDENT. Break out FRAM_CS_N and the private bus separately.

Tune the populated tank with a weakly coupled VNA loop. Probe TANK, RECT, Q1 drain and the ASK test point with low-capacitance probes. With chip 5 V disconnected, monitor the rail, injection current, reset and isolated clock before connecting a reader.
