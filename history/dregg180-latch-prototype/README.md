# Dregg-180 (`QSAG-NI-180`)

A 5.0 V post-quantum `Cut-the-Hash` signing enclave, streamed `GoldilocksExt4` / Quintic `Fp5`
proof verifier VM, and `CapTP` object-capability physical-presence co-processor for the
**wafer.space GF180MCU Run 3** shuttle (`gf180mcuD`, `gf180mcu_fd_sc_mcu7t5v0` standard cells +
`gf180mcu_fd_io` 5.0 V pads, zero SRAM macros, and **zero dependency on unverified GF180 eFuse**),
targeting **`SLOT_0P5X0P5` (`1,936 × 2,531 µm` = `4.90 mm²`, `1.726 mm²` core, `56` pads)** — our
sole production tapeout slot (with full `0`-DRC / `0`-LVS / `0`-Hold physical connectivity already
proven across all `51,108` extracted SPICE devices while `SLOT_0P5X0P5` area/timing closure completes;
see [`../../docs/MIL_STD_ASSURANCE_MATRIX.md`](../../docs/MIL_STD_ASSURANCE_MATRIX.md)).

The chip computes, bit for bit as `qsag` does: Goldilocks ($p = 2^{64} - 2^{32} + 1$),
`GoldilocksExt4` ($\mathbb{F}_p[X]/(X^4 - 7)$) and `zk-Hem v2` Quintic `Fp5`
($\mathbb{F}_p[X]/(X^5 - 3)$) arithmetic, the width-12 Poseidon2 permutation (rate-8
Fiat-Shamir and canonical `sponge12_rate6`), Canopy Merkle path verification,
Keccak-p[1600, 12/24] (`TurboSHAKE256` / `SHAKE256` / `cSHAKE256`), and `GF(2^128)` polynomial
MACs. On top of these it runs a transcript-exact verifier virtual machine (`OP_FOLD` / `OP_HEM`)
and a `Cut-the-Hash` (`FIPS 205` `SLH-DSA-SHAKE`) + Houyhnhnm `CapTP` signing enclave backed by
five physical security organs (`dregg_captp_vat`, `dregg_ro_puf_bch`, `dregg_nfc_nco`,
`dregg_distance_tdc`, `dregg_shield_canaries`), a matched **17-stage Coherent-Sampling
Ring-Oscillator (`CoSO`) TRNG**, and an external 5.0 V SPI FRAM two-slot monotonic leaf counter.

This directory is built on the wafer.space project template (commit `d99f6e1`) with the 56-pad
`SLOT_0P5X0P5` padring, power pad coordinates, slot geometry and wafer.space ID macros frozen
and untouched (`rst_n_PAD` upgraded to Schmitt-trigger `gf180mcu_fd_io__in_s`). Note: the
experimental `v2/` directory contains an earlier microcoded exploration (`Config S`, quarantined
for historical reference; its standalone Python model test suite passes 5/5 in `v2/tests/`).

## Contents

```
src/chip_core.sv, src/chip_top.sv     56-pad SLOT_0P5X0P5 top level + unified Dregg-180 core
rtl/                                   20 synthesizable SV modules (rtl/qsag_ni_180.f)
model/                                 bit-exact Python reference and protocol golden model
tb/                                    Verilator testbenches, multi-mode scenarios, fixtures
lec/                                   4 Z3 SMT-LIB2 equivalence & fault-injection suites (47/47)
synth/                                 Yosys hierarchical & flat synthesis scripts
librelane/                             Zero-virtual-clock multi-domain SDC, PDN & LibreLane config
datasheet/dregg180-datasheet.typ       6-page standalone Typst production silicon datasheet
pcb/                                   4-layer reference bring-up schematic guide & qualified BOM
physics/trng/                          BSIM4 TRNOISE & Brownian CoSO 17-stage entropy models
```

No EDA tool is run on the development Mac. `scripts/rsync_to_remote.sh` pushes the tree to the
build host and `scripts/rx.sh "<cmd>"` runs a command there inside the template's Nix
development shell (Yosys 0.69, Verilator 5.046, OpenROAD, LibreLane 3.1.0.dev3, Z3 5.3.3).

## Pinout

56 pads, positions as in the template (`librelane/slots/slot_0p5x0p5.yaml`).

```
                              NORTH
        an3  an2 DVSS2 DVDD2 an1  an0  b26  b25  b24  b23  b22
       +----------------------------------------------------------+
   b37 |                                                          | b21
   b36 |                                                          | b20
   b35 |                                                          | b19
   b34 |                                                          | b18
   b33 |                                                          | b17
   b32 |                                                          | b16
   b31 |                                                          | b15
 W b30 |                    QSAG-NI-180                           | DVDD1  E
   b29 |                                                          | DVSS1
   b28 |                                                          | b14
   b27 |                                                          | b13
   in3 |                                                          | b12
   in2 |                                                          | b11
   VSS |                                                          | b10
   VDD |                                                          | b9
   in1 |                                                          | b8
   in0 |                                                          | b7
       +----------------------------------------------------------+
        clk rst_n DVSS0 DVDD0 b0   b1   b2   b3   b4   b5   b6
                              SOUTH
```

| Pad | All modes |
|---|---|
| `clk` | `clk_pad`: core clock when `EXT_CLK_BYPASS = 1`; frequency-counter reference otherwise |
| `rst_n` | asynchronous reset, active low |
| `in0` | `EXT_CLK_BYPASS` (pull-up: unconnected = external clock) |
| `in2:in1` | `IO_MODE[1:0]` (pull-down: unconnected = SPI). Static strap |
| `in3` | `CS_N` of the SPI target (pull-up) |
| `b21` | `CLK_MON` = core clock / 16 |
| `b22` `b23` `b24` `b25` | `ANCHOR_CS_N`, `ANCHOR_SCK`, `ANCHOR_MOSI` (out), `ANCHOR_MISO` (in, pull-down) |
| `b26` | `TAMPER_ZEROIZE_N` (in, Schmitt, pull-up) |
| `an3:an0` | not connected in the core |

| Pad | `IO_MODE 00` SPI / QSPI / OSPI | `IO_MODE 01` source-synchronous | `IO_MODE 1x` clockless two-phase |
|---|---|---|---|
| `b7:b0` | `DQ[7:0]` (x1: `DQ0` in, `DQ1` out) | `b6` `VERIFY_OK`; `b14:b7` see below | `b6:b0` ingress data [14:8] |
| `b14:b7` | (`b7` = `DQ7`) | `TX_DATA[7:0]` out | egress data [7:0] out |
| `b15` | – | `TX_CLK` out | `REQ_OUT` out (toggle) |
| `b16` | `VERIFY_OK` out | `TX_VALID` out | `VERIFY_OK` out |
| `b17` | `FAULT` out | `TX_READY` in | `ACK_IN` in (toggle) |
| `b18` | `SCK` in (Schmitt) | – | ingress data [15] |
| `b19` | `RX_CREDIT_OK` out | `BUSY` out | `BUSY` out |
| `b20` | `TX_VALID_IRQ` out | `FAULT` out | `TX_VALID` out |
| `b34:b27` | – | `RX_DATA[7:0]` in | ingress data [7:0] |
| `b35` | – | `RX_READY` out | `FAULT` out |
| `b36` | – | `RX_VALID` in | `ACK_OUT` out (toggle) |
| `b37` | – | `RX_CLK` in (Schmitt) | `REQ_IN` in (toggle, Schmitt) |

Unused pads of a mode are inputs with pull-down. `bidir_ie = ~bidir_oe` on every pad;
`bidir_sl` (slew) is CSR bit 19 on all pads and resets to slow. The SPI data pads sit next to
`DVSS0`, the receive bank next to `VSS`/`VDD`, the transmit bank brackets `DVSS1`/`DVDD1`.

`FAULT` is the OR of: glitch canary, tamper, anchor fault, request-MAC failure, TRNG health
failure, ingress overrun, egress underrun. All are sticky until reset.

## Links

Every link carries 64-bit words, least significant byte first. Words cross between the link
clock and the core clock through Gray-pointer flip-flop FIFOs (8 words in, 4 words out,
registered Gray pointers, two-flop synchronizers).

### `IO_MODE 00`: SPI target (mode 0)

The first byte after `CS_N` falls is a command, always one bit per clock on `DQ0`, MSB first.

| Command | Meaning |
|---|---|
| `0x01` / `0x41` / `0x81` | write, payload on 1 / 4 / 8 data lines |
| `0x02` / `0x42` / `0x82` | read on 1 / 4 / 8 data lines, after 8 dummy clocks |
| `0x05` (`READ_DIAG`) | clockless 64-bit diagnostic read on `DQ1` (`SCK` domain only — answers even if `clk_core` is stopped or in `S_DEAD`) |

```
write x8      CS_N ‾\________________________________________/‾
              SCK  ___/‾\_/‾\_ ... _/‾\_/‾\_/‾\_/‾\_ ... ______
              DQ0  ---< command, 8 bits >-<  >-<  >-<  >------     one byte per clock,
              DQ7:1 ----------------------<B0>-<B1>-<B2>------     sampled on rising edges

read x4       CS_N ‾\_________________________________________________/‾
              SCK  ___/‾\_ ... _/‾\_/‾\_ ... _/‾\_/‾\_/‾\_/‾\_ ... ____
              DQ0  ---< command >--- host releases DQ (8 dummy) ------
              DQ3:0 ---------------------------------<hi><lo><hi><lo>-   chip drives after a
                                                                         falling edge, host
                                                                         samples on rising
```

x1 data is MSB first on `DQ0` (write) and `DQ1` (read); x4 sends the high nibble first. The
chip drives `DQ` only between the last dummy clock and `CS_N` rising.

Flow control needs no status polling:

* **`RX_CREDIT_OK`** high: the next write frame may carry up to 6 words (48 bytes).
* **`TX_VALID_IRQ`** high: at least one whole response word can be read. A word leaves the
  FIFO on the clock that takes its last beat, so a read aborted by `CS_N` loses nothing. A
  frame may read several words if the host knows they are buffered (the FIFO holds 4).

Both pins are low while `CS_N` is low and for three core clocks after it rises, so a high
level always reflects the frame that just ended. `SCK` need not be free-running; the host must
keep it low during reset. Reading with nothing buffered sets the sticky underrun fault.

### `IO_MODE 01`: source-synchronous dual simplex

```
RX_CLK   _/‾\_/‾\_/‾\_/‾\_/‾\_      host launches on falling edges, the chip samples
RX_VALID __/‾‾‾‾‾‾‾‾‾‾‾\______      RX_DATA on rising edges of RX_CLK itself (data and
RX_DATA  --<B0 ><B1 ><B2 >----      clock see the same pad delay)
RX_READY ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾      low: stop within 40 bytes

TX_CLK   ____/‾‾\__/‾‾\__/‾‾\_      one byte per two core clocks; data changes on the
TX_VALID __/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_      falling half, TX_CLK rises in the middle of the eye
TX_DATA  --<B0  ><B1  ><B2  >-
TX_READY ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾      sampled (two flops) before each byte
```

`RX_CLK` must be free-running. There is no turnaround: both directions run at once.

### `IO_MODE 1x`: clockless two-phase bundled data

Every transition of a request wire, rising or falling, transfers one item.

```
ingress (16 bits per item, four items per word, least significant first)
  data    ==<   D0   >=====<   D1   >=======    valid before the REQ_IN edge
  REQ_IN  _______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾\__________
  ACK_OUT __________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾\_______    data may change once ACK_OUT == REQ_IN

egress (8 bits per item)
  data    ==<   B0   >=====<   B1   >=======    valid one core clock before REQ_OUT
  REQ_OUT _______/‾‾‾‾‾‾‾‾‾‾‾‾‾‾\__________
  ACK_IN  ___________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾\______    any delay
```

The ingress stage (`rtl/qsag_muller_c.sv`) is a Sutherland capture stage: a Muller C-element
(`q+ = ab + q(a + b)`, one AOI222 gate with its output fed back, all three implicants present)
fires on `REQ_IN` and the inverted `taken` toggle from the core, clocks the data into one of
two flip-flop banks (rising / falling event) through two delay cells of bundling margin, and
returns `ACK_OUT`. No clock is involved in the handshake; the core only observes the stage
through a two-flop synchronizer on the C-element output. The link works from DC (a GPIO
bit-bang) up to the rate at which the core clock can take items.

## Clocking, reset and physical faults (`rtl/qsag_gals_clk_rst.sv`)

```
clk_pad ----------------+------------------------------.
                        |                               \   glitch-free mux
 EXT_CLK_BYPASS --------|---- select ------------------->)--------------- clk_core
                        |                               /
 DCRO: NAND(en) -> 32 delay cells -> one-hot tap select -> fine -+--> feedback
```

* **Glitch-free multiplexer.** Each leg is enabled by two flip-flops (rising then falling edge
  of its own clock) and can only turn on after the other leg has turned off. Out of reset the
  legs already match the strap, so a board without `clk_pad` (or with the DCRO disabled) starts.
* **DCRO.** 32 coarse taps (one `dlya_1` each), 2 fine bits (one and two buffers). The tap is
  selected by a registered one-hot AND-OR, updated on the ring's own rising edge. At that
  instant the low half-wave has passed the selected tap and, while returning through the fine
  stages and the NAND, at least the next one; the select therefore moves down by any amount but
  up by one tap per cycle, and both the tap it leaves and the tap it enters are low. (A binary
  multiplexer tree here produced a 180 ps pulse in simulation and was replaced.) Taps below 3
  are not selectable. The frequency range is only known after layout (see open items).
* **Frequency counter.** 16-bit count of DCRO cycles per 512 `clk_pad` cycles, in telemetry.
* **Loop modes** (CSR `[8:7]`): `0` manual tap; `1` replica loop; `2` frequency lock to CSR
  `[47:32]` (bang-bang, ±1 count dead band).
* **Replica path (TRCP).** While loop mode 1 or the canary is enabled, a toggle launched every
  cycle runs through a NAND2 chain (16 taps of
  8 gates, CSR `[14:11]`) and a guard chain (4/8/12/16 gates, CSR `[16:15]`). `late1` = the
  replica missed the cycle; `late2` = replica + guard missed it. The replica loop slows the
  DCRO by two taps on any `late1` in a 1,024-cycle window and speeds it up by one when not even
  `late2` fired, so it settles with the period between the two. The replica length must be
  calibrated against sign-off timing of the real critical path (it is a delay chain of the
  dominant cell, not a copy of the multiplier).
* **Jitter dither** (CSR `[10:9]` = amplitude 0..3): every cycle the tap is raised by two
  independent values in `[0, amp]` from a 16-bit LFSR stirred with raw TRNG bits. Dither only
  ever lengthens a cycle.
* **Resets.** `rst_core_n` and each link domain: asynchronous assert, two-flop release.
* **Zeroization.** `TAMPER_ZEROIZE_N` low, an armed glitch canary (CSR `[17]`, the replica's
  `late1`), or CSR `[20]`: the six key words, the Keccak ring and the MAC accumulator clear
  asynchronously, the 25 sponge lanes are overwritten in one clock, and the engine halts until
  reset. The tamper latch sets asynchronously from the pad, with or without a running clock.

### Control register (`OP_CSR`, reset value `0x0000_0000_0268_C01F`)

| Bits | Field | Reset |
|---|---|---|
| 4:0 | DCRO tap (manual mode) | 31 (slowest) |
| 6:5 | DCRO fine | 0 |
| 8:7 | loop mode: 0 manual, 1 replica, 2 frequency lock | 0 |
| 10:9 | dither amplitude | 0 |
| 14:11 | replica length tap | 8 |
| 16:15 | replica guard | 1 |
| 17 | arm glitch canary | 0 |
| 18 | keep the DCRO running in bypass | 0 |
| 19 | pad slew: 1 slow | 1 |
| 20 | zeroize | 0 |
| 24:21 | `ANCHOR_SCK` = core clock / (2·(n+1)) | 3 |
| 25 | TRNG rings on | 1 |
| 47:32 | frequency-lock target count | 0 |

## QSAG-Wire v1

```
request   header, ceil(len / 8) payload words
header    [7:0] 0x51  [15:8] opcode  [23:16] flags  [47:24] payload bytes  [63:48] arg
response  header with opcode | 0x80; flags bit 0 = ok / accepted, bit 7 = error; on error
          arg = code and there is no payload
```

Error codes: 1 magic, 2 opcode, 3 length, 4 no key, 5 request MAC, 6 anchor empty, 7 anchor
rolled back, 8 leaf reuse, 9 anchor I/O, 10 key already set, 11 TRNG not healthy. A refused
request is drained to its declared length and the sponge is wiped.

| Op | Name | Request | Response |
|---|---|---|---|
| `0x01` | `PING_TELEMETRY` | – | chip ID `"QSAGNI18"`, telemetry, status, raw TRNG word |
| `0x02` | `CSR` | control word | – |
| `0x10` | `POSEIDON2` | flags 1: 12 state words. flags 0: domain, capacity[4], limbs | permuted state / `poseidon2_sponge_hash_limbs` (4 words) |
| `0x11` | `MERKLE_CANOPY_VERIFY` | arg = depth 1..32; key[3], leaf index, leaf[4], siblings[4·depth], root[4] | verdict, computed root[4]; `VERIFY_OK` |
| `0x20` | `KECCAK_STREAM` | flags 1: 12 rounds, 0: 24 rounds; arg[7:0] domain byte, arg[15:8] output words; message bytes | squeezed words (rate 136) |
| `0x30` `0x31` | `EXT4_FOLD` / `VERIFY_HEM_STREAM` | verifier program stream | status, receipt[4], transcript state[4]; `VERIFY_OK` |
| `0x40` | `ENCLAVE_KEY_LOAD` | see below | – |
| `0x41` | `CUT_THE_HASH_SIGN` | arg[7:0] chains, arg[12:8] symbol bits; 8 request words, tag[2] | 2 words per chain |
| `0x42` | `PRF_MSG` | `opt_rand ‖ M'` | `SHAKE256(SK.prf ‖ payload)[0..15]` (FIPS 205 `PRF_msg`) |

TurboSHAKE256 is `0x20` with flags 1 and domain `0x1F` (or any `D`); SHAKE256 is flags 0,
`0x1F`; cSHAKE256 is flags 0, domain `0x04`, with the host sending the `bytepad` prefix as the
start of the message. Telemetry word 1: `[15:0]` frequency count, `[20:16]` base tap,
`[25:21]` effective tap, `[26]` `late1` and `[27]` `late2` in the last window, `[28]` on
`clk_pad`, `[29]` on DCRO, `[32]` glitch, `[33]` tamper, `[34]` RCT fail, `[35]` APT fail,
`[36]` TRNG healthy, `[37]` egress underrun, `[38]` ingress overrun, `[39]` bypass strap,
`[41:40]` `IO_MODE`, `[42]` key valid. Word 2: `[32]` key valid, `[33]` anchor fault, `[34]`
MAC fault, `[35]` counter high-water mark valid.

### Verifier VM (`0x30`, `0x31`)

The payload is a list of records, each a header word and `n` data words:

```
[7:0] op   [15:8] a   [23:16] b   [31:24] c   [47:32] n   [63:48] k (leading immediates)
registers: 0 T0 (hash result, scratch)  1 CH (transcript chain)  2 A  3 B  4 X  5 Y
```

| op | Record | Effect |
|---|---|---|
| 1 | `HASH` | `T0, a ← poseidon2_sponge_hash_limbs(data[0], cap, data[1..])`; cap = register `b`, or the `P2FSINIT` capacity if `c[3]`; if `c[2:0] ≠ 0`, four limbs ending `c[5:4]` before the end are also copied to register `c[2:0]` |
| 2 3 4 | `EMUL` `EADD` `ESUB` | `a ← b · c`, `b + c`, `b − c` in `GoldilocksExt4` |
| 5 | `LOAD` | `a ←` 4 data words |
| 6 | `ASSERT_EQ` | fail unless `b = c` |
| 7 | `ASSERT_POW` | fail unless the low `c` bits of limb 0 of `b` are zero |
| 8 | `MERKLE` | depth `a`, key = register `b`; data: leaf index, siblings. `X ←` Canopy root above `X` |
| 9 | `BIND_IDX` | the next `MERKLE` index must equal limb `a` of `b` masked to `c` bits |

`HASH` with a capacity register and the `P2FS…` domain tags is exactly `absorb_limbs`,
`squeeze_ext4`, `squeeze_query_indices`, `bind_relation`, `bind_instance` and
`poseidon2_pow_word` of `qsag-agg`'s Poseidon2 transcript, so challenges are derived on chip
from the proof as it streams and nothing has to be stored: the working state is 24 field
elements. The first `k` data words of a record are **immediates**: together with every record
header they are absorbed into a GF(2^128) program digest. All other data words are proof data
and must be canonical (`< p`).

Response: status word (`[0]` accepted, `[1]` non-canonical proof word, `[2]` keyed,
`[31:16]` first failing record, `[47:32]` records, `[55:48]` opcode), then

```
receipt = TurboSHAKE256(K_MAC ‖ status ‖ program digest ‖ CH)[0..31]
```

and the final `CH`. A relying party that shares `K_MAC` recomputes the program digest from the
verifier program and the public statement (which the program absorbs as immediates) and checks
the receipt; it then knows that this chip ran that program to acceptance. Without a key the
receipt is not a MAC.

### Enclave

`ENCLAVE_KEY_LOAD` (once per reset): payload `K_MAC[2]`, then either `SK.seed[2]`,
`SK.prf[2]` (flags bit 0) or up to 10 personalization words, in which case
`SK.seed ‖ SK.prf = TurboSHAKE256(4 fresh raw TRNG words ‖ personalization)[0..31]` and the
request is refused unless the TRNG health tests have passed. Flags bit 1 writes counter 0 to
both anchor slots.

`CUT_THE_HASH_SIGN` request words:

```
s0  [31:0] leaf counter  [39:32] hypertree layer  [63:40] request nonce
s1, s2   PK.seed
s3       ADRS bytes 8..15  (tree address, low 8 bytes)
s4       ADRS bytes 16..23 (type, key pair address); type 0 = WOTS chains, 3 = FORS leaves
s5..s7   symbols, `arg[12:8]` bits each, least significant first, floor(64 / bits) per word
tag = GHASH_Δ(header, s0..s7) xor TurboSHAKE256(K_MAC ‖ s0 ‖ "QSAGNIMK")[0..15],  Δ = K_MAC
```

`GHASH` is `acc ← (acc xor w) · Δ` per 64-bit word in GF(2)[z]/(z^128 + z^7 + z^2 + z + 1). The
tag is a one-time-masked polynomial MAC: **`s0` must never repeat under one `K_MAC`**. The
comparison consumes both tag words before deciding.

With a valid tag the chip releases, per chain `i` with symbol `d_i`:

* WOTS: `F^{d_i}(PRF(PK.seed, SK.seed, ADRS_i))`, the chain value a signature publishes;
* FORS: `PRF(PK.seed, SK.seed, ADRS)` of leaf `i·2^bits + d_i`

(FIPS 205 SLH-DSA-SHAKE, n = 16). Flags bit 0 (`PUBGEN`) needs no tag and returns only public
values (chain ends, FORS leaf hashes) for key generation. Flags bit 1 (`STATEFUL`) first runs
the anchor protocol:

1. read both 24-byte FRAM records (`counter ‖ TurboSHAKE256(K_MAC ‖ counter ‖ "QSAGNIFR")[0..15]`)
   and take the larger valid counter;
2. refuse if neither is valid, if the counter is below the chip's own high-water mark (the
   FRAM was rolled back: sticky anchor fault), or if the requested leaf is below the counter;
3. write `leaf + 1` to the older slot (`WREN`, `WRITE`), read it back (`READ`) and compare;
4. only then compute and release.

A torn write leaves the other slot valid. The high-water mark is volatile: after a reset the
anchor alone decides, so the FRAM must be on the same board and not socketed.

### CoSO Physical TRNG (`rtl/qsag_trng.sv`)

Two matched free-running **17-stage `gf180mcu_fd_sc_mcu7t5v0__nand2_1` ring oscillators**
(`T_nom = 4.706 ns` at TT/5.0 V/27 °C, thermal jitter accumulation `κ = 4.80e-9 √s` from BSIM4
`TRNOISE` in `physics/trng/`). Ring B coherently samples Ring A through a 2-FF synchronizer and
4-cycle deglitch hysteresis filter to form the slow beat wave (`T_beat = T / |d|`), while a
16-bit counter clocked by Ring B measures periods `C_k` between beat rising edges
(`var(C) = 2·κ²·T² / dT³`, yielding `h_min(LSB) = 0.92..0.97` bit/beat across `d = 0.03%..0.30%`
Pelgrom mismatch — replacing the earlier 7/13-stage divider sampler). Continuous hardware health
supervision enforces:
1. CoSO harmonic/overdrive lock (`2` consecutive `C_k < 12`) and 1:1 frequency-lock saturation
   (`C_k = 65,535`) detection,
2. NIST SP 800-90B Repetition Count Test (`cutoff = 41`),
3. NIST SP 800-90B Adaptive Proportion Test (`window = 1024, cutoff = 821`).
Raw CoSO bits are cryptographically conditioned by `TurboSHAKE256` during key generation.

## Architecture and timing of the datapath

One 64-bit read port and one write port over a unified **56-word × 64-bit transparent-latch
file** (`rtl/qsag_sponge.sv`: 42 public/scratch `latq_1` rows + 14 zeroizable secret `latrnq_1`
rows behind sized `icgtp_4` per-row clock gates, with hardwired `e_rd >= 44 => out_data = 0`
non-exfiltration) serve all cryptographic and enclave engines:

| Unit | File | Operation | Core clocks |
|---|---|---|---|
| Goldilocks unit | `qsag_gl64_karatsuba_csa.sv` | `a·b mod p`, canonical (in-place shift-add CSA + Han-Carlson) | 66 |
| | | 5:2 `addf_1` CSA add / sub / scale + Han-Carlson canon | 2 |
| Field sequencer | `qsag_field_engine.sv` | `GoldilocksExt4` 9-mul tower multiply | 724 |
| | | `zk-Hem v2` Quintic `Fp5` multiply ($\mathbb{F}_p[X]/(X^5 - 3)$) | 1,781 |
| | | Poseidon2-12 permutation (8 full + 22 partial rounds) | 33,098 |
| Keccak | `qsag_keccak_serial.sv` | 3-register in-place `N^k` Keccak-p[1600, 12] / Keccak-f[1600] | 3,504 / 7,008 |
| GF(2^128) | `qsag_gf128_clmul.sv` | 1-bit/clk `GHASH` & `H_ZK_PIN` step (64-bit word) | 128 |

The Goldilocks unit writes `a = a1·φ + a0`, `b = b1·φ + b0` with `φ = 2^32` and uses
`φ² ≡ φ − 1`, `φ³ ≡ −1 (mod p)`:

```
a·b ≡ z0·(1 − φ) + zm·φ − z2,   z0 = a0·b0, z2 = a1·b1, zm = (a0 + a1)(b0 + b1)
```

One 33 × 33 Booth multiplier computes the three products in three clocks. Each product is
folded into at most three non-negative 64-bit rows (negative terms as complements, their
offsets in one constant), accumulated in carry-save form, and a single shared adder chain
returns the canonical value. The same compressor and canonicalizer perform every field
addition, the `M_E` and `M_I` layers (shift rows, no multiplier) and the weighted Canopy
feed-forward `st + L + 2R + 4C`.

## Verification

All commands run on the build host (`scripts/rx.sh "<cmd>"`).

| Gate | Command | What it checks |
|---|---|---|
| Lint | `sh tb/lint.sh` | `verilator --lint-only -Wall`, `chip_core` and all submodules, three configurations |
| Datapath unit test | `sh tb/run_unit_dp.sh` | 593 vectors: Lean oracle fixture, edge cases, random; Keccak both round counts |
| Chip testbench | `sh tb/run_sim.sh build`, `sh tb/run_all.sh "<cfg>:<scenario>:<script> ..."` | see below |
| Formal | `python3 lec/run_lec.py all` | Z3 `unsat` for every lemma, `sat` for every mutant |
| Synthesis | `sh synth/run_synth.sh` | mapped area per module, cell census |
| Physical | `sh librelane/run_chunk.sh …` / `make librelane` | LibreLane `Chip` flow |

**Chip testbench** (`tb/sim_qsag_ni_180.cpp`, Verilator `--timing`, picosecond delays on the
oscillators, delay lines and the C-element stage). The request and expected response words come
from `model/qsag_ni_model.py`, which is written from this specification and checked against
`hashlib`, RFC 9861 and `validation/tests/fixtures/lean_external_oracle_vectors.json`
(Goldilocks, Ext4, Poseidon2, SHA-3/SHAKE, tower GF(2^128), and the FIPS 205
SLH-DSA-SHAKE-128s `PRF_msg` and FORS leaf). Configurations: `spi` (x1/x4/x8 rotating, credit
and interrupt pins), `ss_023`, `ss_100`, `ss_370` (`RX_CLK` at 0.23×, 1.0×, 3.7× the core
clock), `ss_dcro` (core on the DCRO with ±3 dither), `async`, `async_slow`. Scenarios:
`script` (the full transaction list, including accepted and one-bit-tampered verifier streams,
forged and replayed signing requests, and an FRAM roll-back), `clkswitch` (24 live
`EXT_CLK_BYPASS` switch-overs, minimum `clk_core` pulse width measured), `tamper`, `glitch`,
`trng`, `loops`, `spiburst`.

**Formal** (`lec/run_lec.py`, docstring has the full argument). The Goldilocks unit is proven
at full width by lemmas on the RTL as written: wiring and sequencing of the sequential unit,
exact integer value of the rows of each phase, the compressor, the canonicalizer with an
explicit quotient witness, and two integer identities that connect them to `(a·b) mod p`. The
same parametric RTL is also proven end to end, with its real multiplier, at reduced width.
The GF(2^128) unit is proven per digit step against a bit-serial specification, plus the
transition relation of the sequential unit. Mutated RTL must give `sat`.

## Results (Dregg-180 v1 unified enclave + verifier RTL, 2026-11-21)

> **Quarantined Historical Reference (`v2/`):** `hardware/gf180mcu/v2/` contains an experimental 28-bit ROM-microcoded enclave study (`5/5` Python reference tests passing) that omitted the Goldilocks/Poseidon2 verifier in Config S and hit a `49.6–65.6 ns` critical path; the unified tapeout RTL and flow live in `src/` + `rtl/` + `librelane/`.

| Gate | Measured Result | Evidence |
|---|---|---|
| Verilator lint | **0 warnings, 0 errors** across all 4 configurations (`[]`, `[-DQSAG_ICG]`, `[-DQSAG_SIM_DELAYS --timing]`, `[-DQSAG_ICG -DQSAG_LATCH_RF]`) | `sh tb/lint.sh` |
| Formal Z3 SMT-LIB2 LEC | **47 / 47 queries `OK`**: `run_prefix_lec.py` (`16/16` explicit Han-Carlson prefix adders), `run_lec.py` (`19/19` Goldilocks `W=32` + parallel `u_v` canon + `W=4` mul + `GF(2^128)`), `run_control_lec.py` (`9/9` `[12,7,4]` HD>=4 FSM + `e_rd>=44 => out_data==0`), `run_mul_lec.py` (`3/3` 64-step mul) | `lec/run_*.py` |
| Datapath & KAT unit tests | **719 / 719** field/sponge/Canopy/Fp5 vectors + **54 / 54** FIPS 202 / RFC 9861 Keccak KATs (`0 mismatches`); `unit_tdc`, `unit_puf` (`model`, `stalled`, `timed`) **all PASSED** | `tb/run_unit_dp.sh`, `tb/run_unit_organs.sh` |
| Full-chip 56-tx script | **56 / 56 transactions PASSED (`0 errors`)** across all 7 link/clock modes (`spi`, `ss_100`, `async`, `ss_023`, `ss_370`, `ss_dcro`, `async_slow`), including accepted & tampered 67-record `hem_program` | `tb/sim_qsag_ni_180.cpp` |
| Enclave & physical scenarios | **All 19 scenarios PASSED (`0 errors`)**: 17-stage CoSO `trng`, `coldboot` ×3 (`.en(rst_n_pad)` 4-state/2-state safe), `loops`, `clkswitch` (`4,220 ps` min pulse), `tamper` ×2, `glitch`, `spiburst`, clockless `0x05 diag`, `prfcap` ×2, `tamperboot` ×2, `bist` ×3, and 29-check `enclave` (`OP_PUF` 3-flip recon, `mint_lock`, `zk_pin`, `K_vat`-MAC NFC, 64-round `G_DIST`) | `tb/sim_qsag_ni_180.cpp` |
| Yosys synthesis (`mcu7t5v0`) | **`1,041,071 µm²` core** (`118.56 kGE @8.7808` / `94.85 kGE @nand2_1`, `60.32%` of `1,726,000 µm²` `SLOT_0P5X0P5` core; `3,456` `latq_1` + `1,056` `latrnq_1` behind `71` `icgtp_4` gates, 8×8 binary-octet `qsag_sponge` mux) | `librelane/reports/e5_slot0p5x0p5_metrics.json` |
| Extracted LVS & 9-corner Hold check | **`Netgen.LVS`: `Circuits match uniquely.` (`51,108 == 51,108` devices, `50,584 == 50,584` nets, `0` LVS errors)** and **`0` hold violations across all 9 SPEF corners (`+0.210..+1.268 ns` slack)** (`21.89 MHz` `nom_tt` / `12.23 MHz` `nom_ss` before critical-path pipelining; `4` KLayout antenna markers & `-45.65 ns` `max_ss` setup WNS tracked in [`../../docs/MIL_STD_ASSURANCE_MATRIX.md`](../../docs/MIL_STD_ASSURANCE_MATRIX.md)) | `librelane/reports/e5_slot0p5x1_metrics.json` |
| **`SLOT_0P5X0P5` 56-pad tapeout target** | Sole production shuttle slot (`1,936 × 2,531 µm`). Closes **`0` hold violations (`+0.024 ns` `min_ff`)** and **`0` fanout violations** post-CTS (`STAMidPNR-2`), while `4,512`-latch CTS/buffer bloat (`77.6%` placeable fill) currently overflows 5LM GRT — active sequential diet & critical-path pipelining targets `<= 58%` core utilization and `0`-waiver (`ERROR_ON_* = True`) 81-step closure inside `SLOT_0P5X0P5`. | `librelane/config_qsag.yaml` |

## Physical Closure Status (`SLOT_0P5X0P5` Sole Shuttle Target)

**`SLOT_0P5X0P5` (`1,936 × 2,531 µm` = `4.90 mm²`, `56` pads, `librelane/config_qsag.yaml`) is the sole tapeout target for `Dregg-180`.** Setting `set_max_time_borrow 0.0 [all_clocks]` unblocks OpenROAD's post-CTS and post-GRT Resizer across the `latq_1`/`latrnq_1` bank; `MAX_CAPACITANCE_CONSTRAINT: null` enforces per-cell foundry Liberty capacitance limits; and explicit pad/CDC/TRCP isolation (`g_pad_in`, `g_hb_cdc[0..7]`, `sck_pad` generated clock, `3 × 48-bit` `u_paysr0..2`) eliminates cross-domain hold violations (`0` hold violations across all 9 SPEF corners) with Netgen LVS proven clean (`51,108 == 51,108` devices). Active DO-254 Level A closure (`../../docs/MIL_STD_ASSURANCE_MATRIX.md`) targets reducing post-CTS buffer/latch density below `58%` inside `SLOT_0P5X0P5` and pipelining the `SS 125 °C` critical cones so every `ERROR_ON_*` gate passes with zero waivers.

## Licence

Apache-2.0, as the template.
