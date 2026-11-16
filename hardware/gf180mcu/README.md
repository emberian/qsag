# QSAG-NI-180

A `qsag` coprocessor and signing enclave for the **wafer.space GF180MCU Run 3** shuttle
(`gf180mcuD`, `SLOT_0P5X0P5`, 1,936 × 2,531 µm die, 1,052 × 1,647 µm core,
`gf180mcu_fd_sc_mcu7t5v0` cells, no hard macros).

The chip computes, bit for bit as `qsag` does: Goldilocks and `GoldilocksExt4` arithmetic,
the width-12 Poseidon2 permutation, sponge and Canopy node hash, Keccak-f[1600] /
TurboSHAKE256 / SHAKE256, and GF(2^128) polynomial MACs. On top of these it runs a
transcript-exact verifier virtual machine and a Cut-the-Hash signing oracle whose keys never
leave the die and whose stateful signatures are gated on an external FRAM counter.

This directory is the wafer.space project template (commit `d99f6e1`) with `src/chip_core.sv`
replaced; `src/chip_top.sv`, the padring, the slot geometry and the ID macros are untouched.

> **Read [Status and open items](#status-and-open-items) before ordering.** It lists what was
> measured, what differs from the original brief, and what is not yet done.

## Contents

```
src/chip_core.sv, src/chip_top.sv     top level (template padring)
rtl/                                   design (15 files, rtl/qsag_ni_180.f)
model/                                 bit-exact Python reference and protocol golden model
tb/                                    Verilator testbenches, script generator, fixtures
lec/                                   Z3 SMT-LIB2 equivalence proofs and mutation checks
synth/                                 Yosys synthesis scripts and area reports
librelane/                             LibreLane configuration, multi-clock SDC, PDN
scripts/                               remote-execution helpers (REMOTE_SETUP.md), constant generator
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

### TRNG (`rtl/qsag_trng.sv`)

Two free-running NAND rings (7 and 13 stages); the slow ring divided by 64 samples the fast
one. Raw bits pass the SP 800-90B repetition-count (cutoff 41) and adaptive-proportion
(window 1024, cutoff 821) tests for an assumed 0.5 bit per sample; a failure is sticky and
blocks key generation. Raw bits are conditioned only by TurboSHAKE256 in the key load. The
entropy claim has to be established on silicon.

## Architecture and timing of the datapath

One 64-bit read port and one write port over a 33-word register file (25 sponge lanes, 8
shadow words) serve everything:

| Unit | File | Operation | Core clocks |
|---|---|---|---|
| Goldilocks unit | `qsag_gl64_karatsuba_csa.sv` | `a·b mod p`, canonical | 4 |
| | | add / sub / scale rows, canonical | 1 |
| Field sequencer | `qsag_field_engine.sv` | `GoldilocksExt4` multiply | 122 |
| | | Poseidon2-12 permutation | 3,074 |
| Keccak | `qsag_keccak_serial.sv` | Keccak-p[1600, 12] / Keccak-f[1600] | 1,500 / 3,000 |
| GF(2^128) | `qsag_gf128_clmul.sv` | one MAC word | 64 |

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

## Results (final RTL, 2026-11-16)

| Gate | Result | Log |
|---|---|---|
| Lint | 0 warnings, 0 errors in all three configurations | `tb/logs/lint.log` |
| Datapath unit test | 593 / 593, with and without clock-gated registers | – |
| Chip testbench, full script (54 transactions) | pass: `spi`, `ss_100`, `async` | `tb/logs/sim_*_script.log` |
| Chip testbench, short script (38 transactions) | pass: `ss_023`, `ss_370`, `ss_dcro`, `async_slow` | `tb/logs/` |
| Scenarios | pass: `clkswitch` (narrowest `clk_core` pulse 4,220 ps over 24 switch-overs), `tamper` ×2, `glitch`, `trng`, `loops`, `spiburst` | `tb/logs/` |
| Z3 | Goldilocks 12 / 12 at W = 32, 4 / 4 end to end at W = 4 (W = 6 timed out at 75 s); GF(2^128) 5 / 5 | `lec/logs/` |
| Synthesis | 835,495 µm² flat, 48.2 % of the core, 30,069 cells, 5,579 flip-flops | `synth/reports/area.txt` |
| LibreLane | through detailed placement (55.2 % at global placement); CTS and everything after not run | `librelane/reports/ll_summary.txt` |

Cost of typical transactions in core clocks, request to last response word (`ss_100`):
Poseidon2 permutation 3.4 k, Canopy node 3.4 k, TurboSHAKE256 of one block 3.2 k, key load with
anchor initialisation 10 k, stateful signature of two WOTS chains 32 k, six WOTS chains 105 k,
14 FORS public leaves 85 k, the 67-record verifier program 122 k.

## Status and open items

**Do not order this yet.** There is no routed layout and no timing closure.

**Timing.** No valid Fmax exists. Clock-tree synthesis did not finish inside the 600 s limit
this work ran under, so the only timing reports are before buffering or with an unbuffered
clock net, and neither says anything about the logic. What they do show is a worst data path
of 164 stages with AND-OR-invert carry chains: synthesis was area-driven and the three adders
of the canonicalizer and the multiplier's final adder came out as ripple chains. Expect well
under the 50 MHz target until those are synthesized for delay (or written as parallel-prefix
adders) and a post-CTS STA is run.

**Differences from the brief, with the reason**

| Brief | As built | Why |
|---|---|---|
| 50–64 kGE, ≤ 44 % of the core | 95.2 kGE in the brief's unit (76.1 kGE in real `nand2_1`), 48.2 % | the brief's 8.78 µm² per gate is not this library's `nand2_1` (10.976 µm²); the 5,579 flip-flops the feature list requires are 379,464 µm² (43 kGE in its unit) on their own. Next lever: a latch-based register file (about −4 kGE) |
| Keccak one round per clock (12 / 24 clocks) | word-serial, 125 clocks per round | a round-per-clock datapath measured 26 kGE plus a multiplexer on each of 1,600 state flops |
| 2-cycle Karatsuba, 9-multiply Ext4 in ~18 clocks | 4-clock multiply on one 33 × 33 multiplier; Ext4 = 16 products, 122 clocks | one multiplier instead of three or more |
| GF(2^128) at 16 bits per clock | 2 bits per clock (parameter `GF_D`) | area; not on a throughput path |
| 64-byte shadow buffer, one-clock block absorb | the 8-word ingress FIFO is the rate buffer; a block is absorbed word by word | the shadow words hold operands and request parameters |
| Merkle depth 1..62 | 1..32 | the canonical Canopy node tag carries a 32-bit node index |
| 100+ MB/s both ways in mode 01 | receive limited by `RX_CLK` timing; transmit is one byte per two core clocks | the transmit clock is generated from the core clock |
| `VERIFY_HEM_STREAM` verifies a Hem proof | a verifier VM that executes Hem's Poseidon2-regime checks, tested on a reduced Hem-shaped program | compiling the production verifier schedule into a record stream is host software that does not exist yet; byte-hash (cSHAKE / TurboSHAKE Canopy) regimes are not supported |

**Not done**

* No clock tree, routing, DRC, LVS or GDS (`librelane/reports/ll_summary.txt`). `make librelane`
  runs the whole flow where there is no time limit; expect to iterate on CTS with eight clock
  roots and on timing.
* No gate-level simulation of the mapped netlist; the delay-line, oscillator and C-element
  cells are simulated with behavioural delays, not with extracted ones.
* DCRO frequency range, replica calibration and TRNG entropy are design intent until measured.
* No power analysis; no side-channel countermeasure beyond the clock dither (no masking).
* The clockless stage relies on the bundling margin of two delay cells over the pad-to-flop
  data skew; this must be checked in sign-off timing (`areq` paths in the SDC).
* `PRF_MSG` is not gated by a request tag.
* The request tag is this design's own construction, not `qsag`'s BDOZ / BeltLatch format.

## Licence

Apache-2.0, as the template.
