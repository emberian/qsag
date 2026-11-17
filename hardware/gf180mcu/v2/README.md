# Dregg-180 v2: microcoded model (stage 1 of `ARCHITECTURE.md` 9.3)

This directory holds the executable model of the architecture in `../ARCHITECTURE.md`: a microcode
assembler, an interpreter for the sequencer and its decoder rules, models of the register file and the
units, and the microcode for the commands ported so far. There is no RTL here yet. The existing RTL, test
bench and golden model one level up are unchanged and are the reference.

Everything is plain Python 3 with the standard library. Primitives (Keccak, Poseidon2, Goldilocks) are
imported from `../model/qsag_prims.py`.

```
model/isa.py        micro-instruction layout, operation tables, register-file row map
model/uasm.py       assembler and disassembler
model/regfile.py    the register file (storage and class-wise clears)
model/units.py      word unit, Keccak unit, field unit, FRAM master; clock counts
model/framing.py    QSAG-Wire word framing (link-independent)
model/link.py       SPI link (words <-> bytes)
model/machine.py    sequencer, decoder rules, egress, clock accounting
model/chip.py       top level: ROM image + machine + pins
model/romcheck.py   static checks on a ROM image
model/host.py       host-side request builders and a hashlib FIPS 205 reference
ucode/*.uc          microcode sources; ucode/push_manifest.txt: reviewed list of response writers
tests/              unittest suites; tests/report.py prints the measured figures below
```

## Running

```
python3 -B -m unittest discover -s hardware/gf180mcu/v2/tests      # 75 tests, about 2 s
python3 -B hardware/gf180mcu/v2/model/romcheck.py S                 # static ROM checks, also L
python3 -B hardware/gf180mcu/v2/tests/report.py                     # ROM size and clocks per command
```

`tests/test_reference_script.py` runs `../tb/gen_script.py` (the reference generator, unmodified, into a
temporary directory) and replays its directives on the v2 model.

## Result of the stage exit test

The reference script has 54 transactions. In configuration L:

| Class | Count | Meaning |
|---|---:|---|
| Request sent unchanged, response equal word for word | 38 | PING, Poseidon2, Merkle, Keccak, framing errors, key load, PRF_msg |
| Request rebuilt in the v2 `CTH` format, expected response unchanged | 12 | every `CTH` transaction |
| Not implemented in this stage; the model answers `E_OPCODE` | 4 | verifier VM, opcodes 0x30 and 0x31 |

All `PIN`, `FRAMCHK`, `FRAMSAVE` and `FRAMRESTORE` directives are applied, except the four `PIN VERIFY_OK`
lines that follow the verifier-VM transactions. In configuration S the 15 Poseidon2 and Merkle
transactions are also answered with `E_OPCODE` (no field unit); the other 35 pass as above. The quick
script (38 transactions) passes the same way.

So the exit stated in `ARCHITECTURE.md` ("reproduces the 54-transaction script") is met for 50 of 54. The
remaining four belong to stage 7; see deviation 11.

## Deliberate differences from the reference model

Transactions of the reference script whose request or response differs:

| Transaction (script note) | What differs | Why |
|---|---|---|
| Cut-the-Hash without a key: refused | request format | v2 `CTH` layout (below); response `E_NOKEY` unchanged |
| FORS public leaves (PUBGEN) | request format, tag | leaf indices are sent as 16-bit tree indices; PUBGEN now needs the tag; values unchanged |
| FORS secret leaves released under a valid request tag | request format, tag | as above |
| WOTS chain values, stateless, valid tag | request carries a 16-byte message whose first six base-16 digits are the reference digits 0, 1, 15, 7, 3, 2 | the chip derives chain positions; a request cannot name them. Values unchanged |
| same request, forged tag: refused | request format; one tag bit flipped | response `E_MAC`, `FAULT` pin unchanged |
| same tag, one digit changed: refused | request format; one tag bit flipped | the reference alters a digit after tagging; the replay cannot recover the untampered request, so it invalidates the tag. Body tampering is covered by `test_commands.RequestTag` |
| WOTS public chain ends (PUBGEN) | request format, tag | PUBGEN now needs the tag; values unchanged |
| stateful signature at leaf 0; leaf 0 again; leaf 5; leaf 6; leaf 7 after the roll-back | request format, tag | responses, error codes, FRAM records and `FAULT` pin unchanged |
| duet fold step (accept, reject); Hem-shaped verification (accept, reject) | response is `E_OPCODE` | the verifier machine is stage 7, and the reference behaviour (unpinned program latching a root, register CH in the response) is the defect of state report section 2 item 2 |
| PING (twice) | response words 2..4 are status, 0, 0 | the reference does not check them; the raw TRNG word is no longer returned |

Behaviour that differs and that the reference script does not exercise:

- `CTH` in the reference format (length 80) is refused with `E_LEN`.
- `CTH` with PUBGEN and no valid tag is refused with `E_MAC` (state report S1).
- The Winternitz width is not a request field; `lg_w = 4` is fixed (state report S1).
- A STATEFUL request must have key pair address = leaf counter (deviation 10).
- `KEYLOAD` with flag 0 clear (TRNG-derived keys) answers `E_OPCODE`; that path is stage 3.
- `PRF_MSG` requires flags = 0. Bytes past the stated length in the last payload word are ignored.
- Opcodes 0x02 CSR, 0x03 BIST, 0x50 PUF, 0x51 VAT, 0x52 DB_NCO, 0x53 VAT_ZK answer `E_OPCODE`
  (stages 3, 5, 6).
- A decoder-rule violation is a control fault: every latch is cleared and no response is sent.

## `CTH` request, v2

```
header   op 0x41; flags bit 0 PUBGEN, bit 1 STATEFUL; length 88
         arg [7:0] n = chains or leaves, arg [15:8] = first chain (WOTS)
s0       [31:0] leaf counter, [39:32] hypertree layer
s1, s2   PK.seed
s3       ADRS bytes 8..15 (tree address)
s4       ADRS bytes 16..23: type (0 WOTS, 3 FORS) and key pair address
s5..s8   WOTS: s5, s6 = the 16-byte message to sign; FORS: up to 16 tree indices, 16 bits each
tag[2]   TurboSHAKE256(K_host || header || s0..s8, D = 0x21)[0..15]
```

- WOTS: the chip computes the 32 message digits and the 3 checksum digits (FIPS 205, `lg_w = 4`) and
  returns `F^{d_i}(sk_i)` for chains `first .. first + n - 1`, `first + n <= 35`. PUBGEN returns `F^15(sk_i)`.
- FORS: returns `PRF(PK.seed, SK.seed, ADRS(FORS_PRF, index))` per index; PUBGEN returns `F` of it.
- STATEFUL without PUBGEN: both anchor records are read and authenticated, the request is refused if
  the leaf is below the larger counter, `leaf + 1` is written to the other slot and read back, and only then
  is anything computed from `SK.seed`.
- Response: `16 n` bytes.

`model/host.py` builds these requests.

## Micro-instruction format, as implemented

One word is 28 bits in both configurations.

| Bits | Field | Use |
|---|---|---|
| 27:23 | `op` | operation (31 defined) |
| 22:16 | `A` | source row, or function code, condition, constant index, immediate bits 13:7 |
| 15:9 | `B` | destination row, or immediate bits 6:0, or branch target bits 10:4 |
| 8:5 | `fn` | bit 0 `W`: store H to row B; bit 1 `I`: operand is the immediate; bits 3:2: immediate bits 15:14; or branch target bits 3:0 |
| 4 | `ia` | row A is indexed: A + X mod 128 |
| 3 | `ib` | row B is indexed: B + X mod 128 |
| 2 | `xi` | X += 1 after the instruction |
| 1:0 | `seq` | 0 next, 1 return after this instruction |

`H` is the hold register of the register file's write path and the accumulator of the word unit. A data
instruction computes `H' = f(H, operand)` and may store `H'` to one row; one row is read and one written
per clock.

| Group | Operations |
|---|---|
| Word unit, two operands (row or 16-bit immediate) | `LD XOR AND OR ADD SUB CMP`; `ADD`/`SUB` are 32-bit and set the carry; `CMP` ORs "differs" into the sticky flag Z |
| Word unit, wiring only | `UN` with `ID NIB BE32 HSWAP LO32 HI32 SHR1 SHR4 SHR8 SHR16 SHL1 SHL4 SHL8` |
| Sources | `DIN` (next payload word), `LDF` (framer field: header, flags, length, words left, arg, X, status), `LDC` (64-bit constant) |
| Response | `HDR #cap [okz]` (header; length H words, at most `cap`), `PUSH row` or `PUSH H`, `FAIL #code` |
| Keys | `KMOV keyrow > lane`, `KEYWR > keyrow`, `CTL SETKV` |
| Units | `KEC 24|12`, `FLD PERM|RED`, `FADD` (configuration L), `FRAM RSTART|WSTART|RWORD|WWORD|DONE`, `WIPE #classes` |
| Control | `BR [cond] target`, `BXNE #k target` (X != k), `DBNZ 0|1 target`, `CALL`, `SETX`, `SETC`, `CTL` (`CLRZ SETFM SETFA VOK FLUSH DRAIN`), `DISP`, `IDLE` |

Sequencer state: 11-bit micro-PC, two-entry return stack, two 12-bit down counters, 7-bit index register
X, flags Z and carry, session flags `keyed`, `dirty`, header issued, failed, flushed, and the response
word counter. Conditions: Z, carry, H = 0, payload words left, key valid, counter 1 = 0, and their
complements.

Register file, configuration S (64 rows; L adds rows 64..127):

| Rows | Count | Class |
|---|---:|---|
| 0..24 | 25 | lanes |
| 25..31 | 7 | Keccak work rows |
| 32..43 | 12 | scratch |
| 44..53 | 10 | keys: `K_dev` 4 (unused in this stage), `K_host` 2, `SK.seed` 2, `SK.prf` 2 |
| 54..59 | 6 | pins (unused in this stage) |
| 60..61 | 2 | state: anchor high-water mark |
| 62..63 | 2 | out (egress FIFO) |

### Structural rules

Each is a decoder or sequencer check that does not depend on the ROM contents. `machine.py` implements
them; `tests/test_output_bound.py` has a refusing microprogram for each.

1. Key rows are read only by `KMOV` and written only by `KEYWR`. `KEYWR` and `CTL SETKV` decode only
   while the micro-PC is inside the key range (the `KEYLOAD` routine).
2. `KMOV` writes a rate lane (0..16), sets `keyed` and `dirty`, and clears H.
3. While `dirty` (a key was copied into the lanes and no Keccak permutation has run since), a lane is read
   only by an `XOR` that stores back to the same lane, and H is cleared afterwards.
4. While `keyed` (until `IDLE`), lanes 17..24 are never read by the word unit, so a keyed sponge state
   cannot be read out whole and inverted. The Keccak work rows are never read or written by the word unit.
5. The response is written only by `PUSH`. `PUSH` needs the header issued, `dirty` clear, and a source
   that is H or a readable lane, scratch, pin, state or challenge row.
6. Out rows are not addressable. The egress reads only them.
7. `HDR` executes once; its length is at most the cap in the instruction; the egress stops at that
   length and `FLUSH` pads to it. `FAIL` is refused after `HDR`.
8. `DISP` decodes only at address 0. Address 0 is entered only by `IDLE`, `IDLE` decodes only at the last
   address of the epilogue, and the epilogue (flush, wipe all working rows, drain, idle) is entered only
   at its first address.

What these rules do not decide is which hash output a routine emits (for example a chain value after
the right number of steps and not an earlier one). That is a property of the ROM: `ucode/push_manifest.txt`
lists every response-writing instruction with its source row and reason, and `romcheck.py` fails if the
image and the list differ. The tests also check that no response word in the regression equals a key
row, and that every working row is zero after every command.

## ROM size so far

| | Words | Bits (28 per word) | Constants | Dispatch entries | Synthesized area |
|---|---:|---:|---:|---:|---:|
| Configuration S | 418 | 11,704 | 4 x 64 | 5 | 19,072 µm² |
| Configuration L | 575 | 16,100 | 4 x 64 | 7 | 24,981 µm² |

Words per source: `main.uc` 9, `ping.uc` 12, `keccak.uc` 46, `fram.uc` 47, `keyload.uc` 35, `sign.uc` 269,
`field.uc` 157 (L only). Areas are Yosys flat synthesis of the actual image as a case table, with the
constant and dispatch tables, on hbox (job `arch6`, see the lane report); 45.6 µm² per word in S.

## Commands, routines and clocks

Clocks are counted by the interpreter from the dispatch to the idle point, with the link never
stalling. Unit counts are in `model/units.py`: Keccak-f 721, Keccak-p12 373 and the Poseidon2 permutation
3,074 are measured on the existing RTL; a micro-instruction is 1 clock, plus 1 when it reads the row the
previous instruction wrote (the row is transparent in that clock), `KMOV` is 2; field add and reduce
(1 clock) and the FRAM transfers (SCK = clk / 4) are estimates.

| Command | Opcode | Routine (`ucode/`) | Case | Clocks | At 25 MHz |
|---|---|---|---|---:|---:|
| PING | 0x01 | `ping` (`ping.uc`) | | 17 | 0.7 µs |
| KECCAK | 0x20 | `keccak`, `absorb_pad`, `perm_sel` (`keccak.uc`) | TurboSHAKE256, up to 135 bytes, 4 words out | 412–496 | 16–20 µs |
| | | | each further 136-byte block | 452 | 18 µs |
| | | | SHAKE256, up to 135 bytes | 760–844 | 30–34 µs |
| | | | each further block | 800 | 32 µs |
| KEYLOAD | 0x40 | `keyload` (`keyload.uc`), `fram_*` (`fram.uc`) | with anchor initialisation | 4,017 | 0.16 ms |
| PRF_MSG | 0x42 | `prfmsg` (`sign.uc`) | 32-byte payload | 771 | 31 µs |
| CTH | 0x41 | `cth` (`sign.uc`) | fixed part: tag check, shape, header, one chain of 0 steps | 1,239 | 50 µs |
| | | `f_step` | one F call (lane build + Keccak-f) | 755 | 30.2 µs |
| | | `prf_step`, `next_digit` | one chain start (digit + PRF call) | 765 | 30.6 µs |
| | | | WOTS public key, 35 chains (561 Keccak calls) | 422,392 | 16.9 ms |
| | | | WOTS signature, most steps (all message digits 15; 516 calls) | 388,762 | 15.6 ms |
| | | | WOTS signature, digits spread evenly (291 calls) | 219,335 | 8.8 ms |
| | | `fors` | 14 FORS leaves, secret / public | 11,098 / 21,598 | 0.44 / 0.86 ms |
| | | `anchor_read`, `fram_tag`, `fram_write`, `fram_check` | STATEFUL: two record reads, write, read-back | + 4,775 | + 0.19 ms |
| | | | refused for a bad tag | 429 | 17 µs |
| P2 (L) | 0x10 | `p2` (`field.uc`) | raw permutation | 3,151 | 0.13 ms |
| | | | sponge hash, per 8 limbs | about 3,110 | 0.12 ms |
| MERKLE (L) | 0x11 | `merkle` (`field.uc`) | per level | about 3,175 | 0.13 ms |
| error exits | | `main.uc` | bad magic, unknown opcode | 6 | |

Against `ARCHITECTURE.md` 7.4: the spec assumed about 760 clocks per F or PRF call; the model gives 755
and 765. The spec's "one-time signature, up to 600 calls, 0.46 M clocks, 18 ms" compares with 0.39–0.42 M
clocks for a 35-chain WOTS signature or public key here.

## Deviations from ARCHITECTURE.md

Since this list was written the specification was re-targeted at the small slot (its section 11): the
register file is now specified at 72 rows with 20 scratch rows, the totals in item 7 are superseded (S is
822,700 µm²), and four decoder rules were added to its 5.3 after the review in
`scratch/lanes/sonnet-audit-dregg180-v2-stage1.last.md` (FRAM writes bounded, taint on derived secrets,
hardwired ranges, lifecycle-gated dispatch). The model here still has 64 rows and does not implement those
four rules; they are stage 2 work. The "fixed part 1,239" in the table above includes one PRF call; the
fixed part proper is about 474 clocks.

Each of these is now written into `ARCHITECTURE.md` at the section named. Item 9 is the exception: the
specification does not define wire formats, so the layout lives here.

1. **Row map (5.2).** Scratch is 12 rows, not 8, and out is 2 rows, not 6; configuration S stays at 64
   rows. Reason: `CTH` holds five address words and four message words through the anchor protocol, which
   needs two more (12 used). The out rows became a 2-deep egress FIFO because the response header is built
   by the framer and results are pushed one word at a time.
2. **Output bound (5.3).** The length limit is the length declared by the one `HDR` instruction, capped by
   a constant in that instruction, not a per-command ROM constant: `KECCAK` and `CTH` have request-dependent
   lengths. The egress pads a short response to the declared length. Out rows are written by `PUSH`, not
   by a generic move.
3. **Keyed-state rules (5.3).** Rules 2, 3 and 4 above are new. Without them a routine could copy a key
   lane, or the capacity of a keyed sponge, to scratch and from there to the response; the spec's two
   rules (egress wired to out rows, key-write range) did not prevent that.
4. **Instruction format and sequencer (5.5).** 28 bits in L as well as S (7-bit row fields address 128
   rows). There are no loop-sequencing bits and no loop-start registers: loops are `DBNZ` and `BXNE`
   instructions. A 7-bit index register X with post-increment replaces "row + loop counter". Immediates are
   16 bits. 64-bit constants and the opcode dispatch table sit beside the word ROM.
5. **Word unit (5.4, 7.1).** `OR` instead of AND-NOT; the "base-16 digit extract" became the wiring
   functions listed above (nibble swap, byte reversal of halves, half swap, masks, fixed shifts), which the
   ADRS byte order, the sponge suffix position and the Merkle index also need. Measured area of a skeleton
   with exactly these functions: 34,329 µm² (spec: 23,594). Dropping `HI32`, `SHR8`, `SHR16` and `SHL8`
   saves 1,579 µm² and is not worth the extra microcode.
6. **Sequencer area (7.1).** Skeleton of the sequencer as modelled, with the rule comparators: 23,985 µm²
   (spec budget: 20,000).
7. **ROM (5.5, 7.1).** The ported routines are 418 words where the spec's estimates for the same set
   (framing 80, sponge and MAC 90, signer 160, FRAM 80) sum to 410; inside that, the signer is 269 words
   and still lacks `H_msg` and the tagged-root rule, while framing is 21. The S estimate moves from about
   1,420 to about 1,500 words, against 1,536 budgeted. The real image is denser than random content
   (45.6 µm² per word measured), so the ROM budget is restated as 70,000 µm² for 1,536 words (S) and
   93,400 for 2,048 (L); these are extrapolations from a quarter of the ROM.
   Net effect of items 5, 6, 7 on the totals: S 909,374 → 909,070 µm²; L 1,586,188 → 1,572,139 µm².
8. **`PRF_MSG` is not tagged (2).** It releases only the randomiser R, which every signature publishes,
   and tagging an arbitrary-length payload would need a second sponge state or the GF(2^128) fingerprint
   with a secret evaluation point in a key row. Requests that release values derived from `SK.seed` carry
   the tag.
9. **`CTH` wire format.** New layout (above): Keccak tag in place of the GHASH tag (as 5.4 already
   said), a message in place of host-chosen digits (as section 1 already said), FORS tree indices in place
   of symbol and width.
10. **Anchor counter bound to the key pair (1, U2).** A STATEFUL request is refused unless the key pair
    address in ADRS equals the leaf counter in the request. Without this the counter advanced on one
    number while the signer used another. All reference transactions already satisfied it.
11. **Stage 1 exit (9.3).** 50 of 54 reference transactions; the four verifier-VM transactions move to
    stage 7. The Poseidon2 and Merkle commands (configuration L) were done in stage 1 since the script
    needs them.
12. **Signer scope (9.3).** Not done in stage 1 and now listed under stage 5: FORS indices derived on chip
    from `H_msg`, and the rule that a WOTS key above the bottom layer signs only a root the chip computed
    or tagged (7.4). Until then the signer serves any 16-byte message under a valid tag, which is the
    coprocessor trust model of section 2 and not yet the vat model.
13. **Clocks (7.4).** F call 755 and PRF call 765 instead of about 760; `CTH` fixed part 1,239; stateful
    overhead 4,775 (FRAM transfers estimated).

## What this stage does not establish

- Nothing here is RTL. The decoder rules, the two-phase stall and the 2-clock `KMOV` are modelled
  behaviour that stage 2 has to implement and prove.
- The Keccak count of 721 clocks is that of the existing unit with its seven private rows; moving those
  rows into the file is assumed not to change it.
- FRAM and field add/reduce clock counts are estimates. The word-unit and sequencer areas are from
  unsimulated skeletons.
- Lifecycle, enrolment, fuses, the lifecycle record, TRNG, vat, guards, gate: stages 3 to 7. Keys loaded
  by `KEYLOAD` are volatile and host-supplied, and the anchor high-water mark is volatile, as in the
  reference.
- Decision bits (tag compare, key valid) are single flags in the model; the doubled storage of 5.5 is
  stage 6.
