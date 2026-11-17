# Dregg-180 v2: microcoded model (stage 1 of `ARCHITECTURE.md` 9.3)

## What this is, and its security level

This directory is an executable model of the architecture in `../ARCHITECTURE.md`: a microcode assembler,
an interpreter for the sequencer and its decoder rules, models of the register file and the units, and the
microcode for the commands ported so far. There is no RTL. The existing RTL, test bench and golden model
one level up are unchanged and are the reference.

**Stage 1 is a model of a host-trusting signing coprocessor. It is not an enclave.** Plainly:

- **The host knows every signing secret.** `K_host`, `SK.seed` and `SK.prf` are imported from the host
  under an owner-root authorisation. Nothing in this stage hides a signing key from the party that loads it.
  Request tags under `K_host` authenticate the host to the chip, and the host can ask for anything the
  signer serves.
- **The owner-root authorisation is a stand-in.** It is a keyed hash checked by a callable handed to the
  model, in place of the SLH-DSA verification of stage 4. The interface (fresh nonce, statement digest,
  authorisation words, one attempt per nonce) is the real one; the cryptography is not.
- **The device secret is a model parameter.** `K_dev` stands for the PUF output of stage 3. It never crosses
  the host link, and anchor records are tagged under it, so the host cannot forge a record. An attacker who
  can rewrite the FRAM can still restore an older authentic record after a reset (`ARCHITECTURE.md` 3.4).
- **Keys are volatile.** A reset clears them, and loading them again needs the owner root again.
- **The signer signs any 16-byte message** under a valid tag. FORS indices are not derived on chip from
  `H_msg`, and an upper-layer WOTS key is not restricted to roots the chip computed. Any chain value at any
  depth can therefore be requested by choosing the message. What holds is that the 35 chain positions come
  from one consistent message encoding.
- **What the decoder does enforce** (and the tests show by refusing microprograms): key rows and
  key-derived data reach the response, the FRAM, the response length, loop counts and branches only
  through three kinds of declared point; FRAM writes are bounded; the wipe at the end of a command is
  hardware; signer commands do not decode without a key; provisioning does not decode with one.
- **What no rule here enforces**: that a routine releases the right hash output. See "What cannot be
  enforced structurally".

Everything is plain Python 3 with the standard library. Primitives (Keccak, Poseidon2, Goldilocks) are
imported from `../model/qsag_prims.py`.

```
model/isa.py        micro-instruction layout, operation tables, row map, hardwired sequencer constants
model/uasm.py       assembler and disassembler
model/regfile.py    the register file (storage and class-wise clears)
model/units.py      word unit, Keccak unit, field unit, FRAM master; PUF and entropy interfaces; clock counts
model/framing.py    QSAG-Wire word framing (link-independent)
model/link.py       SPI link (words <-> bytes)
model/machine.py    sequencer, decoder rules R1..R12, egress, clock accounting
model/chip.py       top level: ROM image + machine + pins
model/romcheck.py   static checks on a ROM image
model/host.py       host-side request builders, the owner stand-in, a hashlib FIPS 205 reference
ucode/*.uc          microcode sources
ucode/push_manifest.txt   reviewed list of response writers and declassification points
tests/              unittest suites; report.py prints the measured figures; mutation.py is the mutation harness
```

## Running

```
python3 -B -m unittest discover -s hardware/gf180mcu/v2/tests      # 132 tests, about 4 s
python3 -B hardware/gf180mcu/v2/model/romcheck.py S                 # static ROM checks, also L
python3 -B hardware/gf180mcu/v2/tests/report.py                     # ROM size and clocks per command
python3 -B hardware/gf180mcu/v2/tests/mutation.py -j 8              # 153 mutants, about 2.5 minutes
```

`tests/test_reference_script.py` runs `../tb/gen_script.py` (the reference generator, unmodified, into a
temporary directory) and replays its directives on the v2 model. `tests/mutation.py` applies each mutant
to a temporary copy and requires the suite to fail; it exits non-zero if a mutant survives.

## Result of the stage exit test

The reference script has 54 transactions. In configuration L:

| Class | Count | Meaning |
|---|---:|---|
| Request sent unchanged, response equal word for word | 36 | PING, Poseidon2, Merkle, Keccak, framing errors, PRF_msg |
| Request rebuilt in the v2 format, expected response unchanged | 14 | the 12 `CTH` transactions and the 2 key loads |
| Not implemented in this stage; the model answers `E_OPCODE` | 4 | verifier VM, opcodes 0x30 and 0x31 |

Two steps that the reference script does not have are inserted by the replay: one `PROVISION_NONCE` request
before the key load, and, before the first stateful transaction, a reset with a second authorised load of
the same keys as a counted key. `FRAMCHK` directives are compared with a record computed under the device
secret for the counter the reference record names. `FRAMSAVE`, `FRAMRESTORE` and `PIN` directives are
applied, except the four `PIN VERIFY_OK` lines after the verifier-VM transactions.

In configuration S the 15 Poseidon2 and Merkle transactions are also answered with `E_OPCODE` (no field
unit); the other 35 pass as above. The quick script (38 transactions) passes the same way.

This is equality with the reference Python model, for 50 of 54 transactions, 14 of them through a
translation. It is not a reproduction of the reference protocol for those 14, and it is not a comparison
with the RTL.

## Deliberate differences from the reference model

| Transaction (script note) | What differs | Why |
|---|---|---|
| key load (host-provisioned, anchor initialised) | preceded by a nonce request; carries an owner authorisation; anchor records are tagged under the device secret | no provisioning without the owner root; no host-known anchor key |
| second key load: refused | request format; response `E_KEYSET` unchanged, now issued by the dispatcher | |
| Cut-the-Hash without a key: refused | request format; response `E_NOKEY` unchanged, now issued by the dispatcher | |
| FORS public leaves (PUBGEN) | request format, tag | indices are 16-bit tree indices; PUBGEN needs the tag; values unchanged |
| FORS secret leaves released under a valid request tag | request format, tag | as above |
| WOTS chain values, stateless, valid tag | request carries a 16-byte message whose first six base-16 digits are the reference digits | the chip derives chain positions; values unchanged |
| same request, forged tag: refused | request format; one tag bit flipped | `E_MAC`, `FAULT` unchanged |
| same tag, one digit changed: refused | request format; one tag bit flipped | the replay cannot recover the untampered request, so this is the same test as the previous one. Body binding is tested for every request type in `test_commands.RequestTag` |
| WOTS public chain ends (PUBGEN) | request format, tag | values unchanged |
| the five stateful transactions | request format, tag, no STATEFUL flag; run on a counted key after an inserted reset and reload | whether the counter applies is a property of the key. Responses, error codes and `FAULT` unchanged; FRAM records as above |
| duet fold step, Hem-shaped verification (accept and reject each) | `E_OPCODE` | the verifier machine is stage 7; the reference behaviour is the unpinned-program defect of the state report |
| PING (twice) | words 2..4 are status, 0, 0 | the reference does not check them; the raw TRNG word is no longer returned |

Not exercised by the reference script:

- `CTH` in the reference format (length 80) is refused with `E_LEN`; so is any flag but PUBGEN.
- On a counted key, a non-PUBGEN request must be WOTS with key pair address = leaf, else `E_CLASS` (13).
- `KEYLOAD` without a valid authorisation: `E_AUTH` (12). `PROVISION_NONCE` without entropy: `E_TRNG` (11).
- Error precedence differs from the reference: the dispatcher's refusals (`E_MAGIC`, `E_OPCODE`, `E_NOKEY`,
  `E_KEYSET`) come before any length check.
- `PRF_MSG` requires flags = 0. Bytes past the stated length in the last payload word are ignored.
- Opcodes 0x02 CSR, 0x03 BIST, 0x50 PUF, 0x51 VAT, 0x52 DB_NCO, 0x53 VAT_ZK answer `E_OPCODE`.
- A decoder-rule violation is a control fault: every latch is cleared and no response is sent. (Hardware
  would already have sent the words pushed before the fault; the model discards them.)

## Commands

```
PING            0x01  diag    -> chip id, status, 0, 0
KECCAK          0x20  diag    flags bit 0: 12 rounds; arg [7:0] suffix, [15:8] output words; payload = message
P2, MERKLE      0x10, 0x11  diag, configuration L
PROVISION_NONCE 0x43  prov    -> 128-bit nonce
KEYLOAD         0x40  prov    flags bit 0 = 1, bit 1 anchor init, bit 2 counted key; length 64
                              payload K_host[2], SK.seed[2], SK.prf[2], authorisation[2]
PRF_MSG         0x42  keyed   payload opt_rand || M -> R
CTH             0x41  keyed   flags bit 0 PUBGEN; length 88; arg [7:0] n, [15:8] first chain (WOTS)
                              payload s0 [31:0] leaf, [39:32] layer; s1, s2 PK.seed; s3 tree address;
                              s4 type (0 WOTS, 3 FORS) and key pair address; s5..s8 16-byte message (WOTS)
                              or up to 16 tree indices of 16 bits (FORS); tag[2]
                              tag = TurboSHAKE256(K_host || header || s0..s8, D = 0x21)[0..15]
```

Dispatch class: `diag` always decodes; `prov` needs the device secret and no valid key; `keyed` needs a
valid key. The owner authorises `(nonce, TurboSHAKE256(header || six key words, D = 0x22)[0..31])`.
`model/host.py` builds all of these.

- WOTS: the chip computes the 32 message digits and 3 checksum digits (FIPS 205, `lg_w = 4`) and returns
  `F^{d_i}(sk_i)` for chains `first .. first + n - 1`. PUBGEN returns `F^15(sk_i)`.
- FORS: returns `PRF(PK.seed, SK.seed, ADRS(FORS_PRF, index))` per index; PUBGEN returns `F` of it.
- Counted key, not PUBGEN: both anchor records are read and authenticated, the request is refused if the
  leaf is below the larger counter, `leaf + 1` is written to the other slot and read back, and only then is
  anything computed from `SK.seed`.

## Micro-instruction format

One word is 28 bits in both configurations.

| Bits | Field | Use |
|---|---|---|
| 27:23 | `op` | operation |
| 22:16 | `A` | source row, or function code, condition, constant index, immediate bits 13:7 |
| 15:9 | `B` | destination row, or immediate bits 6:0, or branch target bits 10:4 |
| 8:5 | `fn` | bit 0 `W`: store H to row B; bit 1 `I`: operand is the immediate; bits 3:2: immediate bits 15:14; or branch target bits 3:0. `CMP` with bit 0 is `CMPT`; `PUSH` with bit 0 is `REL`, with bit 1 pushes H |
| 4 | `ia` | row A is indexed: A + X mod 128 |
| 3 | `ib` | row B is indexed: B + X mod 128 |
| 2 | `xi` | X += 1 after the instruction |
| 1:0 | `seq` | 0 next, 1 return after this instruction |

`H` is the hold register of the register file's write path and the accumulator of the word unit.

| Group | Operations |
|---|---|
| Word unit, two operands (row or 16-bit immediate) | `LD XOR AND OR ADD SUB CMP`; `ADD`/`SUB` are 32-bit and set the carry; `CMP` ORs "differs" into the sticky flag Z |
| Word unit, wiring only | `UN` with `ID NIB BE32 HSWAP LO32 HI32 SHR1 SHR4 SHR8 SHR16 SHL1 SHL4 SHL8` |
| Sources | `DIN` (next payload word), `LDF` (header, flags, length, words left, arg, X, status, nonce, key attribute), `LDC` (64-bit constant) |
| Response | `HDR #cap [okz]`, `PUSH row`, `PUSH H`, `REL lane`, `FAIL #code`, `END` |
| Keys | `KMOV keyrow > lane`, `KEYWR > keyrow`, `CTL SETKV`, `CTL AUTH`, `CTL NONCE` |
| Units | `KEC 24|12`, `FLD PERM|RED`, `FADD` (L), `FRAM RSTART|WSTART|DONE`, `FRAM RWORD [> row]`, `FRAM WWORD row`, `WIPE #classes` |
| Control | `BR [cond] target`, `BXNE #k target`, `DBNZ 0|1 target`, `CALL`, `SETX`, `SETC`, `CMPT lane`, `CTL` (`CLRZ SETFM SETFA VOK`), `DISP`, `ILL` |

Hardwired constants of the sequencer (`model/isa.py`; the assembler lays the image out with `.org`, and
`romcheck.py` fails an image that does not match):

| Address | Use |
|---|---|
| 0 | the idle point: the only `DISP` |
| 1..63 | provisioning range: `KEYWR`, `CTL SETKV`, `CTL AUTH`, `CTL NONCE` decode only here |
| 64..127 | record range: `FRAM` instructions decode only here |
| 128.. | everything else |

Register file, configuration S (64 rows; L adds rows 64..127). The specification now asks for 72 rows with
20 scratch rows; the model grows when a routine needs them.

| Rows | Count | Class |
|---|---:|---|
| 0..24 | 25 | lanes |
| 25..31 | 7 | Keccak work rows |
| 32..43 | 12 | scratch (row 41 is the record counter, the one scratch row the FRAM may be sent) |
| 44..53 | 10 | keys: `K_dev` 4, `K_host` 2, `SK.seed` 2, `SK.prf` 2 |
| 54..59 | 6 | pins (unused) |
| 60..61 | 2 | state: anchor high-water mark |
| 62..63 | 2 | out (egress FIFO) |

## Structural rules

Each is a decoder or sequencer check that uses only the hardwired constants and sequencer state; none
reads a property of the ROM image. `machine.py` implements them; `tests/test_output_bound.py` has a
refusing microprogram for each, and `tests/mutation.py` removes each one in turn and requires a failure.

Key rows
- **R1** Key rows are read only by `KMOV` and written only by `KEYWR`. `KEYWR`, `CTL SETKV`, `CTL AUTH`
  and `CTL NONCE` decode only at addresses 1..63. `KEYWR` and `SETKV` also need the authorisation latch,
  which only a successful `CTL AUTH` sets, in the same command.
- **R2** `KMOV` writes a rate lane (0..16), sets `keyed`, `dirty` and the lane taint, and clears H.
- **R3** While `dirty` (a key was copied into the lanes and no permutation has run since), a lane is read
  only by an `XOR` that stores back to the same lane, and H is cleared afterwards.
- **R4** While `keyed` (until the command ends), lanes 17..24 are never read by the word unit. The Keccak
  work rows are never read or written by the word unit.

Taint
- **R5** Four flags: T_lanes (the lanes hold key-derived data), T_H, T_Z, T_CY. `KMOV` sets T_lanes; only
  a wipe of all lanes clears it. Reading a lane while T_lanes taints H; H's taint follows it through the
  word unit; `CMP` taints Z; `ADD` and `SUB` taint the carry.
- **R6** A tainted H is stored only to a lane or, by `KEYWR`, a key row. Scratch, pin, state and challenge
  rows, the index register and the loop counters therefore never hold key-derived data.
- **R7** Refused when the value is tainted: `PUSH`, `HDR` (length and flag), `SETX H`, `SETC H`,
  `FRAM RSTART` and `WSTART` (slot), `CTL SETKV`, `CTL VOK`, and every branch on a tainted flag.
- **R8** Declassification points, below.

Response and end
- **R9** The response is written only by `PUSH` and `REL`, after the one `HDR` of the command. `HDR`'s
  length is at most the cap in the instruction; the egress stops at that length and the end action pads
  to it. Out rows are not addressable. `FAIL` is refused after `HDR`.
- **R10** A command ends only by `END` or `FAIL` (or a refusal by the dispatcher). The end action is
  hardware: pad the response, clear every working row and the session flags, discard unread payload, go
  to address 0. No instruction can branch to address 0, and `DISP` decodes only there.

FRAM and lifecycle
- **R11** `FRAM` instructions decode only at addresses 64..127. `FRAM WWORD` sends one of three rows: the
  record counter row, or lane 0 or 1 after a permutation. A transaction is three words in one direction.
- **R12** The dispatcher refuses by class (see "Commands"), and refuses bad magic and unknown opcodes
  itself.

### Declassification points

Key-derived data crosses R7 in exactly three ways. Every instance in the ROM is listed in
`ucode/push_manifest.txt`, and `romcheck.py` fails if the image and the list differ.

| Point | What the decoder requires | Instances in the ROM |
|---|---|---|
| `REL lane` | a rate lane (0..16), after a permutation (not `dirty`), inside the declared response length | 6: `PRF_MSG` R (2 words), WOTS chain value (2), FORS leaf value (2) |
| `CMPT lane` | H untainted (a word from the host or the FRAM), a rate lane, after a permutation; only the equal/unequal verdict leaves, in Z | 6: request tag (2), stored record authentic (2), record read back (2) |
| `FRAM WWORD lane 0` or `1` | address in the record range, after a permutation, inside a three-word write | 2: the record tag |

### What cannot be enforced structurally

- **Which hash output is released.** `REL` proves that the value is the rate of a completed permutation
  over a keyed state. It cannot tell `F^d(sk)` from `F^(d-1)(sk)`, or a chain value from a raw PRF output:
  that is the microprogram's arithmetic. The barriers are the manifest (six lines, reviewed), the FIPS 205
  comparisons in `test_commands.py`, and stage 5's on-chip digest.
- **What the verdict of a tag compare is used for.** `CMPT` leaks one bit by design. The rule bounds what
  is compared, not what the routine does with the answer.
- **Timing through unit calls.** The number of `KEC` calls a routine makes is public by rule (loop counts
  cannot be tainted), and `test_commands.Invariants.test_cycle_counts_do_not_depend_on_the_keys` checks the
  shipped ROM. Data-dependent timing inside a unit is a property of the unit's RTL, not of this decoder.
- **Host-chosen inputs.** Layer, tree, key pair, `PK.seed`, the chain window and the message are host
  data. The rules do not restrict them; the counted attribute and, later, the vat do.
- **The dispatch table** is part of the ROM image. Its class bits are checked against the hardwired key
  range by `romcheck.py`, not by the decoder.

## ROM size

| | Code words | Image words (with `.org` padding) | Bits | Constants | Dispatch entries |
|---|---:|---:|---:|---:|---:|
| Configuration S | 432 | 455 | 12,740 | 4 x 64 | 6 |
| Configuration L | 589 | 612 | 17,136 | 4 x 64 | 8 |

Words per source: `main.uc` 1, `provision.uc` 58, `fram.uc` 46, `ping.uc` 17, `keccak.uc` 46, `sign.uc` 264,
`field.uc` 157 (L only). An earlier image of 418 words synthesized to 19,072 µm² (45.6 µm² per word); the
current image was not re-synthesized.

## Commands, routines and clocks

Clocks are counted by the interpreter from the dispatch to the idle point, with the link never
stalling. Unit counts are in `model/units.py`: Keccak-f 721, Keccak-p12 373 and the Poseidon2 permutation
3,074 are measured on the existing RTL; a micro-instruction is 1 clock, plus 1 when it reads the row the
previous instruction wrote; `KMOV` is 2; the end action is 3. Estimates: field add and reduce (1 clock),
FRAM transfers (SCK = clk / 4), nonce draw (8), and the owner-root verification stand-in (3.9 M clocks,
the bound of `ARCHITECTURE.md` 4.3).

| Command | Routine (`ucode/`) | Case | Clocks | At 25 MHz |
|---|---|---|---:|---:|
| PING | `ping` | | 15 | 0.6 µs |
| KECCAK | `keccak`, `absorb_pad`, `perm_sel` | TurboSHAKE256, up to 135 bytes, 4 words out | 410–494 | 16–20 µs |
| | | each further 136-byte block | 452 | 18 µs |
| | | SHAKE256, up to 135 bytes | 758–842 | 30–34 µs |
| | | each further block | 800 | 32 µs |
| PROVISION_NONCE | `prov_nonce` (`provision.uc`) | | 22 | |
| KEYLOAD | `keyload` (`provision.uc`), `fram_*` (`fram.uc`) | with anchor initialisation, without the verification | 4,416 | 0.18 ms |
| | | owner-root verification (stand-in, estimate) | 3,900,000 | 0.16 s |
| PRF_MSG | `prfmsg` (`sign.uc`) | 32-byte payload | 768 | 31 µs |
| CTH | `cth` (`sign.uc`) | fixed part: tag check, shape checks, header | 472 | 19 µs |
| | `f_step` | one F call (lane build + Keccak-f) | 755 | 30.2 µs |
| | `prf_step`, `next_digit` | one chain start (digit + PRF call) | 765 | 30.6 µs |
| | | WOTS public key, 35 chains (561 Keccak calls) | 422,683 | 16.9 ms |
| | | WOTS signature, most steps (all message digits 15; 516 calls) | 388,760 | 15.6 ms |
| | | WOTS signature, digits spread evenly (291 calls) | 219,333 | 8.8 ms |
| | `fors` | 14 FORS leaves, secret / public | 11,099 / 21,596 | 0.44 / 0.86 ms |
| | `anchor_read`, `fram_tag`, `fram_write`, `fram_check` | counted key: two record reads, write, read-back | + 4,780 | + 0.19 ms |
| | | refused for a bad tag | 429 | 17 µs |
| P2 (L) | `p2` (`field.uc`) | raw permutation | 3,149 | 0.13 ms |
| MERKLE (L) | `merkle` (`field.uc`) | per level | about 3,175 | 0.13 ms |
| any | dispatcher | refused by the dispatcher | 3 | |

## Deviations from ARCHITECTURE.md

The specification has since been re-targeted at the small slot (its section 11) and its 5.3 now states
the rules above. Items 1 to 13 are from the first pass of this stage; 14 to 24 are the ones a review found
missing (`scratch/lanes/sonnet-audit-dregg180-v2-stage1.last.md`), each with what was done about it.

1. **Row map (5.2).** Scratch 12 and out 2 here; the specification now says 20 and 2, 72 rows in all.
2. **Output bound (5.3).** One `HDR` per command declares the length under a cap in the instruction; the
   end action pads. For `KECCAK` the cap is 255 words, the most the request can ask for, so the cap is a
   bound on the routine and not on that command.
3. **Keyed-state rules (5.3).** R2 to R4 were added in the first pass; R5 to R8 in the second.
4. **Instruction format and sequencer (5.5).** 28 bits in L as well; index register X; `DBNZ` and `BXNE`
   in place of loop-sequencing bits; 16-bit immediates; constant and dispatch tables beside the word ROM.
5. **Word unit (5.4).** `OR` in place of AND-NOT; wiring functions in place of a digit extractor.
6. **Sequencer area (7.1).** The skeleton measured before these rules is 23,985 µm²; the taint flags,
   range comparators and dispatch classes are not in it.
7. **ROM (5.5).** 432 code words, of which the signer is 264 (estimate 160) and unfinished.
8. **`PRF_MSG` is not tagged.** It is an oracle for `SHAKE256(SK.prf || payload)[0..15]` to any host. That
   value is the public randomiser of a signature, and tagging an arbitrary-length payload needs a second
   sponge state.
9. **`CTH` wire format** (above). The specification does not define wire formats.
10. **Counter bound to the key pair.** On a counted key the key pair address must equal the leaf.
11. **Stage exit.** 50 of 54; the four verifier-VM transactions belong to stage 7.
12. **Signer scope.** `H_msg`-derived FORS indices and root tagging are stage 5.
13. **Clocks (7.4).** As in the table above.
14. **Anchor MAC key (3.1).** Was `K_host`, which the host knows. Now the device secret `K_dev`, a model
    parameter standing for the PUF (`units.PufUnit`). The specification's `K_fram = KDF(K_dev)` and the
    lifecycle record format are stage 3; this is still the reference's three-word record.
15. **Host-supplied signing keys (2).** `SK.seed` and `SK.prf` are still imported from the host, now under
    the owner authorisation. The specification derives them from `K_dev`. Kept because the reference
    vectors need known seeds; stage 3 replaces the import.
16. **Lifecycle gate (3.2, 5.5).** Was absent. Now dispatch classes R12. The states of 3.2 (`BLANK`,
    `ORPHAN`, leases) are not modelled; the gate has three: no device secret, no key, key valid.
17. **Hardwired ranges (5.3).** Were read from ROM directives. Now constants of `isa.py`; the `.keyrange`
    and `.epilogue` directives are gone, and the wipe is the hardware end action R10.
18. **Taint (8.3).** Was a comparison of response words with key-row values. Now R5 to R8. The value
    comparison is kept as a second check.
19. **Signature scheme.** FIPS 205 WOTS+ with 35 chains and `lg_w = 4` only. The WOTS+C and FTS operations
    of Baggy and Jorts that the specification's use U1 names cannot be requested: the width is no longer a
    request field. The row "one-time signature (WOTS+C, FTS), up to 600 calls" in 7.4 has no model
    counterpart.
20. **Counted keys (1, U2).** Was a request flag. Now an attribute stored by `CTL SETKV` at provisioning.
    A counted key signs WOTS only; an uncounted key never touches the anchor.
21. **One counter for the whole key.** The counter is a single number, while a request names layer, tree
    and key pair. It is conservative, and a hypertree with more than one key pair per counter value cannot
    be served on a counted key.
22. **Not modelled from 5.5.** The Hamming-distance-4 micro-PC code, and doubled storage of decision bits.
23. **Error precedence and codes.** The dispatcher's refusals come first. `E_CLASS` (13) separates
    "wrong class of request for this key" from a shape error; `E_AUTH` (12) is new.
24. **FRAM writes (5.3).** Were unrestricted. Now R11.

## What this stage does not establish

- Nothing here is RTL. Every rule above is modelled behaviour that stage 2 has to implement and prove.
- The Keccak count of 721 clocks is that of the existing unit with its seven private rows; moving those
  rows into the file is assumed not to change it.
- FRAM, field add/reduce, nonce and verification clock counts are estimates.
- Lifecycle states, enrolment, the lifecycle record, leases, TRNG, PUF, vat, guards and the gate are
  stages 3 to 7. The PUF, entropy and owner interfaces here are stand-ins.
- The taint rule is coarse: all lanes share one flag. A routine that needs a clean lane beside a
  key-derived one cannot be written without a wipe.
