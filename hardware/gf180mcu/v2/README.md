# Dregg-180 v2: microcoded model (stages 1, 3 and 4 of `ARCHITECTURE.md` 9.3, model side)

## What this is, and its security level

This directory is an executable model of the architecture in `../ARCHITECTURE.md`: a microcode assembler,
an interpreter for the sequencer and its decoder rules, models of the register file, the units and the
organs' digital side, and the microcode for the commands written so far. The RTL of stage 2 is in `rtl/`
(another lane's; it implements the stage-1 machine). The old RTL, test bench and golden model one level up
are unchanged.

**The model is now an enclave in the sense of the specification, for the commands it has, and with
stand-ins named below.** Plainly:

- **No key comes from the host.** The device key `K_dev` is derived at boot from the PUF response and
  helper data that the owner root signed; `SK.seed`, `SK.prf` and `K_host` are derived from `K_dev` each
  time they are used. `K_host` is released once, in the response to `COMMIT`. A host that holds `K_host`
  may ask for anything the signer serves (coprocessor mode).
- **Authorisation is real signature verification in microcode.** Enrolment, boot and re-initialisation
  verify an SLH-DSA-SHAKE signature by the owner root, whose public-key digest is a constant of the ROM;
  leases and transitions verify `k` signatures by distinct members of the committee pinned in the lifecycle
  record. The keyed-hash stand-in of stage 1 is gone. The verification is public computation: it uses no
  key and no entropy.
- **The PUF and the TRNG are models.** The PUF is a 252-bit response with a settable set of bits that read
  wrong, and a BCH(63,36,5) decoder; the TRNG is a stochastic model of eight rings with the failure modes
  of `ARCHITECTURE.md` 6.5. Nothing here says anything about the circuits. The microcode that uses them
  (check tag before any key row is written; pair selection, health tests, conditioning) is the real one.
- **Rollback.** Lifecycle records are authentic under `K_dev` and not fresh. On an unleased chip an older
  FRAM image restored across a reset is accepted, and a one-time key can be used again
  (`ARCHITECTURE.md` 3.4; a test asserts this residual). On a leased chip the counter starts where the
  authority's lease says.
- **The signer still signs any 16-byte message** under a valid tag. FORS indices are not derived on chip
  from `H_msg`, and an upper-layer WOTS key is not restricted to roots the chip computed (stage 5).
- **The fingerprint argument of the verifier is unreviewed** (`ARCHITECTURE.md` 4.3).
- **What no rule enforces**: that a routine releases the right hash output. See "What cannot be enforced
  structurally".

Everything is plain Python 3 with the standard library. Primitives (Keccak, Poseidon2, Goldilocks) are
imported from `../model/qsag_prims.py`.

```
model/isa.py        micro-instruction layout, operation tables, row map, hardwired sequencer constants
model/uasm.py       assembler and disassembler
model/regfile.py    the register file (storage and class-wise clears)
model/units.py      word unit, Keccak unit, field unit, FRAM master, PUF organ with its BCH decoder, TRNG organ
model/framing.py    QSAG-Wire word framing (link-independent)
model/link.py       SPI link (words <-> bytes)
model/machine.py    sequencer, decoder rules R1..R15, egress, clock accounting
model/chip.py       top level: ROM image (per signature parameter set and owner root) + machine + pins
model/romcheck.py   static checks on a ROM image
model/host.py       host side: request builders, FIPS 205 signer and verifier on hashlib, committee tree,
                    statement builders, the enrolment flow
ucode/defs.uc       constants, state rows, scratch rows
ucode/main.uc       the idle point
ucode/key.uc        key range: lifecycle register, verdict latch, PUF check tag, K_dev
ucode/rec.uc        record range: helper record, lifecycle records, transitions' record updates
ucode/hash.uc       key derivation on use; the tweakable hashes shared by signer and verifier
ucode/trng.uc       pair selection, health tests, nonce conditioning
ucode/slh.uc        SLH-DSA-SHAKE verification with the hash chain and fingerprint
ucode/life.uc       BOOT, ENROL, COMMIT, NONCE, REINIT, LEASE, GATE; statements; committee paths
ucode/sign.uc       PRF_MSG, CTH
ucode/keccak.uc, ping.uc, field.uc
ucode/push_manifest.txt   reviewed list of response writers and declassification points
tests/              unittest suites; report.py prints the measured figures; mutation.py is the mutation harness
```

## Running

```
python3 -B -m unittest discover -s hardware/gf180mcu/v2/tests      # 189 tests, about 90 s
python3 -B hardware/gf180mcu/v2/model/romcheck.py S                 # static ROM checks, also L
python3 -B hardware/gf180mcu/v2/tests/report.py                     # ROM size and clocks per command
python3 -B hardware/gf180mcu/v2/tests/mutation.py -j 10             # MUTANTS mutants, about MUTMIN minutes
```

Signature parameter sets. The ROM is assembled for one set (`chip.SLH`): `128s` (FIPS 205
SLH-DSA-SHAKE-128s: k = 14, a = 12, d = 7, h' = 9), and two reduced sets for the tests, `tiny` (k = 4,
a = 4, one layer of height 2) and `small` (k = 6, a = 8, two layers of height 3). The microcode text is the
same; six constants differ. A verification takes 0.15 s of wall time on `tiny` and about 2 s on `128s`, so
the tests use `tiny` except `ParameterSets` (one test on `small`, for the step between layers; one on
`128s`). The FIPS 205 signer the tests verify against is `host.Slh`, written from the standard on hashlib;
for 128s its key generation and signature equal, byte for byte, those of the PyPI package `slh-dsa`
0.2.5 (`slhdsa.lowlevel.slhdsa.sign` on the raw message; checked by hand once, not part of the suite, which
has no dependency). It has not been compared with `crates/qsag-core`.

`tests/mutation.py` applies each mutant to a temporary copy and requires the suite to fail; it exits
non-zero if a mutant survives. It sets `DREGG_FAST=1`, which skips the one `128s` test.

## The reference script

`tests/test_reference_script.py` runs `../tb/gen_script.py` (the reference generator, unmodified, into a
temporary directory) and replays its 54 transactions. The reference chip takes its signing keys from the
host and the v2 chip derives them, so signer values can no longer equal the reference's. In
configuration L:

| Class | Count | Meaning |
|---|---:|---|
| Request sent unchanged, response equal word for word | 34 | PING, Poseidon2, Merkle, Keccak, framing errors |
| Signer request rebuilt in the v2 format; refusals equal the reference's, served values equal FIPS 205 under the chip's own derived keys | 13 | 11 `CTH`, 2 `PRF_MSG` |
| The reference behaviour no longer exists | 3 | the two key loads (`E_OPCODE`: there is no key import); one roll-back refusal (served: within a power session the chip does not read the FRAM) |
| Not implemented; the model answers `E_OPCODE` | 4 | verifier VM, opcodes 0x30 and 0x31 |

Inserted by the replay: a chip that has been enrolled, committed and booted, at the first key load; a second
one with the counted policy, before the first stateful transaction. In configuration S the 15 Poseidon2 and
Merkle transactions are answered with `E_OPCODE`. This is no longer a comparison of the signer with the
reference model; it is a comparison with FIPS 205 through `host.py`.

## Commands

```
PING     0x01  any state       -> chip id constant, status, 0, 0
KECCAK   0x20  any state       flags bit 0: 12 rounds; arg [7:0] suffix, [15:8] output words; payload = message
P2, MERKLE  0x10, 0x11  any state, configuration L
BOOT     0x44  RESET           payload: nothing (expecting a blank chip), or the owner root's public key (4 words)
                               and the package of its signature over the helper record
                               -> lifecycle state, chip id, record word 0, nonce[2]
ENROL    0x45  BLANK           -> syndromes[2], check tag[2], nonce[2]
COMMIT   0x46  BLANK           payload: check tag[2], commit word, root[2], owner key[4], package -> K_host[2]
NONCE    0x43  ORPHAN, LEASE   -> nonce[2]
REINIT   0x47  ORPHAN          payload: commit word, root[2], owner key[4], package
LEASE    0x48  LEASE           arg = 1; payload: base | bound << 32, 0, 0, statement -> record words 0, 1
GATE     0x49  READY           arg = type (2 EPOCH, 3 RETIRE, 4 ROTATE); payload: arguments[3], statement -> record word 0
PRF_MSG  0x42  READY           payload opt_rand || M -> R
CTH      0x41  READY           flags bit 0 PUBGEN; length 88; arg [7:0] n, [15:8] first chain (WOTS)
                               payload s0 [31:0] leaf, [39:32] layer; s1, s2 PK.seed; s3 tree address;
                               s4 type (0 WOTS, 3 FORS) and key pair address; s5..s8 16-byte message (WOTS)
                               or up to 16 tree indices of 16 bits (FORS); tag[2]
                               tag = TurboSHAKE256(K_host || header || s0..s8, D = 0x21)[0..15]
```

Lifecycle states (a register of the sequencer): `RESET` 0, `BLANK` 1, `ORPHAN` 2, `LEASE` 3, `READY` 4,
`LOCKED` 5. Every dispatch-table entry names the states its command decodes in; anything else is refused
by the dispatcher in one clock (`E_NOKEY` for a command that needs `READY`, else `E_STATE`).

Formats (all hashes TurboSHAKE256 over whole 64-bit words; `host.py` builds every one of these):

- **Commit word**: first use counter [31:0], generation [47:32], flags [55:48] (1 vat, 2 leased, 4 counted,
  8 mint lock, 16 retired), threshold `k` [63:56]. Record word 0 is the same with the sequence number in
  [31:0]; record word 1 is the use counter [31:0] and the epoch [63:32].
- **Owner statement** (`COMMIT`, `BOOT`: label `DREGG.CM`; `REINIT`: `DREGG.RI`): label, nonce[2],
  syndromes[2], check tag[2], commit word, root[2]; D = 0x22; 32 bytes.
- **Transition message**: `DREGG.TR`, check tag[2], record word 0, type, session nonce[2] (zero unless a
  lease is pending), arguments[3]; D = 0x22; 32 bytes.
- **Statement**: `k` members in strictly increasing index, each: index | path length << 32, public key[4],
  path (16 bytes a level), package, path again. A single authority is one member with an empty path.
- **Package** of a signature (2,018 words for 128s): `R`; per FORS tree the secret value and its path; the
  FORS roots; the FORS roots again; per layer the 35 signature values, the 35 chain ends, the chain ends
  again, the authentication path.
- **Committee**: leaf `TurboSHAKE256(index, pk[4], D = 0x24)[0..15]`, node `TurboSHAKE256(left, right,
  D = 0x25)[0..15]`. The owner root's ROM constant is the leaf hash of its key at index 0.
- **Keys**: check tag `TS(w[4], "DREGGPCK", D = 0x29)[0..15]`; `K_dev = TS(w[4], "DREGGKDV", enrolment
  nonce[2], D = 0x2A)[0..31]`; derived key `TS(K_dev[4], label, D = 0x23)[0..15]` with labels `DREGGKHO`,
  `DREGGSKS`, `DREGGSKP`; record tag `TS(K_dev[4], "DREGGREC", record[5], D = 0x1F)[0..15]`.
- **FRAM**: three records of up to 16 words at byte addresses 0, 128, 256: the helper record (commit word,
  syndromes[2], root[2], check tag[2], enrolment nonce[2]) and two lifecycle slots (record[5], tag[2]); the
  record with sequence number `s` is in slot `1 + s mod 2`.

Signer behaviour is as in stage 1 (WOTS digits derived on chip, FORS leaves, PUBGEN, the request tag on
every request), with these changes: keys are derived; the signer serves only in coprocessor mode
(`E_CLASS` in vat mode); on a counted chip the counter is the use counter `u` of the lifecycle record, a
request below it is `E_REUSE`, at or past the lease bound `E_LEASE`, and the record with `u = leaf + 1` is
written and read back before anything is computed from `SK.seed`.

## Micro-instruction format

One word is 28 bits in both configurations. The layout is unchanged from stage 1; the changes are in the
tables and are listed under "Changes the RTL has to follow".

| Bits | Field | Use |
|---|---|---|
| 27:23 | `op` | operation |
| 22:16 | `A` | source row, or function code, condition, constant index, immediate bits 13:7 |
| 15:9 | `B` | destination row, or immediate bits 6:0, or branch target bits 10:4, or the operand of `CTL LC` and `CTL SYNW` |
| 8:5 | `fn` | bit 0 `W`: store H to row B; bit 1 `I`: operand is the immediate; bits 3:2: immediate bits 15:14; or branch target bits 3:0. `CMP` with bit 0 is `CMPT`; `PUSH` with bit 0 is `REL`, with bit 1 pushes H; `KMOV` with bit 0 is `PMOV` |
| 4 | `ia` | row A is indexed: A + X mod 128 |
| 3 | `ib` | row B is indexed: B + X mod 128 |
| 2 | `xi` | X += 1 after the instruction |
| 1:0 | `seq` | 0 next, 1 return after this instruction |

| Group | Operations |
|---|---|
| Word unit, two operands (row or 16-bit immediate) | `LD XOR AND OR ADD SUB CMP`; `ADD`/`SUB` are 32-bit and set the carry; `CMP` ORs "differs" into the sticky flag Z |
| Word unit, wiring only | `UN` with `ID NIB BE32 HSWAP LO32 HI32 SHR1 SHR4 SHR8 SHR16 SHL1 SHL4 SHL8 XT SHL1C`. `XT` multiplies by x in GF(2^64) (modulus x^64 + x^4 + x^3 + x + 1); `SHL1C` is `SHL1` with the bit shifted out to the carry |
| Sources | `DIN` (next payload word), `LDF` (`HDRW FLAGS LEN NWORDS ARG ARGLO ARGHI X STATUS LC SYN0 SYN1 PNOISE TS1 TS4 TSUM TFLAGS TRAW`), `LDC` (64-bit constant) |
| Response | `HDR #cap [okz]`, `PUSH row`, `PUSH H`, `REL lane`, `FAIL #code`, `END` |
| Keys | `KMOV keyrow > lane`, `PMOV #i > lane` (word i of the PUF response register), `KEYWR > keyrow`, `CTL AUTH` (verdict latch from a clear Z), `CTL ZKEY` (clear the key rows) |
| Organs | `CTL PUFE`, `CTL PUFR` (measure; enrol or reconstruct), `CTL SYNW #i` (syndrome register word i from H), `CTL TSEL` (ring pair from H), `CTL TRUN` (64 counts), `CTL TCLR`, `CTL TARM` |
| Units | `KEC 24|12`, `FLD PERM|RED`, `FADD` (L), `FRAM RSTART|WSTART|DONE`, `FRAM RWORD [> row]`, `FRAM WWORD row`, `WIPE #classes` |
| Control | `BR [cond] target`, `BXNE #k target`, `DBNZ 0|1 target`, `CALL`, `SETX`, `SETC`, `CMPT lane`, `CTL` (`CLRZ SETFM SETFA VOK`, `LC #state`), `DISP`, `ILL` |

Hardwired constants of the sequencer (`model/isa.py`; the assembler lays the image out with `.org`, and
`romcheck.py` fails an image that does not match):

| Address | Use |
|---|---|
| 0 | the idle point: the only `DISP` |
| 1..79 | key range: `KEYWR`, `PMOV`, `CTL LC`, `CTL AUTH`, `CTL PUFE`, `CTL PUFR`, `CTL SYNW` decode only here (56 words used) |
| 80..287 | record range: `FRAM` instructions and writes of state rows decode only here (191 words used) |
| 288.. | everything else; every command entry is here |

Return stack: four entries. Register file, configuration S, 72 rows (L adds rows 72..127):

| Rows | Count | Class |
|---|---:|---|
| 0..24 | 25 | lanes |
| 25..31 | 7 | Keccak work rows |
| 32..55 | 24 | scratch |
| 56..59 | 4 | keys: `K_dev` |
| 60..69 | 10 | state: record words 0..2, authority root 2, PUF check tag 2, session nonce 2, lease bound. Public; kept between commands; cleared only by reset |
| 70..71 | 2 | out (egress FIFO) |

## Structural rules

Each is a decoder or sequencer check that uses only the hardwired constants and sequencer state; none
reads a property of the ROM image. `machine.py` implements them; `tests/test_output_bound.py` has a
refusing microprogram for each, and `tests/mutation.py` removes each one in turn and requires a failure.

Key rows
- **R1** Key rows are read only by `KMOV` and written only by `KEYWR`. `KEYWR` decodes only in the key
  range and needs the verdict latch, which only `CTL AUTH` sets, in the key range, from a compare flag that
  is clear and not key-derived, in the same command. (In the ROM: the PUF check-tag compare.)
- **R2** `KMOV` writes a rate lane (0..16), sets `keyed`, `dirty` and the lane taint, and clears H.
- **R3** While `dirty` (a key was copied into the lanes and no permutation has run since), a lane is read
  only by an `XOR` that stores back to the same lane, and H is cleared afterwards.
- **R4** While `keyed` (until the command ends), lanes 17..24 are never read by the word unit. The Keccak
  work rows are never read or written by the word unit.

Taint
- **R5** Four flags: T_lanes (the lanes hold key-derived data), T_H, T_Z, T_CY. `KMOV` and `PMOV` set
  T_lanes; only a wipe of all lanes clears it. Reading a lane while T_lanes taints H; H's taint follows it
  through the word unit; `CMP` taints Z; `ADD`, `SUB` and `SHL1C` taint the carry.
- **R6** A tainted H is stored only to a lane or, by `KEYWR`, a key row. Scratch, state and challenge
  rows, the index register and the loop counters therefore never hold key-derived data.
- **R7** Refused when the value is tainted: `PUSH`, `HDR` (length and flag), `SETX H`, `SETC H`,
  `FRAM RSTART` and `WSTART` (record index), `CTL AUTH`, `CTL VOK`, `CTL SYNW`, `CTL TSEL`, and every
  branch on a tainted flag.
- **R8** Declassification points, below.

Response and end
- **R9** The response is written only by `PUSH` and `REL`, after the one `HDR` of the command. `HDR`'s
  length is at most the cap in the instruction; the egress stops at that length and the end action pads
  to it. Out rows are not addressable. `FAIL` is refused after `HDR`.
- **R9a** There is one hold register. A permutation, `PUSH row` and `REL` leave H cleared (the unit writes
  through it; a pushed row passes through it). On a control fault the words already pushed have left the
  chip: `ControlFault.sent` holds them, and the link returns a frame shorter than its header states
  (`model/link.py` states the frame format).
- **R10** A command ends only by `END` or `FAIL` (or a refusal by the dispatcher). The end action is
  hardware: pad the response, clear every working row, the PUF response register and the session flags
  (the verdict latch among them), discard unread payload, go to address 0. No instruction can branch to
  address 0, and `DISP` decodes only there.

FRAM, state and lifecycle
- **R11** `FRAM` instructions decode only in the record range. `FRAM WWORD` sends a state row, or lane 0
  or 1 after a permutation. A transaction is at most 16 words in one direction, to one of three records.
- **R12** The dispatcher decodes a command only in the lifecycle states its entry names, refuses bad
  magic and unknown opcodes itself, and faults on a table entry whose address is below the ordinary code.
  Undefined function codes (unary, `LDF`, `CTL`, `FRAM`, condition) and constant indices are control
  faults. The runaway limit is 2^28 micro-instructions (a statement of 256 members is about 2^27.4).
- **R13** The PUF response register is read only by `PMOV`, in the key range, into a rate lane, under the
  rules of a key (R2, R3, R5). `CTL PUFE`, `PUFR` and `SYNW` decode only in the key range. The syndrome
  register is public.
- **R14** State rows are written only in the record range.
- **R15** The lifecycle register is written only by `CTL LC` in the key range: `READY` only with the verdict
  latch set and only from `RESET` or `LEASE`; nothing leaves `LOCKED`; `RESET` only by reset.

### Declassification points

Key-derived data crosses R7 in exactly three ways, the same three as in stage 1. Every instance in the ROM
is listed in `ucode/push_manifest.txt`, and `romcheck.py` fails if the image and the list differ.

| Point | What the decoder requires | Instances in the ROM |
|---|---|---|
| `REL lane` | a rate lane (0..16), after a permutation (not `dirty`), inside the declared response length | 10: `PRF_MSG` R (2 words), WOTS chain value (2), FORS leaf value (2), **new:** the PUF check tag at `ENROL` (2), `K_host` at `COMMIT` (2) |
| `CMPT lane` | H untainted (a word from the host, the FRAM or a state row), a rate lane, after a permutation; only the equal/unequal verdict leaves, in Z | 8: request tag (2), stored record authentic (2), record read back (2), **new:** PUF check tag at boot and commit (2) |
| `FRAM WWORD lane 0` or `1` | address in the record range, after a permutation | 2: the lifecycle record tag |

Why the new instances are needed and what each releases:

- **Check tag at `ENROL`** (`enrol+12`, `+13`): a 128-bit hash of the PUF response under its own domain.
  It is public helper data by design (`ARCHITECTURE.md` 6.1): the chip must be able to recognise a correct
  reconstruction before it derives anything, and the owner root must sign it. It reveals `w` only to
  someone who can invert the hash; `K_dev` is a hash of `w` in a different domain with the enrolment nonce.
- **`K_host` at `COMMIT`** (`cm_auth+19`, `+20`): the one key a host is meant to hold. Released once, only
  in state `BLANK`, only after the owner root's signature verified and the PUF reconstructed to the signed
  tag, and not in vat mode. After `COMMIT` the chip is `LOCKED` until reset, and `COMMIT` never decodes
  again on a provisioned chip.
- **Check-tag verdict** (`puf_key+4`, `+6`): one bit, whether this die reconstructs the tag in the
  authenticated helper record. It is what R1's latch is set from.

Not declassification points, though they look like ones: the syndromes (`LDF SYN0/SYN1`) are public helper
data that the organ produces as such; `PNOISE` is counter noise of the characterisation rings, which feed no
key; the statement verifier handles no key at all (`test_lifecycle.Invariants.
test_verification_is_public_computation` checks that no key is in the lanes while it runs).

### What cannot be enforced structurally

- **Which hash output is released.** `REL` proves that the value is the rate of a completed permutation
  over a keyed state. It cannot tell `F^d(sk)` from `F^(d-1)(sk)`, `K_host` from `SK.seed`, or the check
  tag from `K_dev`: that is the microprogram's choice of label and domain. The barriers are the manifest
  (ten lines, reviewed), the value comparisons of the tests against `host.py`, and the mutants that swap
  labels.
- **What a verdict is used for.** `CMPT` leaks one bit by design; `CTL AUTH` accepts any clear, untainted
  Z. In the ROM it is set in two places of the 56-word key range: after the PUF check-tag compare (which
  lets `K_dev` be written and an unleased chip become `READY`) and, through `auth_z`, after an accepted
  lease statement (which lets a leased chip become `READY`). That nothing else calls `auth_z` is the ROM's
  property, not the decoder's.
- **That a statement was verified before a state row is written.** The record range may write state rows
  whenever it is called. That `COMMIT`, `REINIT`, `LEASE` and the transitions call it only after the
  verdict is ROM content, covered by tests and mutants (every conditional branch and compare of
  `life.uc` is removed in turn), not by a decoder rule. `ARCHITECTURE.md` 8.2 item 4 asks for the formal
  version.
- **Timing through unit calls**, host-chosen inputs, and the dispatch table: as in stage 1.

## ROM size

| | Code words | Image words (with `.org` padding) | Bits | Constants | Dispatch entries |
|---|---:|---:|---:|---:|---:|
| Configuration S | 1,452 | 1,492 | 41,776 | 15 x 64 | 11 x 25 bits |
| Configuration L | 1,609 | 1,649 | 46,172 | 15 x 64 | 13 |

Words per source: `main` 1, `key` 56, `rec` 191, `ping` 21, `keccak` 46, `hash` 65, `trng` 145, `slh` 307,
`life` 413, `sign` 207, `field` 157 (L only). Not re-synthesized: the stage 2 RTL's 455-word ROM is 42.6 µm² per word. With stage 5 still to come the image will reach about 2,000 words; the
micro-PC has 11 bits (`ARCHITECTURE.md` 5.5).

## Commands, routines and clocks

Clocks are counted by the interpreter from the dispatch to the idle point, with the link never stalling.
Unit counts are in `model/units.py`: Keccak-f 721, Keccak-p12 373 and the Poseidon2 permutation 3,074 are
measured on the existing RTL; a micro-instruction is 1 clock, plus 1 when it reads a row that was written in the
previous clock (by a store, as lane 24 of a permutation, or by a wipe of its class); `KMOV` is 2; the end action is 3. Estimates: field add and reduce (1 clock), FRAM
transfers (SCK = clk / 4), the PUF measurement (1,142,000 clocks: 252 quads × 4 rings × 3 measurements ×
15 µs, and a fixed-time decoder), TRNG counts (a ring period of 4.706 ns, the beat lengths of the modelled
ring spread). Signature figures are for 128s.

| Command | Case | Clocks | At 25 MHz |
|---|---|---:|---:|
| PING | | 15 | 0.6 µs |
| KECCAK | TurboSHAKE256, one block / each further block | 410 / 452 | 16 / 18 µs |
| | SHAKE256, one block / each further block | 758 / 800 | 30 / 32 µs |
| PRF_MSG | 32-byte payload (with the `SK.prf` derivation) | 1,169 | 47 µs |
| CTH | fixed part: `K_host` derivation, tag check, shape checks, header | 867 | 35 µs |
| | refused for a bad tag | 822 | 33 µs |
| | one F call (lane build + Keccak-f) | 748 | 29.9 µs |
| | one chain start (digit, `SK.seed` derivation, PRF call) | 1,150 | 46.0 µs |
| | WOTS public key, 35 chains (597 Keccak calls) | 432,875 | 17.3 ms |
| | WOTS signature, most steps / digits spread evenly (552 / 327 calls) | 399,269 / 231,417 | 16.0 / 9.3 ms |
| | 14 FORS leaves, secret / public | 16,870 / 27,267 | 0.68 / 1.09 ms |
| | counted chip: record tag, write, read-back | + 4,298 | + 0.17 ms |
| BOOT | blank chip | 2,446 | 0.1 ms |
| | to READY: verification 2.68 M, PUF 1.14 M, records | 3.83 M | 0.15 s |
| | leased: the same and TRNG start-up with one nonce (0.31 M) | 4,133,568 | 0.17 s |
| ENROL | TRNG start-up and nonce, PUF | 1,455,811 | 58 ms |
| COMMIT | verification, PUF, three record writes | 3,826,938 | 0.15 s |
| LEASE | one authority signature (2,569 Keccak calls) | 2,620,905 | 0.10 s |
| GATE | one authority signature (2,704 Keccak calls; 949,619 micro-instructions) | 2,718,597 | 0.11 s |
| | 3 of 5 | 8,094,277 | 0.32 s |
| | of which the fingerprint: 1,036 words folded, 422 micro-instructions per GF(2^64) product | 874,580 | 35 ms |
| P2 (L) | raw permutation | 3,149 | 0.13 ms |
| any | refused by the dispatcher | 3 | |

A verification's clocks depend on the signature (how many chain steps the digits leave); the bound is
about 4.1 M (`ARCHITECTURE.md` 4.3).

## Changes the RTL has to follow

The stage 2 RTL implements the stage-1 machine. Everything below is a change to an interface it
implements. The list with old and new values is `scratch/lanes/fable-dregg180-spec2.last.md`, "For the RTL
lane".

## Deviations from ARCHITECTURE.md

The specification was revised with this stage; these are the places where the model still differs from it
or decides something it leaves open.

1. **Counted keys and leases (3.4).** One counter, the use counter `u`; the lease is `(base, bound)` on it.
   Spend counters and the NFC counter have a row (record word 2) and no command.
2. **`CHECKPOINT`** (returning unused lease grants) is not specified and not modelled.
3. **Transitions (4.2).** `LEASE`, `EPOCH`, `RETIRE`, `ROTATE`. `MINT`, `LIMIT`, `RELEASE`, `INVOKE` are
   stage 5. `ROTATE` changes the authority root and the threshold; there is no verifier pin in S.
4. **Characterisation read-out (D13)** under an owner-root signature: not modelled; the model's `PNOISE`
   stands for its counters.
5. **Retirement.** A retired chip refuses `BOOT` with `E_RETIRED` after the PUF has run and the record has
   been authenticated; it holds no key afterwards.
6. **Failed boot.** `LOCKED` until reset, FAULT raised, nothing written. There is no failure counter
   (`ARCHITECTURE.md` 3.1 says why).
7. **`BOOT` is a host command** carrying the owner-root signature; the FRAM holds only the nine-word helper
   record.
8. **Equal sequence numbers** in the two slots (possible only for a forged-looking but authentic pair,
   which the chip itself never writes): slot 1 is kept.
9. **TRNG start-up bound.** A pair whose first 64 beats average more than 3,600 periods is abandoned; the
   specification says "after 4 ms". With every pair that slow, the start-up takes at most 3.6 M clocks.
10. **Signer scope**, `PRF_MSG` untagged, one counter for the whole key, the Hamming-distance-4 micro-PC
    and doubled decision bits not modelled: as in stage 1 (items 8, 12, 19, 21, 22 of the earlier list).
11. **Error codes.** `E_STATE` 14, `E_LEASE` 15, `E_PUF` 16, `E_RETIRED` 17, `E_ARG` 18 are new;
    `E_RECORD_IO` 9 replaces `E_ANCHOR_IO`; 6, 7 and 10 (`E_ANCHOR_EMPTY`, `E_ROLLBACK`, `E_KEYSET`) are no
    longer issued.

## What this model does not establish

- Nothing here is RTL, and the RTL in `rtl/` does not have these stages.
- The PUF and TRNG models are not the circuits. The BCH decoder is a Python function; the fixed-time
  decoder of the specification is hardware that does not exist in this form. The TRNG model's statistics
  follow the physics lane's table and nothing else.
- The FIPS 205 reference is this repository's own Python; equality with `crates/qsag-core` is untested.
- The fingerprint argument (4.3) is unreviewed. The tests show that a wrong stated value is refused in
  every position class tried, not that the bound holds.
- PUF, FRAM, field and TRNG clock counts are estimates.
- Vat, seal, NFC token, distance rounds, guards, the rest of the signer, the fault-injection sweep and
  self-test are not modelled.
- The taint rule is coarse: all lanes share one flag.
