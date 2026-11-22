# Dregg-180 architecture specification

Status: proposal for the owner's agreement. No RTL has been changed to match it. Where this document and
`README.md` disagree, `README.md` describes the RTL as it is and this document describes the target.
Stage 1 of section 9.3 (the executable model and its microcode) is in `v2/`, and so is the digital side of
stages 3 and 4 (boot, enrolment, lifecycle records, leases, the TRNG and PUF interfaces, signature
verification and the gate); `v2/README.md` lists each place where implementing them changed this document,
and those changes are already made below. The device-physics simulations of
`scratch/lanes/fable-efuse-and-process-sim.last.md` and `fable-physics-fixes.last.md` are integrated in 3,
4.3, 6.1, 6.5, 6.6 and 7; label **[S]** marks a figure simulated there.

Number labels used throughout:

- **[M]** measured: Yosys 0.69 flat synthesis, `gf180mcu_fd_sc_mcu7t5v0` TT 25 °C 5 V liberty, on `hbox` in
  container `dregg180-astra`, with the repository's own `synth/synth.sh`. Commands and logs are listed in
  `scratch/lanes/fable-dregg180-architecture.last.md`.
- **[E]** estimate, with the arithmetic or the measured figure it is scaled from.
- **[D]** derived by arithmetic from cited constants.
- **[C]** claim taken from a named file and not re-measured.

Areas are synthesized standard-cell area in µm² before buffering, clock tree, taps and fill. Throwaway
experiment RTL was synthesized for area only; none of it was simulated.

Contents: 1 uses · 2 trust model · 3 security state and lifecycle · 4 the verifier as gate · 5 datapath and
control · 6 organs · 7 budget · 8 verification plan · 9 migration and schedule · 10 decisions ·
11 configuration S, maximised · 12 microcode placement and the v3 shape · appendix A configuration L.

**Result in one paragraph.** The target is `SLOT_0P5X0P5` with chip-on-board packaging and the default pad
ring (owner decision; section 11). Configuration **S** is one 72-row register file, one lane-serial Keccak
unit, a word unit, a microcoded sequencer, an SPI link, and the PUF, NFC, distance, tamper and TRNG organs.
With the PUF array and the TRNG that the physics simulations require, the register file as the
physical-design lane has to build it, the control logic as the stage 2 RTL measures it, and the microcode
ROM at the size the model measures, S with every organ is about **1.02 M µm²** of synthesized cells. That
does not fit: the largest design placed legally in this slot is 0.89 M, the ceiling is about 0.92 M, and
nothing has been routed. Section 7.3 ranks what can give way. Without use U5 (distance bounding and the NFC
presence token) S is **0.93 M**, still about 23,000 µm² above the placed point after buffer repair; the rest
has to come from the sequencer's 64-bit data routing (7.1), or from the shield, or from the PUF, in that
order of preference (decision D14). The gate verifies, with the Keccak unit alone, either one authority
signature or `k` signatures of distinct members of a pinned committee (4.6); the verification is public
computation and needs no entropy source. On-chip verification of aggregate (Hem/WHIR) proofs needs a field
unit and about 76,000 µm² more and is not in S (11.3). The eFuse macros are not relied on for any bit: the
chip has no non-volatile state of its own, and section 3 states what follows from that. What can be taped
out in which run is section 9.4, which this revision did not re-examine. The larger-slot variant **L** is
appendix A.

---

## 1. Purpose and uses

Dregg-180 is a hardware root of trust for the qsag protocol suite. It holds secrets that an untrusted host
must not be able to read or use outside a policy, and it advances security state only on evidence it has
verified itself. The protocol roles below are taken from the crates named; "in scope" means this silicon
implements the chip-side operation.

| Use | Protocol role (source) | Chip operation | What the chip guarantees that host software cannot | Scope |
|---|---|---|---|---|
| U1 Signer | SLH-DSA-SHAKE, n = 16 (128s, 128f) and the WOTS+C / FORS operations of Baggy and Jorts (`crates/qsag-core/src/fips205.rs:452-530`, the four secret-touching oracles at `:3225-3290`) | `PRF`, `PRF_msg`, `H_msg` digits, WOTS chains and FORS leaves from `SK.seed`, `SK.prf` | The seed never leaves. Chain positions are chosen by the chip from a digest it computed, so no request can obtain a chain value below the one a valid signature publishes. This holds once the digest is computed on chip (stage 5); the model in `v2/` still takes a 16-byte message from the host | In |
| U2 Leaf-reuse guard | FTS `uses_completed` (`crates/qsag-fts`, `frontier.rs:11-13`: one use per key), Jorts BeltLatch epoch (`belt_latch.rs:1-30`) | Monotone counter bound to each one-time operation, committed before the secret-dependent output is released. The counter value is the key pair address the signer uses, so advancing it on one number and signing with another is refused. Whether a key is counted is a property of the key's address class fixed at provisioning, not a flag of the request: a signing request on a counted key always goes through the counter | A one-time key is used once, across resets and power loss: against host software always; against someone holding the board only on a leased chip (3.4) | In |
| U3 Capability vat | Capability tokens with attenuation (`crates/qsag-policy/src/macaroon.rs`; chip format `rtl/dregg_captp_vat.sv`) | Mint, attenuate, check and count invocations | The chip, not the bearer, decides whether a request is within rights, epoch, spend and guards | In |
| U4 Sealed share and gated release | Custodian share at rest for the MPC protocols of `qsag-quorum`, `qsag-hd`; classical scalar of `qsag-migrate` | Seal a blob under a device key; unseal to the host only on a gated transition | A share on disk is useless without this die and an authorised release; releases are counted | In (seal, release). The MPC itself runs on the host and is out of scope |
| U5 Presence and proximity | Not in any Rust crate; `paper/qsag.typ:765-766` and the RTL only | NFC presence token and distance bound as capability guards | A guarded invocation needs a fresh keyed token from a second device, or a timed keyed exchange | In, as guards of U3 |
| U6 Authorised state transition | Threshold signatures (Jorts, QS-B) and Hem aggregation (`crates/qsag-agg`) | Verify a statement and only then mint, raise a limit, release a key, advance the epoch or the lifecycle | A transition happens only if a pinned authority, or `k` distinct members of a pinned committee, signed that exact transition for this chip | In (section 4) |
| — | Credential presentation proofs (`qsag-cred`), CoZK migration proofs, MPC signing rounds | — | — | Out: host computations on public or shared data |

No host-side driver for the chip exists in `crates/` (searched; none found). The wire format and the host
library are part of the work in section 9.

---

## 2. Trust model

| Party | Trusted for | Not trusted for |
|---|---|---|
| The die | Everything inside the pad ring while powered and untampered | — |
| Owner root key | Authenticating enrolment, re-initialisation after a lost FRAM, and the read-out of the characterisation array. Its public-key digest is a mask constant (decision D3) | Nothing else at run time; it never sees a chip secret |
| Enrolment station | One session per chip, in state BLANK: it sees the PUF helper data and relays the owner root's signed choice of mode, policy and authority pin | Anything on its own: without the owner-root signature it can commit nothing |
| Authority | Policy: it signs transitions (section 4) and, for leased chips, issues the lease at each power-up (3.4). It is one key, possibly held by a threshold of custodians, or a committee of which `k` members must sign | Secrets: it never receives key material |
| Host, coprocessor mode | A host that holds `K_host` may request any U1 operation. `K_host` is derived from `K_dev` and released once, in the response to `COMMIT` | Reading any other key; changing lifecycle |
| Host, vat mode | Transport only. It is the bearer of capabilities | Confidentiality, integrity, choice of chain positions, time, counters, guard results |
| FRAM | Availability | Confidentiality, integrity, freshness. It is on the carrier board, outside the chip-on-board package: an attacker with board access can read it, rewrite it and restore an older image |
| NFC token, distance peer | Holding `K_tok`, derived for it at provisioning | Anything not carried under that key |
| Physical attacker | — | Assumed able to drive every pad, reset and power-cycle at will, glitch clock and supply, rewrite the FRAM, and run the chip from a rail that is back-powered through its signal pads (6.6). Invasive attacks on the powered die are addressed only by the tamper input, the shield and zeroisation |

**Two modes, chosen once.** The coprocessor role (the host with `K_host` is trusted to ask for signatures)
and the vat role (the host is an untrusted bearer) cannot hold on the same keys at the same time. The mode
is fixed at enrolment commit and carried in every lifecycle record (3.1):

- **COPROCESSOR**: every U1 request that releases a value derived from `SK.seed` (WOTS chains, FORS leaves,
  public-key generation included) carries a MAC under `K_host`. `PRF_msg` is not tagged: it releases only the
  randomiser that every signature publishes. Vat, guard and gate commands for capabilities are
  refused. `K_host` is a derivation from `K_dev`, released to the enrolment station once, in the response to `COMMIT`;
  the chip stores no key that a host supplied.
- **VAT**: `K_host` does not exist. Every secret-touching request, including public-key generation, needs a
  capability. Root capabilities are minted during enrolment or by a gated transition.

Everything else (U2, U4, U6, lifecycle) is the same in both modes.

---

## 3. Security state and lifecycle

The chip has no non-volatile state of its own. The eFuse macros in the PDK come from a compiler whose authors
describe them as not proven in silicon, and no programming conditions are published
(`scratch/lanes/sonnet-slot-price-and-efuse.last.md`). Electro-thermal simulation of the fuse and its drivers
[S, `scratch/lanes/fable-efuse-and-process-sim.last.md` A] adds that the array macro's programming margin is
1.0 to 1.25 at its weak corner and vanishes inside the model's uncertainty, and that the read circuit calls a
fuse blown only above 2 to 20 kΩ depending on corner, so a partly programmed fuse can read differently at
different corners. No security property below depends on a fuse, and none is fitted (decision D2). Every
bit that survives power loss is in the FRAM on the carrier board, outside the chip-on-board package. Section
3.4 states what that does and does not allow.

### 3.1 Where state lives

| State | Storage | Survives reset | Survives power loss | Cleared by |
|---|---|---|---|---|
| Device key `K_dev` (256 bit) | Four key rows, written at boot from the PUF response and the helper data after the check tag has matched | re-derived | re-derived | any reset, tamper, zeroise |
| `SK.seed`, `SK.prf`, `K_host`, `K_vat`, `K_seal`, `K_tok`, the record MAC key | Not stored. Each is a labelled TurboSHAKE256 derivation from `K_dev`, computed into the lanes when it is used and wiped with them at the end of the command. This costs one short Keccak call per use and saves six key rows (5.2) | re-derived | re-derived | every command end |
| Helper record, nine words: PUF syndromes, check tag (the public chip identifier), enrolment nonce, and the first record's commit word (mode, policy, threshold, generation, first use counter) and authority pin | FRAM, written once at `COMMIT`. The owner-root signature over it is public data that the host keeps and presents at every boot (3.3) | yes | yes | — (public, static, replayable by design) |
| Lifecycle record: `seq`, `gen`, mode, policy flags (leased, counted, mint lock, retired), threshold, use counter `u`, epoch, spend and NFC counters, authority pin (key, or committee root) | FRAM, two slots written alternately (the record with sequence number `s` goes to slot `s mod 2`), each with a 128-bit tag under `K_dev` in its own domain | yes | yes | superseded by a higher `seq` |
| The loaded record: the counters as the chip last advanced them | Volatile state rows. They are read from the FRAM once, at boot, and are the only copy the chip consults afterwards | no | no | reset |
| Session lease: nonce, upper bounds on `u` and spend for this power session | Volatile state rows | no | no | reset |
| Session state: gate verdict, transition register, guard results, working rows | Volatile, wiped by the epilogue of every command | no | no | every command end |

Nothing that authorises an action is a volatile bit whose reset value is permissive. After any reset the chip
holds no key and accepts only diagnostics and `BOOT` until boot (3.3) completes.

A count of failed PUF reconstructions, which an earlier draft kept in the lifecycle record, cannot exist: a
failed reconstruction yields no key, so the chip cannot authenticate a record update. A failed boot raises
FAULT and changes nothing; with fixed pairing, a fixed-time decoder and a constant-time tag compare it
reveals nothing that needs rationing.

### 3.2 States and allowed transitions

`BLANK` (no helper record) → `PROVISIONED`. Each power session starts in `RESET`, where only diagnostics and
the `BOOT` command decode, and goes `BOOT` → `READY`, or `BOOT` → `LEASE_PENDING` → `READY`, or `BOOT` →
`ORPHAN`, or `BOOT` → `BLANK`, or `BOOT` → `LOCKED_OUT`. The state is a register of the sequencer that only
instructions in the hardwired key range can write, and the dispatcher decodes each command only in the
states its table entry names (5.3). Retirement is a flag of the lifecycle record.

| From | To | Trigger | Condition | Effect |
|---|---|---|---|---|
| BLANK | BLANK (enrol session) | `ENROL` | No helper record; the TRNG passes its start-up and health tests (6.5), so a die without a working entropy source cannot be enrolled | PUF enrolment. The chip emits the syndromes, the check tag and a fresh nonce `N`. Nothing is written to the FRAM, no key is usable and nothing else is enabled |
| BLANK | PROVISIONED | `COMMIT` | In the same power session: an owner-root signature (4.3 routine, mask-constant key digest, D3) over `N`, the syndromes, the check tag, the mode, the policy flags and the first authority pin; the PUF reconstructed again from those syndromes and matching that tag; helper record and both lifecycle slots written and read back | First lifecycle records. The record never grants more than later ones: there is no enrolment-only privilege to return to. In coprocessor mode the response carries `K_host`. The chip then accepts only diagnostics until the next reset |
| PROVISIONED | BOOT → READY | `BOOT` after reset release | Helper record authentic under the owner-root signature the host presents; PUF reconstruction passes its check tag; a lifecycle record with a valid MAC exists; not retired; policy not leased | `K_dev` written; counters loaded |
| BOOT | LEASE_PENDING → READY | as above, policy leased; then `LEASE` | A gate statement (4.1) for transition `LEASE` over this session's nonce, the reported `seq`, the authority's `gen`, and the granted base and bounds | `u` and the spend counters jump to the granted base; they may not pass the granted bounds in this session. The nonce is cleared by the first attempt, accepted or not |
| BOOT | ORPHAN | `BOOT` | Helper record authentic, PUF reconstructed, no valid lifecycle record | Only `NONCE` and `REINIT` are accepted |
| ORPHAN | PROVISIONED | `REINIT` | Owner-root signature over a nonce drawn in this power session, the chip identifier and a new first record | New record with `gen` above any the owner has issued for this chip. The chip then accepts only diagnostics until the next reset |
| BOOT | BLANK | `BOOT` | The helper slot of the FRAM does not hold a helper record | `ENROL` and `COMMIT` are accepted |
| BOOT | LOCKED_OUT | `BOOT` | Any other check fails: owner signature, check tag, retired flag | Diagnostics only until the next reset. Nothing is written or erased, so a transient fault, a failed sensor or a noisy PUF read cannot brick the part |
| READY | READY | gated transitions of 4.2 | Gate verdict for that exact transition | Record updated, `seq` + 1 |
| READY | READY (retired) | `RETIRE` | gated | Retired flag set; the chip derives no keys at later boots |

`ENROL` is not usable by replay: erasing the FRAM and writing the original helper record back gives `ORPHAN`,
not an enrolment session, and `COMMIT` and `REINIT` need a signature over a nonce the chip drew in the same
power session. A chip whose FRAM is lost is useless until the owner root re-initialises it. `ENROL` writes
nothing to the FRAM, so an enrolment that is never committed leaves the chip `BLANK`; a `COMMIT` interrupted
after the helper record and before the lifecycle slots leaves it `ORPHAN`.

### 3.3 Boot

1. Reset releases on the pad clock (6.6). The chip is in `RESET`: diagnostics and `BOOT` only. No internal
   oscillator, sensor or the TRNG is needed up to step 5.
2. `BOOT` (a host command, because the owner-root signature is 16 kB of public data that the host carries
   more cheaply than the FRAM). The chip reads the helper record from the FRAM. No record: `BLANK`.
3. It verifies the owner-root signature over the helper record with the ROM routine of 4.3. The routine is
   public computation: no secret, no entropy. This happens before the PUF is touched.
4. Run the PUF with the authenticated syndromes, decode, compare the check tag in constant time (6.1).
   Write `K_dev` to its four key rows.
5. Read both lifecycle slots, verify each tag under `K_dev`, load the valid one with the larger `seq`. None:
   `ORPHAN`. Retired: the key rows are cleared and the chip is `LOCKED_OUT`.
6. Unleased policy: `READY`. Leased policy: start the TRNG (6.5), draw the session nonce, emit it with the
   chip identifier and `seq`, and wait in `LEASE_PENDING`. If the TRNG fails its tests the chip still enters
   `LEASE_PENDING`, without a nonce; `NONCE` tries again, and no lease can be accepted until it succeeds.

Time at 25 MHz: about 0.25 s to step 6 [E] (one signature verification at most 0.17 s [D], PUF 30 to 60 ms
[D, 6.1]); a lease adds the TRNG start-up (up to 0.12 s, 6.5), one gate verification (4.6) and the round trip
to the authority.

### 3.4 What is and is not guaranteed

The FRAM is on the chip's own SPI master and is not reachable by host software, but it sits on the carrier
board. Records are authentic (MAC under a PUF-derived key) and not fresh: the chip cannot tell the newest
authentic image from an older one after a power cycle. Within a power session the volatile high-water marks
make the counters monotone whatever the FRAM returns.

| Attacker | Unleased chip | Leased chip |
|---|---|---|
| Host software only | Every counter and limit is monotone; lifecycle transitions are one-way; no re-enrolment | Same |
| Board access: can read, rewrite and restore the FRAM and power-cycle at will | **Can** restore any earlier authentic image: counters, spend limits, epoch, mint lock, retirement and the authority pin return to their values in that image. One-time keys can then be used again, so the guarantee of use U2 does not hold against this attacker. **Cannot** forge a record, read a key, change the mode (every authentic record carries the same one), enrol or re-initialise | **Can** deny service and waste a lease. **Cannot** re-use any value of `u`, exceed the authority's ledger of spend, or resume under a superseded authority pin: the authority refuses a lease to a `gen` it has replaced, and bases never go backwards |
| The authority (or `k` committee members together) | Can authorise any gated transition | Same, and can refuse leases |
| Invasive attack on the powered die | Addressed only by the tamper input, the shield and zeroisation | Same |

How a lease closes rollback. The authority keeps, per chip, a ledger: the current `gen`, the next free value
of `u`, and the spend it has granted. A lease grants a range of `u` and an amount of spend starting at the
ledger values, and the ledger moves past them at once. The chip sets its counters to the granted base, so a
restored older image changes nothing: whatever the image said, the session starts where the authority says.
Values granted and not used are lost; an in-session `CHECKPOINT` report that returns them needs a
chip-to-authority authenticator and is not specified yet.

What a lease costs: the authority must be reachable at every power-up; the chip must have a working entropy
source, and it refuses to leave `LEASE_PENDING` if the TRNG health tests fail; the lease check is one more
decision that a fault must not flip (doubled decision bits, 5.5). An entropy source that is biased without
failing its health tests would allow an old lease to be replayed; the nonce therefore mixes two sources. The
TRNG's variance test bounds the jitter directly (6.5); interference near the beat rate is the case the second
source is for.

The entropy source is needed for exactly three things, all of them public nonces: enrolment, `REINIT`, and
the lease. An unleased chip that has been enrolled never needs it again: boot, the signer, and every gate
verification run without it. A leased chip whose TRNG has failed for good is unusable, since nothing else on
the die can make a lease fresh; that is the price of the policy and it is why the policy is chosen per chip.

The choice between the two policies is made per chip at `COMMIT` (decision D11). A chip that guards one-time
keys or spend limits against someone who may hold the board has to be leased.

No fuse backs any of this. What it would take to change that is known from the simulations [S, report
section A.7] and is not in S: every one-way bit stored as the OR of the eight fuses of one
`efuse_async_mem_1x8` macro (a single programmed fuse may read 0 at some corner with a probability budgeted
at 0.1 to 0.2 until silicon says otherwise), generations counted in unary, one programming pulse per fuse,
verification at the strictest read corner, and nothing in the programming path able to act while reset is
low on a back-powered rail (6.6). A generation counter of `n` steps is `n` macros of 8,075 µm². It is
revisited when the characterisation structure of 6.6 has been measured on silicon.

---

## 4. The verifier as gate

### 4.1 What is verified

A **transition** is a change of security state. The chip builds the transition message itself:

```
m = TurboSHAKE256( "DREGG.TR" ‖ chip_id ‖ (seq, gen, flags, threshold) ‖ type ‖ nonce ‖ arguments )[0..31]
```

`chip_id` is the 128-bit PUF check tag, public and fixed at enrolment; `seq` is the current record
counter, in one word with the generation, the policy flags and the threshold; the arguments are three words,
absorbed as they are; the nonce is the session nonce while a lease is pending and zero otherwise. `COMMIT` and `REINIT` have statements of the same shape under
their own labels (the enrolment nonce, syndromes, check tag and first record; the session nonce, chip
identifier and first record). The host never supplies `m`. A statement is accepted only for the `m` the chip computed, so it cannot be used on another
chip (`chip_id`), a second time (`seq` advances on acceptance), or for a different transition (`type`,
arguments). The verdict is a session register cleared by the command that consumes it.

Three statement forms are specified. All end in the same verdict register. G1 and G3 are in configuration S;
G2 needs option F (11.3).

- **G1, authority signature.** An SLH-DSA-SHAKE-128s signature (FIPS 205; `n = 16, h = 63, d = 7, a = 12,
  k = 14`, 7,856 bytes) on `m` under the authority public key pinned in the lifecycle record. The authority
  key may be held by a threshold of custodians; qsag's threshold signing produces an ordinary signature.
- **G3, committee threshold.** `k` SLH-DSA-SHAKE-128s signatures on `m` by distinct members of the committee
  whose Merkle root and threshold `k` are pinned in the lifecycle record (4.6). Keccak unit only.
- **G2, aggregate proof** (option F, or configuration L). A Hem proof (`crates/qsag-agg`) that at least `t`
  members of the committee with pinned root `committee_root` signed `m` (shared-message mode). Checked by the
  verifier machine of 4.4 under a pinned program.

### 4.2 Which transitions are gated

| Transition | Gated | Notes |
|---|---|---|
| `MINT` a root capability | yes | There is no ungated mint, in enrolment or after. `MINT`, `LIMIT`, `RELEASE` and `INVOKE` belong to the vat and the seal (stage 5); the model in `v2/` has `LEASE`, `EPOCH`, `RETIRE` and `ROTATE` |
| `LIMIT`: raise or re-arm a spend limit | yes | |
| `EPOCH`: advance the epoch counter | yes | Gives the epoch guard a source the host cannot choose |
| `RELEASE`: unseal a blob to the host (U4) | yes | Counted in the record |
| `INVOKE` under a capability with guard `G_PIN_VK` | yes, per invocation | Replaces today's `OP_VAT_ZK` |
| `LEASE` (leased chips, each power-up), `RETIRE`, `ROTATE` (change the authority or verifier pin) | yes | `ROTATE` raises `gen`; the authority refuses leases to a superseded `gen` |
| `COMMIT`, `REINIT`, characterisation read-out | owner root | Signature over a nonce drawn in the same power session (3.2) |
| Mint lock | no | One-way in the record; subject to 3.4 |
| Attenuation, ordinary invocation, U1 requests | no | Authorised by capability or `K_host` |

### 4.3 G1: cost and method

Verification is public computation on the Keccak unit and the word unit. No value in it is secret, and it
needs neither the TRNG nor `K_dev`: the same ROM routine verifies the owner-root signature at boot before
the PUF is touched, and every gate statement on a chip whose entropy source has failed.

Count per FIPS 205 [D]: FORS 14 × (1 leaf + 12 path nodes) = 182 calls; seven layers of at most 35 × 15 =
525 chain steps; 63 tree nodes; `T_k`, seven `T_len` and `H_msg`. Average about 2,100 calls, at most about
3,900, at about 760 clocks each.

`T_len` absorbs 35 chain ends over five sponge blocks while each chain needs the sponge for itself, and the
file holds one sponge state. Holding the chain ends would take 70 rows and saving the sponge 25. The routine
instead makes three passes over the 35 values, bound together by a two-row hash chain and a fingerprint:

1. **Pass 1, the signature values.** For each chain the chip computes the chain end `c_i` and extends a hash
   chain over them, `D ← TurboSHAKE256(D ‖ c_i)[0..15]`.
2. **Points.** `r_0, r_1 = TurboSHAKE256(D)` in its own domain. They are public, and they are fixed only
   after every chain end is.
3. **Pass 2a, the chain ends as the host states them.** The chip extends a second hash chain over the stated
   values, which must end in `D`, and folds each 64-bit word `w` into two accumulators,
   `a_j ← (a_j ⊕ w)·r_j` in GF(2^64).
4. **Pass 2b, the stated chain ends again.** The chip absorbs them into `T_len` and folds them the same
   way. The accumulators of 2a and 2b must be equal.

`T_k` over the 14 FORS roots is handled the same way. The product is a shift-and-XOR microroutine on the
word unit, most significant bit of the point first (422 clocks per product, measured on the model; 2,072
products per signature, 0.88 M clocks). It costs six rows in place of a second sponge, and no unit.

Why it is sound, and what that rests on. To make the chip absorb into `T_len` anything but the chain ends
it computed, the stated values must either differ from the computed ones under an equal hash chain (a second
preimage), or differ between passes 2a and 2b and still agree in both accumulators. The points are a hash of
the computed chain ends, so each choice of signature values succeeds in the second way with probability at
most (70 / 2^64)^2 < 2^-115, and the search is offline: about 2^115 trials of at least 35 chains each, which
is the cost of the generic attack on a 128-bit hash. An earlier draft drew secret points from the TRNG
conditioned with `K_dev`: per attempt that is the same bound with no offline search, but it made every
verification depend on the entropy source and on a key that does not exist before the PUF has run, and it
put key-derived data in rows the output rules treat as public. A third point (three more rows, half as many
products again) would take the bound to 2^-173. The argument needs review by a cryptographer before it is
relied on (stage 4 of section 9).

Data. The host sends, per signature: `R`; the FORS values; the 14 roots twice; and per layer the 35
signature values, the 35 chain ends twice and the authentication path: 2,018 words, 16,144 bytes, against
7,856 for the signature alone.

Rows used by one verification: digest and digit queue 4, address 3, `PK.seed` 2, current node 2, hash chain
and fingerprint 6, loop work 2; with a gate statement, its arguments 5 (the transition message is recomputed
from them for each signature, not stored). That is 24 scratch rows.

The public key is not held in rows. The host states it, the chip checks it against its pin before the
signature (the owner root's against a mask-constant digest, a committee member's against the pinned Merkle
root) and checks the root the signature leads to against the same pin afterwards; the single authority key
of G1 is the pin itself.

Time: at most about 4.1 M clocks, 0.16 s at 25 MHz [D: 3,900 calls at about 760 clocks, 530 short calls for
the hash chains and points, 0.88 M for the fingerprint]. One verification of a real 128s signature on the
model takes 2.7 M clocks (0.11 s; 2,648 Keccak calls), of which the fingerprint is a third.

### 4.4 G2: parameters, cost and how the program is pinned

G2 is not in configuration S. It needs a field unit: the digit-serial unit of option F (11.3) or the parallel
unit of configuration L (appendix A). The counts below are per proof; the clock columns are for the parallel
unit, and 7.4 gives the times for option F.

Parameters the chip must handle (regimes 7 and 8 of `crates/qsag-agg/src/pcs.rs:141-160`, the only ones
whose Merkle trees and transcript use Poseidon2; the default regime 4 hashes with cSHAKE256 and is not
supported):

- Field `p = 2^64 − 2^32 + 1`, extension degree 4. Poseidon2 width 12, rate 8, 4 + 22 + 4 rounds, `x^7`.
- 24 variables by default (`arithmetize.rs:215`), at most 28. Stages (blow-up, folded variables) at 24:
  (4, 6) (16, 4) (64, 3) (256, 3), final polynomial of 8 variables. Queries per stage 202 / 102 / 70 / 52 with
  16-bit proof of work (regime 7), or 216 / 109 / 74 / 56 without (regime 8). Two out-of-domain samples.

Work per proof at 24 variables, one committed polynomial [D, from the formulas of `recursion_census.rs:161-337`,
which exclude transcript and field arithmetic]:

| Item | Count | Clocks |
|---|---:|---:|
| Merkle node hashes, depths 20/18/17/16, no path sharing | 7,898 permutations | |
| Leaf hashes | 3,346 permutations | |
| Tree keys, roots, transcript, proof of work | about 800 permutations [E] | |
| Poseidon2 total | about 12,000 | 36.9 M at 3,074 each [M] |
| Fold arithmetic: 202·64 + 102·16 + 70·8 + 52·8 values | about 15,500 Ext4 products | 1.6 M at 105 each [M] |
| Sumchecks, final polynomial (256 coefficients), instruction overhead | | about 1.5 M [E] |
| **Total** | | **about 40 M: 1.6 s at 25 MHz** |

The proof is about 0.5 MB (480 kB measured for the default regime at 256 signers, `docs/PERFORMANCE.md:11`;
no size is recorded for regimes 7 and 8), which is 0.8 s of transfer at 5 Mbit/s and overlaps the computation.

**Working storage.** A query point of one stage is weighed against the fold challenges of all later stages,
so the 16 fold challenges (64 words) are needed before the transcript has produced them all. Configuration L
keeps them in 64 public rows. Option F does not store them: the host states the 16 challenges at the start,
the chip keeps a 4-word Poseidon2 digest of the stated vector, reads the vector again and re-hashes it at
each use, and when the transcript produces a challenge compares it with the stated one. Stated values never
enter the transcript. This costs about a third more permutations and has not been reviewed or checked
against the structure of the `qsag-agg` verifier.

**Pinning.** The verifier is a stream of instruction records supplied by the host (the existing record
format, `README.md` "Verifier VM"), because the constraint evaluation of the Hem relation is too large and too
likely to change to be put in ROM. Soundness then rests on four structural rules:

1. Every record header and immediate is folded into a digest under `K_dig`. The verdict is set only if, at the
   end of the stream, the digest equals the verifier pin in the lifecycle record. The pin is written at
   enrolment or by `ROTATE`. A program that does not match the pin cannot set the verdict.
2. The public inputs do not come from the stream. `BIND_M` absorbs the chip's `m`; `BIND_ROOT` absorbs the
   pinned `committee_root`; `ASSERT_COUNT_GE` checks the signer bitmap weight against the pinned threshold.
3. The machine is straight-line: no instruction branches on host data, a failed assertion is sticky, proof
   words must be canonical, and Merkle indices are bound to transcript output (`BIND_IDX`, as today).
4. No instruction can move a register to the output. The response is a fixed status word.

Not yet existing and required before G2 can be claimed: the compiler from the `qsag-agg` verifier to a
record stream (`README.md:467` says so), and an end-to-end test on a real regime-7 proof. Whether the Hem
instance binds the signed message in a form the chip can reproduce (`signing_mode_digest`, a cSHAKE256 value,
`arithmetize.rs:411`) was read but not tested; the chip computes it on the Keccak unit before the stream starts.

### 4.5 What configuration S enforces without G2

With G1 the chip trusts the holders of one authority key; a threshold exists only in how that key is held.
With G3 the chip itself checks that `k` distinct members of a pinned committee signed. What S does not have
is a proof whose size and checking time are independent of the committee, and a general proof checker.

### 4.6 G3: committee threshold on the Keccak unit

- **Committee.** `n` members, each with an SLH-DSA-SHAKE-128s public key (`PK.seed ‖ PK.root`, 32 bytes).
  Leaf `i` is `TurboSHAKE256(i ‖ pk_i)` and a node is `TurboSHAKE256(left ‖ right)`, 16 bytes each, with
  distinct domain bytes for leaf and node. The root and the threshold `k` are the authority pin in the
  lifecycle record, set at `COMMIT` or by `ROTATE`; the depth is whatever path the host presents, at most
  16. A single authority key (G1) is the committee of one member with an empty path, so G1 and G3 are one
  routine. Sixteen-byte nodes give 128 bits against presenting a key that is not in the tree, the same
  level as the signatures; they give 64 bits against whoever builds the tree making two trees with one
  root, and that party is the authority itself. The owner root's mask constant is the same leaf hash.
- **Statement.** For the transition message `m` of 4.1, the host supplies `k` items in strictly increasing
  member index: index, public key, Merkle path, signature on `m` (with the stated values of 4.3), and the
  Merkle path again. For each the chip recomputes the root from the leaf and path and compares it with the
  pin, runs the 4.3 routine under that public key, recomputes the root from the leaf made of the stated
  `PK.seed` and the root the signature led to, and counts. The verdict is set when the count reaches `k`.
  Increasing indices make the members distinct with one row.
- **Cost.** Per member one verification (at most about 0.16 s, 0.11 s typical; 7.4) and
  16,144 + 40 + 32 × depth bytes.

| Committee | Time, at most | Data |
|---|---:|---:|
| 3 of 5 | 0.5 s (0.32 s measured on the model) | 49 kB |
| 11 of 16 | 1.8 s | 0.18 MB |
| 67 of 100 | 11 s | 1.1 MB |
| 171 of 256 | 28 s | 2.8 MB |

- **What it enforces.** At least `k` distinct holders of committee keys signed exactly this transition, for
  this chip and this sequence number. Members sign ordinary FIPS 205 signatures with existing code.
- **What it needs that does not exist.** A host driver in the protocol crates (`v2/model/host.py` has the
  committee tree, the statement builder and the packaging of a signature with its stated values, in Python).
  No compiler, no new cryptographic argument beyond the fingerprint of 4.3.
- **Cheaper member keys.** A member key that is a single XMSS tree (one layer of the same structure, stateful
  on the member's side) verifies in about 20 ms with a signature under 1 kB, using a subset of the same
  routine. Not specified further here.

---

## 5. Datapath and control

### 5.1 Principle

One 64-bit register file holds every word of working state and the device key. Four arithmetic units read one
row at a time through a single read port and write through a single hold register. One microcoded sequencer
drives them. No unit and no organ keeps a private copy of secret state beyond pipeline registers.

Word width is 64 bits: a Keccak lane, a Goldilocks element and half a GF(2^128) element.

### 5.2 Register file

- Rows of 64 `latrnq_1`, one `icgtp_1` per row, one 64-bit write-hold register, one read port.
  Measured [M]: 64 rows 263,672; 72 rows 296,497; 80 rows 328,657; 128 rows 550,122 (about 4,110 per row, of
  which 3,091 is latches), with the read multiplexer inferred by synthesis. Built as the placed array that
  the physical design needs (one 64-bit word per standard-cell row, row-local read gates and a column tree,
  word-line drivers sized for 64 loads), 72 rows are 329,434 [M, `scratch/lanes/fable-dregg180-phys.last.md`]:
  about 4,575 per row. That is the figure the budget uses. A second read port costs 85,666 at 96 rows [M]
  and is not used.
- A foundry SRAM is not used: `gf180mcu_fd_ip_sram__sram512x8m8wm1` is 431.86 × 484.88 µm = 209,400 µm² for
  4,096 bits (LEF), no smaller than latches, byte-wide, and it cannot be cleared with the clock stopped.
- **Zeroisation.** The asynchronous clear of every latch and of the hold register is driven only by a
  flop-registered secret-reset net (pad reset, tamper latch, zeroise request). It acts with the clock stopped.
  Command-level wiping goes through the write path.
- **Two-phase discipline.** The hold register captures on the rising edge; the addressed row is transparent
  during the following high phase and closed at the falling edge. A row is never read in the cycle in which it
  is transparent. The sequencer enforces this and an assertion checks it. Borrowing through the row is limited
  to 15 % of the period in the SDC, as today.

Row map:

| Rows | Count | Class | Contents |
|---|---:|---|---|
| lanes | 25 | working, secret-capable | Keccak state; Poseidon2 state and verifier registers share these rows |
| Keccak work | 7 | working | Column parities and saved lanes of the lane-serial unit (today private to it) |
| scratch | 24 | working, public | Staging, capability words, the hash chain and fingerprint of 4.3. The signer uses 12; a gate statement uses all 24 (4.3) |
| keys | 4 | key | `K_dev`. Every other key is derived from it into the lanes when it is used (3.1) |
| state | 10 | public, kept between commands | The loaded lifecycle record 3 (sequence, generation, flags and threshold; use counter and epoch; spend and NFC counters), authority root 2, PUF check tag 2 (the chip identifier), session nonce 2, lease bound 1 |
| out | 2 | output | Egress FIFO; the only rows the egress mux can read |
| **S total** | **72** | | |

The count is unchanged from the previous revision and its use is not: six key rows became four scratch rows
and two state rows, and the pin rows are state rows like the others. Configuration L (appendix A) adds public challenge rows up to a 128-row file. The model
in `v2/` has this map.

### 5.3 Structural output bound

Decoder and sequencer rules, independent of the ROM contents (implemented and tested in `v2/model/machine.py`,
`v2/tests/test_output_bound.py`):

- The egress multiplexer is wired to the two `out` rows and nothing else. `out` rows are not addressable; they
  are written only by the `PUSH` micro-operation.
- The response header is issued by one `HDR` micro-operation per command. Its length is at most a cap constant
  in that instruction; a hardware counter stops the egress at the declared length and pads a short response
  to it.
- Key rows are read only by `KMOV` (key row to a rate lane) and written only by `KEYWR`, which the decoder
  accepts only while the micro-program counter is inside the boot and enrolment address range (two hardwired
  comparators). `KMOV` clears the hold register.
- While a key has been copied into the lanes and no permutation has run since, a lane is read only by an XOR
  that stores back to the same lane, and the hold register is cleared afterwards. `PUSH` is refused.
- From the first `KMOV` until the command ends, the capacity lanes (17–24) are never read by the word unit,
  so a keyed sponge state cannot be read out whole. The Keccak work rows are never read by the word unit.
- Every command ends in one shared epilogue that clears all working rows. The sequencer cannot return to idle
  by any other address, and the epilogue is entered only at its first word.

Rules added after the review of the stage-1 model (`scratch/lanes/sonnet-audit-dregg180-v2-stage1.last.md`),
now implemented and tested in `v2/` (rules R5 to R12 of `v2/model/machine.py`):

- **Derived secrets do not leave the lanes or steer control.** Four taint flags: the lanes as a group, the
  hold register, the compare flag and the carry. A key copied into the lanes taints them until all lanes are
  wiped. A tainted hold register is stored only to a lane or a key row, so scratch rows, the index register
  and the loop counters never hold key-derived data. A tainted value cannot be pushed, set the response
  length, a loop count or the index register, choose a FRAM slot, or decide a branch.
- **Three declassification points**, each an instruction of its own and each listed per instance in the
  output manifest: `REL` (a rate lane after a permutation, to the response); `CMPT` (an untainted word
  compared with a rate lane after a permutation; only the verdict leaves); and the record tag written to the
  FRAM. Stages 3 and 4 added instances (the check tag and `K_host` at enrolment; the tag verdicts of boot)
  and no new kind.
- **The FRAM master is an output too.** FRAM instructions decode only inside the address range of the
  record routines. A write sends a state row, or lane 0 or 1 after a permutation. A transaction is at
  most sixteen words in one direction, to one of three records.
- **One hold register.** The Keccak unit writes through it and a pushed row passes through it, so H is
  cleared by a permutation and by `PUSH row` and `REL`. A row written in one clock (by a store, as the last
  lane of a permutation, or by a wipe of its class) is transparent in the next, and reading it then costs a
  clock. A command starts only at an address in the ordinary code; the dispatcher checks the table entry.
  Undefined function codes are control faults.
- **A fault cuts the response short.** Words already pushed have left the chip; the frame then holds fewer
  words than its header states and FAULT is raised. A host treats a short frame as no response.
- **The ranges are hardwired.** Idle address, key range and record range are constants of the sequencer,
  not data read from the ROM image; the build fails if the image does not match them. Padding, the wipe of
  every working row and the return to idle are one hardware end action (`END`, `FAIL`), not ROM content.
- **Dispatch is gated by lifecycle state** (3.2): every dispatch-table entry carries the set of states in
  which its command decodes, and the dispatcher itself refuses bad magic and unknown opcodes. The state
  register is written only by an instruction of the key range, and `READY` only with the verdict latch set.
- **Key writes need a verdict.** The key-write instruction needs a latch that one instruction of the key
  range sets from an untainted, clear compare flag in the same command: in the ROM, the PUF check-tag
  compare.
- **Lifecycle state is written in one place.** State rows are written only by instructions in the record
  range, which is also the only place the FRAM master can be driven. A FRAM write sends a state row, or
  the record tag.
- **The PUF's response is a key.** It leaves its organ only into a rate lane, under the rules of a key row;
  the organ's instructions decode only in the key range. The syndromes are public by construction and are
  the one thing the organ gives the word unit.

What these rules cannot decide is listed in `v2/README.md`: chiefly, which hash output a routine releases.

Which hash output a routine emits is a property of the ROM image: every `PUSH` in the image is listed, with
its source row and reason, in a reviewed manifest that a script compares with the image (8.2).

So no command can read state it did not compute for output, and this is checked on a small machine rather
than argued per command.

### 5.4 Units

| Unit | Function | Source | Area | Clocks |
|---|---|---|---:|---|
| Keccak | Keccak-f[1600] and Keccak-p[1600,12], lane-serial, in place | `qsag_keccak_serial`, unchanged | 112,280 alone [M], of which 21,630 is rows that move into the file | 721 / 373 [M] |
| Goldilocks, parallel (configuration L only) | Multiply-accumulate, canonical reduction, Poseidon2 round, Ext4 | `qsag_gl64_karatsuba_csa`, unchanged | 241,580 [M] | product 3; Poseidon2 3,074; Ext4 product 105 [M] |
| Goldilocks, digit-serial (option F, not in S) | One accumulator: load, add, subtract, double, and multiply by the register-file row, most significant multiplier bit first; the multiplicand stays on the read port | new | 37,801 / 57,211 / 92,376 for 1 / 2 / 4 multiplier bits per clock [M, skeletons, not simulated] | product 64 / 32 / 16; Poseidon2 about 36,000 / 21,000 / 14,000 [D] |
| Field micro-sequencer and constants (L); constants only (option F, sequencing in microcode) | Poseidon2 permutation, Ext4 operations; round constants | `qsag_field_engine` 14,618, `qsag_p2_rc` 19,691 [M] | 34,309 (L); 19,691 (F) | — |
| GF(2^128) (configuration L only; in S the fingerprint is microcode on the word unit) | 128-bit carry-less multiply-accumulate, 2 bits per clock | `qsag_gf128_clmul`, unchanged | 48,545 [M] | 64 per product |
| Word unit | XOR, AND, OR, 32-bit add and subtract with carry, constant-time compare accumulator, 16-bit immediates; wiring functions on the hold register: nibble swap, byte reversal of each half, half swap, half masks, shifts right by 1, 4, 8, 16 and left by 1, 4, 8; for the fingerprint of 4.3, a left shift by one that puts the bit shifted out in the carry, and multiplication by x in GF(2^64) (a shift and four conditional XORs) | new | 34,329 [M, skeleton without the two fingerprint functions, which add about 700 E; an earlier skeleton without the wiring functions was 23,594] | 1 |

Earlier digit-serial skeletons with their own operand registers and one reduction per function were far larger
(4 bits 89,083; 8 bits 103,802; 16 bits 139,683 [M]); sharing one add-fold-subtract path among all functions
and taking the multiplicand from the read port is what brings the unit to 37,801. Its add, fold and
conditional-subtract chain is three 64-bit additions deep; whether that meets 40 ns is not known.

A round-per-clock Keccak (state in 1,600 `dffrnq_1`) measures 342,265 [M]. It does not fit S. It would cut a
hash call from about 760 clocks to about 40 [E] (appendix A).

Scheduling of each primitive:

| Primitive | Schedule |
|---|---|
| TurboSHAKE256, SHAKE256, cSHAKE256 | Microcode absorbs words into the lane rows through the word unit, starts the Keccak unit, moves rate lanes to `out` or to key rows |
| WOTS chain, FORS leaf | Microroutine: build `PK.seed ‖ ADRS ‖ value` in the lanes, permute, repeat for the count the chip derived |
| Keyed MAC (request tags, FRAM record, NFC token, seals) | TurboSHAKE256 with the key row absorbed first; the tag is compared through the word unit's accumulator |
| Poseidon2, Ext4 (option F, L) | L: field micro-sequencer on the parallel unit over lane rows 0–11 and the verifier registers. Option F: microroutines on the digit-serial unit |
| Merkle (Canopy) path (option F, L) | Microroutine: one permutation per level with the feed-forward; index bits from a transcript-bound register |
| Committee Merkle path (G3) | Microroutine: one TurboSHAKE256 call per level |
| Fingerprint (4.3) | Two points, two accumulators and the saved pair of the earlier pass in six scratch rows; shift-and-XOR product in microcode on the word unit |
| Key derivation on use | Microroutine: `K_dev` and a label into the lanes, one Keccak-p[1600,12] call; the result stays in the lanes |
| TRNG health tests and conditioning (6.5) | Microcode compares the organ's statistics with constants of the ROM and absorbs the raw words |

### 5.5 Control

A microprogram ROM and a sequencer replace the 124-state process of `rtl/qsag_wire_engine.sv:1227-1758`.

- **Micro-instruction** (28 bits in S and in L; layout in `v2/README.md`): 5-bit operation, two 7-bit row
  fields, a 4-bit field (store and immediate flags, or the low bits of a branch target), two index bits
  (row + index register X), a post-increment bit for X, 2-bit sequencing (next, return). Branch, call,
  compare-X and decrement-and-branch are instructions with an 11-bit target. Immediates are 16 bits; 64-bit
  constants come from a small table beside the ROM.
- **Sequencer**: 11-bit micro-PC, a 28-bit step counter as runaway guard (a statement of 256 members is
  about 2^27.4 micro-instructions), four-entry return stack (signature verification nests four deep; two
  entries served the signer), two 12-bit down counters, 7-bit index register X, response-length counter, the
  rule comparators of 5.3, the lifecycle state register, opcode dispatch gated by it. Skeleton of the
  sequencer as first modelled: 23,985 [M].
- **ROM size.** Estimated routine sizes in micro-words: boot and lifecycle 150, framing and epilogue 80,
  enrolment 180, sponge and MAC subroutines 90, signer 160, G1 160, vat 150, transitions 100, FRAM 80, seal 60,
  NFC 40, distance 60, self-test and diagnostics 80, TRNG 30: about 1,420 for S; plus about 500 for the
  verifier machine in L. Stage 1 wrote the first four of these that it needs (framing, sponge, signer without
  `H_msg` and root tagging, FRAM) in 356 words against 330 estimated (sponge 46, signer 264 against 160, FRAM
  46), plus 58 for a provisioning stand-in and 18 for PING and error exits; framing and the epilogue became
  hardware. With the rest of the signer the S estimate is about 1,500 words [E] against 1,536
  budgeted. ROM cost: an earlier stage-1 image with its constant and dispatch tables was 19,072 for 418 words (S)
  and 24,981 for 575 words (L) [M], 45.6 and 43.4 per word; random content measured 85,024 for 1,536 × 28 [M]. With the committee gate, the fingerprint microroutine, leases and the owner-root routines the
  S estimate was about 1,700 words [E]. **Measured since:** the image with the signer, boot, enrolment,
  records, leases, the TRNG tests, signature verification and the gate is 1,443 words (key range 55, record
  routines 191, TRNG 141, verification 307, lifecycle and gate 409, signer 207, sponge and shared hashing
  111, the rest 22). Still to come: vat about 150, the transitions that belong to it 100, seal 60, NFC 40,
  distance 60, self-test and diagnostics 80, the rest of the signer about 100 [E]: about 2,030 words with
  every organ, 1,930 without U5. Budgeted: 2,000 words at 42.6 = 85,200 [E, the density of the stage 2 RTL's
  455-word ROM]. Two consequences: the micro-PC is 11 bits, so 2,048 words is a hard limit that the full
  image would touch, and a twelfth bit changes the branch encoding; and the routines written so far have not
  been optimised for size, which is the first place to look. Option F adds about 400 words and does not
  fit the 11-bit micro-PC.
- Inner loops with fixed structure stay hardwired in their units (Keccak round sequencing, Poseidon2 and Ext4
  in the field micro-sequencer). They are already tested and are denser than microcode.
- **Host-supplied programs.** None in S. With option F, or in L, only the verifier machine of 4.4 accepts host
  records, under its four rules.
- The micro-PC keeps the Hamming-distance-4 check of today's state register. The decision bits (gate verdict,
  MAC result, lifecycle allow) are each stored twice with opposite polarity and compared at use.

### 5.6 Clocked and asynchronous parts

One core clock. The SPI shifter runs on SCK and hands whole words to the core through a two-word
handshake FIFO; the diagnostic read answers on SCK alone, as today. The NFC receiver runs on the recovered
carrier clock and hands over whole frames. Asynchronous logic is limited to: the reset and tamper latch,
the PUF and TRNG rings with their ripple counters, the distance responder path, and the Vernier chain. The
source-synchronous and clockless links are removed (decision D4).

---

## 6. Organs

Each organ exposes start, done and word-transfer signals to the sequencer and keeps no secret outside the
register file except where noted. "Lock" means that an authentic helper record exists (the chip is not
`BLANK`, 3.2). Because that condition can be undone by erasing the FRAM, no test hook that could expose key
material is tied to it. A sensor or source that fails (TRNG, PUF read, clock monitor) refuses the commands
that need it and changes no stored state; none of them is on the path of an unleased boot except the PUF
itself.

### 6.1 PUF and key derivation

- **Array.** 252 disjoint quads of adjacent ring oscillators in one row (1,008 rings), one ring enabled at a
  time on one counter. One response bit per quad: the sign of (c1 + c4) − (c2 + c3), the four counts taken in
  slot order. The comparison cancels any offset that alternates between neighbouring slots and any linear
  gradient, in space and, measured in that order, in time. Every ring is one slot (enable buffer, five
  `nand2_1`, output buffer, well tap: 24.08 × 3.92 µm) with ring nets routed from one template, dummy slots
  at the row ends and dummy rows above and below. The rules are
  `physics/puf/placement_requirements.md` (R0 to R5) and are part of this specification.
- **Why not pairs.** The array of the previous revision (252 pairs, the two rings of a pair in mirrored rows,
  ring nets left to the router, the ring node itself routed to the multiplexer) supports no entropy claim
  [S, `scratch/lanes/fable-physics-fixes.last.md` 2]. The random spread of a pair is 0.258 % of frequency; a
  filler cell beside one ring moves it by 0.14 %, a row end by 0.24 %, a micrometre of wire by more, and
  h = 0.95 needs every such layout-determined difference below 0.011 % (6 aF on one ring node, 0.8 mV of
  supply). Pairs in one row under the same rules, with five blocks, are the smaller fallback: 630 rings and
  a claim of h = 0.90, which needs the total offset under 0.023 % of frequency and cannot be defended before
  the gradient across the field has been measured on silicon (7.3, decision D6).
- **Entropy account.** Four BCH(63,36,5) blocks in the syndrome (code-offset) construction, fixed grouping,
  no selection mask. Each block publishes 27 syndrome bits. With min-entropy `h` per response bit the
  remainder is 4 × (63·h − 27): 144 bits at h = 1, **131 bits at h = 0.95**, 119 at h = 0.90 [D]. The claim
  is 128 bits and holds for h ≥ 0.94. Three blocks (756 rings) give 98 bits at h = 0.95.
- **What h rests on.** The foundry mismatch model gives h = 1 for any layout, so Monte Carlo cannot confirm
  h; it gives the spread (quad 0.368 % of frequency [S]). h is set by offsets that are the same on every
  die and therefore known to an attacker; 0.95 needs them below 0.044 of the spread. With the quad
  comparison the claim rests on second-order terms only: curvature above 10 %/mm², or a difference between
  the inner and outer slots of a quad that the dummies do not remove [S, `puf/puf_budget.py`]. It is
  confirmed before tape-out by extraction of the placed and routed array (R5: 6 aF per node of the quad
  combination, 0.011 % of frequency per quad, 0.2 mV of supply), and checked on silicon by the
  characterisation array. What silicon can and cannot confirm: a run of 1,000 dies with 16 characterised
  quads resolves an offset common to all positions to 0.024 of the spread, and an offset of one position to
  about 0.1 (h about 0.89), and it measures the characterised positions, not the 252 that make the key.
  The per-position claim therefore rests on the extraction and on the two arrays being built identically;
  the lot statistics can refute it, not prove it. If the upper 99 % bound of the measured offset gives
  h below 0.94, the key-length claim is reduced to 4 × (63·h − 27); it is not waved through.
- **Reliability.** Each bit is the majority of three measurements of its quad; a measurement is four count
  windows of 10–20 µs [C, `astra-dregg180-spice-pcb.last.md`], so enrolment and each reconstruction take 30
  to 60 ms [D]. Rings must be slowed or prescaled so the first counter stage sees at most 400 MHz at the fast
  corner; the measured 400–1,120 MHz range [C] is too fast for an unproven toggle stage. Not established:
  the bit error rate across temperature and supply. The code was chosen without one, and five errors in 63
  bits per block is the whole budget; it must be simulated (ring temperature and supply coefficients with
  mismatch) before the block count is final.
- **Helper data before use.** The helper record is authenticated by the owner-root signature in boot step 3,
  before the PUF runs. After decoding, the check tag `TurboSHAKE256("DREGG.PUFCHK" ‖ w)` is compared in
  constant time before any key row is written. The decoder runs a fixed number of clocks whatever the error
  pattern. With fixed grouping and no mask, a rejected attempt reveals nothing about a bit's value.
- **Key.** `K_dev = TurboSHAKE256("DREGG.KDEV" ‖ w ‖ enrolment nonce)`. All other keys are labelled
  derivations, made when they are used (3.1).
- **Test hooks.** No ring of the key array has a path to a pad in any state, and there is no injected-flip
  input: a hook gated by lifecycle could be re-opened by erasing the FRAM, and ring frequencies with the
  helper data give the key. Silicon characterisation uses a separate array of at least 16 quads, built from
  the same slots in the same block under the same rules, that feeds no key; its counts are read out only
  under an owner-root signature over a fresh nonce (decision D13). The lot qualification it supports
  (per-die: all its ring counts, three windows each, at two supply voltages; per lot: mean and spread of the
  quad combination and of the plain pair differences per position, Hamming distance between dies,
  correlation of neighbouring bits) is station software, specified in the physics report section 2.5. It
  is also the second noise source of the nonces (6.5).
- **Needs from the datapath:** Keccak (KDF, tag) and the lanes; no scratch row. **Private area:** array with
  its dummies 116,300 [M, slot geometry as placed by `v2/phys/floorplan/puf_array.tcl`: 1,008 used and 224
  dummy slots in a 674 × 172.5 µm box, with a 20 µm keep-out]; characterisation quads 6,500 [E]; enable
  decode and output collection for 1,072 rings about 26,800 [E, 25 per ring; the old array figure of 87.5
  per ring included its own, the slot does not]; counters, BCH decoder and control about 70,000 [E, from the
  existing leaf's 76,551 M less its 64 rings]. Total about 219,600, against 118,000 before. The physics report
  put the growth at 51,000; it counted neither the dummies its own rules require nor the selection logic.

### 6.2 NFC front end and presence token

- Receiver for 13.56 MHz ASK frames with load-modulation acknowledge (existing). CRC16 is kept for framing only.
- **Token.** `ctr (32) ‖ bind (64) ‖ tag (128)`, `tag = TurboSHAKE256(K_tok ‖ ctr ‖ bind)`. `bind` is the low
  64 bits of the digest of the request being authorised. `ctr` must exceed the last accepted value, which is
  kept in the lifecycle record. A token is consumed by one invocation and cleared at command end.
- The NCO (carrier, FSK, chirp) has no protocol role in the repository and is not in configuration S
  (decision D7). It is 25,940 µm² of the existing leaf [M].
- **Needs:** Keccak, word unit. **Private area:** 28,729 [M, existing leaf synthesized with the NCO inputs
  tied off] plus about 6,000 for the longer frame [E]. **Test hooks:** none.

### 6.3 Distance bounding and TDC

- **Roles.** Prover: the chip answers 64 rapid challenges; an external verifier times them. Verifier: the chip
  challenges a token and times the answers.
- **Keyed bits.** Both response registers are loaded by microcode from `TurboSHAKE256(K_tok ‖ N_V ‖ N_P)`.
  The host cannot load them.
- **Validity.** As verifier, the chip sets `dist_ok` for the current request only if every round returned the
  expected bit within the limit in the capability. `dist_ok` is a session bit cleared at command end.
  Calibration is a separate command that writes a diagnostic register and cannot set `dist_ok`.
- **Fast path.** Pad 13 → capture latch → select → pad 14 is one placed block next to those pads, kept out of
  synthesis optimisation and out of clock-tree synthesis. Its delay is dominated by the pads: 2.4–6.2 ns across
  corners [C, same SPICE report]. The 4.8 ns constraint in the SDC cannot be met at the slow corner and is
  replaced by 6.5 ns; the 3.8 ns spread is a distance uncertainty of about 0.6 m that a verifier must budget.
- **Timer.** Range at least 100 ns, resolution at most 0.5 ns, calibrated against the pad clock: a gated ring
  count for the coarse part and the existing 32-tap chain for the fine part.
- **Needs:** Keccak. **Private area:** 44,593 [M, existing leaf]. **Test hooks:** calibration only, as above.

### 6.4 Tamper, shield, glitch sensors

- Tamper input, blanking and the secret-reset latch as today. The tamper input is armed only once the chip
  has booted from an authentic helper record, so an unbonded pad cannot kill a blank part.
- The shield becomes a real net: a serpentine on the top metal over the register file and key rows, driven and
  checked by the existing canary logic, with the route fixed in the floorplan script. Today's chain of sixteen
  buffers has no routing constraint and is not a shield.
- Sensors are armed by the lifecycle (not `BLANK`), not by a host-writable register. A sensor event clears
  secrets and raises FAULT; it changes no stored state, so the part boots again after a reset.

### 6.5 TRNG

The existing design (a divided 13-stage ring sampling a 7-stage ring) yields about 0.005 bit of min-entropy
per raw bit from thermal jitter, not the 0.5 its header claims: 2.6 bits in the 512 raw bits a nonce
conditions [S, transient-noise simulation, kappa = 5.3e-9 √s]. Its repetition-count and adaptive-proportion
tests pass on a noise-free source, because the beat of two incommensurate rings looks balanced. It is
replaced.

- **Source.** Coherent sampling: 8 rings of 17 `nand2_1` in the same template-routed slots as the PUF rings,
  in one row. A selected pair runs, one ring sampling the other; a counter measures each beat in ring
  periods; the least significant bit of each count is the raw bit. 64 to 425 kbit/s [S].
- **Claim.** 0.5 bit of min-entropy per count for a pair whose count-variance statistic V is at least 2.0
  when it is selected. The stochastic model gives at least 0.93 for such a pair [S, `trng/coso_model.py`];
  the factor of two is the margin for what the model leaves out, chiefly flicker noise.
- **Start-up**, on first use in a power session and never at boot: for each candidate pair 256 counts (a pair
  is abandoned after 4 ms); pairs with V ≥ 2.0 and a mean count between 400 and 3,600 qualify; the qualifying
  pair with the smallest mean count is used; then 1,024 counts under the health tests. At most 0.12 s.
- **Health tests**, over every 256 consecutive counts: H1, V below 1.25 twice in a row (loss of jitter: a
  noise-free pair gives at most 0.33 [S]); H2, 2^14 sampling periods without a beat, or a count below 64
  (locked or stuck rings); H3, the same statistic on sums of four counts above 8 V, where white noise gives
  4 V (jitter that is slow or periodic and not thermal); H4, repetition count and adaptive proportion on
  the raw bit, as today. The organ accumulates the statistics; the thresholds, the selection and what
  happens on a failure are microcode, in the ROM. H3 is designed from the scaling of white and correlated
  noise and has not been simulated: its false-alarm rate is unknown, and it can refuse a lease, so its
  threshold is provisional until it has been simulated with the foundry flicker model or measured.
- **On a failure** the routine runs the start-up once more and tries again; if that fails too, the command
  that asked is refused with a status bit and nothing else changes. What can be refused is listed in 3.4:
  enrolment, `REINIT`, and the lease nonce. Boot, the signer and the gate do not use the source.
- **Conditioning.** A nonce is TurboSHAKE256 over 512 counts' raw bits (256 bits of claimed min-entropy for
  128 bits out; 1.2 to 4.8 ms) and a word of counter noise from the PUF characterisation rings, a second
  source that shares nothing with the TRNG rings. Raw words are never output. `K_dev` is not mixed in:
  every use of the source is a public nonce, and what a nonce needs is not to repeat, which a key does not
  add.
- **Not fitted: a long-divider fallback.** The physics report proposes that a die with no qualifying pair
  (6.5e-6 of dies at the simulated spread) fall back to a divided ring at 460 bit/s. That figure is for the
  old 7-stage ring; with the 17-stage rings it is 64 bit/s [D, same formula], eight seconds a nonce, and no
  test of this section observes the jitter in that mode. Such a die fails `ENROL` and is screened out.
- **Not covered by any test:** interference at a frequency near the beat rate that acts differently on the
  two rings. The defence is structural (adjacent identical rings on one strap) and the second source.
- **Area** about 19,000 [E: rings 1,800, selectors and sampler 800, counter and capture 2,400, statistics
  6,000, control 2,500, 64-bit shift register and bit tests 6,000], against 13,035 [M] for the old one.

### 6.6 Clock, reset, pads, power

- **Clock.** The core runs on the pad clock from reset, selected combinationally by a strap. One fixed ring
  oscillator serves as loss-of-clock and frequency-window detector and, by strap, as an alternative clock for
  bring-up. The tunable DCRO, its loops, the replica path and dither are removed.
- **Design clock 25 MHz** (40 ns). The current 20 ns target has never been met. First timing, on the
  physical-design lane's proxy after placement: the path micro-PC → ROM (25 ns) → row address → row read
  (16 ns) → word unit (32 ns) → hold register is 79 ns at the slow corner, so one clock per micro-instruction
  does not make 25 MHz. The ROM output needs an instruction register: a two-stage machine (fetch, execute).
  The RTL lane is implementing it behind a parameter. What it costs in clocks is not yet known: one clock
  per taken transfer at least, and the stall rule for a row written in the previous clock has to be restated
  for the new stage. Until its counts are in, every figure in 7.4 that comes from the model is for the
  one-stage machine and is a lower bound; unit times (Keccak 721 clocks) are not affected. The model follows
  the RTL's counts when they are reported, as it did for the stalls of 5.3.
- **Reset.** Schmitt-trigger reset pad with pull-down (the pending `scripts/pending_src_b4_b6.patch`), external
  supervisor on the board. The secret-reset net asserts asynchronously and releases synchronously; the
  sequencer waits 16 clocks after release before its first write.
- **Back-powering.** A signal pin at 5 V lifts the unpowered rail to 4.4–5.3 V through the pad's upper diode,
  at every corner and whatever series resistor is fitted [S, `physics/pads`, nine corners]; a resistor
  limits the current, not the voltage, and no practical bleed holds the rail down. Requirements on the chip:
  while reset is low every bidirectional pad is high-impedance, every internal oscillator is off, the FRAM
  chip-select is inactive or released, and nothing acts on the rail being up; no output enable can be high
  in reset, to be shown on the gate-level netlist (8.4). Requirements on the board: the reset supervisor
  senses the supply ahead of a reverse-blocking element, not the chip rail; a series resistor at the chip
  on every pin that something outside the chip's own rail can drive (1 kΩ on the SPI lines, 10 kΩ on straps
  and tamper, 330 Ω on outputs; 5 mA per pad and 20 mA in total are project limits, the foundry publishes
  none); a 100 kΩ bleed; the FRAM supplied from the chip rail with a 100 kΩ pull-up on its chip-select; the
  NFC pads reached only through the isolated front end, with at most 0.2 V at the pad when the chip is off
  (conduction starts at 0.25 V at the fast hot corner). The distance-bounding lines cannot take a resistor
  (nanosecond edges allow 50–100 Ω, which passes 30–50 mA into an unpowered pad): they need a buffer beside
  the chip, supplied from the chip rail and specified for partial power-down, whose delay enters the
  calibration. None of this protects against someone who holds the board: they can release reset themselves
  and run the chip from a back-powered rail at reduced voltage. The defences against that are on the die
  (5.5: the coded micro-PC and the doubled decision bits), and there is no on-chip supply monitor. Latch-up
  when real power arrives on a forward-biased pad cannot be simulated from this PDK.
- **Pads:** the default pad ring, unchanged, as chip-on-board requires (11.2). SPI 4, FRAM SPI 4, NFC 3,
  distance 2, tamper 1, FAULT 1, BUSY/IRQ 1, clock monitor 1 (pad clock divided, no internal node), 2 straps:
  19 of the 42 general pads, plus the dedicated clock and reset pads. Unused pads are tied as inputs with
  pull-downs.
- **Power.** One 5 V domain; core and pad rails are shorted in the pad library. The 1.2 V ground bounce [C]
  came from the eight-bit parallel link switching together; with SPI only, one output switches at a time,
  slew-limited. The default ring has four supply pad pairs, one per side, and none can be added.
- **Fuses.** None in configuration S, and no bit depends on one (3.4). `gf180mcu_re_efuse` in the PDK
  provides `efuse_async_mem_1x8` (97.27 × 83.02 µm, 8 bits) with 5 V timing libraries; it programs from the
  5 V rail through on-macro PMOS with a 50 µs pulse [C, compiler documentation]. Its authors describe it as
  not proven in silicon; simulation finds enough drive in the asynchronous macro and too little margin in
  the array macro [S]. A characterisation-only block is specified in
  `physics/efuse/test_structure_spec.md`: 64 bare fuse cells in eight driver variants, one analog pad,
  controlled by an owner-root command, about 33,000 µm² (17,000 for half). It carries the same foundry-deck
  risk as any fuse layout and is not in S: there is no area for it (7.3). It belongs on the engineering
  sample of 9.4, where the organs are present for measurement and nothing depends on them.

---

## 7. Budget

### 7.1 Area

Core of `SLOT_0P5X0P5`: 1,052 × 1,647 = 1,732,644 µm². How much of it can be filled is 7.3 and section 11.1.

| Block | S, every organ | Basis |
|---|---:|---|
| Register file, 72 rows, as a placed array | 329,434 | M, physical-design lane (the inferred file of the previous revision was 296,497) |
| Keccak unit less its rows | 89,988 | M, stage 2 RTL (`scratch/lanes/fable-dregg180-v2-stage2.last.md` 6) |
| Word unit | 21,400 | 20,683 M, stage 2 RTL (its operand and hold-register multiplexers are counted in the sequencer) + 700 E for the two fingerprint functions |
| Microcode ROM | 85,200 | E: 2,000 words at the 42.6 µm² per word of the stage 2 RTL's 455-word ROM; 1,443 words exist (5.5) |
| Sequencer, decoder rules, egress, framer | 82,500 | 100,542 M on the stage 2 RTL of the stage-1 machine (sequencer with rules 76,724, egress 10,915, framer 12,903), less 8,403 M for a shadow hold register the model no longer needs and about 9,600 D for a nonce register that is now two state rows; the lifecycle register, deeper stack and wider step counter of this revision are not in it. The skeleton figure of earlier revisions was 23,985 |
| SPI link, diagnostics | 27,776 | M, stage 2 RTL |
| PUF, 1,008 rings in quads | 219,600 | 116,300 M (slots and dummies) + 6,500 E (characterisation quads) + 26,800 E (ring selection) + 70,000 E (counters, decoder, control); 6.1 |
| NFC receiver, no NCO | 35,000 | 28,729 M (existing leaf with the NCO removed) + 6,000 E for the longer token frame |
| Distance, TDC | 45,000 | 44,593 M |
| Clock, reset, tamper, shield | 35,000 | 14,291 M skeleton + 16,306 M (existing shield leaf) + E for the ring and glue |
| TRNG, FRAM SPI master | 34,500 | 19,000 E (6.5) + 15,540 M, stage 2 RTL (three-word transactions; sixteen now) |
| Redundant decision bits, micro-PC code, glue | 10,000 | E; the taint flags and comparators that were in this line are now measured in the sequencer |
| **Total** | **1,015,400** | |
| **Share of core** | **58.6 %** | |

Of the total, about 230,000 is estimate with no synthesis behind it (most of the ROM, PUF selection, decoder
and characterisation quads, TRNG, redundancy, parts of NFC and clock). The datapath and control lines are now
synthesis of RTL that simulates against the model, for the stage-1 machine. The largest single estimate is
the PUF's counters, decoder and control.

**Where the sequencer's area goes** [M and D, stage 2 report]: 334 flops; the 64-bit multiplexers that the
instruction set asks for (the operand select, the hold register's input with its many sources, the framer's
header fields); a 64-bit header register and a 22-bit word counter in the framer; the egress. The decoder
rules themselves are 7,901: the rule set is not the cost, the 64-bit data routing is. Changes to the
instruction set that would cut it, none measured, each a decision for the stage that implements it:
(1) `LDF` has 18 sources, of which only the header word, the two syndrome words, the counter-noise word and
the TRNG raw word are 64 bits wide; routing those five through one organ-data port, like `DIN`, leaves a
24-bit multiplexer; (2) the framer need not hold the header for the whole command: the microcode can store
it to a scratch row with its first instruction; (3) the response-length counter, the 28-bit step counter and
the two loop counters could share one down-counter structure. The RTL lane is the one that can measure these.

What moved since the previous revision (822,700):

| Change | Effect | Why |
|---|---:|---|
| PUF array: 504 rings in pairs → 1,008 in quads, with dummies | + 72,200 | 6.1: pairs across mirrored rows support no entropy claim |
| PUF ring selection for 1,072 rings | + 26,800 | the slot has no selection logic of its own |
| Characterisation quads counted in the total | + 6,500 | the entropy claim cannot be checked without them (was 4,000, outside the total) |
| Register file as a placed array | + 32,900 | measured by the physical-design lane; the file cannot be placed as synthesis infers it |
| TRNG replaced | + 6,000 | 6.5: the old source has no entropy to speak of |
| Word unit, fingerprint functions | + 700 | 4.3 |
| ROM 1,700 → 2,000 words, at the measured density | + 7,700 | 5.5: 1,443 words measured with stages 3 and 4 in, stage 5 still to come |
| Sequencer, egress and framer measured on RTL | + 58,500 | the skeleton predated the taint rules and had no framer or egress |
| Word unit, Keccak, SPI link, FRAM master measured on RTL; glue line halved | − 18,700 | stage 2 RTL |
| Key rows 10 → 4, scratch 20 → 24, state and pins 8 → 10 | 0 | keys derived on use pay for the rows that verification needs (5.2) |

Not in the total, each a separate decision:

| Addition | Area | Basis | Decision |
|---|---:|---|---|
| Option F, field kit for aggregate-proof verification: digit-serial Goldilocks unit, round constants, verifier microcode | 75,800 | 37,801 M skeleton + 19,691 M + 18,300 E | D5 |
| NCO (carrier, FSK, chirp) | 25,940 | M: 54,669 − 28,729 | D7 |
| Fuse characterisation block | 33,000 (half: 17,000) | E, `physics/efuse/test_structure_spec.md` | D2 |

### 7.2 What changed from the first S

| Change | Effect | Why |
|---|---:|---|
| Register file 64 → 72 rows | + 32,825 | Signature verification needs the scratch rows of 4.3; the first S never tallied them |
| GF(2^128) unit removed | − 48,545 | The fingerprint is two GF(2^64) products in microcode on the word unit |
| Fuse macros removed | − 18,150 | Not relied on (section 3) |
| NCO removed | − 25,940 | No protocol role; measured by synthesizing the leaf without it |
| SPI link 45,000 → 25,000 | − 20,000 | Skeleton measured |
| Clock unit 50,000 → 35,000 | − 15,000 | Skeleton and shield leaf measured |
| NFC frame growth restated on the smaller base | + 940 | |
| ROM 1,536 → 1,700 words | + 7,500 | Committee gate, fingerprint, lease and owner-root routines |
| Physics findings, the placed register file, the measured ROM and the stage 2 RTL figures (table in 7.1) | + 192,700 | |

### 7.3 Does it fit, and what gives way

Evidence (11.1, and `scratch/lanes/fable-dregg180-phys.last.md`, preliminary): a proxy of 889,888 µm² with the
register file as a placed array has been placed legally in this slot; buffer repair added 15.7 %, none of it
in the register file, which is about 25 % of the cells that are placed automatically; the result is 61.5 %
of the placeable area. Clock tree and routing are still to run. Nothing above 61.5 % after repair has been
legalised, and the configured target corresponds to about 68 %.

The comparison that carries over is fill after repair, with the two hand-placed arrays (register file, PUF
slots: 452,200 together) taken at their size and everything else grown by 25 % [D]:

| Configuration | Synthesized | After repair | Fill | Against 61.5 % placed |
|---|---:|---:|---:|---|
| S with every organ | 1,015,400 | 1,157,700 | 69.2 % | 128,000 µm² over |
| without distance bounding | 967,800 | 1,098,200 | 65.6 % | 69,000 over |
| without distance bounding and NFC: no U5 | 931,100 | 1,052,300 | 62.9 % | 23,000 over |
| **no U5, no shield (D14)** | **914,800** | **1,031,900** | **61.7 %** | **2,000 over: the same point** |
| no U5, PUF of three blocks | 899,800 | 1,020,500 | 61.0 % | 9,000 under |
| no U5, no shield, PUF of three blocks | 883,500 | 1,000,100 | 59.8 % | 29,000 under |
| no U5, PUF of 630 rings in pairs | 877,100 | 995,700 | 59.5 % | 34,000 under |

Each organ removed also takes its microcode (distance 60 words, NFC 40).

What the physical-design lane has measured since, and what it does to this table
(`scratch/lanes/fable-dregg180-phys.last.md`, preliminary; detailed routing still to run):

- The placed proxy has its clock tree at 62.4 %, legal, and global routing uses 37 % of the tracks: the chip
  as a whole is not routing-limited at this fill. The rule to budget by is synthesized area × about 1.16
  against the 1,673,768 µm² placeable; the "after repair" column above is that rule with the hand-placed
  arrays exempted, and the two agree within 1 % for these configurations.
- **The microcode ROM as random logic is the one congested block**: all the routing overflow is in the ROM
  and sequencer region, and the ROM needs about 50 % local fill, that is, twice its cell area. At 2,000 words
  that is another 85,000 µm² of floor that the table does not show. Either the ROM is counted double (S
  without U5 and the shield then stands at about 1.00 M of floor demand: it does not fit), or the ROM gets
  another structure. Two that need no foundry macro, neither measured: a NOR-plane ROM placed by script
  like the register file (one row of cells per bit line, routed by template), or splitting the image so
  that the routines of the hardwired key and record ranges, which change least, are a separate small block.
  This is now the first thing to resolve, ahead of the sequencer reductions of 7.1, because it is larger.
- Every separately fenced organ costs about 19,000 µm² of slack and 15 to 45 % of its own area. Fence only
  the PUF array (which needs its keep-out), the distance fast path if it stays, and the TRNG rings.
- The 9-track library is never denser. Not pursued.

S with every organ does not fit: it is above anything placed, with a quarter of it estimated, and nothing
routed. What can give way, in the order recommended:

| # | Reduction | Saves | What is lost | Whose decision |
|---|---|---:|---|---|
| 1 | Distance bounding and its timer | 47,600 | The proximity guard of use U5. The presence token stays. It is also the organ with the most unresolved board work: its two pins cannot be protected by a resistor (6.6) | owner (D14) |
| 2 | NFC receiver and token | 36,700 | The presence guard; with 1, all of U5: capabilities then have no guard that needs a second device | owner (D14) |
| 3 | Shield | 16,306 | The top-metal serpentine over the register file, the only measure against probing from above | owner (D14) |
| 4 | PUF of three blocks, 756 rings | 31,300 | Key entropy claim 131 → 98 bits. Every key on the chip derives from this one | owner (D6) |
| 5 | PUF of 630 rings in pairs, five blocks | 54,000 | The claim becomes h = 0.90 on a gradient that has not been measured: defensible only after silicon | owner (D6) |
| — | PUF decoder measured instead of estimated | unknown | Nothing. 70,000 is the largest estimate in the table; stage 3 synthesizes it | — |
| — | Microcode written for size | perhaps 100 to 200 words, 5,000 to 9,000 | Nothing; 5.5 | — |
| — | Register-file rows | 4,575 a row | Scratch rows are at their floor for a gate statement (4.3); a routine rewritten to use fewer frees rows only in whole-file steps | — |

Where this stands: with the stage 2 RTL's measured control logic in the budget, S does not fit with margin
under any combination that keeps both the full PUF and the shield. Without use U5 it is 931,100, which is
23,000 µm² above the one point that has been placed; without U5 and the shield it is at that point; margin
below it needs a third of the PUF as well, or the sequencer reductions listed in 7.1 to come true.

Recommendation, in order: (a) remove use U5 now (reductions 1 and 2): it is a guard on capabilities that no
crate implements yet (section 1), and its two organs have the most board work outstanding (6.6);
(b) have the RTL lane measure the three sequencer reductions of 7.1 and the microcode written for size,
which together are the only candidates that cost no function; (c) decide between the shield and the PUF's
fourth block only when (b) and the physical-design lane's routed result are in. The PUF is the root of
every key and the one block whose claim cannot be repaired after tape-out, so of the two the shield goes
first; but that is a security reduction either way and it is the owner's decision (D14). Options 4 and 5 are
listed so that the choice is explicit; 5 is not recommended at all.

- The estimates are replaced by synthesis of real RTL at the end of stage 3. Additions are decided then.
- Option F (75,800) fits beside nothing in this table.
- The 20 µm keep-out and the routing obstructions of the PUF array (R2.3, R3.2 to R3.4) are the physical
  lane's to account for; the fills above count cells only.

### 7.4 Time per operation at 25 MHz

Model figures are clocks of the one-stage machine. The two-stage machine that 25 MHz needs (6.6) adds
clocks to microcode, not to the units; in a signature verification about two thirds of the clocks are
Keccak unit time and one third is microcode, so the times below grow by less than the microcode share
times the pipeline's overhead. Alternatively the one-stage machine runs at about 12 MHz and every time
below doubles.

| Operation | Clocks | Time | Basis |
|---|---:|---:|---|
| Keccak-f[1600] / Keccak-p[1600,12] | 721 / 373 | 28.8 µs / 14.9 µs | M |
| One `F` call / one chain start, as the signer microcode runs them | 748 / 1,150 | 29.9 µs / 46.0 µs | model (`v2/tests/report.py`). A chain start derives `SK.seed` from `K_dev` (about 390 clocks) and runs one `PRF` call |
| Signer request, fixed part (`K_host` derivation, tag check, shape checks, header) | 867 | 35 µs | model: a request with one chain of zero steps, less its chain start |
| Counted-key request, added (record tag, write of seven words, read-back) | 4,298 | 0.17 ms | model; FRAM transfers estimated at SCK = clk / 4 |
| WOTS signature, 35 chains, FIPS 205: most steps / digits spread evenly | 399,269 / 231,417 | 16.0 ms / 9.3 ms | model: 552 / 327 Keccak calls |
| WOTS public key, 35 chains | 432,875 | 17.3 ms | model: 597 Keccak calls |
| One-time signature (WOTS+C, FTS), up to 600 calls | 0.46 M | 18 ms | D |
| SLH-DSA-128f signature, cold / with tagged root cache | 78 M / 6.6 M | 3.1 s / 0.27 s | D: 102,800 / 8,700 calls |
| SLH-DSA-128s signature, cold / with tagged root cache | 1.61 G / 305 M | 64 s / 12 s | D: 2.12 M / 401,000 calls |
| G1: one SLH-DSA-128s verification, with the hash chains and the fingerprint | at most about 4.1 M; 2.7 M for the signature measured | at most 0.16 s; 0.11 s | D (4.3); model: `GATE` with one authority signature, 2,718,597 clocks |
| G3: `k` member signatures and Merkle paths | `k` × 4.1 M at most | 0.5 s for 3 of 5 (model: 8.1 M clocks, 0.32 s); 1.8 s for 11 of 16; 11 s for 67 of 100 | D (4.6), model |
| Boot to READY, unleased | 3.8 M | 0.15 s | model: one verification 2.7 M, PUF 1.14 M (E: 252 quads × 4 rings × 3 measurements × 15 µs, and the decoder), two record reads |
| Boot of a leased chip to `LEASE_PENDING` | 4.1 M | 0.17 s | model: as above, and TRNG start-up with one nonce 0.31 M for the modelled ring spread |
| Enrolment: `ENROL` / `COMMIT` | 1.5 M / 3.8 M | 58 ms / 0.15 s | model |
| TRNG start-up, first use in a power session | at most 3 M | at most 0.12 s | S (6.5); pairs whose beats are too long are abandoned after 64 counts |
| Nonce: 512 counts and conditioning | 30,000–120,000 | 1.2–4.8 ms | S (6.5) |
| Key derivation on use | about 390 per use | 16 µs | model |
| Lease at power-up | one gate verification | + 0.10 s per signature (2.62 M clocks on the model), plus the authority round trip | model |
| Capability check, per attenuation level | about 400 | 16 µs | D |
| NFC token | — | 2.3 ms on air | D: 248 bits at 106 kbit/s |
| Option F: Poseidon2 permutation, 1 / 2 / 4 multiplier bits per clock | about 36,000 / 21,000 / 14,000 | 1.5 / 0.85 / 0.55 ms | D: 472 products and about 3,700 other clocks |
| Option F: G2 verification, 24 variables, 1 bit per clock | about 0.6 G | about 24 s, plus 0.8 s transfer | D, E (4.4) |

The "tagged root cache" is a required feature of U1, not an optimisation. A WOTS key in the hypertree may sign
only the root of the tree below it. The chip signs a root only if it computed that root in the same command or
the host returns it with a MAC the chip issued when it did. The host then stores public roots and the chip
recomputes only the bottom tree and FORS for each signature.

SLH-DSA-128s signing time is set by the lane-serial Keccak. A round-per-clock Keccak is 342,265 µm² [M] and
does not fit this slot.

### 7.5 Floorplan sketch (core 1,052 × 1,647 µm, not to scale)

The floorplan is the physical-design lane's (`v2/phys/floorplan/regions.tcl`), which is the reference; this
is its outline. The register file is a placed array across the full width and splits the core. The
identification macros that the precheck requires sit in the die corners outside the core
(`librelane/macros/macros_qsag.yaml`) and take no core area.

```
                 NORTH: analog 3..0 (unused), FRAM SPI 22..25, tamper 26
        +--------------------------------------------------------------+
        | PUF ring array 674 x 172 um, placed slots | keep- | FRAM     |
        | (north-west corner; 20 um keep-out)       | out   | master   |
        +-------------------------------------------+-------+----------+
        | PUF decoder, counters, ring selection | shield logic | TRNG  |
        +==============================================================+
 WEST   |   REGISTER FILE 72 x 64, placed array, shield route above    |  EAST
 straps +==============================================================+  FAULT, IRQ,
 CS_N   | word unit and hold register (strip under the read port)      |  CLK_MON
        +-------------------------------------+------------------------+  distance 13, 14
        | Keccak                              | distance, TDC (D14)    |  (fast path placed
        +-------------------------------------+------------------------+   against the pads)
        | microcode ROM + sequencer           | NFC front end          |  NFC 8..10
        +---------------+---------------------+------------------------+
        | clock, reset  | SPI link                                     |
        +--------------------------------------------------------------+
                 SOUTH: clock, reset, SPI 0..3
```

---

## 8. Verification plan

### 8.1 Golden model

The model in `v2/model` executes **the same microcode image** as the RTL, over a Python model of the
register file and units. It has models of the PUF (a response, a set of bits that read wrong, the BCH
decoder), the TRNG (a stochastic model of the ring pairs with the failure modes of 6.5), the FRAM (which
tests rewrite and restore), and, in `host.py`, the owner root, the authority, committee members and a
FIPS 205 signer built on hashlib. Still to come: an authority with its lease ledger as a party of its own,
the NFC token and the distance exchange. The G1 routine is checked against `crates/qsag-core` FIPS 205
vectors; G3 against the same code with a committee tree; the G2 machine, if option F is taken, against
`crates/qsag-agg` proofs.

### 8.2 Formal and static checks

On the sequencer, egress and register-file control (a few hundred flops), by bounded model checking and
induction with the Yosys flow already used in `lec/`:

1. Egress data always comes from an `out` row and at most the limit loaded by the prologue.
2. Idle is reached only through the epilogue; after it every working row is zero.
3. A key row is written only inside the boot and enrolment address range.
4. Lifecycle-record writes that change mode, policy, pins or `gen` occur only at the ROM addresses that
   implement `COMMIT`, `REINIT`, `ROTATE` and `RETIRE`, and only after the verdict that 4.2 requires is set.
   On a leased chip no counter passes its session bound.
5. The gate verdict is cleared by the command that consumes it, and by every exit.
6. A row is never read while transparent.

On the ROM image, by script (`v2/model/romcheck.py`, with `v2/ucode/push_manifest.txt` as the reviewed list):
the micro-instructions that write the response are exactly the listed ones, with the listed source rows; key
writes lie inside the key range; no branch targets the idle address or the inside of the epilogue; no
instruction names a key, out or work row as a word-unit operand. Still to add: every routine ends at the
epilogue on every path.

Kept: the equivalence proofs of the Goldilocks and GF(2^128) units (`lec/run_lec.py`, `run_mul_lec.py`,
`run_prefix_lec.py`), re-run on the tape-out RTL.

### 8.3 Regression: every guard has a test that fails without it

Each row is a pair: the accepting case and the refusing cases. A test is admitted only after it has been
shown to fail on a build with the guard removed. On the model the rows Lifecycle, Rollback, Gate (G1, G3),
Entropy source, Output bound and the model's part of Survival exist in `v2/tests`, and
`v2/tests/mutation.py` removes each guard in turn; Signer is as far as stage 1 took it; Vat, NFC, Distance
and Faults do not exist yet.

| Area | Accept | Refuse |
|---|---|---|
| Lifecycle | enrol → commit → reset → boot → same keys; re-initialisation of an orphan by the owner root; reconstruction with up to five wrong bits in a block | enrol after commit; commit or re-initialise with a signature over an old nonce; enrol after the FRAM is erased and the helper record written back; boot with altered helper data; boot with a wrong owner signature; boot with six wrong bits in a block; any command but `NONCE` and `REINIT` in `ORPHAN`; any keyed command before `BOOT` |
| Rollback | counter advances across reset; leased chip resumes at the granted base | leased chip: older image restored, then any value of `u` at or below one already granted; lease over an old nonce; lease naming a superseded `gen`; counter past the session bound; leaving `LEASE_PENDING` with the TRNG failed. Unleased chip: the test asserts the documented residual, that an older authentic image is accepted |
| Signer | signatures verify under `crates/qsag-core` | any request naming a chain position; WOTS signing of a root without a valid tag; one-time key used twice, including across reset |
| Vat | mint, attenuate, invoke within limits | wider child rights; removed guard; spend over limit, including across reset; mint after mint lock, including after reset; expired epoch |
| Gate | valid statement for this transition | same statement on a second chip model; replay after `seq` advanced; statement for another type or other arguments; bad signature; a stated chain end or FORS root that differs in either pass, in every position class; G3: `k` − 1 members, a member repeated, indices out of order, a key not under the pinned root, a path to another root; G2 (option F): unpinned program, program with an assertion removed, bitmap under threshold, a stated challenge that differs from the transcript |
| NFC | fresh token bound to the request | replayed counter; wrong binding; bad tag; valid CRC only |
| Distance | all rounds correct in time | one wrong bit; late answer; calibration result presented as validity |
| Output bound | — | for every opcode: response longer than its limit; any key-dependent word in any response, FRAM write, response length or cycle count that the manifest does not list (checked by propagating a taint from key rows in the model and the RTL, not by comparing values) |
| Faults | — | reset or zeroise injected at every micro-PC of every routine: no key-dependent output, lifecycle not advanced without its record write |
| Survival | boot with TRNG dead, internal oscillator dead, FRAM absent, tamper pad floating before lock; a gate statement accepted with the TRNG dead | — |
| Entropy source | nonce from a pair that passes | a noise-free source (V at most 0.33); locked rings; jitter that is not white; no qualifying pair; a source that degrades after start-up; enrolment, `REINIT` and lease with the source failed |

### 8.4 Gate level

Post-route netlist, latches and flops initialised to X, SDF at SS 125 °C 4.5 V and FF −40 °C 5.5 V: reset and
boot, the self-test, one signer transaction, one gated transition, one tamper event with the clock stopped,
and the register-file write/read sequence at the borrow limit. The self-test command is extended to cover a
key derivation, a FRAM round trip and each organ's start/done handshake.

### 8.5 Signoff

Static timing at all corners with the reset tree and the latch borrow limit; Magic DRC and KLayout DRC;
Netgen LVS with power pins; antenna and density; a clock-domain crossing review of the two remaining
crossings (SCK, NFC clock); then an audit of the diff and of every number by a model that did not write them.

---

## 9. Migration from the current RTL, and schedule

### 9.1 Kept unchanged

| Module | Evidence carried over |
|---|---|
| `qsag_keccak_serial` | 54 FIPS 202 / RFC 9861 known-answer tests (`tb/unit_dp.cpp`) |
| `qsag_p2_rc` (option F); `qsag_gl64_karatsuba_csa`, `qsag_field_engine` (configuration L only) | 593 vectors against the Lean oracle fixture; `lec/run_lec.py`, `run_mul_lec.py`, `run_prefix_lec.py` |
| `qsag_gf128_clmul` (configuration L only) | `lec/lec_gf128.sv` |
| `qsag_cells` | used by every regression |
| `qsag_anchor_spi` | FRAM rollback transactions. `qsag_trng` is not kept: 6.5 |
| Latch-row and hold-register scheme of `qsag_sponge` | full-chip regression |
| BCH decoder, counters and ring cell of `dregg_ro_puf_bch` | `tb/unit_puf.cpp` |
| Receiver of `dregg_nfc_nco`; responder latch and Vernier chain of `dregg_distance_tdc` | `tb/unit_tdc.cpp` |
| Tamper latch, blanking and reset synchroniser of `qsag_gals_clk_rst`; SPI and diagnostic read of `qsag_io_shell` | scenarios `tamper`, `tamperboot`, `coldboot`, `spiburst`, diagnostic read |
| `tb/` harness, `model/qsag_prims.py` | — |

### 9.2 Rewritten or new

`qsag_wire_engine` (replaced by sequencer, ROM, word unit and egress); `qsag_sponge` (replaced by the single
file); `dregg_captp_vat` (its checks become microcode; its rows move into the file); the PUF array and its
helper-data handling; NFC and distance authentication; the clock unit's oscillator part; the authority's
lease ledger; microcode assembler; model interpreter; host library; committee-tree builder; with option F,
the digit-serial field unit and the verifier-program compiler.

Removed: `qsag_muller_c`, `qsag_async_fifo_gray` in its present depth, the source-synchronous and clockless
personalities of `qsag_io_shell`, the DCRO and its loops, the NCO, and in S the Goldilocks and GF(2^128) units.

### 9.3 Stages

Each stage ends with the stated regression passing. Effort is lane-days for one lane with hbox access [E].

| # | Stage | Ends with | Days |
|---|---|---|---:|
| 1 | Model first: microcode assembler, model interpreter, register-file and unit models; port PING, hash, key load, PRF_msg, WOTS and FORS, the anchor, and (L) Poseidon2 and Merkle. **Done, in `v2/`** | Model answers 50 of today's 54 script transactions identically, 14 of them from requests rebuilt in the new signer and provisioning formats; the four verifier-VM transactions belong to stage 7. Every decoder rule of 5.3 has a refusing test, and a mutation harness (`v2/tests/mutation.py`, 153 mutants) keeps it so | 4 |
| 2 | Register file, sequencer, word unit, egress in RTL with the kept Keccak unit; SPI link only, with the decoder rules of 5.3 as modelled | RTL equals model on stage 1, including every refusing microprogram of `v2/tests/test_output_bound.py`; properties 1, 2, 3, 6 of 8.2 proved | 5 |
| 3 | Lifecycle: FRAM records, owner-root enrolment and re-initialisation, boot, PUF array in quads, the coherent-sampling TRNG, leases and the authority model. **Model and microcode done, in `v2/`; RTL and synthesis not** | Lifecycle and rollback rows of 8.3; synthesis of everything so far, replacing the estimates of 7.1 | 6 |
| 4 | G1 routine with the microcoded fingerprint, G3, transitions; review of the fingerprint and lease arguments. **Model and microcode done, in `v2/` (transitions `LEASE`, `EPOCH`, `RETIRE`, `ROTATE`); RTL and the review not** | Gate rows of 8.3 for G1 and G3 | 5 |
| 5 | Vat in microcode; NFC token; distance roles; guards; rest of the signer: FORS indices from `H_msg` on chip, root tagging (7.4) | Vat, NFC, distance rows; signer rows | 5 |
| 6 | Survival: clock strap, reset pad, tamper arming, self-test extension, fault-injection sweep | Faults and survival rows | 3 |
| 7 | Option F only (decided after stage 3): digit-serial field unit, verifier machine in microcode with stated challenges, program pinning, compiler from `qsag-agg` | Real regime-7 proof accepted; mutated proof and unpinned program refused; the four verifier-VM transactions of today's script, re-expressed under 4.4 | 10 |
| 8 | Synthesis, floorplan, placement, clock tree, routing, timing | Routed design, timing met at 25 MHz at all corners | 5 |
| 9 | Gate-level simulation (8.4) | Passing at both SDF corners | 4 |
| 10 | DRC, LVS, antenna, density; independent audit | Clean reports | 5 |

Configuration S: stages 2 to 6 and 8 to 10 remain, 38 lane-days. Option F adds stage 7. The largest
uncertainties are the physical stages, none of which has ever completed on this chip, and, for option F, a
compiler that does not exist and a verifier machine that has never run a real proof.

### 9.4 Run 3 and a later run

Run 3 closes for purchase on 9 Dec 2026 and needs a clean GDS on 16 Dec 2026, thirty days after this was
written. The stages still to do for configuration S are 38 lane-days, and stages 8 to 10 have never been run
on any version of this chip: no clock tree has completed, nothing has been routed, and no DRC, LVS, antenna
or density check has run. **Configuration S cannot credibly be taped out in Run 3.**

What could be, with two lanes in parallel, is an engineering sample:

| | Engineering sample for Run 3 | Held for a later run |
|---|---|---|
| Logic | Stage 2 machine (register file, sequencer, word unit, Keccak, SPI) with the stage-1 ROM as modelled and tested: PING, hashing, key load, PRF_msg, WOTS and FORS, the FRAM anchor | Lifecycle, enrolment, PUF key derivation, leases, the gate (G1, G3), vat, seal, option F |
| Organs | Present for measurement, with open read-out and no security claim: the PUF ring array, the TRNG, the distance fast path, the NFC receiver front end, the clock monitor and tamper input | Their authenticated use: helper data, tokens, keyed distance rounds |
| Area | about 660,000 µm² [E, from before the stage 2 RTL was measured: its datapath, control, ROM and link alone are 562,579 M], 39 % geometric | 1,015,400 with every organ (7.3) |
| What it is | A signing coprocessor with volatile host-loaded keys, and a characterisation vehicle: PUF entropy and reliability across 1,000 dies, ring speeds, TRNG quality, latch-array timing, pad and supply behaviour | The product |
| What it is not | A root of trust. It has no lifecycle and its test read-outs are open | |
| Also carried, if it passes the foundry decks | The fuse characterisation block of 6.6 and the PUF and TRNG ring slots under the placement rules of 6.1, so that their measurements set the product's parameters | |

Lane A writes stage 2 RTL against the model (5 days) and the measurement read-outs (2 days). Lane B starts the
physical flow on day one with the existing leaves and a register-file stub, so that the first complete pass
through routing, DRC and LVS does not wait for the logic. Then placement and timing (5 days), gate-level
simulation (4 days), sign-off and precheck (5 days).

Two gates decide it. Do not buy the slot unless both are met:

1. **30 Nov:** stage 2 RTL passes the 50-transaction regression in simulation, and one full pass of the flow
   through DRC and LVS exists on a design of comparable size.
2. **7 Dec:** a routed design meets timing at its stated clock at all corners, gate-level simulation of reset,
   boot and one signing transaction passes, and the wafer.space precheck is clean on a complete GDS.

The plan that optimises for the chip and not the date: finish stages 2 to 6 and 8 to 10 for configuration S
(38 lane-days, five to six weeks with two lanes), replace the 178,000 µm² of estimates with synthesis of real
RTL after stage 3 and decide option F and the cuts of 11.3 then, have the fingerprint and lease arguments
reviewed, and tape out in the first run after that with an independent audit of the diff. If the
engineering sample was made, its parts ship in Q2 2027 and its PUF and TRNG measurements set the fuzzy
extractor parameters of the product; if it was not, the product run carries the characterisation array of
D13 and is first silicon for everything.

---

## 10. Decisions

Taken by the owner:

| # | Decision | Outcome |
|---|---|---|
| D1 | Slot and package | `SLOT_0P5X0P5`, chip-on-board, default pad ring. Run 3 prices: $3,000 + $1,500; purchase closes 9 Dec 2026, clean GDS due 16 Dec 2026. The budget for December is not certain |

Open, with recommendations:

| # | Decision | Recommendation | Cost either way |
|---|---|---|---|
| D2 | Fuses | **None in S, for any bit, and no characterisation block either.** One fuse cannot carry a one-way bit (3.4); a redundant scheme is whole macros per bit; the characterisation block is 33,000 µm² that S does not have, with a foundry-deck risk on the whole die. Put the block on an engineering sample if one is made | No: `ROTATE`, `REINIT` and `RETIRE` stay reversible on an unleased chip, and the PDK fuse stays unmeasured |
| D3 | Owner root public-key digest as a mask constant | **Yes.** Enrolment, re-initialisation and debug unlock all rest on it now | Yes: every die of the run trusts one key, fixed at tape-out, and that key can unlock the characterisation read-out. No: nothing authenticates enrolment, and an erased FRAM can be re-enrolled by anyone |
| D4 | Host link | **SPI only** (as built in `v2/`) | Other links: about 55,000 µm² and two more clock domains |
| D5 | Gate | **G1 and G3 in the baseline.** Option F (G2, aggregate proofs) decided after stage 3, when the estimates in 7.1 are measured; it is not for Run 3 | Option F: 75,800 µm², about 24 s per proof, a verifier compiler that does not exist, and about 60,000 to 75,000 µm² of organs to give up (distance bounding first) unless the measured baseline comes in low |
| D6 | PUF array | **1,008 rings as 252 quads, four blocks, under the placement rules of 6.1** | 219,600 µm² against 118,000. Three blocks: 31,300 less and a 98-bit claim. 630 rings in pairs with five blocks: 54,000 less and a claim that cannot be defended before silicon. The array as drawn before: no claim |
| D7 | NCO | **Deferred** | 25,940 µm² measured |
| D9 | Mode (coprocessor or vat) fixed per chip at `COMMIT` | **Yes** | A chip serves one role |
| D10 | Design clock 25 MHz | **Yes** | Every time in 7.4 scales with it; no timing result exists |
| D11 | Rollback policy per chip: leased or unleased (3.4) | **Leased** for any chip that guards one-time keys or spend limits against someone who may hold the board; unleased otherwise | Leased: the authority must be online at every power-up, and unused grants are lost. Unleased: an attacker with the board can restore any earlier state |
| D12 | Run 3 | **Tape out only the engineering sample of 9.4, and only if both gates there are met and the money is there.** Otherwise skip Run 3 | Engineering sample: $4,500 and about three weeks of two lanes, for silicon data on the PUF, TRNG, register file and pads. Skip: first silicon is also the first product attempt |
| D13 | Characterisation ring array with owner-signed read-out | **Yes**, at least 16 quads in the key array's block; now in the total | 6,500 µm². Without it there is no silicon measurement of PUF entropy that does not also expose key material |
| D14 | What gives way for the PUF, the placed register file and the measured control logic (7.3) | **Use U5 now. Then, only if the sequencer reductions of 7.1 and the routed result do not find the rest: the shield before any part of the PUF** | Every organ: 1,015,400 µm², far above anything placed. Without U5: 931,100, still 23,000 over the placed point. Without U5 and the shield: 914,800, at it. Each further step is a security claim given up: probing resistance (shield) or key entropy 131 → 98 bits (PUF of three blocks) |

D8 (round-per-clock Keccak) is closed: it does not fit this slot.

---

## 11. Configuration S, maximised

This section records how the configuration in sections 3 to 7 was arrived at for `SLOT_0P5X0P5` with
chip-on-board packaging: how much area is really available, what the default pad ring fixes, and which ways
of getting a stronger gate into the slot were weighed. New measurements are from hbox jobs `arch7` and
`arch8` (`scratch/lanes/fable-dregg180-smax.last.md`).

### 11.1 How much area is available

Nothing has ever been routed in this slot by this project. The evidence is three placement runs here and one
run in the larger slot:

| Run | Synthesized cells µm² | Geometric fill | Placer-reported | Outcome |
|---|---:|---:|---:|---|
| Pre-Dregg chip, 30,069 cells (`librelane/reports/ll_summary.txt`) [C] | about 835,000 | 50 % | 55.2 % | 7,362 repair buffers, legal placement; clock tree never finished; nothing after it ran |
| Tree at the time of the state report, `pnr1` [C] | 1,276,978 | 76 % | 83.8 % | stopped in buffer repair |
| Basin search, 13:30 snapshot [C] | 1,451,093 | 87 % | 96.7 % | 12,886 repair buffers took cells to 1,791,602 (+ 23.5 %), 107 %: no legal placement. With a third of the repair, 102 cells could not be legalised at 93.6 % |
| Same netlist in `SLOT_1X0P5` [C] | 1,451,093 | 29 % | 31 % | placed, clock tree, global route with zero overflow |

Reading them:

- **Placeable area** is 1,673,768 µm² after tap and endcap cells [C]. The identification macros are in the die
  corners outside the core and cost nothing. Geometric fill is cells over that area.
- **The placer's own figure** is 10 to 15 % above geometric in every run (cell padding); the 62 % target in
  `config_qsag.yaml` is on that scale and corresponds to 54 to 56 % geometric, 0.90 to 0.94 M µm².
- **Growth after synthesis.** Buffer repair added 23.5 % in the one run where it completed. Clock-tree and
  hold buffers come after that and have never been measured here.
- **Routing was not the limit** in any run: global routing used 39 % of the tracks even with cells at 107 %.
  Legal placement after repair is the limit.

| Line | Synthesized area | Fill after + 23.5 % repair | Status |
|---|---:|---:|---|
| Demonstrated | about 0.84 M | 62 % | The one design that passed repair and legal placement |
| Ceiling: the configured 62 % target | 0.92 M | 68 % | Never reached with a legal result; no failure known below it either |
| Known failures | 1.28 M, 1.45 M | 94 %, 107 % | Repair or legalisation failed |

Superseded by the measurements of the physical-design lane reported in 7.3: budget by synthesized area ×
about 1.16 against the placeable area, with the ROM counted at twice its cell area. The reasoning below is
the earlier estimate, kept for the record.

**The area ceiling is 0.92 M µm² of synthesized cells, and the design point should be at or below 0.84 M.**
Between 0.92 M and 1.28 M there is no evidence at all. The organ regions (PUF corner with a halo, NFC and
distance against their pads) need local fill of at most 70 to 75 % [C, basin search]; after repair, 0.92 M
leaves almost nothing for that and 0.84 M leaves some.

Since this was written the physical-design lane has placed a proxy of 889,888 µm² legally with the register
file as a placed array (61.5 % after a repair growth of 15.7 %; `scratch/lanes/fable-dregg180-phys.last.md`,
preliminary, clock tree and routing pending), which moves the demonstrated line from 0.84 M to 0.89 M of
this cell mix. Hand-placed arrays take no repair buffers, so the comparison is made on fill after repair in
7.3. Configuration S with every organ is 1,015,400 and does not fit; without use U5 it is 931,100, and
without U5 and the shield 914,800.

### 11.2 What the default pad ring fixes

From `librelane/slots/slot_0p5x0p5.yaml` and the template's rules [C, slot lookup report]:

- 56 pads at fixed positions: clock, reset, 38 bidirectional, 4 inputs, 4 analog (48 signal), and 8 supply
  pads (3 DVDD, 3 DVSS, 1 VDD, 1 VSS). Chip-on-board needs these positions unchanged; signal pads may change
  type among bidirectional, input and analog; the supply pads may not change.
- In the foundry pad library the core and pad rails are shorted, so the core is fed by four supply pairs,
  one per side. No more can be added. The ground-bounce finding of the SPICE lane (1.2 V with an eight-bit
  bus switching) is answered by never switching more than one or two outputs together, not by more pads.
- Pin plan: SPI 4 (south 0..3, beside clock, reset and a supply pair), FRAM SPI 4 and tamper (north 22..26),
  NFC 3 (east 8..10), distance challenge and response (east 13, 14, adjacent to the east supply pair), FAULT,
  IRQ, clock monitor (east 16, 17, 21), 2 straps and chip select (west inputs): 19 of the 42 general pads.
  The other 23 bidirectional pads and the 4 analog pads are unused and tied as inputs with pull-downs. It fits.
- Not established: whether swapping the reset pad cell for the Schmitt-trigger variant at the same position
  counts as leaving the default ring unchanged. Ask wafer.space before relying on it; the fallback is an
  external supervisor with a clean edge.
- Chip-on-board means the die is bonded to its own small board. The FRAM, the antenna and any tamper mesh
  are on the carrier, outside that board. Anyone holding the module has board access in the sense of 3.4.

### 11.3 A stronger gate in the small slot: what was weighed

| Option | Area | Rows | Time per verification | What the gate enforces | What does not exist yet |
|---|---:|---|---|---|---|
| G1 only (first S) | 0 beyond the Keccak unit | about 15 scratch | at most 0.16 s | One authority key signed this transition; a threshold only through custody of that key | Host driver; review of the fingerprint argument |
| (d) **G3: `k` of `n` member signatures under a pinned committee root** (4.6) | 0 units; about 50 ROM words | about 19 scratch | `k` × 0.16 s | At least `k` distinct members of the pinned committee signed this transition | Host driver; committee-tree builder. Member signing is ordinary SLH-DSA |
| (a) Goldilocks arithmetic in microcode on the word unit, no field unit | constants 19,691 + about 20,000 of ROM | as option F | about 430,000 clocks per Poseidon2 permutation [E]: about 3.5 minutes per proof | As G2 | Everything listed for option F |
| (a) **Option F: digit-serial Goldilocks unit** sharing the register file | unit 37,801 / 57,211 / 92,376 for 1 / 2 / 4 multiplier bits per clock [M skeletons]; with constants and ROM 75,800 at 1 bit | no extra rows with (b) | about 24 s / 14 s / 9 s per 24-variable proof [D, E] | G2: a Hem proof that a threshold of the pinned committee signed, under a pinned verifier program | Compiler from the `qsag-agg` verifier; restructured verifier per (b); end-to-end run on a real proof; none of the unit is simulated |
| (b), (c) Fold challenges not stored: the host states them up front, the chip keeps a 4-word digest of the stated vector, re-reads and re-hashes the vector at each use, and checks each stated value against the transcript when the transcript produces it | no area | 4 rows instead of 64 | about a third more Poseidon2 permutations | Unchanged, if the argument holds: stated values never enter the transcript and every one is checked equal | The argument is new and unreviewed; it has not been checked against the structure of the real verifier |
| (b) variant: challenges MACed by the chip and held by the host or in FRAM | no area | 4 rows | one Keccak MAC per use; contends with the lanes that hold verifier registers | Unchanged | Not pursued: the digest form needs no key |
| (e) Cuts made to pay for rows and margin | − 48,545 (GF(2^128) unit to microcode), − 25,940 (NCO), − 18,150 (fuses), − 35,000 (link and clock unit restated from skeletons) | | | | |
| (e) Cuts available if option F is wanted | distance and TDC 45,000; shield 16,306; fifth-to-fourth PUF block already taken | | | Loses the proximity guard, or the shield | |

Conclusions:

1. **G3 is the gate for this slot.** It gives the property that was lost when the aggregate verifier was
   dropped, a threshold of a committee checked on the chip, with the Keccak unit alone, no new cryptography
   and no compiler. Its cost is time and bandwidth that grow with `k`: fine for committees of tens, about
   half a megabyte and ten seconds at 67 of 100.
2. **What only G2 would add** is a proof whose size and verification time do not grow with the committee,
   and a general proof-checking machine that could later verify statements other than signatures. That is
   what option F buys for 75,800 µm² and tens of seconds per proof.
3. **Option F fits under the ceiling only on paper** (898,500 against 0.92 M, with 178,000 of estimate in
   the baseline); honestly it displaces an organ. It also rests on a compiler and a verifier
   restructuring that do not exist. It is not part of the baseline and not for Run 3 (decision D5). The row
   problem that excluded it from the first S is solved on paper by (b); the unit is three times smaller
   than the smallest one measured before.

### 11.4 What configuration S is, in one list

- One 72-row register file; lane-serial Keccak; word unit; microcoded sequencer with about 2,000 ROM words.
- SPI host link; FRAM master; TRNG; pad clock with a fixed ring as monitor; tamper, shield, glitch sensors.
- PUF with 1,008 rings in 252 quads; NFC receiver with a keyed, counted token; distance bounding with
  keyed response bits and a placed fast path; decision D14 recommends building without these two.
- Signer (use U1), anchor and leases (U2), vat (U3), seal and release (U4), guards (U5).
- Gate (U6): G1 and G3. No algebraic verifier, no GF(2^128) unit, no NCO, no fuses, no second link.
- 1,015,400 µm² synthesized with every organ, 931,100 without use U5 [M and E as labelled in 7.1]: 69.2 % and
  62.9 % of the placeable area after buffer repair, against 61.5 % placed so far (7.3).


---

## 12. Microcode placement and the v3 shape

Asked by the owner: could the microcode live outside the chip, and what would let the design scale to faster
clocks and smaller nodes. Figures are from the model's interpreter on real 128s statements
(`v2/tests/report.py` and a trace of every micro-PC), the stage 2 RTL's synthesis, and the physical-design
lane's placement; [D] marks arithmetic on them.

### 12.1 What the ROM costs and what is in it

The image is 1,443 words now and about 2,000 with stage 5: 85,200 µm² of cells at 42.6 per word, and about
twice that in floor, because the ROM as random logic is the block that congests (7.3). By source: key range
55, record routines 191, sponge and shared hashing 111, signer 207, PING 21, idle 1 ("hot": 586); TRNG policy
141, signature verification 307, lifecycle, statements and gate 409 ("cold": 857).

Two measured facts decide most of what follows.

- **A stored bit that can be written costs about 47 times a ROM bit here.** The register file is 4,575 µm²
  a row, 71 per bit; the ROM is 42.6 a word, 1.5 per bit (3 with its routing floor). There is no dense
  writable memory in this flow: the foundry SRAM macro is 51 µm² a bit and byte-wide (5.2).
- **The work is not where the words are.** One gate statement runs 950,000 micro-instructions, 872,000 of
  them in the 30-word fingerprint loop, between 2,704 Keccak calls that take 1.86 M of its 2.8 M clocks. A
  WOTS signature runs 14,005 micro-instructions around 552 Keccak calls: 25 instructions a call, 96 % of the
  clocks in the unit.

### 12.2 External microcode

Fetch cost [D]: the FRAM port at SCK = clk / 4 moves a 28-bit word in 112 clocks and re-addresses in 128; a
quad-SPI flash at SCK = clk / 2 moves a word in 14 clocks and re-addresses in 28. While the Keccak unit runs
(721 clocks) a prefetcher can bring 6 words over plain SPI or 51 over quad.

| Variant | ROM words left (of about 2,000) | Cells / floor freed | Signer | One gate statement (0.11 s today) |
|---|---:|---:|---|---|
| (c) none: today | 2,000 | 0 | as 7.4 | as 7.4 |
| (b) hybrid: cold routines external, executed in place, no cache | about 900 | 47,000 / 94,000 | unchanged (in ROM) | quad: + 18.7 M clocks, 0.86 s. Plain SPI: + 128 M clocks, 5.2 s |
| (b) with a cache of two 16-word blocks | about 900 | as above, less 64,000 for the cache | unchanged | quad + 64 %; plain SPI + 490 % (6,026 block fetches) |
| (b) with a cache of four 16-word blocks | about 900 | as above, less 128,000 for the cache | unchanged | quad + 3 %; plain SPI + 22 % (274 block fetches) |
| (a) everything external but a stub (key and record routines, sponge, authenticator: about 360 words) | 360 | 70,000 / 140,000 | quad: prefetch hides it (25 words a call against 51). Plain SPI: 4.8 times slower | as (b) |

The cache is what makes it fast and the cache is what makes it pointless: 64 words of latches cost more than
the 1,100 words of ROM they would replace. Register-file rows cannot be borrowed: a row holds two
micro-words, a 16-word block is eight rows, and a gate statement already uses all 24 scratch rows (4.3).
Executed in place without a cache, the fingerprint loop alone makes verification seven times slower on the
best link. So on performance and area: (a) and (b) do not pay in this node. They would pay in a node with
dense memory, which is 12.4.

**The security argument** is the larger objection, and it would remain in any node.

What an arbitrary program cannot do, by the decoder rules alone (5.3; proved on the stage 2 RTL with ROM
contents free for the stage-1 rule set): put a key row, the PUF response, or anything computed from them
into the response, the FRAM, a scratch or state row, a loop count, an index or a branch, except through the
three declassification instructions; read the capacity of a keyed sponge; address the out rows; end a
command without the wipe. If it runs outside the hardwired key and record ranges it cannot itself issue a
key write, a FRAM instruction, a state-row write or a lifecycle change.

What it can do, with the rules as they are:

- **Misuse declassification.** `REL` releases the rate of any completed permutation over a keyed state. A
  program that copies `K_dev` into the lanes with a label of its choosing and permutes can release
  `SK.seed`, `SK.prf`, the record MAC key, or a chain value at step 0. Every derived key falls; only the
  raw `K_dev` rows and the raw PUF response do not.
- **Skip the counter, a check, or a verdict.** The counter discipline, the request tag, the lease bound
  and the retirement check are sequences of instructions, not rules.
- **Call into the middle of the trusted ranges.** The range rules restrict where an instruction sits, not
  how it is reached. A `CALL` to the record-update routines writes any lifecycle record, tagged under
  `K_dev`; a cleared compare flag and a `CALL` to the latch routine gives `READY`.
- **Declare any response length.** The cap is an operand of the routine's own `HDR`.

So an unauthenticated external program is a total loss of everything but `K_dev` itself, and fetched code
has to be exactly as authentic as the ROM. Against someone who holds the board:

- A digest of the whole image checked at boot is defeated by changing the memory, or the bus, afterwards.
  Authentication has to be per block and has to finish before any word of the block executes, which is
  another reason a block buffer is unavoidable.
- **What can authenticate a block.** (i) The sponge: not available, the running routine's state is in the
  lanes; a tag checked only at routine boundaries leaves every block in between unauthenticated when it
  runs. (ii) A hash tree under a pinned root: seven Keccak calls a block for 128 blocks, and the same
  conflict. (iii) A dedicated polynomial MAC over GF(2^64) under a key derived from `K_dev`: the multiplier
  is small (about 20,000 µm² [E, half the measured GF(2^128) unit]), but a polynomial tag stored in the
  clear on the board gives its key away after two blocks, so each tag needs a pad from a keyed function of
  the block address and image version, and the only keyed function on the chip is the sponge. That means a
  second, small PRF in hardware (20,000 to 30,000 µm² [E]) and a new cryptographic design to review.
  Only (iii) works, and with the block buffer it costs more than the ROM it frees.
- Tags under a device key mean each chip signs its own image at enrolment, so the enrolment, boot and
  verification code that decides which image to accept must be in ROM anyway: that is most of the cold set.
- **Rollback.** The image version has to be bound into every tag and held in the lifecycle record. On an
  unleased chip a restored FRAM image then restores the old version with it, and the old microcode is
  authentic again: the residual of 3.4 would extend from counters to code, so a routine with a known defect
  could be put back by anyone holding the board. A leased chip could have the authority name the minimum
  version in the lease.
- Every fetch is also a place to inject a fault from the board.

### 12.3 Hardware macro-operations, so that code need not be trusted

The idea: make the declassification points and the counter discipline hardware-sequenced operations that
carry their own checks, and give every row a taint tag with a kind, so that code can sequence the
operations and cannot misuse them.

What that takes, concretely:

- **Typed key derivation.** A derive operation whose label is one of a hardwired few and which tags the
  lanes with the kind of what they now hold (request-tag key, signing seed, randomiser key, record key).
  `REL` and `CMPT` check the kind: a signing seed is never releasable; a randomiser output is.
- **A chain operation.** PRF, then exactly `d` steps of `F`, with `d` from a hardware digit queue loaded
  from a digest the hardware computed, and a release only at the end. About the 60 words of the signer's
  inner loops as a state machine.
- **An atomic counted-sign start.** Compare the leaf with the counter, write the record, read it back, and
  only then arm the chain operation for that key pair.
- **Entry points.** Trusted ranges enterable only at listed addresses.
- **Per-row tags.** Three bits a row, 216 flops, about 15,000 µm² [E].

With all code free this would make provable: no signing seed or derived key leaves except as the public
outputs of the signature scheme at the step counts the scheme prescribes; a counted key's counter is
advanced and stored before its first release. That is use U1 and U2 against a malicious program.

What it does not reach is authorisation. A gated transition is safe only if the verdict is true, and the
verdict is the output of 300 words of signature verification, the statement hashing and the committee
check. If that code is not trusted, the record-update operations are open to it whatever their own checks
are. The same holds for the nonce policy (a lease is only as fresh as the health tests are honest) and for
boot. Making those hardware operations too is writing the ROM again as state machines: no smaller, and
harder to review. Counted in words, the code that would still have to be authentic is the key and record
routines, the hashing, verification, statements and the gate, and the TRNG policy: about 1,000 of the 1,443.

So in this chip the trusted core cannot be made small, because almost nothing on it is anything but
security policy. Macro-operations are the right structure for a chip that also runs code it does not
trust (a vat with programmable guards, new protocols loaded in the field). They are not a way to save area
in S. Two pieces are worth taking into v2 regardless, because they close gaps found in 12.2 for a few
dozen gates: **entry points** for the trusted ranges, and a **kind tag on the lane taint** so that `REL`
cannot release a derived key. Both are decoder rules of the kind already modelled and proved.

### 12.4 What ties v2 to this node, and the parameters of a generator

| In v2 | Tied to | Parameter a generator exposes |
|---|---|---|
| Lane-serial Keccak, 721 clocks a call | area in a 180 nm slot | Keccak slicing: clocks per round, from 30 (lane-serial) to 1 (round per clock: 342,265 µm² here [M], negligible below 65 nm) |
| Register file of standard-cell latches, one read port | no dense memory in the flow | storage: latch array or memory macro; ports. The clear-with-clock-stopped requirement (5.2) is what a macro has to meet |
| One clock from micro-PC to hold register, 79 ns at SS | the ROM and word unit in one stage | pipeline depth: 1, 2 (instruction register), 3 (row read registered) |
| Fingerprint as 422 instructions a product | no multiplier in S | a GF(2^64) multiply-accumulate unit, serial or one clock |
| ROM as random logic | synthesis | ROM structure; microcode in a memory macro (which is where 12.2 becomes cheap, and where its authentication question stays) |
| Ring-oscillator PUF and TRNG, their thresholds | process, layout, supply | organ interfaces as they already are in the model: start, done, a statistics port, a response port under the key rule; all thresholds are microcode constants |
| FRAM as the only non-volatile state | no trustworthy NVM in the PDK | a monotonic counter organ, if a node has one: it removes the unleased residual of 3.4 |

What the instruction set, the microcode, the model and the proofs depend on: the row classes and their
counts, the hardwired address ranges, the rule set, and the unit and organ interfaces (start, done, clocks).
What they do not depend on: how many clocks a unit takes, how the file is built, the pipeline depth (it
changes the stall rule, which is a rule about clocks and not about values: the output-bound and taint
properties are stated over instructions), the clock, the node. The model takes unit clock counts as
constants (`units.py`), so a design point is a set of constants; the clocks-per-instruction rules are the
one place where the RTL lane reports and the model follows.

Per-operation times at three design points. A is S as specified; B adds one unit to it; C is a v3 shape.
Arithmetic [D] from the measured instruction and call counts: one gate statement is 2,704 Keccak calls,
950,000 instructions of which 872,000 are the fingerprint, 221,000 taken transfers; a worst-case WOTS
signature is 552 calls, 14,005 instructions, 3,354 taken transfers.

| | A: v2, two-stage, 25 MHz, GF180 | B: A with a serial GF(2^64) unit (64 clocks a product, about 20,000 µm² E) | C: v3, round-per-clock Keccak (about 32 clocks a call E), one-clock GF(2^64) product, two-stage, 100 MHz |
|---|---:|---:|---:|
| Keccak call as microcode uses it | 748 clocks | 748 | about 60 |
| One gate statement (128s) | 3.04 M clocks, 0.12 s | 2.2 M, 0.09 s | 0.19 M, 1.9 ms |
| 3 of 5 committee | 0.36 s | 0.26 s | 6 ms |
| WOTS signature, most steps | 0.40 M, 16 ms | same | 35,000, 0.35 ms |
| SLH-DSA-128s signature, cold / with root cache | 64 s / 12 s | same | 1.3 s / 0.24 s |
| What limits it | the Keccak unit (two thirds of a verification, 96 % of signing) | the Keccak unit | microcode: half the clocks of a call are lane set-up |

A assumes one more clock for each taken transfer and nothing else; the RTL lane's measured two-stage counts
replace that. At C the microcode around each hash call is as long as the call, so the next step there is
fused set-up operations, not a faster unit.

### 12.5 Recommendation

1. **v2: microcode stays in ROM** (variant c). External microcode saves no area in this node once its
   buffer and authentication are counted, slows verification several times without a buffer, and extends
   the rollback residual from counters to code.
2. **Fix the ROM's floor cost where it arises.** In order: write the 1,443 words for size; split the image
   into banks that place separately (the congestion is one block of 28 outputs fanning out of one region);
   a ROM array placed by script, as the register file is; only then a custom contact-programmed array,
   which carries the same foundry-deck risk as any custom cell. The physical-design lane can measure the
   second and third on the image that exists.
3. **Take the two decoder rules of 12.3 into v2** (entry points; a kind tag on the lane taint). They cost
   little and remove the two ways in which the present rules lean on ROM content that 12.2 exposed.
4. **v3 is a generator**, with the parameters of 12.4, the same instruction set and model, and macro-
   operations if and only if the chip is to run code that is not part of its own policy.

The decision is the owner's: whether any of 3 goes into this tape-out, and whether v3 is specified as a
generator now (which constrains how stage 5 is written) or after first silicon.

---

## Appendix A. Configuration L, the larger-slot variant

Not the target. `SLOT_1X0P5` is $5,000 plus $1,500 for chip-on-board in Run 3. This is the configuration as
specified before the small-slot decision; its numbers were not revised with the measurements of section 11.

L is S plus: the existing parallel Goldilocks unit (`qsag_gl64_karatsuba_csa`, 241,580 µm² [M]: product in 3
clocks, Poseidon2 permutation 3,074, Ext4 product 105 [M]) with its micro-sequencer and constants (34,309);
64 challenge rows (rows 64 to 127 of a 128-row file) that hold the G2 fold challenges; the GF(2^128) unit;
a 256-bit fuse macro; a fifth PUF block; the NCO.

| Block | L | Basis |
|---|---:|---|
| Register file, 128 rows | 550,122 | M |
| Keccak unit less its rows | 90,650 | M |
| Goldilocks unit | 241,580 | M, existing |
| Field micro-sequencer, constants | 34,309 | M |
| GF(2^128) unit | 48,545 | M |
| Word unit | 34,329 | M, skeleton |
| Microcode ROM, 2,048 words | 93,400 | E |
| Sequencer | 23,985 | M, skeleton |
| SPI link, diagnostics | 45,000 | E |
| PUF, 630 rings | 125,000 | 55,440 M + 70,000 E |
| NFC, NCO | 60,000 | 54,669 M + E |
| Distance, TDC | 45,000 | M |
| Clock, reset, tamper, shield | 50,000 | E |
| TRNG, FRAM SPI master | 25,739 | M |
| Fuse macros and glue | 84,480 | LEF + E |
| Redundant decision bits, checkers, glue | 20,000 | E |
| **Total** | **1,572,139** | 31.3 % of the 5,020,056 µm² core |

In L the G2 verification of a 24-variable proof is about 40 M clocks, 1.6 s at 25 MHz plus 0.8 s of transfer
[D, E], and a round-per-clock Keccak (+ 223,000 µm² net) would take SLH-DSA-128s signing with the root cache
from 12 s to about 0.7 s [E]. The same netlist class placed, clock-treed and globally routed with zero
overflow at 31 % in this slot [C, basin search]. `v2/` already carries the Poseidon2 and Merkle commands for
this configuration (`ucode/field.uc`).
