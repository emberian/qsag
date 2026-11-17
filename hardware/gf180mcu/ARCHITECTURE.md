# Dregg-180 architecture specification

Status: proposal for the owner's agreement. No RTL has been changed to match it. Where this document and
`README.md` disagree, `README.md` describes the RTL as it is and this document describes the target.
Stage 1 of section 9.3 (the executable model and its microcode) is in `v2/`; `v2/README.md` lists each place
where implementing it changed this document, and those changes are already made below.

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
11 configuration S, maximised · appendix A configuration L.

**Result in one paragraph.** The target is `SLOT_0P5X0P5` with chip-on-board packaging and the default pad
ring (owner decision; section 11). The configuration specified for it, **S**, is about 0.82 M µm² of
synthesized cells: one 72-row register file, one lane-serial Keccak unit, a microcoded sequencer, an SPI
link, and the PUF, NFC, distance, tamper and TRNG organs. That is just under the size of the only design
that has passed buffer repair and legal placement in this slot (0.84 M); the ceiling is about 0.92 M, and
nothing has ever been routed in it. The gate verifies, with the Keccak unit alone, either one authority signature or `k` signatures
of distinct members of a pinned committee (4.6). On-chip verification of aggregate (Hem/WHIR) proofs needs a
field unit and about 76,000 µm² more; it is an option that does not fit beside all the organs (11.3). The
eFuse macros are not relied on: the chip has no non-volatile state of its own, and section 3 states what
follows from that. Configuration S cannot credibly be taped out in Run 3; an engineering sample might be
(9.4). The larger-slot variant **L** is appendix A.

---

## 1. Purpose and uses

Dregg-180 is a hardware root of trust for the qsag protocol suite. It holds secrets that an untrusted host
must not be able to read or use outside a policy, and it advances security state only on evidence it has
verified itself. The protocol roles below are taken from the crates named; "in scope" means this silicon
implements the chip-side operation.

| Use | Protocol role (source) | Chip operation | What the chip guarantees that host software cannot | Scope |
|---|---|---|---|---|
| U1 Signer | SLH-DSA-SHAKE, n = 16 (128s, 128f) and the WOTS+C / FORS operations of Baggy and Jorts (`crates/qsag-core/src/fips205.rs:452-530`, the four secret-touching oracles at `:3225-3290`) | `PRF`, `PRF_msg`, `H_msg` digits, WOTS chains and FORS leaves from `SK.seed`, `SK.prf` | The seed never leaves. Chain positions are chosen by the chip from a digest it computed, so no request can obtain a chain value below the one a valid signature publishes. This holds once the digest is computed on chip (stage 5); the stage-1 model takes a 16-byte message from the host | In |
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
| Host, coprocessor mode | A host that holds `K_host` may request any U1 operation | Reading keys; changing lifecycle |
| Host, vat mode | Transport only. It is the bearer of capabilities | Confidentiality, integrity, choice of chain positions, time, counters, guard results |
| FRAM | Availability | Confidentiality, integrity, freshness. It is on the carrier board, outside the chip-on-board package: an attacker with board access can read it, rewrite it and restore an older image |
| NFC token, distance peer | Holding `K_tok`, derived for it at provisioning | Anything not carried under that key |
| Physical attacker | — | Assumed able to drive every pad, reset and power-cycle at will, glitch clock and supply, and rewrite the FRAM. Invasive attacks on the powered die are addressed only by the tamper input, the shield and zeroisation |

**Two modes, chosen once.** The coprocessor role (the host with `K_host` is trusted to ask for signatures)
and the vat role (the host is an untrusted bearer) cannot hold on the same keys at the same time. The mode
is fixed at enrolment commit and carried in every lifecycle record (3.1):

- **COPROCESSOR**: every U1 request that releases a value derived from `SK.seed` (WOTS chains, FORS leaves,
  public-key generation included) carries a MAC under `K_host`. `PRF_msg` is not tagged: it releases only the
  randomiser that every signature publishes. Vat, guard and gate commands for capabilities are
  refused. `K_host` is loaded at enrolment and is the only key a host ever supplies.
- **VAT**: `K_host` does not exist. Every secret-touching request, including public-key generation, needs a
  capability. Root capabilities are minted during enrolment or by a gated transition.

Everything else (U2, U4, U6, lifecycle) is the same in both modes.

---

## 3. Security state and lifecycle

The chip has no non-volatile state of its own. The eFuse macros in the PDK come from a compiler whose authors
describe them as not proven in silicon, and no programming conditions are published
(`scratch/lanes/sonnet-slot-price-and-efuse.last.md`), so no security property below depends on a fuse. Every
bit that survives power loss is in the FRAM on the carrier board, outside the chip-on-board package. Section
3.4 states what that does and does not allow.

### 3.1 Where state lives

| State | Storage | Survives reset | Survives power loss | Cleared by |
|---|---|---|---|---|
| Device key `K_dev` (256 bit) | Not stored. Re-derived at each boot from the PUF response and the helper data | re-derived | re-derived | any reset, tamper, zeroise |
| `SK.seed`, `SK.prf`, `K_host`, `K_vat`, `K_fram`, `K_seal`, `K_tok` | Key rows of the register file, derived from `K_dev` by labelled TurboSHAKE256 at boot or on use | re-derived | re-derived | any reset, tamper, zeroise |
| Helper record: PUF syndromes, check tag, owner-root signature over them | FRAM, written once at enrolment | yes | yes | — (public, static, replayable by design) |
| Lifecycle record: `seq`, `gen`, mode, policy flags (leased, mint lock, retired), use counter `u`, spend counters, epoch, NFC counter, authority pin (key, or committee root and threshold), verifier pin, PUF failure count | FRAM, two slots written alternately, each MACed under `K_fram = KDF(K_dev, "fram")` | yes | yes | superseded by a higher `seq` |
| High-water marks of `seq` and `u` | Volatile registers | no | no | reset |
| Session lease: nonce, upper bounds on `u` and spend for this power session | Volatile registers | no | no | reset |
| Session state: gate verdict, transition register, guard results, working rows | Volatile, wiped by the epilogue of every command | no | no | every command end |
| Optional: fuse bits mirroring `gen` and the retired flag | One `efuse_async_mem_1x8` macro, if fitted (decision D2) | yes | yes | never |

Nothing that authorises an action is a volatile bit whose reset value is permissive. After any reset the chip
holds no key and accepts only diagnostics until boot (3.3) completes.

### 3.2 States and allowed transitions

`BLANK` (no authentic helper record) → `PROVISIONED`. Each power session of a provisioned chip goes
`BOOT` → `READY`, or `BOOT` → `LEASE_PENDING` → `READY`, or `BOOT` → `ORPHAN`, or `BOOT` → `LOCKED_OUT`.
Retirement is a flag of the lifecycle record.

| From | To | Trigger | Condition | Effect |
|---|---|---|---|---|
| BLANK | BLANK (enrol session) | `ENROL` | No authentic helper record | PUF enrolment. The chip emits the helper data and a fresh nonce `N`. No key is usable and nothing else is enabled |
| BLANK | PROVISIONED | `COMMIT` | In the same power session: an owner-root signature (4.3 routine, mask-constant key digest, D3) over `N`, the helper-data digest, the mode, the policy flags and the first authority pin; helper record and both lifecycle slots written and read back | First lifecycle record, `seq = 0`. The record never grants more than later ones: there is no enrolment-only privilege to return to |
| PROVISIONED | BOOT → READY | reset release | Helper record authentic; PUF reconstruction passes its check tag; a lifecycle record with a valid MAC exists; not retired; policy not leased | Keys derived; counters loaded |
| BOOT | LEASE_PENDING → READY | as above, policy leased | A gate statement (4.1) for transition `LEASE` over this session's nonce, the reported `seq`, the authority's `gen`, and the granted base and bounds | `u` and the spend counters jump to the granted base; they may not pass the granted bounds in this session |
| BOOT | ORPHAN | reset release | Helper record authentic, no valid lifecycle record | Only `REINIT` is accepted |
| ORPHAN | PROVISIONED | `REINIT` | Owner-root signature over a fresh nonce and a new first record | New record with `gen` above any the owner has issued for this chip |
| BOOT | LOCKED_OUT | reset release | Any other check fails | Diagnostics only until the next reset. Nothing is erased, so a transient fault cannot brick the part |
| READY | READY | gated transitions of 4.2 | Gate verdict for that exact transition | Record updated, `seq` + 1 |
| READY | READY (retired) | `RETIRE` | gated | Retired flag set; the chip derives no keys at later boots |

`ENROL` is not usable by replay: erasing the FRAM and writing the original helper record back gives `ORPHAN`,
not an enrolment session, and `COMMIT` and `REINIT` need a signature over a nonce the chip drew in the same
power session. A chip whose FRAM is lost is useless until the owner root re-initialises it.

### 3.3 Boot

1. Reset releases on the pad clock (6.6). No internal oscillator, sensor or the TRNG is needed to reach step 4.
2. Read the helper record. Verify the owner-root signature over it with the ROM routine of 4.3 (no secret is
   involved, so this happens before the PUF is touched). No record: `BLANK`.
3. Run the PUF, decode, compare the check tag in constant time (6.1). Derive `K_dev` and the key rows.
4. Read both lifecycle slots, verify each MAC under `K_fram`, take the valid one with the larger `seq`.
5. Unleased policy: `READY`. Leased policy: draw the session nonce from the TRNG and the PUF counter noise
   (6.5), emit it with the chip identifier and `seq`, and wait in `LEASE_PENDING`.

Time at 25 MHz: about 0.2 s to step 5 [E] (one signature verification at most 0.16 s [D], PUF 16 ms [D]); a
lease adds one gate verification (0.16 s per signature, 4.6) and the round trip to the authority.

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
failing its health tests would allow an old lease to be replayed; the nonce therefore mixes two sources.

The choice between the two policies is made per chip at `COMMIT` (decision D11). A chip that guards one-time
keys or spend limits against someone who may hold the board has to be leased.

If the optional fuse macro is fitted and proves to work, `ROTATE`, `REINIT` and `RETIRE` also burn a bit, read
back and verified, and boot takes the larger of the fuse and record generations. That would make those three
transitions irreversible on an unleased chip. A fuse that fails to program leaves the chip exactly as
described above.

---

## 4. The verifier as gate

### 4.1 What is verified

A **transition** is a change of security state. The chip builds the transition message itself:

```
m = TurboSHAKE256( "DREGG.TRANSITION/v1" ‖ chip_id ‖ gen ‖ seq ‖ type ‖ H(arguments) )
```

`chip_id` is a public identifier derived from `K_dev`; `seq` is the current record counter. The host never
supplies `m`. A statement is accepted only for the `m` the chip computed, so it cannot be used on another
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
| `MINT` a root capability | yes | There is no ungated mint, in enrolment or after |
| `LIMIT`: raise or re-arm a spend limit | yes | |
| `EPOCH`: advance the epoch counter | yes | Gives the epoch guard a source the host cannot choose |
| `RELEASE`: unseal a blob to the host (U4) | yes | Counted in the record |
| `INVOKE` under a capability with guard `G_PIN_VK` | yes, per invocation | Replaces today's `OP_VAT_ZK` |
| `LEASE` (leased chips, each power-up), `RETIRE`, `ROTATE` (change the authority or verifier pin) | yes | `ROTATE` raises `gen`; the authority refuses leases to a superseded `gen` |
| `COMMIT`, `REINIT`, characterisation read-out | owner root | Signature over a nonce drawn in the same power session (3.2) |
| Mint lock | no | One-way in the record; subject to 3.4 |
| Attenuation, ordinary invocation, U1 requests | no | Authorised by capability or `K_host` |

### 4.3 G1: cost and method

Verification is public computation on the Keccak unit. Count per FIPS 205 [D]: FORS 14 × (1 leaf + 12 path
nodes) = 182 calls; seven layers of at most 35 × 15 = 525 chain steps; 63 tree nodes; `T_k`, seven `T_len`
and `H_msg`. Average about 2,100 calls, at most about 3,900. At 760 clocks per call (721 for Keccak-f [M]
plus load and unload [E]) that is at most 3.0 M clocks for the hashing; with the fingerprint passes below, at
most 3.9 M clocks: **0.16 s at 25 MHz**, about 0.10 s on average.

`T_len` absorbs 35 chain ends over five sponge blocks while each chain needs the sponge for itself, and the
file holds one sponge state. The routine therefore runs two passes: it computes each chain end and folds it
into a polynomial fingerprint under fresh secret points (TRNG output conditioned with `K_dev`); the
host then supplies the chain ends, which the chip absorbs into `T_len` and folds into a second fingerprint;
the two fingerprints must be equal. `T_k` over the 14 FORS roots is handled the same way. The fingerprint is
two polynomial evaluations over GF(2^64) at independent points, computed by a shift-and-XOR microroutine on
the word unit (about 420 clocks per product [E]; about 2,070 products per signature); a wrong sequence passes
with probability below 2^-115 per check. It costs four rows instead of a second 25-row sponge, and no unit:
the GF(2^128) multiplier of the first draft is not needed.
The argument needs review by a cryptographer before it is relied on (stage 4 of section 9).

Rows used by one verification: the digest indices or the WOTS digit queue 4, address context 3, current node
2, fingerprint 4, loop work 2; with G3, the transition message 4. That is 19 scratch rows, which is why
configuration S has 20.

The same ROM routine verifies the owner-root signature at boot.

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
  Leaf `i` is `TurboSHAKE256(i ‖ pk_i)` and a node is `TurboSHAKE256(left ‖ right)`, 32 bytes each, with
  distinct domain bytes for leaf and node. The root, the depth and the threshold `k` are the authority pin
  in the lifecycle record, set at `COMMIT` or by `ROTATE`.
- **Statement.** For the transition message `m` of 4.1, the host supplies `k` items in strictly increasing
  member index: index, public key, Merkle path, signature on `m`. For each the chip recomputes the root from
  the leaf and path and compares it with the pin, runs the 4.3 routine under that public key, and counts.
  The verdict is set when the count reaches `k`. Increasing indices make the members distinct with one row.
- **Cost.** Per member at most 3.9 M clocks (0.16 s) and 7,856 + 32 + 32 × depth bytes.

| Committee | Time, at most | Data |
|---|---:|---:|
| 3 of 5 | 0.5 s | 24 kB |
| 11 of 16 | 1.7 s | 88 kB |
| 67 of 100 | 10.5 s | 0.54 MB |
| 171 of 256 | 27 s | 1.4 MB |

- **What it enforces.** At least `k` distinct holders of committee keys signed exactly this transition, for
  this chip and this sequence number. Members sign ordinary FIPS 205 signatures with existing code.
- **What it needs that does not exist.** The host driver and a committee-tree builder. No compiler, no new
  cryptographic argument beyond the fingerprint of 4.3.
- **Cheaper member keys.** A member key that is a single XMSS tree (one layer of the same structure, stateful
  on the member's side) verifies in about 20 ms with a signature under 1 kB, using a subset of the same
  routine. Not specified further here.

---

## 5. Datapath and control

### 5.1 Principle

One 64-bit register file holds every word of working state and every key. Four arithmetic units read one
row at a time through a single read port and write through a single hold register. One microcoded sequencer
drives them. No unit and no organ keeps a private copy of secret state beyond pipeline registers.

Word width is 64 bits: a Keccak lane, a Goldilocks element and half a GF(2^128) element.

### 5.2 Register file

- Rows of 64 `latrnq_1`, one `icgtp_1` per row, one 64-bit write-hold register, one read port.
  Measured [M]: 64 rows 263,672; 72 rows 296,497; 80 rows 328,657; 128 rows 550,122 (about 4,110 per row, of
  which 3,091 is latches). A second read port costs 85,666 at 96 rows [M] and is not used.
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
| scratch | 20 | working | Staging, capability words, fingerprint accumulators. The signer uses 12 (five address words, four message words, anchor work); signature verification uses 19 (4.3) |
| keys | 10 | key | `K_dev` 4, `SK.seed` 2, `SK.prf` 2, `K_host` or `K_vat` half 2; other keys are derived on use into scratch |
| pins | 6 | public | Capability rights and limits 2, pinned root or authority key 4 |
| state | 2 | public | Loaded lifecycle counters |
| out | 2 | output | Egress FIFO; the only rows the egress mux can read |
| **S total** | **72** | | |

Configuration L (appendix A) adds 64 public challenge rows for a 128-row file. The stage-1 model in `v2/`
still has 12 scratch rows and 64 rows; it grows with the stage that needs them.

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

Rules added after the review of the stage-1 model (`scratch/lanes/sonnet-audit-dregg180-v2-stage1.last.md`);
they are requirements on stage 2 and are not yet in `v2/`:

- **The FRAM master is an output too.** FRAM write instructions decode only inside the address range of the
  record routines, and their data comes only from the record rows and the MAC lanes of that routine.
- **Derived secrets do not steer control.** A taint flag follows the hold register, the index register, the
  loop counters and the compare flag once a keyed permutation has run. A tainted value cannot set the response
  length, a loop count, the index register or a branch, and cannot be written to scratch; the listed
  exceptions are the tag-comparison verdict and the moves in the output manifest.
- **The ranges are hardwired.** Key range, record range, epilogue and idle addresses are constants of the
  sequencer, not data read from the ROM image; the build fails if the image does not match them. The wipe of
  working rows on the way to idle is a sequencer action, not ROM content.
- **Dispatch is gated by lifecycle state** (3.2): before boot completes only diagnostics decode.

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
| Word unit | XOR, AND, OR, 32-bit add and subtract with carry, constant-time compare accumulator, 16-bit immediates; wiring functions on the hold register: nibble swap, byte reversal of each half, half swap, half masks, shifts right by 1, 4, 8, 16 and left by 1, 4, 8 | new | 34,329 [M, skeleton with these functions; an earlier skeleton without the wiring functions was 23,594] | 1 |

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
| Fingerprint (4.3) | Two GF(2^64) accumulators and two points in four scratch rows; shift-and-XOR product in microcode on the word unit |

### 5.5 Control

A microprogram ROM and a sequencer replace the 124-state process of `rtl/qsag_wire_engine.sv:1227-1758`.

- **Micro-instruction** (28 bits in S and in L; layout in `v2/README.md`): 5-bit operation, two 7-bit row
  fields, a 4-bit field (store and immediate flags, or the low bits of a branch target), two index bits
  (row + index register X), a post-increment bit for X, 2-bit sequencing (next, return). Branch, call,
  compare-X and decrement-and-branch are instructions with an 11-bit target. Immediates are 16 bits; 64-bit
  constants come from a small table beside the ROM.
- **Sequencer**: 11-bit micro-PC, two-entry return stack, two 12-bit down counters, 7-bit index register X,
  response-length counter, the rule comparators of 5.3, opcode dispatch gated by lifecycle state. Skeleton of
  this sequencer: 23,985 [M].
- **ROM size.** Estimated routine sizes in micro-words: boot and lifecycle 150, framing and epilogue 80,
  enrolment 180, sponge and MAC subroutines 90, signer 160, G1 160, vat 150, transitions 100, FRAM 80, seal 60,
  NFC 40, distance 60, self-test and diagnostics 80, TRNG 30: about 1,420 for S; plus about 500 for the
  verifier machine in L. Stage 1 wrote the first four of these that it needs (framing, sponge, signer without
  `H_msg` and root tagging, FRAM) in 383 words against 410 estimated, plus 35 for a key-load stand-in; within
  that the signer is 269 against 160 and framing 21 against 80. With the rest of the signer the S estimate is about 1,500 words [E] against 1,536
  budgeted. ROM cost: the stage-1 image with its constant and dispatch tables is 19,072 for 418 words (S) and
  24,981 for 575 words (L) [M], 45.6 and 43.4 per word; random content measured 85,024 for 1,536 × 28 [M]. With the committee gate, the fingerprint microroutine, leases and the owner-root routines the
  S estimate is about 1,700 words [E]. Budgeted: 1,700 words at 45.6 = 77,500 [E, extrapolated from a quarter
  of the ROM]; option F adds about 400 words.
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
material is tied to it.

### 6.1 PUF and key derivation

- **Array.** 252 disjoint pairs of adjacent ring oscillators (504 rings), one pair enabled at a time, each pair
  placed as neighbours. One response bit per pair. The existing 64-ring design compares 32 rings against 32 at
  16 offsets; its 480 bits are not independent and are replaced.
- **Entropy account.** Four BCH(63,36,5) blocks in the syndrome (code-offset) construction, fixed pairing, no
  selection mask. Each block publishes 27 syndrome bits. With min-entropy `h` per response bit the remainder is
  4 × (63·h − 27): 144 bits at h = 1, **131 bits at h = 0.95**, 119 at h = 0.90 [D]. The claim is 128 bits and
  holds for h ≥ 0.94. `h` must be measured (Monte Carlo before tape-out, silicon after). Five blocks (630
  rings) give 148 bits at h = 0.90 for about 11,000 µm² more (decision D6).
- **Reliability.** Each bit is the majority of three measurements. Count windows of 10–20 µs [C,
  `astra-dregg180-spice-pcb.last.md`]. Rings must be slowed or prescaled so the first counter stage sees at most
  400 MHz at the fast corner; the measured 400–1,120 MHz range [C] is too fast for an unproven toggle stage.
- **Helper data before use.** The helper record carries a signature by the owner root key, verified in boot
  step 3 before the PUF runs. After decoding, the check tag `TurboSHAKE256("DREGG.PUFCHK" ‖ w)` is compared in
  constant time before any key row is written. The decoder runs a fixed number of clocks whatever the error
  pattern. With fixed pairing and no mask, a rejected attempt reveals bit reliability, not bit value.
  Failed attempts are counted in the lifecycle record.
- **Key.** `K_dev = TurboSHAKE256("DREGG.KDEV" ‖ w ‖ enrolment nonce)`. All other keys are labelled derivations.
- **Test hooks.** No ring of the key array has a path to a pad in any state, and there is no injected-flip
  input: a hook gated by lifecycle could be re-opened by erasing the FRAM, and ring frequencies with the
  helper data give the key. Silicon characterisation uses a separate array of 16 pairs that feeds no key; its
  counts are read out only under an owner-root signature over a fresh nonce (decision D13).
- **Needs from the datapath:** Keccak (KDF, tag), one scratch row per block. **Private area:** array 44,115 [M
  for 252 pairs; 55,440 for 315]; counters, BCH decoder and control about 70,000 [E, from the existing leaf's
  76,551 M less its 64 rings]. Total about 114,000.

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

Existing two-ring source with repetition-count and adaptive-proportion tests. Raw words are never output
after lock. Every use conditions at least 512 raw bits through TurboSHAKE256 together with `K_dev`. Boot does
not need the TRNG; a health failure refuses only the commands that need fresh randomness (enrolment, G1
fingerprint points, nonces) and sets a status bit; a leased chip then stays in `LEASE_PENDING`. The lease
and enrolment nonces also absorb the low bits of the PUF ring counters of that boot, a second noise source
that shares nothing with the TRNG rings. Area 13,035 [M].

### 6.6 Clock, reset, pads, power

- **Clock.** The core runs on the pad clock from reset, selected combinationally by a strap. One fixed ring
  oscillator serves as loss-of-clock and frequency-window detector and, by strap, as an alternative clock for
  bring-up. The tunable DCRO, its loops, the replica path and dither are removed.
- **Design clock 25 MHz** (40 ns). The current 20 ns target has never been met; no timing exists for this RTL.
- **Reset.** Schmitt-trigger reset pad with pull-down (the pending `scripts/pending_src_b4_b6.patch`), external
  supervisor on the board. The secret-reset net asserts asynchronously and releases synchronously; the
  sequencer waits 16 clocks after release before its first write.
- **Pads:** the default pad ring, unchanged, as chip-on-board requires (11.2). SPI 4, FRAM SPI 4, NFC 3,
  distance 2, tamper 1, FAULT 1, BUSY/IRQ 1, clock monitor 1 (pad clock divided, no internal node), 2 straps:
  19 of the 42 general pads, plus the dedicated clock and reset pads. Unused pads are tied as inputs with
  pull-downs.
- **Power.** One 5 V domain; core and pad rails are shorted in the pad library. The 1.2 V ground bounce [C]
  came from the eight-bit parallel link switching together; with SPI only, one output switches at a time,
  slew-limited. The default ring has four supply pad pairs, one per side, and none can be added.
- **Fuses.** None in configuration S. `gf180mcu_re_efuse` in the PDK provides `efuse_async_mem_1x8`
  (97.27 × 83.02 µm, 8 bits) with 5 V timing libraries; it programs from the 5 V rail through on-macro PMOS
  with a 50 µs pulse [C, compiler documentation]. Its authors describe it as not proven in silicon, and no
  programming current, retention or yield figure was found. It may be fitted later as redundant hardening
  only (3.4, decision D2).

---

## 7. Budget

### 7.1 Area

Core of `SLOT_0P5X0P5`: 1,052 × 1,647 = 1,732,644 µm². How much of it can be filled is section 11.1.

| Block | Configuration S | Basis |
|---|---:|---|
| Register file, 72 rows | 296,497 | M |
| Keccak unit less its rows | 90,650 | M: 112,280 − 21,630 |
| Word unit | 34,329 | M, skeleton of the unit as modelled in `v2/` |
| Microcode ROM | 77,500 | E: 1,700 words at the 45.6 µm² per word measured on the stage-1 image |
| Sequencer | 23,985 | M, skeleton of the sequencer as modelled in `v2/` |
| SPI link, diagnostics | 25,000 | E from a 22,764 M skeleton |
| PUF, 504 rings | 114,000 | 44,115 M + 70,000 E |
| NFC receiver, no NCO | 35,000 | 28,729 M (existing leaf with the NCO removed) + 6,000 E for the longer token frame |
| Distance, TDC | 45,000 | 44,593 M |
| Clock, reset, tamper, shield | 35,000 | 14,291 M skeleton + 16,306 M (existing shield leaf) + E for the ring and glue |
| TRNG, FRAM SPI master | 25,739 | M |
| Redundant decision bits, checkers, glue | 20,000 | E |
| **Total** | **822,700** | |
| **Share of core** | **47.5 %** | |

Of the total, about 178,000 is estimate with no synthesis behind it (ROM, PUF decoder, redundancy, parts of
NFC and clock) and about 95,000 comes from skeletons that were synthesized and never simulated (word unit,
sequencer, SPI link, clock monitor).

Not in the total, each a separate decision:

| Addition | Area | Basis | Decision |
|---|---:|---|---|
| Option F, field kit for aggregate-proof verification: digit-serial Goldilocks unit, round constants, verifier microcode | 75,800 | 37,801 M skeleton + 19,691 M + 18,300 E | D5 |
| NCO (carrier, FSK, chirp) | 25,940 | M: 54,669 − 28,729 | D7 |
| One `efuse_async_mem_1x8` macro and glue | 10,100 | LEF 8,075 + 2,000 E | D2 |
| Characterisation ring array, 16 pairs, with owner-signed read-out | 4,000 | E from 175 µm² per pair M | D13 |

For comparison: the tree today is 1,297,563 µm² flat [M, state report]; configuration S as first written
(64 rows, GF(2^128) unit, fuse macros, NCO, estimated link and clock unit) was 909,070.

### 7.2 What changed from the first S

| Change | Effect | Why |
|---|---:|---|
| Register file 64 → 72 rows | + 32,825 | Signature verification needs about 19 scratch rows (4.3); the first S never tallied them |
| GF(2^128) unit removed | − 48,545 | The fingerprint is two GF(2^64) products in microcode on the word unit |
| Fuse macros removed | − 18,150 | Not relied on (section 3) |
| NCO removed | − 25,940 | No protocol role; measured by synthesizing the leaf without it |
| SPI link 45,000 → 25,000 | − 20,000 | Skeleton measured |
| Clock unit 50,000 → 35,000 | − 15,000 | Skeleton and shield leaf measured |
| NFC frame growth restated on the smaller base | + 940 | |
| ROM 1,536 → 1,700 words | + 7,500 | Committee gate, fingerprint, lease and owner-root routines |

### 7.3 Utilisation and margin

- Ceiling 0.92 M µm² of synthesized cells, design point at most 0.84 M (11.1). S is 822,700: 49 % of the
  placeable area, about 55 % as the placer reports it.
- Margin to the ceiling: about 97,000 µm², 12 % of S. Margin to the demonstrated point: about 12,000.
- Option F on top of S gives 898,500, about 21,000 under the ceiling. Since 178,000 of S is estimate, that is
  no margin. Option F beside every organ does not honestly fit; it fits if about 60,000 to 75,000 of organs
  give way (11.3), or if the measured baseline comes in that much under its estimate.
- The estimates are replaced by synthesis of real RTL at the end of stages 2 and 3. Additions are decided
  then, not now.

### 7.4 Time per operation at 25 MHz

| Operation | Clocks | Time | Basis |
|---|---:|---:|---|
| Keccak-f[1600] / Keccak-p[1600,12] | 721 / 373 | 28.8 µs / 14.9 µs | M |
| One `F` call / one `PRF` call, as the signer microcode runs them | 755 / 765 | 30.2 µs / 30.6 µs | model (`v2/tests/report.py`) |
| Signer request, fixed part (tag check, shape checks, header) | about 474 | 19 µs | model: 1,239 for a request with one chain of zero steps, less its one PRF call |
| Stateful request, added (two record reads, write, read-back) | 4,775 | 0.19 ms | model; FRAM transfers estimated at SCK = clk / 4 |
| WOTS signature, 35 chains, FIPS 205: most steps / digits spread evenly | 388,762 / 219,335 | 15.6 ms / 8.8 ms | model: 516 / 291 Keccak calls |
| WOTS public key, 35 chains | 422,392 | 16.9 ms | model: 561 Keccak calls |
| One-time signature (WOTS+C, FTS), up to 600 calls | 0.46 M | 18 ms | D |
| SLH-DSA-128f signature, cold / with tagged root cache | 78 M / 6.6 M | 3.1 s / 0.27 s | D: 102,800 / 8,700 calls |
| SLH-DSA-128s signature, cold / with tagged root cache | 1.61 G / 305 M | 64 s / 12 s | D: 2.12 M / 401,000 calls |
| G1: one SLH-DSA-128s verification, with the fingerprint passes | at most 3.9 M | at most 0.16 s, about 0.10 s on average | D, E (4.3) |
| G3: `k` member signatures and Merkle paths | `k` × 3.9 M | 0.5 s for 3 of 5; 1.7 s for 11 of 16; 10.5 s for 67 of 100 | D (4.6) |
| Boot to READY, unleased | about 5 M | about 0.2 s | E |
| Lease at power-up | one gate verification | + 0.16 s per signature, plus the authority round trip | D |
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

Pad sides as in `librelane/slots/slot_0p5x0p5.yaml`. The identification macros that the precheck requires sit
in the die corners outside the core (`librelane/macros/macros_qsag.yaml`) and take no core area.

```
                         NORTH: analog 3..0 (unused), FRAM SPI 22..25, tamper 26
        +--------------------------------------------------------------+
        | PUF array + decoder 114k        | TRNG, FRAM master 26k      |
        | (quiet corner, halo)            | clock, reset, tamper 35k   |
        +---------------------------------+----------------------------+
 WEST   |        REGISTER FILE 296k  (shield route above)              |  EAST
 straps |        key rows in the centre, away from every edge          |  NFC 8..10
 CS_N   +-------------------------------+------------------------------+  distance 13, 14
 27..37 | Keccak 91k                    | NFC 35k                      |  (fast path placed
 unused | word unit 34k                 | distance + TDC 45k           |   against the pads)
        +-------------------------------+------------------------------+  FAULT, IRQ, CLK_MON
        | sequencer + ROM 101k          | SPI link 25k | glue 20k      |
        +--------------------------------------------------------------+
                         SOUTH: clock, reset, SPI 0..3
```

---

## 8. Verification plan

### 8.1 Golden model

`model/qsag_ni_model.py` is extended to the whole command set and executes **the same microcode image** as
the RTL, over a Python model of the register file and units. It gains models of the PUF (parametrised by a
response and a noise vector), the FRAM (with an interface to rewrite it and restore old images), an authority
with its lease ledger,
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
shown to fail on a build with the guard removed.

| Area | Accept | Refuse |
|---|---|---|
| Lifecycle | enrol → commit → reset → boot → same keys; re-initialisation of an orphan by the owner root | enrol after commit; commit or re-initialise with a signature over an old nonce; enrol after the FRAM is erased and the helper record written back; boot with altered helper data; boot with a wrong owner signature; any command but `REINIT` in `ORPHAN` |
| Rollback | counter advances across reset; leased chip resumes at the granted base | leased chip: older image restored, then any value of `u` at or below one already granted; lease over an old nonce; lease naming a superseded `gen`; counter past the session bound; leaving `LEASE_PENDING` with the TRNG failed. Unleased chip: the test asserts the documented residual, that an older authentic image is accepted |
| Signer | signatures verify under `crates/qsag-core` | any request naming a chain position; WOTS signing of a root without a valid tag; one-time key used twice, including across reset |
| Vat | mint, attenuate, invoke within limits | wider child rights; removed guard; spend over limit, including across reset; mint after mint lock, including after reset; expired epoch |
| Gate | valid statement for this transition | same statement on a second chip model; replay after `seq` advanced; statement for another type or other arguments; bad signature; G3: `k` − 1 members, a member repeated, indices out of order, a key not under the pinned root, a path to another root; G2 (option F): unpinned program, program with an assertion removed, bitmap under threshold, a stated challenge that differs from the transcript |
| NFC | fresh token bound to the request | replayed counter; wrong binding; bad tag; valid CRC only |
| Distance | all rounds correct in time | one wrong bit; late answer; calibration result presented as validity |
| Output bound | — | for every opcode: response longer than its limit; any key-dependent word in any response, FRAM write, response length or cycle count that the manifest does not list (checked by propagating a taint from key rows in the model and the RTL, not by comparing values) |
| Faults | — | reset or zeroise injected at every micro-PC of every routine: no key-dependent output, lifecycle not advanced without its record write |
| Survival | boot with TRNG dead, internal oscillator dead, FRAM absent, tamper pad floating before lock | — |

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
| `qsag_trng`, `qsag_anchor_spi` | scenarios `trng`, FRAM rollback transactions |
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
| 1 | Model first: microcode assembler, model interpreter, register-file and unit models; port PING, hash, key load, PRF_msg, WOTS and FORS, the anchor, and (L) Poseidon2 and Merkle. **Done, in `v2/`** | Model answers 50 of today's 54 script transactions identically, 12 of them from requests in the new signer format; the four verifier-VM transactions belong to stage 7 | 4 |
| 2 | Register file, sequencer, word unit, egress in RTL with the kept Keccak unit; SPI link only. In the model first: the rules added to 5.3, and a refusing test for each guard the review found untested | RTL equals model on stage 1; properties 1, 2, 3, 6 of 8.2 proved | 6 |
| 3 | Lifecycle: FRAM records, owner-root enrolment and re-initialisation, boot, PUF array with fixed pairing, leases and the authority model | Lifecycle and rollback rows of 8.3; synthesis of everything so far, replacing the estimates of 7.1 | 6 |
| 4 | G1 routine with the microcoded fingerprint, G3, transitions; review of the fingerprint and lease arguments | Gate rows of 8.3 for G1 and G3 | 5 |
| 5 | Vat in microcode; NFC token; distance roles; guards; rest of the signer: FORS indices from `H_msg` on chip, root tagging (7.4) | Vat, NFC, distance rows; signer rows | 5 |
| 6 | Survival: clock strap, reset pad, tamper arming, self-test extension, fault-injection sweep | Faults and survival rows | 3 |
| 7 | Option F only (decided after stage 3): digit-serial field unit, verifier machine in microcode with stated challenges, program pinning, compiler from `qsag-agg` | Real regime-7 proof accepted; mutated proof and unpinned program refused; the four verifier-VM transactions of today's script, re-expressed under 4.4 | 10 |
| 8 | Synthesis, floorplan, placement, clock tree, routing, timing | Routed design, timing met at 25 MHz at all corners | 5 |
| 9 | Gate-level simulation (8.4) | Passing at both SDF corners | 4 |
| 10 | DRC, LVS, antenna, density; independent audit | Clean reports | 5 |

Configuration S: stages 2 to 6 and 8 to 10 remain, 39 lane-days. Option F adds stage 7. The largest
uncertainties are the physical stages, none of which has ever completed on this chip, and, for option F, a
compiler that does not exist and a verifier machine that has never run a real proof.

### 9.4 Run 3 and a later run

Run 3 closes for purchase on 9 Dec 2026 and needs a clean GDS on 16 Dec 2026, thirty days after this was
written. The stages still to do for configuration S are 39 lane-days, and stages 8 to 10 have never been run
on any version of this chip: no clock tree has completed, nothing has been routed, and no DRC, LVS, antenna
or density check has run. **Configuration S cannot credibly be taped out in Run 3.**

What could be, with two lanes in parallel, is an engineering sample:

| | Engineering sample for Run 3 | Held for a later run |
|---|---|---|
| Logic | Stage 2 machine (register file, sequencer, word unit, Keccak, SPI) with the stage-1 ROM as modelled and tested: PING, hashing, key load, PRF_msg, WOTS and FORS, the FRAM anchor | Lifecycle, enrolment, PUF key derivation, leases, the gate (G1, G3), vat, seal, option F |
| Organs | Present for measurement, with open read-out and no security claim: the PUF ring array, the TRNG, the distance fast path, the NFC receiver front end, the clock monitor and tamper input | Their authenticated use: helper data, tokens, keyed distance rounds |
| Area | about 660,000 µm² [E], 39 % geometric | 822,700 |
| What it is | A signing coprocessor with volatile host-loaded keys, and a characterisation vehicle: PUF entropy and reliability across 1,000 dies, ring speeds, TRNG quality, latch-array timing, pad and supply behaviour | The product |
| What it is not | A root of trust. It has no lifecycle and its test read-outs are open | |

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
(39 lane-days, five to six weeks with two lanes), replace the 178,000 µm² of estimates with synthesis of real
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
| D2 | Fit one eFuse macro as redundant, read-back-verified hardening (3.4) | **Not on the first tape-out.** It is an experimental hard macro that has to pass the foundry decks; nothing depends on it. Revisit when silicon results for the macro exist | Yes: 10,100 µm² and a DRC risk on the whole die. No: `ROTATE`, `REINIT` and `RETIRE` stay reversible on an unleased chip |
| D3 | Owner root public-key digest as a mask constant | **Yes.** Enrolment, re-initialisation and debug unlock all rest on it now | Yes: every die of the run trusts one key, fixed at tape-out, and that key can unlock the characterisation read-out. No: nothing authenticates enrolment, and an erased FRAM can be re-enrolled by anyone |
| D4 | Host link | **SPI only** (as built in `v2/`) | Other links: about 55,000 µm² and two more clock domains |
| D5 | Gate | **G1 and G3 in the baseline.** Option F (G2, aggregate proofs) decided after stage 3, when the estimates in 7.1 are measured; it is not for Run 3 | Option F: 75,800 µm², about 24 s per proof, a verifier compiler that does not exist, and about 60,000 to 75,000 µm² of organs to give up (distance bounding first) unless the measured baseline comes in low |
| D6 | PUF size | **504 rings, four blocks** | A fifth block is 11,000 µm² and buys margin against biased bits |
| D7 | NCO | **Deferred** | 25,940 µm² measured |
| D9 | Mode (coprocessor or vat) fixed per chip at `COMMIT` | **Yes** | A chip serves one role |
| D10 | Design clock 25 MHz | **Yes** | Every time in 7.4 scales with it; no timing result exists |
| D11 | Rollback policy per chip: leased or unleased (3.4) | **Leased** for any chip that guards one-time keys or spend limits against someone who may hold the board; unleased otherwise | Leased: the authority must be online at every power-up, and unused grants are lost. Unleased: an attacker with the board can restore any earlier state |
| D12 | Run 3 | **Tape out only the engineering sample of 9.4, and only if both gates there are met and the money is there.** Otherwise skip Run 3 | Engineering sample: $4,500 and about three weeks of two lanes, for silicon data on the PUF, TRNG, register file and pads. Skip: first silicon is also the first product attempt |
| D13 | Characterisation ring array with owner-signed read-out | **Yes** | 4,000 µm². Without it there is no silicon measurement of PUF entropy that does not also expose key material |

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

**The area ceiling is 0.92 M µm² of synthesized cells, and the design point should be at or below 0.84 M.**
Between 0.92 M and 1.28 M there is no evidence at all. The organ regions (PUF corner with a halo, NFC and
distance against their pads) need local fill of at most 70 to 75 % [C, basin search]; after repair, 0.92 M
leaves almost nothing for that and 0.84 M leaves some. Configuration S is 822,700.

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

- One 72-row register file; lane-serial Keccak; word unit; microcoded sequencer with about 1,700 ROM words.
- SPI host link; FRAM master; TRNG; pad clock with a fixed ring as monitor; tamper, shield, glitch sensors.
- PUF with 504 rings and fixed pairing; NFC receiver with a keyed, counted token; distance bounding with
  keyed response bits and a placed fast path.
- Signer (use U1), anchor and leases (U2), vat (U3), seal and release (U4), guards (U5).
- Gate (U6): G1 and G3. No algebraic verifier, no GF(2^128) unit, no NCO, no fuses, no second link.
- 822,700 µm² synthesized [M and E as labelled in 7.1]: 49 % geometric, about 55 % as the placer reports it.


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
