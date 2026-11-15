# Migration proof version 3

The integrated main-library axiom audit checks **59,257 declarations, including 28,744 kernel theorem declarations, across 57 modules**, with **0 rejected axioms**. This includes private and compiler-generated declarations and 277 pure assurance-infrastructure declarations; 131 compile-time tactic declarations are excluded. Counts describe the checked definitions and premises, not complete production refinement. The combined extracted-MIR and custody audit checks **5,318 declarations / 2,093 theorems / 44 contributing modules**; the WHIR audit checks **1,558 / 718 / 7**. Both report **0 rejected axioms**. Sandboxed six-kernel challenge replay passes 107 main theorems and 65 MIR theorems plus 17 definitions.

## Relation and encoding

The witness is a nonzero canonical **spending scalar**, not a derivation seed.
A GF(2) circuit checks its 256-bit encoding against the relevant subgroup order.
Four-bit window selection feeds complete projective secp256k1 addition or
complete extended Edwards addition. The inverse check rejects infinity. Both
coordinate encodings are canonical.

Window tables are public and affine. The sixteen selector wires of a window sum
to one as a polynomial identity in the four lifted bits, so the selected Edwards
point has `Z = 1` as a public constant and the selected secp256k1 point has
`Z = 1 - sel_0` (only entry 0, the identity, has `Z = 0`). Neither shortcut
depends on the bits being Boolean or on any private wire value.

The four statements are:

* Bitcoin: RIPEMD-160(SHA-256(compressed secp256k1 public key)).
* Ethereum: the last 20 bytes of Keccak-256(uncompressed x || y).
* Taproot: the x coordinate of an even-y secp256k1 output key.
* Ed25519: canonical y with the parity of x in the high bit.

SHA-256, RIPEMD-160 and Keccak-f[1600] execute as Boolean word circuits.
Taproot witness normalization performs the tagged SHA-256 tweak and parity
normalization before proving. The proved witness is the resulting output
spending scalar: possession of the internal key or a particular derivation
path is not part of the statement. Likewise, Ed25519 seed expansion is outside
the relation; possession of the normalized scalar is sufficient to spend.

The exact nullifier relation is

```
Poseidon2_hash_limbs(
    0x4d49475f4e554c31,
    [group_tag] || pack56(spending_scalar_be) || pack56(migration_domain)
)
```

Group tags are 1 for secp256k1 and 2 for Ed25519. `pack56` is the existing
injective, delimiter-terminated encoding from qsag-accel. The circuit uses the
same width-12 Goldilocks permutation and rate-8 sponge padding as the native
implementation. The same scalar bits feed the curve and the nullifier.
The destination and every other public statement field are bound directly by
the Fiat-Shamir transcript. The reserved `witness_anchor` must be zero.

Use `prove_migration_in_domain` to allocate an application-wide replay domain
independent of the destination. The compatibility entry point derives its
domain from the epoch. Reusing a key in another domain or epoch intentionally
produces another nullifier. Applications must track spent nullifiers and choose
the replay scope; proof verification alone does not prevent replay.

## Mixed-domain decomposition

Arithmetic runs in GF(2), Goldilocks, the secp256k1 base field, and the Edwards
base field. Values and transcript encodings are canonical. Public constants
are injected into head 0. Public-only constant folding depends exclusively on
node kinds, never on private wire values.

To convert a Boolean shared bit into an arithmetic field, each head locally
injects its own XOR share into a separately owned arithmetic wire. The circuit
combines the three owned wires with `x XOR y = x + y - 2xy`. To convert an
arithmetic shared value into bits, each head locally decomposes its canonical
share into owned Boolean wires. Boolean adders and conditional subtraction
compute the sum modulo the source field. These conversions introduce neither
unconstrained witness hints nor cleartext coordinate checks. Each opened head's
local conversion is replayed, including the neighboring head's conversions.

At every multiplication the three-head evaluator uses

```
z_i = a_i*b_i + a_i*b_(i+1) + a_(i+1)*b_i + r_i - r_(i+1).
```

A challenge opens the ordered pair `(e, (e+1) mod 3)`. The verifier recomputes
`z_e`, compares it exactly with the committed primary transcript, and consumes
the neighboring head's committed multiplication outputs. It does not attempt
to recompute that neighbor's multiplication without the third head's operands.
Both opened views, every hidden output share, the repetition index and the
head index are authenticated by the root committed before challenge selection.
The verifier authenticates the complete root before gate replay and checks every
recomputable multiplication residual and output share **exactly** across all
opened `(e, (e+1) mod 3)` views; all public output constraints reconstruct to
zero. Proof verification consists of exact deterministic gate replay and
`cSHAKE256` root binding. Every length, challenge index and field encoding in a
proof is checked before use; a malformed proof returns an error.

## Soundness, Grover search cost, and privacy assumptions

For independently sampled interactive ternary challenges across
`MIT_REPETITIONS = 438` repetitions, three-view consistency and commitment
binding give classical soundness error

```
(2/3)^438 = 2^(-438 * log2(3/2))
          = 2^-256.213575315866...
          < 2^-256.
```

* **Classical random-oracle model:** Fiat-Shamir challenge derivation over
  `QSAG.MIGRATE.ROOT.V3` gives a cheating prover success probability of at most
  `(2/3)^438 < 2^-256` per challenge-oracle query, composed with 256-bit
  `cSHAKE256` commitment binding.
* **Generic quantum search:** Grover search for a root whose challenge string a
  cheating prover can answer succeeds with amplitude `(2/3)^219` per iteration,

  ```
  sqrt((2/3)^438) = (2/3)^219
                  = 2^-128.106787657933...
                  < 2^-128,
  ```

  so it needs more than `2^128` oracle iterations. This is the cost of generic
  search. It is not a quantum random-oracle Fiat-Shamir theorem for this proof
  system, and this crate does not claim one.
* **Source-chain witness boundary:** the proved witness is a legacy `secp256k1`
  or `Ed25519` discrete-logarithm spending scalar. A Shor-capable quantum
  computer recovers it from the source-chain public key in polynomial time, so
  legacy assets must settle on-chain before such computers exist.

The privacy target is computational zero knowledge, conditioned on the public
legacy commitment, deterministic nullifier and remaining public statement.
The assumptions are SHAKE256 pseudorandomness for independent seed-expanded
tapes and cSHAKE256 commitment hiding/binding in the hash/ROM model. Fresh
256-bit caller-provided entropy is required for each proof. Hidden seeds act
as commitment randomness. Reusing the same tapes under multiple challenge
transcripts can expose all three views and is prohibited. Privacy is not an
information-theoretic claim, and the deterministic public outputs are not
claimed to conceal their own information about the spending key.

The standard ordered-pair reference is
[ZKBoo, USENIX Security 2016](https://www.usenix.org/conference/usenixsecurity16/technical-sessions/presentation/giacomelli).
This document records the concrete security model, bounds, and assumptions.

## Distributed execution: active 1-of-3 outer replicated prover

`CoZkCustodianShare::new` takes one physical custodian's XOR share
of the normalized little-endian spending scalar, independent private entropy,
a unique session identifier, and two pairwise channel keys. `prove` consumes
this state by value. There is no dealer API accepting the complete witness.

### Security threshold and non-goals

* **Active 1-of-3 malicious security with abort:** The outer MPC tolerates at
  most **one actively corrupted physical custodian** out of three, preserving
  witness privacy and soundness with **non-identifiable abort** (`Err(...)`
  before any secret-dependent wire opens).
* **2-of-3 collusion reconstructs the witness:** Replication gives each
  physical custodian two of the three additive/XOR components, so **any two
  colluding custodians can immediately reconstruct the spending scalar**.
* **Explicit non-goals:** Identifiable abort (attributing an algebraic
  multiplication check failure or `all_outputs_zero` rejection to a specific
  guilty custodian), fairness / guaranteed output delivery, and crash-resumable
  state persistence are **not** provided. Initial physical witness shares must
  be a uniformly random 3-of-3 XOR sharing; the protocol cannot repair a leaked
  initial sharing.
* **Channel & session requirements:** `Transport` must provide **confidential
  point-to-point delivery** (pairwise keyed `cSHAKE256` tags authenticate
  `session`, `sender`, `recipient`, `sequence`, and `payload`, but do not
  encrypt payloads on a broadcast medium). Fresh independent 256-bit entropy
  and a unique session identifier never reused under the same pairwise channel
  keys are mandatory.

### Mixed-domain sharing, masked conversions, and pre-open barriers

Boolean wires use replicated XOR shares bitsliced across 64 repetitions;
arithmetic wires use replicated additive shares in their native prime field
(`Secp`, `Ed`, `Gold`). `share_uniform_lanes` reshares uniform 64-lane witness
inputs across all repetitions.

Conversions never open unmasked virtual values. A2B still opens a difference
masked by a uniform prime-field element. B2A instead samples each replicated
mask component uniformly in `Z/(2^n)`, where `p = 2^n - c`. At most one corrupt
custodian knows two components; the third makes their ring sum exactly uniform.
Thus the only opened binary difference `delta = V - R mod 2^n` is exactly
uniform, including for Goldilocks; this is not biased reduction of a field mask.

For B2A, write the integer component sum as `S = R + k*2^n`. Two ring additions
produce the two carry bits whose sum is `k`; subtraction produces the borrow
bit `b`. The output field sharing is
`S + delta - (k+b)*c mod p`. The three correction bits are converted by the
existing actively checked bit-lifting gadget and remain secret. Raw components
and public differences are canonicalized by one constant-time subtraction,
since `2^n < 2p`. Boundary tests include components `p-1`, `p`, and `2^n-1`,
both addition carries, and both subtraction-borrow cases across all 64 lanes.

For A2B's component sum, two ring additions produce `R` and `k in {0,1,2}`.
The low and high bits of `k` are mutually exclusive, so `k*c` is encoded with
public XOR masks after one shared AND. A single modular addition yields the
canonical result: `R + k*c < 2^n + 2c < 2p` for all three fields.

Both directions verify **all** pending Boolean and prime-field multiplications
before any masked difference opens. Automatic Boolean checks retain a partial
chunk for the next batch; openings always check that remainder too. Auxiliary
curve inverses multiply by a fresh shared field mask, authenticate that product,
open the masked product, and scale the secret mask by its public inverse.
For nonzero operands the opened product is uniform and independent of the
operand. A zero product retries the mask, with an abort after three attempts;
a zero operand therefore aborts and its zero status is revealed. The curve
inversion gate requires a nonzero projective coordinate on valid witnesses.
The active multiplication checks still run before the masked opening, so this
is one multiplication plus one opening, not two total transport exchanges.
Final ZKBoo shares and the proof format are unchanged; outer-MPC traffic changes.

### Mandatory active multiplication verification (`P0-01`)

`Engine::verify_all_pending` executes **before every wire opening** (`open`,
`fopen_many`, `agree`, masked A2B/B2A differences, upfront `Tape` `valid`,
`all_outputs_zero`, view commitments, output shares, and challenged ZKBoo
views). Any detected algebraic inconsistency poisons the engine (`self.poisoned = true`)
and returns `Err(Error::MultiplicationCheck)` before any secret-dependent wire
is transmitted:

1. **Two-round transcript-bound coin-flipping (`Engine::coin_flip`):** Every
   verification challenge commits (`QSAG.OUTER.COIN.COMMIT.V1`) to fresh hedged
   randomness (`QSAG.OUTER.COIN.HEDGE.V1`) and both incident pairwise
   domain-separated transcript digests, echoes peer commitments, verifies three-edge
   transcript agreement and commitment openings in constant time, and derives
   public coins via `QSAG.OUTER.COIN.DERIVE.V1`. No single rushing custodian can
   bias challenges after sending multiplication shares.
2. **64-lane Boolean `AND` verification (`< 2^-244` per flush):** Up to `262,144`
   bitsliced 64-lane `AND` words (`4,096` groups of `64` words) per flush are
   embedded into `GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)` via `6`
   packed ternary sumcheck rounds (`729` combinations), `12` group + `6` lane
   halving folds (`VPCLMULQDQ`/`PCLMULQDQ` / `PMULL`), and **two independent**
   locked-pair BBCGGI19 inner-product passes with PRSS-masked non-zero base-case
   sacrifices (`r_b in GF(2^128)^*`). Per-flush false-acceptance probability is
   `< (63 / (2^128 - 1))^2 < 2^-244` (`> 122` bits generic Grover): the error
   numerator per pass is `6 + 1 + 6*3 + 2*(12 + 6) + 2 = 63` (`6` word-offset
   weights plus `1` unstructured group weight, `6` ternary sumcheck rounds,
   `18` group/lane halving folds, and base sacrifice; `BIT_CHECK_NUMERATOR`,
   asserted at compile time).
   Byte tables contain shares but are indexed only by public challenge masks;
   their storage is wiped with the rest of the verification scratch.
3. **Prime-field multiplication verification (`< 2^-186` per flush):** Up to
   `1,024` field words (`65,536 = 2^16` lane products) per flush are combined
   with independent uniform challenges and reduced by an Arity-2 logarithmic
   BBCGGI19 inner product plus a PRSS-masked base-case sacrifice with a non-zero
   challenge. The error numerator is `1 + 2*16 + 2 = 35`: the random linear
   combination, sixteen binary folds, and base sacrifice
   (`FIELD_CHECK_NUMERATOR`, asserted at compile time).
   * `Secp` and `Ed`, directly over `F_p`: per-flush cheating probability
     `<= 35 / (p - 1)`, which is `< 2^-250.87` for `Secp` and `< 2^-249.87` for
     `Ed`, hence `< 2^-249` for both.
   * `Gold` (`p = 2^64 - 2^32 + 1`), lifted into the irreducible cubic extension
     `F_p[u]/(u^3 - 7)` (`3 | (p - 1)`, `7^((p-1)/3) != 1`, `|F_{p^3}| > 2^191.99`):
     per-flush cheating probability `<= 35 / (p^3 - 1) < 2^-186.87 < 2^-186`.

A failed check aborts the ceremony, so a cheating custodian gets one attempt:
the ceremony-level bound is the largest per-flush bound, `< 2^-127.99`.

### Input-substitution closure (`P0-1`, `all_outputs_zero`)

To prevent a malicious custodian from substituting a modified witness share and
learning linear/differential information about honest custodians' shares from
opened public-key or nullifier output residuals, `evaluate_inner` verifies inside
MPC that **every** Boolean and prime-field circuit output reconstructs to zero
across all 64 lanes of every batch (`all_outputs_zero`: each prime-field output
sum is converted to its canonical bits by the masked A2B conversion, and all
residual bits are NOR-reduced), runs `verify_all_pending()`, and opens **only**
that single 1-bit predicate. If any lane fails (`!= u64::MAX`), the ceremony
aborts immediately with
`Err(Error::InvalidProof)` before any output share, view commitment, or view
opens.

### Witness-independent canonical tape sampling (`C0-5`)

Native Goldilocks tape sampling scans three consecutive words and selects the
first canonical candidate with masks. The word-aligned sponge scans fixed
addresses and computes one next-state permutation regardless of its secret
cursor. Masked cursor/state advancement consumes exactly the original rejection
stream, including across rate boundaries and subsequent Boolean refills. Only
three simultaneous rejections enter the fallback loop (probability less than
2^-96 per independent uniform window). This is a source-level constant-work
construction; it is not a claim of a compiler-level timing proof.

Tape expansion first tries the fixed schedule (`QSAG.MIGRATE.TAPE.V3`),
followed by an upfront batched range check (`less_than_modulus_many` and
`fold_valid_bits` in `evaluate_inner`). A noncanonical candidate triggers
canonical rejection sampling instead of an honest `Error::InvalidTape` abort.
The repair path conditionally removes rejected words from each lane's unread
stream using shared masks. Previously cached Boolean bits are preserved, and
all subsequent field draws and Boolean refills move with the unread suffix.
This matches the native `Tape::sample` stream, including the Edwards high-bit
mask and the full byte width consumed by each draw.

Repair starts with two attempts per draw. If any draw remains unresolved, the
original PRG stream is extended and replayed with a doubled budget. There is no
fixed rejection limit for honest PRG draws; malformed finite buffers, invalid
schedules, and size overflow return `InvalidTape`. Every scratch buffer remains
wipe-on-drop. Only the same aggregate per-head, per-lane validity masks as the
initial range check are opened, after multiplication verification; individual
candidate values and per-draw rejection masks are never opened.

Conditioned on the public statement, the sampling control flow depends on fresh
seed entropy, not on the private witness:

1. Every custodian's seed contribution is derived via `QSAG.OUTER.SEED.V1`
   exclusively from `(self.entropy, self.session, statement_bytes,
   batch * 64 + lane, head)`; the witness share is not a seed input.
2. Tape generation and repair use only these seeds and the public schedule,
   strictly before witness inputs or conversions are evaluated.
3. The aggregate validity masks and repair budgets therefore reveal no additional
   witness information under the independent-entropy assumption. They do reveal
   tape-dependent sampling information, just as the previous upfront check did.

A failed ceremony still requires fresh session and entropy: the custody state
is single-use. Internal sampling repair continues the original PRG stream and
is not a new ceremony or reuse of consumed custody state.

### Deterministic zeroization (`P3`) and ceremony freeze

The following are wiped with volatile `ct_zeroize_u64s` / `ct_zeroize_bytes` on
both `Ok` completion and every `Err` early return:

* the custodian's witness share, its expanded 64-lane planes, both replicated
  witness components, its seed contributions and its shares of every
  virtual-head tape seed (`CoZkCustodianShare`, `prove`);
* channel keys, MAC prefixes, PRSS and coin sponges, PRSS scratch, and the
  pending Boolean and prime-field triple queues (`Engine`);
* all Boolean-check scratch, including byte and nibble tables, transpose rows
  and folded vectors up to their high-water mark (`BitCheckScratch`), and the
  prime-field check vectors (`FpScratch`, `GoldScratch`);
* shared views, circuit wire values, squeezed tapes and raw tape draws
  (`SharedView`, `SharedValue`, `Word`, `FieldWord`), and outbound message payloads
  (`Envelope`);
* arithmetic gadget words, adder pairs and carries, conversion scratch, validity
  folds, Keccak stack scratch, field multiplication masks/products, and received
  share buffers (`SecretVec`, `Secret`).

The Boolean-check vectors, PRSS scratch and pending Boolean queue wipe their
old allocation before growing, so no reallocation frees secret words.

`Word` and `FieldWord` own `SecretVec` storage. Their destructors wipe on
normal completion, error returns, and unwinding; growth copies into a new
allocation and wipes the old one before releasing it. Truncation/clear and
consuming iteration wipe vacated slots. Mutable access exposes only a slice,
so callers cannot bypass guarded growth through a `Vec` method. Nested field
arrays are flattened for one bulk wipe. Adder loops reuse preallocated pairs
and output words; `fmul_many` generates masks in guarded stack storage one lane
at a time and uses the returned local share buffer instead of duplicating every
product word. Keccak's column and rotation buffers are guarded stack arrays.
Circuit nodes wipe their values individually, including abandoned builders;
builder growth wipes the old node allocation. Hash/curve gadget `Wire` arrays
contain public node indices, not witness values.

These are storage-lifetime guarantees, not a guarantee that Rust/LLVM clears
registers or every compiler-generated copy. Destructors require normal scope
exit or unwinding, rather than process abort. The storage tests cover growth,
truncation, early iterator drop, error return, unwind, and allocation reuse.

Parallel transports may bound active repetition batches with
`Transport::max_parallel_batches`; batches remain in ascending order and all
438 repetitions still pass the same checks before opening. A completed batch
releases and wipes evaluation scratch while retaining its authenticated engine
for the opening rounds. The default transport limit permits all batches, subject to the local available
parallelism cap (at most 16). Native proof repetitions and verifier replay use
ordered scoped workers with the same cap when std is enabled; no-std remains
serial. Tests allow seven live ceremony batches across custodians.

The backend batch sponge hashes native party commitments and opened-view
commitments in verification, including CoZK final verification through
`prove_with_backend`. Secret shared commitments still use interactive Boolean
permutations. An ordinary Keccak permutation on each share cannot substitute
for those permutations, and unopened views are never reconstructed for GPU
hashing. The optional `vulkan` tests require an actually supported backend and
check that its CPU fallback counter does not increase.

All 438 repetitions' view commitments and verified-zero output shares feed the
ceremony-wide `QSAG.MIGRATE.ROOT.V3` Merkle/transcript root. Custodians execute
both cross-batch pre-commit (`QSAG.OUTER.PRECOMMIT.V1`) and post-root freeze
(`QSAG.OUTER.FREEZE.V1`) agreements before opening the two Fiat-Shamir-selected
ZKBoo views per repetition; the unchallenged third head's shares are zeroed
prior to reconstruction. Each custodian runs the unchanged public verifier
`verify_migration_proof` before final completion agreement
(`QSAG.OUTER.COMPLETE.V1`).

### Validation scope

The integrated 2026-11-14 validation run passed all 39 migration unit tests in
892.97 seconds, including both complete 438-repetition Bitcoin and Ed25519
ceremonies and both witness-substitution regressions. Its compile-fail doctest
also passed. This closes the earlier timed-out Bitcoin execution check; it does
not establish the open production privacy or FS/QROM refinements. The unified
proof census and remaining boundaries are tracked in
[the convergence record](../../docs/CONVERGENCE_STATUS.md).

The subsequent gadget-storage update adds two zeroization tests. All unit
tests and the compile-fail doctest pass in host-native release runs; summary
verification status and remaining boundaries are tracked in
[the convergence record](../../docs/CONVERGENCE_STATUS.md).

Unit and adversarial integration tests verify:

* Polynomial-basis `GF(2^128)` transpose/Karatsuba identities, `GoldExt3` cubic
  extension field axioms, `BitCheckScratch` high-water-mark zeroization, and
  stack-streaming `Engine::tag` MAC equivalence.
* Active 1-bit Boolean `AND` faults (both MAC-signed wire tampering and
  algebraically consistent replicated share faults) aborting with
  `Err(Error::MultiplicationCheck)` and zero secret wire openings.
* Active 1-limb canonical prime-field `fmul` faults across `Gold`, `Secp`, and
  `Ed` aborting before any A2B or B2A masked conversion difference opens.
* End-to-end ZKBoo circuit `Bit` `AND` faults, `Field` `fmul` faults, and
  malicious custodian witness-share substitution (`P0-1`) aborting before any
  view commitment, output share, or view opens.
* Byte-for-byte native ZKBoo view/commitment equivalence across 64 lanes, full
  438-repetition distributed Bitcoin `HASH160` and `Ed25519` ceremonies under
  online transcript observers and legacy XOR-reconstruction attack regressions,
  and compile-fail linear consumption of `CoZkCustodianShare`.

Parallel repetition batches stop at their next exchange after a sibling rejects.
Cancellation only returns an error: it cannot bypass multiplication verification
or the ceremony-wide precommit barrier. The initiating rejection is retained
in preference to cancellation's transport error, and outbound share buffers are
wiped on cancellation. Public byte tables are reused for both initial challenge
projections. After projection, Boolean-check vectors are transposed once into
field limbs and kept in that representation throughout binary folding. Batched
hardware field scale-XOR replaces repeated public-matrix evaluation and bit
transposes. The two independent instances, challenge domains, sacrifice, and pre-open
verification barrier are retained. Sixteen-gate initial blocks and 32,768-gate
flushes reduce the degree bound to 54 and bound per-engine scratch memory. Projection scratch retains high-water-mark wiping; contiguous limb buffers
are reused across flushes and owned by the same wipe-on-drop engine scratch.

## General quorum custody: authenticated additive sharing

`CoZkCustodianShare::new_shamir` accepts any `2 <= t <= n <= 64` and an
explicit sorted quorum of at least `t` distinct zero-based party identities.
Shares encode each normalized scalar byte as a degree-at-most-`t-1` polynomial
over GF(256), with AES modulus `X^8 + X^4 + X^3 + X + 1` and evaluation point
`party + 1`. Lagrange weights at zero convert each local share into an XOR
contribution; no process reconstructs the witness. Subsets and supersets of the
threshold work without renumbering the roster. `new_additive` accepts n-of-n
XOR shares of the same bytes (not shares modulo the spending-scalar order).
All selected participants must remain online; abort does not trigger a quorum
change. A new quorum needs a new ceremony and fresh preprocessing.

The selected quorum runs the same distributed prover as the three-custodian
path (same circuit, 438 repetitions, Fiat-Shamir transcript, view encoding and
verifier) on a different engine, `threshold_mpc::SpdzEngine`. Its sharing is
additive over the quorum and every wire is authenticated, so it tolerates the
corruption of all quorum members but one:

* A Boolean wire is a 64-lane word `x` with the MAC `Delta * x(X)` in
  `GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`, where `x(X)` has the lanes as
  coefficients. XOR and constants are local. `AND` consumes one Beaver triple
  whose components carry one MAC per lane, which is what lets a lane-wise
  product with a public word stay authenticated.
* A prime-field wire is one element per lane with the MAC `alpha * v`.
  Goldilocks uses two independent keys, and a check uses an independent
  challenge vector per key, because one 64-bit key or one 64-bit linear
  combination alone would give only 64 bits.
* Boolean-to-field conversion opens `x XOR r` for a doubly authenticated
  random bit `r` and sets `[x]_p = c + (1 - 2c)[r]_p`. Field-to-Boolean opens
  `v - rho` for a random `rho` assembled from doubly authenticated bits and adds
  the public difference back in a Boolean adder. Neither direction takes an
  input from a party, so there is no conversion bit a party could substitute.
  For Goldilocks `rho` is rejected unless it is below the modulus (the
  acceptance bit is opened, the rejected `rho` is discarded); for the 255- and
  256-bit fields the excess above the modulus has probability below `2^-222`
  per lane and is not sampled out.
* Inputs are masked with authenticated random words. A lane-uniform input
  (the witness) is masked with one authenticated bit spread over all lanes
  and every party's masked word must be `0` or all ones, so no party can feed
  different witnesses to different repetitions.
* A challenged view is opened lane-selectively: the lanes of the unopened
  head are one-time padded with authenticated random bits before the word is
  opened, so the hidden head never leaves the sharing.

Every broadcast is sent pairwise, authenticated by a channel MAC, and folded
into a transcript chain. Values opened inside the protocol (Beaver
differences, conversion masks) are *partially* opened: their MAC shares are
queued. `SpdzEngine::check` settles the queue: the quorum compares
transcript chains, flips a coin by commit-then-open, each party commits to
`sigma_i = sum_j chi_j (m_ij - key_i * v_j)` for the coin-derived `chi`, and
the `sigma_i` are opened and must sum to zero. The check runs before any
output opening is sent, again before an opened output is returned to the
caller, inside every `agree`, and on the root engine before the batch engines
start. A custodian that flips a wire share, lies in a Beaver opening, uses a
wrong product share or forges a conversion mask passes one check of one
engine with probability at most `2^-127` (Boolean), `2^-126` (Goldilocks) or
`2^-254` (secp256k1 and Ed25519 base fields); the root and the seven batch
engines share one key, so the ceremony bound is eight times that. Sending
different values to different peers is caught by the transcript comparison of
the next check (or, for a share of an opened value, by the MAC check itself).
The rounds of a check and the final `agree` broadcast are compared only by a
later check, so equivocating there can make one honest custodian abort while
another completes, but cannot make any custodian accept a wrong value. Any
failed check, malformed or unauthenticated message, non-canonical share or
exhausted preprocessing poisons the engine: it erases its MAC key shares and
every interactive operation fails from then on. Abort is not identifiable and
not fair; one corrupt custodian can force it.

Privacy holds against any strict subset of the quorum, and for Shamir custody
against fewer than `t` custodians overall. The security argument is the
standard one for SPDZ (Damgard, Pastro, Smart, Zakarias, CRYPTO 2012; MAC
check as in Damgard et al., ESORICS 2013) with the lane-packed Boolean MAC
above; it is not machine-checked here, unlike parts of the replicated path.

### Preprocessing

The engine consumes witness-independent material through the transport's
`take_*` methods: Boolean triples, authenticated random words, field triples,
field randoms and doubly authenticated bits, all under the MAC key shares
given to `CoZkCustodianShare`. `threshold_prep::PartyPreprocessing` is the
per-custodian store. Material is used once, including across aborts and
forks; each batch stream needs its own supply; a stream that runs dry fails
closed with `MissingPreprocessing` and there is no witness-opening fallback.
The engine checks only counts and canonical encodings of what it is served.
It relies on the ceremony for the MAC relations, the triple and bit relations,
independent Goldilocks keys and a nonzero Boolean key, and on the operator for
identical consumption order at all members and for never serving an item
twice (a restored store is a two-time pad on masks, undetectable online).
Session identifiers must never repeat with the same channel keys.

`threshold_prep::dealerless::run_dealerless_preprocessing` produces the key
shares and the stores without any party that knows a key or a shared value.
It targets security with abort against all quorum members but one:

* Boolean triples and authenticated random words come from `qsag-core`'s
  `Pi_triple_f2` ceremony, run n-of-n over the quorum and converted from
  Shamir shares in the tower basis to additive shares in the polynomial basis.
* Field values are authenticated MASCOT-style (Keller, Orsini, Scholl,
  CCS 2016): the key holder is the OT receiver on the bits of its key share,
  once per ordered pair, so its key is fixed structurally, and the owner's
  consistency is enforced by an opened, masked random combination under a
  commit-then-open MAC check. A further check binds each holder to one key
  towards all owners.
* Field triples follow MASCOT triple generation with privacy amplification
  over `tau` components and `sigma` sacrificial triples: `tau = 3`, `sigma = 1`
  for the 255/256-bit fields, `tau = 7`, `sigma = 2` for Goldilocks.
* Doubly authenticated bits: each owner authenticates its bits under the
  Boolean key and the field key, proves them to be bits with a pairwise
  degree-2 check on the authentication correlation, and proves the two forms
  equal by 128 masked subset-parity repetitions; the joint bit is the XOR over
  owners, one field triple per XOR. A closing check ties the Boolean key used
  here to the key of the `Pi_triple_f2` material.

Every challenge comes from a commit-and-open coin drawn after the checked
data is fixed; a failed check returns no material and erases all state. The
parameter derivations and what each failed check can reveal are in the module
documentation. Limits of what is delivered: it is an in-process ceremony
driver in the model of `qsag-core`'s own preprocessing (all members' steps in
one process on separated state, one transcript chain), not a wire protocol;
its soundness arguments are written out but not machine-checked and have not
had an independent review; and it relies on the security of the `qsag-core`
OT mesh and `Pi_triple_f2`. Measured for three members: mesh setup about 3 s,
a Goldilocks triple about 2 ms, a secp256k1 or Ed25519 triple about 5 ms, a
doubly authenticated bit word 0.3 s (Goldilocks) to 0.8 s (large fields), a
Boolean triple word about 3 ms.

`threshold_prep::FixtureDealer` is a deterministic single-seed generator for
tests and benchmarks. It knows every key and exists only under `cfg(test)` or
the `test-dealer` feature; no constructor of the library takes a dealer.

### Cost

The engine is correct and actively secure for the whole prover, but the
prover's circuit is dominated by shared Keccak permutations (the SHAKE tapes
and the cSHAKE view commitments). Measured on the replicated path, one
repetition batch evaluates about 155 million 64-lane `AND` words per
custodian, about 1.1 billion per ceremony. In the authenticated engine each
`AND` word consumes a triple of roughly 3 KiB per custodian, so a complete
general-quorum ceremony needs on the order of 3 TiB of Boolean preprocessing
per custodian, about five weeks of single-threaded Boolean ceremony at the
measured rate, before any field material. The unit tests therefore cover the engine's
primitives, conversions and cheating cases, byte-exact view and commitment
synthesis on a small circuit, and the engine running on ceremony output, not
a complete general-quorum ownership proof. The replicated three-custodian
engine remains the practical path.

In `std` builds the BLS fixed-base tables are cached process-wide with
`OnceLock`; no-std builds retain allocation-based synthesis because
`std::sync::OnceLock` is unavailable.
