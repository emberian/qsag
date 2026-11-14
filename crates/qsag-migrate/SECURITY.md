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

Conversions never open unmasked virtual values: a fresh uniform replicated field
mask `R` is generated and decomposed into binary via a shared Boolean adder over
its three separately owned components; B2A and A2B open **only** the masked
difference `V - R` (in Boolean or prime-field form, respectively) **after**
verifying all pending Boolean and prime-field multiplications. Auxiliary curve
inverses are computed by shared Fermat exponentiation of the sum of the three
virtual coordinate shares without opening any coordinate.

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
2. **64-lane Boolean `AND` verification (`< 2^-127.99` per flush):** Up to `262,144`
   bitsliced 64-lane `AND` triples per flush are embedded into
   `GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)` (`32`-gate blocks, `128`
   gates per super-block via constant-time butterfly transpose and
   `VPCLMULQDQ`/`PCLMULQDQ` accumulation under a uniform `GF(2^128)` super-block
   combiner, packed `128` gates per `Bs256` quad) and checked by **two independent
   lockstep** Arity-2 BBCGGI19 inner-product instances plus PRSS-masked non-zero
   base-case sacrifice (`r_b in GF(2^128)^*`). Per-flush false-acceptance
   probability is `< 2^-128 + (90 / (2^128 - 1))^2 < 2^-127.99`: `2^-128` for
   the super-block combiner, and `90 / (2^128 - 1)` for each of the two
   instances. The degree budget is `62 + 2*13 + 2 = 90`: the initial polynomial,
   thirteen binary folds over at most `8,192` blocks, and base sacrifice
   (`BIT_CHECK_DEGREE`, asserted at compile time).
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

### Formal witness-independence of upfront `Error::InvalidTape` (`C0-5`)

Tape expansion uses a fixed, data-oblivious schedule (`QSAG.MIGRATE.TAPE.V3`)
followed by an upfront batched range check (`less_than_modulus_many` and
`fold_valid_bits` in `evaluate_inner`). Opening the resulting `valid` mask
has **identically zero mutual information with the witness scalar**:

1. Every custodian's seed contribution is derived via `QSAG.OUTER.SEED.V1`
   exclusively from `(self.entropy, self.session,
   statement_bytes, batch * 64 + lane, head)` — `self.witness_share` is never an
   input to seed derivation.
2. In `evaluate_inner`, `tape_sponges` absorb only `"QSAG.MIGRATE.TAPE.V3"` and
   `seeds`, squeeze candidate tape bits, evaluate `less_than_modulus_many`, fold
   `valid`, run `verify_all_pending()`, and open `valid` **strictly prior to
   Step 5 (`Op::Input`)**, before `witness` is read by any gate or conversion.
3. Consequently, the joint distribution of `(seeds, valid, Error::InvalidTape)`
   is statistically independent of `witness` (`I(InvalidTape; witness) = 0`).
   On `Err(Error::InvalidTape)`, `raw_draw_words` is wiped and no proof or wire
   opening occurs. Any retry **must** allocate a fresh `session` and fresh
   `entropy` because `CoZkCustodianShare` is single-use and the pairwise PRSS
   streams (`QSAG.OUTER.PADS.V1`) and MAC keys (`QSAG.OUTER.MESSAGE.V1`) forbid
   session reuse.

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
  (`SharedView`, `SharedValue`, `ZeroizeWordVec`), and outbound message payloads
  (`Envelope`).

The Boolean-check vectors, PRSS scratch and pending Boolean queue wipe their
old allocation before growing, so no reallocation frees secret words.

Not wiped: short-lived `Word` / `FieldWord` temporaries inside the arithmetic
gadgets (adders, conversions, `fmul_many` products). Each holds two of three
replicated components of an intermediate wire and is released to the allocator
unwiped. A custodian that needs protection against later disclosure of its own
freed heap must run the ceremony in a process whose memory is discarded as a
whole.

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
projections; single-use fold multiplications retain smaller nibble tables.
