# Security invariants, specification tests and constant-time proofs

The release assurance record covers protocol proofs, extracted Rust kernels, compiled binaries and executable cross-checks.

**qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation** uses four
complementary assurance pillars. The theorem source and its premises are the
contract; neither a declaration count nor a passing test substitutes for a bridge
to the deployed code. [ASSURANCE.md](../ASSURANCE.md) defines the full TCB,
[PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md) describes the layout of the Lean library,
and implementation boundaries are collected in the
[last section](#from-component-statements-to-actual-construction-security) of this guide.

## Protocol, UC, storage and QROM spine

Paths in this guide are relative to `lean/Qsag/` unless they begin with another directory.

| Modules under `lean/Qsag/` | Subject | Scope to preserve |
| --- | --- | --- |
| `Spec/IdealSign.lean`, `Spec/IdealCustody.lean`, `Spec/IdealMigrate.lean`, `Spec/IdealCred.lean`, `Spec/IdealAggregate.lean`, `Spec/Assumptions.lean` | Ideal machines for signing (verifying candidates only, strictly increasing epochs in stateful mode, failed signing burns the epoch), custody (`deploymentId`, quorum over recorded approvals of the exact intent, adaptive corruption below threshold), migration (enrolled key, derived nullifier, single claim, conservation), credentials (capability handles, 4-of-5 TOPRF gate, quota), aggregation (break = collision among recorded queries; `AggregateExtractorSound` indexed by error and extractor class); games with separated coins over an explicit adversary class | The epoch-latched production signer refines `idealSignMachine` unconditionally (`productionLatchedSigner_refines_idealSign`). `Top/` also holds `Spec.DataRefines` statements for Lean custody, credential and migration models: `distributedCustody_refines_idealCustody`, `piToprfCredMachine_dataRefines_ideal` and `dlogSettlement_dataRefines_idealMigrate`. `SuccinctWhirExtractorAndIdealAggregate.lean` constructs the aggregate extractor and proves the ideal-aggregate bound under the stated packed-slot game hypotheses. Rust linkage is tracked per extracted function. Hardness for an unrestricted adversary class is refutable. |
| `Spec/Algebra.lean`, `Spec/Parameters.lean`, `Spec/Primitives.lean` | `LawfulField` (with `inv_zero`), `PrimeOrderGroup` (with `n_prime`), deployed parameters, primitive interfaces | Parameters are checked against the Rust constants by inspection of each line, not by extraction. Curve group laws are assumed. |
| `Math/Goldilocks.lean`, `Math/QuinticExt5.lean`, `Math/Gf2Pow128.lean` | Prime field, Quintic challenge field and binary towers | The MIR weld maps each of the five wire limbs to its power-basis coefficient. |
| `Oracle/Keccak.lean`, `Oracle/Poseidon2.lean`, `Oracle/Sponge.lean` | Sponge/permutation algebra and framing | Match byte order, domain tags, lengths and padding to runtime codecs; permutation invertibility is not cryptanalytic security. |
| `Protocol/Signing/Fips205.lean`, `Protocol/Threshold/ThresholdMpc.lean` | SLH-DSA parameters, domain separation, threshold/reference evaluation | Match key, message, context and randomizer before asserting identical output. |
| `Protocol/Signing/HashSigs.lean`, `Protocol/Signing/HypertreeEufCma.lean`, `Protocol/Threshold/BaggyAndRss256Security.lean` | WOTS+C, TSW, hypertrees, Baggy, Waistband and RSS256 | Reductions require reachable layers and valid transcripts; a first-success grinder and cached internal signatures must refine the reference construction. |
| `Machine/MirSpecBridge.lean`, `Protocol/Threshold/MaliciousSecurity.lean`, `Custody/JortsBeltLatchAndQuorumSwitching.lean` | Stateful signing, certified BeltLatch, quorum intersection, active checks | Global latch condition is `2q > n+f`; BFT availability needs `q <= n-f` (feasible together when `n >= 3f+1`). QS-A deliberately uses disjoint committee custody. |
| `Protocol/Aggregation/UcGames.lean`, `Protocol/Threshold/IdealTsig.lean`, `Exec/SimulationSpine.lean`, `Exec/InteractiveUcEngine.lean` | Oracle games, ideal functionality and simulation | Generic simulation premises must be instantiated with the concrete scheduler, messages and shared resources. Sequential sessions do not establish arbitrary concurrent composition. |
| `Exec/PosixCrashWal.lean` | POSIX/NVMe persistence, torn writes, recovery, genesis seals and `OpenDescriptionId` flock ownership | `Exec/CeremonyAtomicityAndAbort.lean` supplies a valid-trace multi-ledger crash/interleaving theorem; production events must instantiate it. Host persistence and snapshot assumptions remain explicit. |
| `Protocol/Aggregation/ConcreteSecurityBudget.lean`, `Oracle/Qrom.lean` | Square-root-free unitary BBBV97/O2H, fiber-cardinality search reductions | A fixed-bad-set search lemma does not automatically establish adaptive multi-round Fiat–Shamir security. |
| `Protocol/Aggregation/PublicHemQuintic128.lean`, `Protocol/Aggregation/ZkHemV2PackedFiberCerts.lean` | Public WHIR and packed-fiber security | Bind the commitment profile, schedule and query cap to the bound. |
| `Protocol/Threshold/LatticePreprocessingFull.lean`, `Math/Lattices.lean` | Lattice preprocessing and extraction | `Math/CyclotomicRlwe.lean` (re-exported by `Protocol/Threshold/RlweExtraction.lean`) proves signed-monomial difference invertibility, short relaxed extraction, and the Euclidean-norm relation. See the exact parameter map below. |
| `Custody/CustodySuiteFull.lean`, `Protocol/Threshold/ThresholdMlDsaAndToprf.lean` | Custody, credentials and migration | Local checks and source-landed bridges are not automatically integrated production theorems. |

The constructive discipline is **0 sorry / 0 Classical.choice**, with permitted
axioms `{propext, Quot.sound}`. Axiom audits must cover loaded/generated modules
and private declarations; CI challenge exports need an explicit production roster.
A recorded audit describes the source bytes it ran on. The module roster it must cover is
`lean/Qsag.lean` together with `lean/AuditAxioms.lean`, both regenerated by
`lean/tools/gen_rosters.py`; `scripts/check_lean_policy.py` rejects a file on disk that is
missing from either, and `scripts/check_extraction_provenance.py` checks the extracted
crates against their recorded source hashes.

The unified Lean 4.35 audit covers 340 `Qsag` modules. The source-policy gate checks
432 files across the three packages. The axiom censuses report 139,005 declarations
(74,363 theorems) in `lean/`, 6,887 (2,917 theorems) in `aeneas/lean/`, and
2,160 (1,185 theorems) in `aeneas/lean-whir/`. Together they cover 148,052
declarations with 0 rejected. The main comparator replays 152 `Qsag.Top`
theorems through 6/6 paranoid kernels, covering 16,829 exported declarations.

### Boundary, bridge and test modules

These results state what a neighbouring theorem does and does not cover, usually with a
proved counterexample or an executed instance. Several formerly separate boundary files now
live inside the domain module named in the first column; executed instances are under `Tests/`.

| Module | Statement | Scope |
| --- | --- | --- |
| `Protocol/Aggregation/HemOpening.lean`; teeth in `Tests/HemExtractedOpeningBridgeTests.lean` | Facts read off `verifyHemAffineWhir` itself: the oracle/claim arity check is necessary (`tooth_missing_batch_claim_erases_oracle`); for a zero-oracle false statement, acceptance forces a linear challenge collision (`verifyHemZeroOracle_implies_linear_collision`, `verifyHemZeroOracle_accepted_pairs_le`); the packaged core agreement is stronger than the checker (`tooth_core_agreement_is_stronger_than_checker`). | One false-statement family, not arbitrary Hem statements; no refinement of the Rust transcript parser. |
| `Protocol/Aggregation/HemRbrSoundness.lean` | The point-reduction wire decoder reconstructs `c1 = claim - 2*c0 - c2`, so the sum equation holds by construction (`hemPointReductionWire_sum`); a wrong hypercube sum agrees on at most two challenges and the bound is attained. | Local algebra; no adaptive composition. |
| `Coding/Cwyz26.lean` (fold-decomposition bridge) | The `UPoly` and coefficient-list forms of the claim-preserving fold relation are equivalent (`hasPolynomialExplanation_iff_decomposes`), with the same selected post-fold polynomial and no uniqueness-radius premise. | Representation bridge between the coding and transcript developments. |
| `Coding/Resultant.lean`, `Coding/AffineProximity.lean`, `Coding/Cwyz26.lean`; instances in `Tests/MathAndCoding.lean` | Primitive plane-curve common-root bound; dimension-one nonpersistent cover; candidate-specific persistent-pair count under $\lvert D\rvert(d+1)<B^2$; inhabited instances and a tooth showing the persistent bound needs the far-from-code premise. | The two-dimensional step of CWYZ Claim 4.8 remains open (multi-sheet branch). |
| `Oracle/Qrom.lean` (extraction boundary) | Measured-query branch masses, observed-response consistency, bridge to `merkleQueryConsistent`; target cardinality does not give locality; recording a query changes Born probability. | Measured-query interface. Coherent extraction is separate. |
| `Oracle/Qrom.lean` (measured-query experiment, Merkle extraction, classical-query transfer); instances in `Tests/OracleAndQrom.lean` | A measured-query experiment with lazy sampling; Merkle extraction-failure mass at most `(d·(3Q+1) + (0+…+(Q-1))) / 2^w` with the consistency premise derived from the log; the same bound on the coherent run for adversaries whose queries sit on one address. | Not coherent-query QROM security: the parity circuit gives 8/8 coherently and 4/8 when measured. |
| `Math/CyclotomicRlwe.lean` | The `ℓ∞`-only short-SIS branch of the fork-extraction dichotomy has the public solution `s=1, e=centered(-A)` (norm ≤6144 always, ≤6142 outside four residues per coefficient). With the production Euclidean check `‖z_s‖₂²+‖z_e‖₂² ≤ 1,500,000,000`, extraction lands in a joint relation with squared norm ≤ 6,060,827,392 that rejects it (`extract_rlwe_or_sigma_24_euclidean_sis_dichotomy`, `tooth_rlweUnitSis_refuted_by_euclidean_bound`). | A statement about the reduction target, not a forged transcript; hardness of the resulting Ring-SIS instance is an assumption. |
| `Oracle/Spn.lean` (trail sampling) | `≤ 6^k` of `N^k` assignments succeed in the fresh-independent-input S-box experiment; a realised trail of the fixed SPN cannot have probability `(6/2^128)^48`. | Separates component arithmetic from a fixed-permutation trail bound. |
| `Custody/SeparatedCustody.lean` (which now contains the former mediation-boundary, core, spine, policy and history modules); `Tests/SeparatedCustodyChecks.lean`, `Tests/SeparatedCustodyHistoryChecks.lean` | One-custodian vault transitions with durable change before release (`release_durable`, `release_replay_rejected`, `forget_burns`, `trace_burned_spend_le_cap`); independently keyed approvals composed into a quorum certificate with structural extraction to the production hash-signature break events; executed cSHAKE256/Jorts construction checks. | Specification level: no fsync, key-isolation, anchor or ELF/MIR refinement; separate keys, not threshold reconstruction of one key. |
| `Oracle/Sponge.lean`, `Tests/CompositionInstances.lean`, `Protocol/Aggregation/ComposedQsAgAndMergeSecurity.lean`, `Protocol/Aggregation/CrossProtocolAndDualOracleComposition.lean` | pad10*1 and cSHAKE prefix injectivity and cross-domain separation; generic composition reductions, with fixtures in which bad and forgery events are false and wrong-context constituents are rejected. | The fixtures use public checksums and a non-succinct reference aggregator; none instantiates a cryptographic assumption. |
| `Exec/IdealOutputBoundary.lean` | Fresh successful ideal release equals the functionality's signature; injective request and key encodings; exact-retry versus changed-intent. | The engine's callbacks are cluster-level; party-local custody and a partial production oracle are separate. |
| `Protocol/Aggregation/ZkHemV2PackedFiberCerts.lean` | A single 400-bit OOD seed has a bounded number of preimages for each quintic value. | The packed-fiber budget includes the resulting list-collision term. |
| `Protocol/Threshold/DensePcgTaps.lean`, `Math/TapRowParityBias.lean` | Exact bias of a linear test as a product over trees; the production tap generator on the Keccak specification; row 0 of one generated matrix has bias between `2^-118` and `2^-117`. | Taps modelled as uniform for the second-moment law; no bound over all row subsets. |

## Signature output laws and Pants state

For FIPS 205 SLH-DSA-SHAKE, Baggy, Jorts 2-of-3 and QS-B, the threshold/reference
claim is equality of successfully evaluated bytes for the same key, parameters,
leaf/message and matched hedging seed. This gives statistical distance **0** under
that coupling. It does not prove equality under different randomness or allocator
policies, nor after adversarially selective abort. FIPS 205 and FIPS 204 outputs
are standard-verifier compatible; ML-DSA compatibility is not a proof of perfect
accepted-output distribution equality. Production reference refinement remains a
per-path obligation.

Baggy is a stateless hypertree + TSW construction. Waistband caches only static
Top-$L$ internal child-root WOTS signatures, never message-binding leaves. Its
256-bit digest WOTS+C profile has `w=4, chains=128, target_sum=192`. Its few-time
layer is PORS+FP and nothing else: one tree of $2^{11}$ leaves per hypertree leaf, 28
distinct leaves revealed, a canonical multiproof of at most 128 nodes (the signer grinds
the public counter until the selected subset qualifies, about one in $2^{10}$), at most
4,994 bytes for the layer and 71,654 for the signature. The verifier refuses unsorted,
duplicated and oversized openings and consumes exactly the canonical node sequence;
PORS geometry is checked before any signature-size arithmetic. The FORS+C layer and
its selection, opening and verification code are deleted. The 256-lane
Keccak path and carryless $GF(2^{128})$ BGIN19 DZK support threshold evaluation.
“Unlimited lifetime” excludes a stateful leaf budget, not finite-query security
accounting or persistence of MPC resources. Corduroy is the algebraic Poseidon2
stateless custody hypertree. Jorts is explicitly crash-WAL/BeltLatch guarded.

**QS-A (`CommitteePartitionedJorts`) reveals the committee** through its disjoint
leaf ranges. It permits t-of-t online signing when $2f>t$ with safety and abort;
malicious online custodians can withhold participation. **QS-B (`BftShamirJorts`)**
uses a global tree and quorum-independent allocation with certified BeltLatch and
self-verifying pre-stepped Shamir WOTS+C. Allocation privacy does not imply
transport anonymity. Match the actual signing threshold and latch quorum.

### Few-time signature profiles

| `qsag-fts` profile | Bytes | Node bytes | $w$ | $h$ | $L$ | Target sum | Uses |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Compact1122` | 1,122 | 32 | 96 | 8 | 34 | 1,615 | 1 |
| `Full256Bit` | 2,338 | 32 | 5 | 8 | 72 | 144 | 1 |

Both have rank domains above $2^{256}$ and 32-byte nodes. The node width gives a nominal
generic preimage scale of $2^{256}$ classical work or $2^{128}$ Grover work; the larger rank
domain does not raise that 256-bit node limit. The former `Compact514`, `Compact770` and `Compact1314`
profiles used 16-byte nodes (64 Grover bits) and two of them allowed two uses; they, their
CLI spellings and their fuzz and test consumers are removed, and the former two-use tests
now assert single-use behaviour. `Fast256Test` is gated by tests or the explicit `test-params` feature. Node width is not a
security reduction: an EUF-CMA proof for the $w=96$ profile is open.

## Quintic Hem security and QROM accounting

All three proof families use $p=2^{64}-2^{32}+1$ and `Fp5` with $X^5=3$. A canonical field element occupies five little-endian limbs (40 bytes), giving $p^5\approx2^{320}$ possible challenges. A commitment digest and a challenge field element have different encodings.

| Proof and statement | Binding and security budget |
| --- | --- |
| Public `HemQuintic128` (`QSAGHQM2`) | `TurboShake400` uses 50-byte / 400-bit TurboSHAKE256 digests. `Poseidon2Gl24` uses seven canonical Goldilocks limbs (56 bytes / 448 bits on the wire, $p^7$ possible digests). Both use a 400-bit Fiat–Shamir chain. The [DKT26] schedule queries 267 distinct Stage-0 fibers at $\log_2 N=16\ldots23$ and 266 at $24\ldots28$. `publicHemQuintic_qrom_soundness_128` gives total QROM error $<2^{-128}$ for all 13 schedules through $Q\le2^{64}$ in the ideal hash model. |
| Committed-mask zk-Hem v2 (`QSAGZKH2` single-party, `QSAGZKS2` split-share) | Every Stage-0 tree binds a 32-byte `tree_nonce` and every leaf has a 32-byte salt. `LookupV2Proof` jointly masks the LogUp helper and assignment openings. [DKT26] Theorem 5.12 bounds the mask-line fold. The packed-fiber certificates give $<2^{-128}$ QROM error for all 13 schedules at $Q\le2^{64}$. |
| Binary IVC (`QSAGIVC1`) | A leaf proves Jorts signatures and registry membership. An internal step verifies both child arguments and binds adjacent shard intervals and their quorum sum. The [DKT26] root is 639,673 B at every depth. `bits_canonical_u64` in the leaf circuit enforces the strict limb bound $x<p$ (`GOLDILOCKS_P`) when binding registry and message bytes. |

The public row verifier pins all 138 non-S-box columns to their prescribed values in inactive padding slots. This prevents padding from supplying extra unconstrained state. [Row constraints](../crates/qsag-agg/src/hem_quintic/rows.rs) · [Public QROM accounting](../lean/Qsag/Protocol/Aggregation/PublicHemQuintic128.lean)

For committed-mask wire profiles in the 16–19 range, both Rust decoders accept 16 (cSHAKE256) and 17 (TurboSHAKE256), each with a 400-bit digest. Tags 18 and 19 fail `Profile::from_wire_tag`. The magic selects single or split proof framing. [Profile decoder and query schedule](../crates/qsag-agg/src/zk_hem/v2/params.rs) · [Wire formats and lookup proof](../crates/qsag-agg/src/zk_hem/v2/protocol.rs)

`MultiDepthRecursiveQromExtractor.lean` constructs the straight-line extractor. Its numerical bound is $<2^{-128}$ through depth $d\le16$ and $Q\le2^{64}$ for a recursive margin schedule with $\log_2 N=20$ and query counts 304/148/100. The Rust root codec selects `IvcStepConfig::dkt26(23)`. The theorem's schedule premise matters when applying its error bound to a binary. [Recursive theorem](../lean/Qsag/Protocol/Aggregation/MultiDepthRecursiveQromExtractor.lean) · [Margin schedule](../lean/Qsag/Protocol/Aggregation/ZkHemV2PackedFiberCerts.lean) · [Rust root profile](../crates/qsag-agg/src/zk_hem/recursive_ivc/tree.rs)

## Blinded MAC checks

The dishonest-majority engine keeps its MAC key $\alpha$ across sessions and through
resharing, so a failed MAC check must not reveal anything about it. A residual
$d=m-\alpha x$ is zero for a correct opening; after a shift $\Delta$ of the opening it
equals $-\alpha\Delta$, and opening it gives away $\alpha$. A degree check does not prevent
this: at $t=n$ there is no redundancy, and a reshare dealer can distribute a
degree-consistent value polynomial whose constant term violates the MAC relation.

`crates/qsag-core/src/preprocessing/mac_blind.rs` opens $w=(\sum_i r_i)(\sum_j d_j)$
instead, for every valid $(t,n)$ and for the scalar Goldilocks, extension-field and Boolean
wrappers. The protocol, step by step:

1. Commit the value shares before opening them. Form additive shares of the folded
   residual privately.
2. Each party draws a private randomizer contribution $r_i$.
3. Compute additive shares of $w$ by oblivious linear evaluation on KOS OT extension, with
   the residual on the sender side and disposable random masks as the receiver's choices.
   Goldilocks: one product in $\mathbb{F}_{p^2}$ (not two independently corruptible
   base-field products), 640 disposable choice bits, then a hash in the native field.
   `Tower128`: six independent 128-bit masks.
4. Derive both hash coins from the completed OT transcript and the ciphertext transcript.
5. Commit every share of $w$, then open $w$, and accept when it is zero. For Shamir MAC
   consistency, blind each degree syndrome and the reconstructed constant with its own
   randomizer.

| Check | Function | False-zero term in the ideal-OLE hybrid |
| --- | --- | --- |
| Goldilocks extension residual and degree syndromes | `blind_open_ext2`, `blind_open_degree_ext2` | $p^{-2}$ per test |
| `Tower128` two-lane residual | `blind_open_tower128`, two independent rounds | $2^{-256}$ |
| Additive Boolean opening (`open_additive_authenticated` in `triple_f2.rs`) | Commit the full residual vector; three projection coins bound to the commitments and the running OT transcript; each projection through `blind_open_tower128` | $(q^{-1}+(1-q^{-1})q^{-2})^3<q^{-2}=2^{-256}$, $q=2^{128}$ |

With every corrupt input fixed, an honest $r_i$ leaves $\sum r_i$ uniform, and for $d\ne0$
the map $r\mapsto rd$ permutes the field, so $w$ is uniform; conditioned on abort it is
uniform on the nonzero elements and independent of $\alpha$. Raw Gilboa multiplication on
the bits of the residual would not have this property, because selective failure on a
choice bit is then a test on the residual. The additive Boolean path never reconstructs an
unblinded residual sum; its projections stay in the MAC's polynomial basis and the final
map into the tower representation is XOR-linear and zero-preserving, so no field
isomorphism is needed to test zero.

Scope: the terms above add to the folding, OT and PRG bounds and assume the
post-correlation entropy amplifier satisfies the leftover-hash criterion of MASCOT
(Appendix C). Evidence is by regression: unanimous Goldilocks and Boolean shifts, a
degree-consistent 3-of-4 coalition shift, a degree-consistent dealer shift with full
redundancy, a fault confined to the second lane, and repeated aborts with $\alpha$, the
corrupt tape and the base OT fixed, in which the opened value equals $r\cdot d$ and differs
across 16 honest tapes. A unanimous reshare with a shifted share ends in
`ReshareMacCheckFailed`, leaves the old custody bytes intact, and the old custody still
signs. No Lean theorem states this property.

Related preprocessing parameters:

| Item | Statement | Source |
| --- | --- | --- |
| Bucket size for Boolean triple combine | Least $f$ with $n/\binom{f(n+1)}{f}\le2^{-40}$ over $n$ output bits, after a post-hoc bit-level permutation: $f=3$ at 8,192 words, $f=4$ at 7,720 words, $f=7$ at one word. One bucket per pass discarded so the pool parity stays hidden; two passes on the claimed-factor PCG path. | `crates/qsag-core/src/preprocessing/triple_f2.rs` |
| `GoldilocksExt2` authentication | Toeplitz combiner in blocks of 32 values; block id binds session, start and total count; fresh 256-bit tail entropy and a post-correlation coin per block; union bound over $\lceil\mathrm{count}/32\rceil$ blocks. The coin binds the completed OT-mesh transcript digest. | `crates/qsag-core/src/preprocessing.rs` |
| Migration preprocessing | Setup binds the session, party and tape identifier to an external monotone checkpoint before any share transmission. | `crates/qsag-migrate/src/hem/collab/engine.rs` |
| 192-bit reduction | `reduce_192_mod_p` has total-variation distance $(p-1)/(p\cdot2^{192})<2^{-192}$ from uniform, not zero. | `crates/qsag-accel/src/keccak.rs` |

## Compiler-extracted MIR and release ownership

The 13-package root workspace consumes two separately rooted extraction crates: `aeneas/qsag-verified` (core/policy/quorum) and `aeneas/qsag-whir-verified` (aggregation). Charon + Aeneas generate `QsagVerified.Funs`; `QsagMirProofs`
provides checked arithmetic, sponge, WOTS+C, BDOZ, BeltLatch, Waistband and
poison-latch guard results under the **0 FunsExternal** extraction discipline.
See [AENEAS_VERIFICATION.md](AENEAS_VERIFICATION.md) for precise statements.

Direct production linkage is present. Fresh extraction and universal bridges remain distinct from finite parity tests. Complete mediation also needs private secret ownership,
bound output objects, disjoint leases, context/poison generation checks and durable
receipts. A verified guard does not constrain an unextracted caller holding raw
shares. A forgotten permit must lose availability rather than return a resource to
reuse; `Drop` is not a durable transaction boundary.

## POSIX, policy, transport and migration

The POSIX model now assigns `flock(2)` to **OpenDescriptionId**, not PID.
Independent opens contend even in one process; dup/fork references share the lock
and do not serialize threads using the same description. File and parent-directory
`fsync`, stable lock sidecars, genesis binding and explicit error recovery remain
part of the contract. No filesystem-only proof prevents a fully cloned disk/VM
rollback without external monotone state.

The journals that count one-time and few-time uses share one layout and one recovery rule:

| Journal | Magic | Layout | Recovery |
| --- | --- | --- | --- |
| FTS burn journal (`crates/qsag-fts/src/wal.rs`) | `QSBURN05` | Page 0 genesis prefix; high-water-mark slots at 4096 and 8192; records from 12288 | Authenticate the committed prefix and the mark; truncate an uncommitted tail to the authenticated boundary and sync; a corrupt or missing committed record or an overclaimed mark fails closed |
| HD query budget (`crates/qsag-hd/src/budget.rs`) | `QSHDQB05` (rejects `QSHDQB04`) | Same paged two-slot layout | Same; the guarded open also checks permissions by `fstat` on its second descriptor |
| Core durable ledger, quorum directory anchor | — | Shared `TwoSlotRecord` (`crates/qsag-core/src/two_slot_record.rs`) | Two-slot recovery with corruption tests |

Records and their locks go through `qsag_asm::durable::LockedRecord`
(`crates/qsag-asm/src/durable.rs`): the lock is identified by the held descriptor and
re-checked inside every read and replace, and on Unix a record or lock with
`mode & 0o077 != 0` is refused, on the path and on the descriptor. External anchors are
consumed through single-use tickets (`AnchorTicket` in `durable_ledger.rs`): a ticket is
reserved, the journal write is made durable, and the ticket is consumed; replay, a failed
persist, a crash at either point and a second consumption are all refused. The CLI gate
(`require_anchor_or_waiver` in `crates/qsag-cli/src/anchor.rs`) demands exactly one of
a monotone anchor (`--anchor-dir`, or `--anchor-tpm-nv` with one never-written counter per
anchored domain) and `--ephemeral-unanchored` for `keygen`, `sign`, `aggregate`,
`quorum keygen` and `policy init`, and the MAC-covered `anchor_required` field stops an
anchored key from being used under the waiver. `--anchor-vmgenid` detects VM snapshot
and clone only and is refused without a disjoint-device directory anchor or a TPM
counter: an in-place restore of same-disk state passes its checks. `Exec/TwoSlotHwmCrashModel.lean` (with
`Exec/TwoSlotHwmBase.lean`, instances in `Tests/TwoSlotHwmTeeth.lean`) is the Lean crash
model of the paged two-slot layout under torn sectors, with the MAC as an assumption.

Leaf use, policy spend, preprocessing, nonce burns and poison state must compose
before any useful partial share release. `Exec/CeremonyAtomicityAndAbort.lean` proves ceremony-level safety for valid crash/interleaving traces; the runtime reservation and release paths must refine that event model. Policy time windows need an authoritative clock or
agreed logical epoch; authenticated caller timestamps alone are insufficient.
Channels must provide confidentiality, authenticity, replay protection and the
broadcast consistency the protocol assumes. Loopback/RAM and simulated-WAN
benchmarks do not certify this deployment boundary; MAC framing is not encryption.

The migration CLI supports 19 credential kinds. The classical key interface exposes
`ClassicalCommitmentKind` and `ClassicalOwnershipWitness` in
`crates/qsag-migrate/src/classical.rs`. Migration uses zk-Hem v2 exclusively.
One prover produces a `QSAGZKH2` proof. Collaborative provers use Toom-3
`Fp5` MPC and produce `QSAGZKS2`. Before round 1,
`hem::collab::Engine::new_anchored` burns `tape_id()` against an
`ExternalMonotoneAnchor`, checking the prior generation and binding the session,
tape and party into the advance. An anchor failure aborts setup before transmission.
[Migration kinds](../crates/qsag-cli/src/migrate.rs) · [Anchored MPC setup](../crates/qsag-migrate/src/hem/collab/engine.rs)

Blind issuance in `qsag-cred/src/blind_vc.rs` uses 438 repetitions of
three-party Goldilocks MPC-in-the-head for the Quantum128 profile. The interactive
cut-and-choose error is $(2/3)^{438}$. Selective-disclosure presentations use
the zk-Hem v2 relation. The constructive cut-and-choose theorems in
`Protocol/Migration/` and `Protocol/Credentials/` analyze their respective
games. [Blind issuance](../crates/qsag-cred/src/blind_vc.rs) · [Presentation relation](../crates/qsag-agg/src/zk_hem/blind_vc.rs)

## Grounded ISA, compiled ELF64 and zeroization

`Machine/ConstantTimeIsa.lean` is the leakage model and taint checker over a hand-written
instruction AST; it models no `qsag-asm` kernel. `Machine/IsaCt.lean`, `Machine/ElfVerify.lean`
and `Machine/ElfFixtureVerify.lean` cover the byte-decoded x86_64
AVX2/PCLMULQDQ/VPCLMULQDQ and aarch64 SHA3/PMULL kernels: taint noninterference,
scratch-register zero-on-exit and mutation `#tooth` witnesses. The release screen below inspects the linked ELF. Connecting every dispatch and caller to a semantic certificate remains a separate obligation. DOIT / **PSTATE.DIT** must be tied to actual runtime state.

PC/memory/latency observations are model-specific, not arbitrary hardware leakage.
Callee scratch wiping does not erase caller frames, restored registers, compiler
copies or OS context saves. `vzeroupper` does not wipe every vector register; calls
are not implicit wipes. `black_box` and fences do not prove whole-process erasure.
Higher-level rustc/LLVM, wrappers and fallbacks remain trusted for leakage claims.
See [CONSTANT_TIME_ASM.md](CONSTANT_TIME_ASM.md) and
[BINARY_RLIB_VERIFICATION.md](BINARY_RLIB_VERIFICATION.md).

### Constant-time screen of the current release archives

The canonical release profile sets `opt-level = 3`, `lto = "thin"` and
`codegen-units = 1`. The recorded `scripts/audit_elf_ct.py` screen reports
zero errors for the linked Linux release ELF and the audited archive symbols.
It tracks secret-dependent control flow and addresses for scalar interfaces
and checks SIMD register hygiene, dividers and gathers for the supported
compiled interfaces. Its 175/175 `#tooth` self-tests exercise the rejection paths.
The result applies to the inspected machine code under the auditor's leakage
model. Changing compiler flags can change that code. [Binary audit](../scripts/audit_elf_ct.py) · [Release assurance record](../ASSURANCE.md)

## Verify your code, test your specs

- **Native spec oracle:** `lean/SpecOracle.lean` / `lake exe spec-oracle` and
  `scripts/spec_differential_fuzz.py` compare Rust and Lean outputs, including
  metamorphic threshold/single-signer cases and clause-drop mutations. `qsag-kat` (`lean/Main.lean`)
  supplies executable known-answer vectors. Check consumed case counts and exact
  framing, not merely process success.
- **Physical ISA cosimulation:** `lake exe isa-cosim` compares modeled operations
  with x86_64 silicon on sampled states. It does not universally validate a decoder
  or prove compiler semantic preservation. Missing native hardware is not a pass.
- **Empirical timing:** `ct_dudect` measures selected dispatched operations with
  Welch t-tests. Passing samples complement model proofs, not establish universal CT.
- **Independent proof checking:** six-kernel `comparator --paranoid` CI challenges
  replay selected exports. Required-gate integration must include fresh extraction,
  both axiom audits, nonempty theorem instantiations and the exact release bytes.
- **Workspace and differential tests.** The release suites exercise production entry points and compare selected outputs with independent implementations in `validation/`.
- **Cross-language known answers.** `scripts/cross_kat_runner.py` checks 317 cross-KAT vectors against linked Rust. The domain inventory tracks 952 domain labels with `scripts/sync_domain_labels.py --check`.

- **Miri:** the full `qsag-asm` invocation passes 19 library tests, 1 integration test
  and 1 compile-fail doctest. Under Miri the backend is the portable one; dispatch,
  unaligned and tail buffers with sentinels, modular arithmetic, Keccak, transpose and
  MAC, NTT and SHA are covered, and the hardware, file-lock and timing modules are
  excluded there and run natively.
- **Fuzzing:** five libFuzzer harnesses in `fuzz/fuzz_targets/`
  (`fuzz_fips205_and_fts_decode`, `fuzz_blind_vc_and_agg_decode`, `fuzz_quorum_frames`,
  `fuzz_whir_agg_verify`, `fuzz_diff_hashes_and_ntt`) build with sanitizer coverage and
  compare tracing and ran ten seconds each with nonzero coverage and no crash. That is
  a build-and-smoke gate; it says little about deep states.

Each security theorem needs a load-bearing-check mutation or concrete attack
witness where feasible. `#tooth` witnesses demonstrate specific failures; their
existence alone does not guarantee that every theorem is nonvacuous. The desired
acceptance chain connects production entrypoint, source/configuration, generated
function, theorem/assumptions, profile, binary digest and tests. Independent green
checks without those links do not close the assurance architecture.


## Current parameter and theorem map

The table identifies the implementation or theorem behind each parameter.

| Parameter / relation | Exact current statement | Source |
| --- | --- | --- |
| RLWE OR-Sigma | `C={±X^k:0≤k<1024}`, 2,048 choices; 24 × 11 = 264 joint bits. Nominal exhaustive-search exponents: 264 classical / 132 generic Grover; these are challenge-space arithmetic, not a quantum-active OT theorem. | `preprocessing.rs`: `RLWE_ZKPOK_REPS`, `RLWE_ZKPOK_CHAL_BITS`, `poly_from_chal11` |
| RLWE response sampler | Truncated Gaussian σ=700, masks in `[-3072,3071]`, accepted responses in `[-3070,3069]` and, per branch pair, `‖z_s‖₂²+‖z_e‖₂² ≤ 1,500,000,000` (`RLWE_ZKPOK_PAIR_L2_SQ_BOUND`, checked by prover and verifier); acceptance `min(1, exp((‖y‖²−‖z‖²)/980000)/M)`, `M=exp(3615102/980000)≈40`. Q192 finite-precision sampling and normalized vector Gaussian/tail hypotheses still need production proof instantiation. | `crates/qsag-core/src/preprocessing.rs` |
| RLWE extraction | For degree `2^ν` and odd `q≥3`, distinct signed monomials satisfy `(c−c′)g=2` and their difference is a unit. Isometric extraction yields `A s_iso+e_iso=(1−c⁻¹c′)u`; at q=12289 the infinity norms are ≤6140. Secret recovery or a nonzero short-SIS relation has bound ≤6142. With the Euclidean check the extracted pair also satisfies `‖s‖₂²+‖e‖₂² ≤ 6,060,827,392`, which the public solution `s=1, e=centered(-A)` fails. This is a relaxed relation, not unconditional recovery of the original CBD witness. | `Math/CyclotomicRlwe.lean` (re-exported by `Protocol/Threshold/RlweExtraction.lean`): `signedMonomial_challenge_set_pairwise_invertible`, `extract_rlwe_or_sigma_13_short_witness_1024_sound`, `short_monomial_witness_recovers_secret_or_breaks_short_sis`, `extract_rlwe_or_sigma_24_euclidean_sis_dichotomy` |
| WHIR fiber queries | 267 at log₂ cells 16–23, 266 at 24–28. Later stages use ⌈532 / log₂(blowup)⌉ + 3. | `crates/qsag-agg/src/zk_hem/v2/params.rs` |
| Packed-fiber budget | The sum of scaled round errors and the commitment term is strictly below $2^{-128}$ for $Q\le2^{64}$ across the 13 single-proof schedules. | `Protocol/Aggregation/ZkHemV2PackedFiberCerts.lean` |
| WOTS+C | 128 base-four digits sum to 192. The accepted language has the coefficient of `x^192` in `(1+x+x²+x³)^128`, namely 3647133497298879801227908259470154861817607767728241841601287895307331452700 elements (≈251.01137 bits); uniform first-success grinding averages ≈31.7488 trials. Encoding width alone does not give 256 bits of accepted-language entropy. | `crates/qsag-core/src/tsw_baggy.rs`; `Protocol/Signing/HashSigs.lean` |
| Baggy few-time layer | PORS+FP `SHA3_128F`: tree height 11, 28 revealed leaves, at most 128 multiproof nodes; layer at most `32·28 + 2 + 32·128 = 4,994` bytes; signature at most 71,654 bytes. Subset-cover bound $\binom{28g}{28}/\binom{2048}{28}$: at least 209, 157, 136, 122 bits for $g=1..4$ (proved in-tree by `sha3_128f_binomial_bits`; the Rust estimate is `forgery_bits_milli`). | `crates/qsag-core/src/pors_fp.rs`; `Protocol/Signing/PorsFpSecurity.lean` |
| Threshold FTS ceremony | Per tuple and ordered pair: 256 random OTs for the shared-operand products (three operands in the three 16-byte segments of a 48-byte KOS pad, plus one set for $a^6$) instead of 7,552; MACs from 128 random OTs per lane on the key share, expanded to cSHAKE256 streams and folded by powers of $z$; squarings checked by one batched linear check; three products combined with weights $s,s^2,s^3$ against one sacrificial product; 9 authenticated values instead of 25. Tested by fault injection, not modelled in Lean. | `crates/qsag-fts/src/dkg.rs`, `crates/qsag-fts/src/ot.rs` |
| Threshold OPRF reservoir | Chunks of 4 power tuples or 32 triples per preprocessing run, each under its own session id `PREPROCESS.V2(binding, sessions, scope, counter)`; union bound over runs. Client checks $ab=c$ on each reconstructed triple (a shifted factor passes with probability $1/p$) and masks each input limb with two triples ($1/p^2$). | `crates/qsag-cred/src/voprf_spdz.rs` |
| Migration | The generation-checked tape burn precedes collaborative proving. Single-party and split proofs have distinct canonical wire magics. | `crates/qsag-migrate/src/hem/collab/engine.rs`, `crates/qsag-agg/src/zk_hem/v2/protocol.rs` |

The theorem `zkHemV2_packed_all13_qrom_lt_128_at_2pow64` covers the entire single-proof schedule family. The packed leaf depth is the log of the fiber domain, and the OOD error uses the preimage count of a 400-bit seed in the quintic field.

`Exec/CeremonyAtomicityAndAbort.lean` establishes batch disjointness, unique ceremony/message per leaf, spend caps and persistent poison or fail-closed behavior for valid multi-ledger crash/interleaving traces. Its pre-open masked-view selective-abort theorem gives statistical-distance numerator zero with positive survival count. Arbitrary post-output withholding is outside that conditioning theorem. `Protocol/Signing/HypertreeEufCma.lean` reduces accepted fresh-message forgeries in the specified stateless signing-log model (at most 2^32 layers) to ITSR, TCR or preimage breaks; this is stronger than its legacy Type-valued extractor interface.

### Runtime consumers and extracted proofs

| Production consumer | Executed extracted interface | Proof surface |
| --- | --- | --- |
| `qsag-core`, `qsag-quorum` | `VerifiedWotsC256Guard`, `VerifiedBeltQuorumGuard` (`record_custodian_ack`, `authorize_release`), `ct_eq_bytes32`, `validate_belt_quorum_config` | `aeneas/lean/QsagVerified/Proofs/PantsAndQuorumGuards.lean`, `aeneas/lean/QsagVerified/Proofs/MultiTurnMediationAndReachability.lean` |
| `qsag-policy` | `checked_velocity_spend`, `StatefulVelocityGuard::authorize_spend` | `aeneas/lean/QsagVerified/Proofs/PolicyAndAddr.lean`, multi-turn reachability |
| `qsag-agg` | `decode_canonical_u64`, `decode_canonical_fp5`, `decode_canonical_gl24_digest`, `cwyz_duet_fold_fp5`, `cwyz_bridge_claim_step_fp5`, `eval_quadratic_sumcheck_wire_fp5`, `eval_fp5_univariate_at_base`, `verify_ood_pin_eq_fp5`, `step_merkle_pair_order_400`, `step_merkle_pair_order_gl24`, `checked_quorum_sum`, `verify_qsaghqm2_header`, `verify_quintic_schedule_envelope` | `aeneas/lean-whir/QsagWhirVerified/{Proofs,Canonical,ProtocolWeld}.lean` covers these entry points and the corresponding fold predicate `verify_cwyz_duet_fold_step_fp5`, exercised in parity tests. |

`RealSpecFieldWeld.lean` (under `aeneas/lean/QsagVerified/Proofs/`) proves Goldilocks inverse refinement and the nonzero multiplicative-inverse law. `RealSpecKeccakWeld.lean` proves the 24-round permutation refinement and the phase law `shake256_absorb_after_squeezing_fails` (absorbing after squeezing fails with `.assertionFailure`; it is not a no-op). `SpongeFraming.lean` (same directory) supplies the rate-block XOR, padding and squeeze bridge: `shake256_absorb_pad_refines` for any split of the input into `absorb` calls, and `shake256_32_refines`, `shake256_squeeze_refines` and `cshake256_squeeze_refines`, which identify the bytes of the first squeeze, for a destination of any length and any customization, with `Qsag.shake256Xof` / `Qsag.cshake256Xof`. These concern the extracted sponge of `aeneas/qsag-verified/src/keccak.rs`; production reaches the constructor state through `Shake256Sponge::new_cshake256` in `crates/qsag-cred/src/toprf_engine.rs`, and the complete extracted `shake256_32` through `crates/qsag-addr/src/lib.rs` (see the coverage table in [AENEAS_VERIFICATION.md](AENEAS_VERIFICATION.md)), and the optimized multi-lane sponges of `qsag-core` and `qsag-agg` are separate implementations. `bdoz_verify_arbitrary_batch` proves slice acceptance under its tag-execution premise; commitment-before-challenge and freshness need state-level binding. Multi-turn guard invariants do not by themselves establish complete mediation of every raw-secret caller.

`Machine/SydTv.lean` provides five looping-kernel functional certificates, including `tower128_bdoz_mac_vpclmul_sydtv_refines_all_n`. `Machine/ClmulSimd.lean` covers the decoded PCLMUL/VPCLMUL/PMULL `gf2_128_mul_acc_*` and transpose kernels. The certified fixtures cover 19 x86-64 and 9 AArch64 symbols with 3,355 decoded instructions. Archive, ELF-member and deterministic-wrapper hashes are separate identifiers in `Machine/ElfFixtures.lean`. RFLAGS validity masks and edge-vector theorems supersede the historical fixed eight-mismatch description; a fresh silicon-run result must identify its artifact.

`Machine/SpirvSimt.lean` supplies modeled codec roundtrip/injectivity, race-conditioned multi-wave schedule confluence, bank-layout arithmetic and SIMT noninterference, with missing-barrier/wiping/leakage counterexamples. Runtime Vulkan shaders target SPIR-V 1.5; an enum named `SpirV15` does not establish exact shader-to-model equivalence. Driver-reported Wave32 and zero scratch, byte-output comparisons, keyed receipts and universal functional refinement are distinct evidence.

## From component statements to actual construction security

- The regional verifier checks the actual child proofs against a prepared policy registry. Binary IVC verifies a separate fixed-size root against an `IvcSubtreeStatement`.
- `succinctWhirAggregate_refines_idealAggregate_128` bounds the modeled aggregate's failure event under its framing, packed-slot game and coin hypotheses. Rust calls the extracted kernels listed above. Correspondence for the surrounding transcript and caller remains an implementation-level obligation.

- The blinded MAC check and the adaptive bucket size now have Lean statements in `Protocol/Threshold/MacBlind.lean` (`macBlind_uniform_of_nonzero_defect`, `macBlind_abort_independent_of_alpha`, the `combineArity` hypergeometric bound), re-exported at the deployed point by `Top/Foundations.lean` (`threshold_three_projection_mac_blind_bound`). These are statements about the Lean model of the check with an ideal-OLE randomizer; they are not a refinement of the Rust preprocessing code. The threshold FTS consistency check is implemented, reviewed and tested against injected faults, and has no Lean statement.
- Poseidon symbolic evaluation and degree upper bounds, active-box counts, and rational trail-factor arithmetic are different statements from actual reduced degree, Gröbner complexity or a differential probability bound for the fixed permutation. Likewise, primitive-break predicates must describe outputs of a reduction from the actual adversary, rather than unrestricted existential collisions.

The acceptance target is a theorem about the implemented key generation, messages, signature/proof verifier, corruption view and abort/retry law. An ideal functionality with an abstract signer is an interface for that proof, not a substitute for it.
