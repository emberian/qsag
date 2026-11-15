# Security invariants, specification tests and constant-time proofs

The later recorded 2026-11-14 freshness check matched 19 x86-64 and 9 AArch64 certified kernels and their Lean certificates. It supersedes the earlier 0/16 and 6/7 failure snapshot. This is named-kernel evidence; exact current-source and linked-program acceptance remain separate.

**qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation** uses four
complementary assurance pillars. The theorem source and its premises are the
contract; neither a declaration count nor a passing test substitutes for a bridge
to the deployed code. [ASSURANCE.md](../ASSURANCE.md) defines the full TCB and
[PROJECT.md](../PROJECT.md) tracks integration work.

## Protocol, UC, storage and QROM spine

| Modules under `lean/Qsag/` | Subject | Scope to preserve |
| --- | --- | --- |
| `Goldilocks.lean`, `BinaryTower.lean` | Prime-field and extension arithmetic, Wiedemann towers | Algebraic laws apply to their exact representations; MIR/binary refinement is separate. Hem uses GoldilocksExt4, not a quadratic challenge field. |
| `Keccak.lean`, `Poseidon2.lean` | Sponge/permutation algebra and framing | Match byte order, domain tags, lengths and padding to runtime codecs; permutation invertibility is not cryptanalytic security. |
| `Fips205.lean`, `ThresholdMpc.lean` | SLH-DSA parameters, domain separation, threshold/reference evaluation | Match key, message, context and randomizer before asserting identical output. |
| `HashSigs.lean`, `HypertreeEufCma.lean`, `BaggyAndRss256Security.lean` | WOTS+C, TSW, hypertrees, Baggy, Waistband and RSS256 | Reductions require reachable layers and valid transcripts; a first-success grinder and cached internal signatures must refine the reference construction. |
| `MirSpecBridge.lean`, `MaliciousSecurity.lean` | Stateful signing, certified BeltLatch, quorum intersection, active checks | Global latch condition is `2q > n+f`; BFT availability needs `q <= n-f` (feasible together when `n >= 3f+1`). QS-A deliberately uses disjoint committee custody. |
| `UcGames.lean`, `IdealTsig.lean`, `SimulationSpine.lean`, `InteractiveUcEngine.lean` | Oracle games, ideal functionality and simulation | Generic simulation premises must be instantiated with the concrete scheduler, messages and shared resources. Sequential sessions do not establish arbitrary concurrent composition. |
| `PosixCrashWal.lean` | POSIX/NVMe persistence, torn writes, recovery, genesis seals and `OpenDescriptionId` flock ownership | `CeremonyAtomicityAndAbort.lean` supplies a valid-trace multi-ledger crash/interleaving theorem; production events must instantiate it. Host persistence and snapshot assumptions remain explicit. |
| `ConcreteSecurityBudget.lean` | Square-root-free unitary BBBV97/O2H, fiber-cardinality search reductions | A fixed-bad-set search lemma does not automatically establish adaptive multi-round Fiat–Shamir security. |
| `Aggregation.lean`, `SuccinctAggregationIop.lean` | Hem WHIR, committed traces, signer disjointness and Canopy commitments | Bind the exact GoldilocksExt4 verifier, profile and transcript to the reduction; no free independence assumptions. |
| `LatticePreprocessingFull.lean` | Lattice preprocessing and extraction | `RlweCyclotomicExtraction.lean` proves signed-monomial difference invertibility and short relaxed extraction; see the exact parameter map below. |
| `CustodySuiteFull.lean`, `ThresholdMlDsaAndToprf.lean` | Custody, credentials and migration | Local checks and source-landed bridges are not automatically integrated production theorems. |

The constructive discipline is **0 sorry / 0 Classical.choice**, with permitted
axioms `{propext, Quot.sound}`. Axiom audits must cover loaded/generated modules
and private declarations; CI challenge exports need an explicit production roster.
Which modules a check covered, and whether those bytes are still the current ones, is
recorded in [CURRENT_SCOPED_CHECKS.json](CURRENT_SCOPED_CHECKS.json) and reported by
`scripts/check_evidence_freshness.py`; see
[current integration checks](CONVERGENCE_STATUS.md#current-integration-checks).

### Boundary, bridge and test modules

These modules state what a neighbouring result does and does not cover, usually with a
proved counterexample or an executed instance. They are registered in the library root and
the axiom audit.

| Module | Statement | Scope |
| --- | --- | --- |
| `HemVerifierAcceptance.lean` | Facts read off `verifyHemAffineWhir` itself: the oracle/claim arity check is necessary (`tooth_missing_batch_claim_erases_oracle`); for a zero-oracle false statement, acceptance forces a linear challenge collision (`verifyHemZeroOracle_implies_linear_collision`, `verifyHemZeroOracle_accepted_pairs_le`); the packaged core agreement is stronger than the checker (`tooth_core_agreement_is_stronger_than_checker`). | One false-statement family, not arbitrary Hem statements; no refinement of the Rust transcript parser. |
| `HemPointReductionSoundness.lean` | The point-reduction wire decoder reconstructs `c1 = claim - 2*c0 - c2`, so the sum equation holds by construction (`hemPointReductionWire_sum`); a wrong hypercube sum agrees on at most two challenges and the bound is attained. | Local algebra; no adaptive composition. |
| `HemFoldDecompositionBridge.lean` | The `UPoly` and coefficient-list forms of the claim-preserving fold relation are equivalent (`hasPolynomialExplanation_iff_decomposes`), with the same selected post-fold polynomial and no uniqueness-radius premise. | Representation bridge between the coding and transcript developments. |
| `CodingTheory/PlaneBezoutResultant.lean`, `NonpersistentIncidenceBound.lean`, `PersistentPairsBound.lean`, `PersistentPairsBoundTests.lean` | Primitive plane-curve common-root bound; dimension-one nonpersistent cover; candidate-specific persistent-pair count under `|D|·(d+1) < B²`; inhabited instances and `tooth_persistent_needs_far`. | The two-dimensional step of CWYZ Claim 4.8 remains open (multi-sheet branch); see the tracker. |
| `QromExtractionBoundary.lean` | Measured-query branch masses, observed-response consistency, bridge to `merkleQueryConsistent`; target cardinality does not give locality; recording a query changes Born probability. | Measured-query interface. Coherent extraction is separate. |
| `QromMeasuredQueryExperiment.lean`, `QromMeasuredMerkleExtraction.lean`, `QromClassicalQueryTransfer.lean`, `QromMeasuredMerkleExtractionTests.lean` | A measured-query experiment with lazy sampling; Merkle extraction-failure mass at most `(d·(3Q+1) + (0+…+(Q-1))) / 2^w` with the consistency premise derived from the log; the same bound on the coherent run for adversaries whose queries sit on one address. | Not coherent-query QROM security: the parity circuit gives 8/8 coherently and 4/8 when measured. |
| `RlweExtractionBoundary.lean` | The short-SIS branch of the fork-extraction dichotomy has the public solution `s=1, e=centered(-A)` (norm ≤6144 always, ≤6142 outside four residues per coefficient). | A statement about the reduction target, not a forged transcript. |
| `HashTrailSampling.lean` | `≤ 6^k` of `N^k` assignments succeed in the fresh-independent-input S-box experiment; a realised trail of the fixed SPN cannot have probability `(6/2^128)^48`. | Separates component arithmetic from a fixed-permutation trail bound. |
| `CompleteMediationBoundary.lean`, `SeparatedCustodyCore.lean`, `SeparatedCustodySpine.lean`, `SeparatedCustodyChecks.lean`, `SeparatedCustodyPolicy.lean`, `SeparatedCustodyHistory.lean`, `SeparatedCustodyHistoryChecks.lean` | One-custodian vault transitions with durable change before release (`release_durable`, `release_replay_rejected`, `forget_burns`, `trace_burned_spend_le_cap`); independently keyed approvals composed into a quorum certificate with structural extraction to the production hash-signature break events; executed cSHAKE256/Jorts construction checks. | Specification level: no fsync, key-isolation, anchor or ELF/MIR refinement; separate keys, not threshold reconstruction of one key. |
| `SpongeFramingAndDomainSep.lean`, `CompositionInstances.lean` and the three composition modules | pad10*1 and cSHAKE prefix injectivity and cross-domain separation; generic composition reductions, with fixtures in which bad and forgery events are false and wrong-context constituents are rejected. | The fixtures use public checksums and a non-succinct reference aggregator; none instantiates a cryptographic assumption. |
| `IdealOutputBoundary.lean` | Fresh successful ideal release equals the functionality's signature; injective request and key encodings; exact-retry versus changed-intent. | The engine's callbacks are cluster-level; party-local custody and a partial production oracle are separate. |
| `CodingTheory/SlicedJetIncidence.lean`, `Cwyz26JohnsonCertificate.lean`, `GoldilocksCharacteristic.lean` | The non-excluded count one challenge slope at a time; `NonExcludedDecompBound` with an explicit `rest`; `1..k` invertible in `Goldilocks` and `QuarticGoldilocks` for `k < p`. | The nonpersistent term is linear in `|S|`, weaker than the paper's constant. |
| `DensePcgTapLinearTests.lean`, `DensePcgProductionTaps.lean` | Exact bias of a linear test as a product over trees; the production tap generator on the Keccak specification; row 0 of one generated matrix has bias between `2^-118` and `2^-117`. | Taps modelled as uniform for the second-moment law; no bound over all row subsets. |

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
256-bit digest WOTS+C profile has `w=4, chains=128, target_sum=192`. The 256-lane
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

## Hem profile and QROM accounting

Hem uses EUROCRYPT 2025 rate-escalating WHIR over
$\mathbb{F}_p[v]/(v^4-7)$, $p=2^{64}-2^{32}+1$, with $p^4>2^{255.99}$.
Steiner-deduplicated `CanopyMultiProof` commitments reduce repeated Merkle paths.
The default Johnson query-accounting regime `BciksJohnsonQrom128` has
$q=(258,130,88,66)$; the classical regime has $q=(129,65,44,33)$.
Capacity-proximity regimes, including Habr24, have been retired; wire tags 0, 1 and 3 reject. The default is `BciksJohnsonQrom128`; `BciksJohnsonClassical128` is available below the aggregate authorization boundary. The aggregate verifier enforces a
mandatory **128-bit QROM Grover query-search floor** and compatible profiles on
merge; this is not a total QROM theorem.

A complete bound must consume the deployed profile and account for list sizes,
Johnson slack, field/folding/OOD errors, hash binding, all sessions and applicable
multi-round FS reduction losses. Squaring an error term requires actual independent
checks and their binding proof. PoW work is not an automatic information-theoretic
soundness multiplier. Binary merge trees establish checked constituent proofs and
disjoint signer sets, not recursive SNARK verification.

## Compiler-extracted MIR and release ownership

The 12-package root workspace consumes two separately rooted extraction crates: `aeneas/qsag-verified` (core/policy/quorum) and `aeneas/qsag-whir-verified` (aggregation), for 14 project packages. Charon + Aeneas generate `QsagVerified.Funs`; `QsagMirProofs`
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

Leaf use, policy spend, preprocessing, nonce burns and poison state must compose
before any useful partial share release. `CeremonyAtomicityAndAbort.lean` proves ceremony-level safety for valid crash/interleaving traces; the runtime reservation and release paths must refine that event model. Policy time windows need an authoritative clock or
agreed logical epoch; authenticated caller timestamps alone are insufficient.
Channels must provide confidentiality, authenticity, replay protection and the
broadcast consistency the protocol assumes. Loopback/RAM and simulated-WAN
benchmarks do not certify this deployment boundary; MAC framing is not encryption.

Migration now implements active pre-open Boolean and prime-field multiplication
checks, including a cross-batch barrier, for three-custodian secp256k1/Taproot/
Ed25519 ownership proofs. Its live ZKBoo default is 438 repetitions, giving interactive error `(2/3)^438 < 2^-256` and nominal generic Grover search exponent 128.1068. Per flush, the large-prime pre-open multiplication checks use `<=35/(p-1)<2^-249`; the cubic-Goldilocks checks use `<=35/(p^3-1)<2^-186`. These are separate field-check errors, not a classical/quantum pair. Full FS/QROM extraction remains a separate reduction.
Threshold ML-DSA has a $2t-1$ active quorum and rejection-transcript assumptions;
six-limb BlindVC's 438-repetition Quantum128 profile likewise needs its FS reduction.

## Grounded ISA, compiled ELF64 and zeroization

`ConstantTimeIsa.lean` and `ElfBinaryVerify.lean` cover scoped x86_64
AVX2/PCLMULQDQ/VPCLMULQDQ and aarch64 SHA3/PMULL programs: taint noninterference,
scratch-register zero-on-exit and mutation `#tooth` witnesses. LNSym / x86lean /
ELFSage grounding, linked ThinLTO and full dispatch/caller closure are active
integration work. DOIT / **PSTATE.DIT** must be tied to actual runtime state.

PC/memory/latency observations are model-specific, not arbitrary hardware leakage.
Callee scratch wiping does not erase caller frames, restored registers, compiler
copies or OS context saves. `vzeroupper` does not wipe every vector register; calls
are not implicit wipes. `black_box` and fences do not prove whole-process erasure.
Higher-level rustc/LLVM, wrappers and fallbacks remain trusted for leakage claims.
See [CONSTANT_TIME_ASM.md](CONSTANT_TIME_ASM.md) and
[BINARY_RLIB_VERIFICATION.md](BINARY_RLIB_VERIFICATION.md).

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

Each security theorem needs a load-bearing-check mutation or concrete attack
witness where feasible. `#tooth` witnesses demonstrate specific failures; their
existence alone does not guarantee that every theorem is nonvacuous. The desired
acceptance chain connects production entrypoint, source/configuration, generated
function, theorem/assumptions, profile, binary digest and tests. Independent green
lanes without those links do not close the assurance architecture.


## Current parameter and theorem map

Source inspection dated 2026-11-14. This map names statements and runtime consumers; it does not report a fresh Lean build of the concurrently edited tree.

| Parameter / relation | Exact current statement | Source |
| --- | --- | --- |
| RLWE OR-Sigma | `C={±X^k:0≤k<1024}`, 2,048 choices; 24 × 11 = 264 joint bits. Nominal exhaustive-search exponents: 264 classical / 132 generic Grover; these are challenge-space arithmetic, not a quantum-active OT theorem. | `preprocessing.rs`: `RLWE_ZKPOK_REPS`, `RLWE_ZKPOK_CHAL_BITS`, `poly_from_chal11` |
| RLWE response sampler | Truncated Gaussian σ=700, masks in `[-3072,3071]`, accepted responses in `[-3070,3069]`; acceptance `min(1, exp((‖y‖²−‖z‖²)/980000)/M)`, `M=exp(3615102/980000)≈40`. Q192 finite-precision sampling and normalized vector Gaussian/tail hypotheses still need production proof instantiation. | `crates/qsag-core/src/preprocessing.rs` |
| RLWE extraction | For degree `2^ν` and odd `q≥3`, distinct signed monomials satisfy `(c−c′)g=2` and their difference is a unit. Isometric extraction yields `A s_iso+e_iso=(1−c⁻¹c′)u`; at q=12289 the infinity norms are ≤6140. Secret recovery or a nonzero short-SIS relation has bound ≤6142. This is a relaxed relation, not unconditional recovery of the original CBD witness. | `RlweCyclotomicExtraction.lean`: `signedMonomial_challenge_set_pairwise_invertible`, `extract_rlwe_or_sigma_13_short_witness_1024_sound`, `short_monomial_witness_recovers_secret_or_breaks_short_sis` |
| WHIR query ladder | Johnson classical `(129,65,44,33)`; default Johnson QROM `ceil(512/log₂ B)+2=(258,130,88,66)` at B=(4,16,64,256). Stage work is 16 bits under `QSAG.PCS.POW2/v1`; `maxQueryCap=512`. The 272/136 round bits are nominal query-plus-work search accounting. Runtime CWYZ witness tables cover the QROM regime; classical witness rows for nv=20/24 are Lean-only. | `pcs.rs`, `sponge.rs`; `Aggregation.lean` |
| Multi-round budget | `multiRoundFsQromCompilerBound` is <2^-128 for Q+1≤2^40, five 256-bit Merkle roots and the deployed 24-variable geometry. Aggregated RBR numerators are `[4182,1644,824,489,792]/p⁴`, sum 7931/p⁴. The same expression fails at 2^41. Hem transcript flip bounds and quantum commitment extraction are premises still to instantiate. | `MultiRoundFsQrom.lean`: `multiRoundFsQrom_budget_bound`, `tooth_multiRoundFsQrom_budget_fails_at_2pow41` |
| WOTS+C | 128 base-four digits sum to 192. The accepted language has `[x^192](1+x+x²+x³)^128` = 3647133497298879801227908259470154861817607767728241841601287895307331452700 elements (≈251.01137 bits); uniform first-success grinding averages ≈31.7488 trials. Encoding width alone does not give 256 bits of accepted-language entropy. | `tsw_baggy.rs`; `HashSigs.lean` |
| Migration | `MIT_REPETITIONS=438`; `(2/3)^438≈2^-256.2136`. Active multiplication errors are <2^-249 over the large primes and <2^-186 over cubic Goldilocks. No one of these numbers is a complete FS/QROM acceptance theorem. | `zk_engine.rs`; `outer_mpc.rs` |

`hem_johnson_qrom_witnesses_cover_every_canonical_stage` checks canonical nv=2…24 stage coverage and equality of the used-row/table counts. It establishes the stated numerical side conditions for the deployed QROM table; the underlying decomposition theorem remains the separate obligation below.

Constructive Guruswami–Sudan interpolation produces nonzero Hasse-vanishing witnesses; arbitrary-multiplicity factor and formal-polynomial list bounds are proved in `AffineProximityGaps.lean`. The remaining CWYZ `NonExcludedDecompBound` must be derived, then connected to the deployed arbitrary-batch, multistage checker. The packaged RBR construction currently has one batch, zero folds and two rounds; it is not the deployed protocol merely because its arithmetic budget is favorable. `MultiRoundFsQrom.lean` also proves adaptive unitary oracle-dependent measure-and-reprogram and multi-round union results; the numerical compiler budget has the explicit protocol premises above.

`CeremonyAtomicityAndAbort.lean` establishes batch disjointness, unique ceremony/message per leaf, spend caps and persistent poison or fail-closed behavior for valid multi-ledger crash/interleaving traces. Its pre-open masked-view selective-abort theorem gives statistical-distance numerator zero with positive survival count. Arbitrary post-output withholding is outside that conditioning theorem. `HypertreeEufCma.lean` reduces accepted fresh-message forgeries in the specified stateless signing-log model (at most 2^32 layers) to ITSR, TCR or preimage breaks; this is stronger than its legacy Type-valued extractor interface.

### Runtime consumers and extracted proofs

| Production consumer | Executed extracted interface | Proof surface |
| --- | --- | --- |
| `qsag-core`, `qsag-quorum` | `VerifiedWotsC256Guard`, `ct_eq_bytes32`, `validate_belt_quorum_config` | `PantsAndQuorumGuards.lean`, `MultiTurnMediationAndReachability.lean` |
| `qsag-policy` | `checked_velocity_spend`, `StatefulVelocityGuard::authorize_spend` | `PolicyAndAddr.lean`, multi-turn reachability |
| `qsag-agg` | `cwyz_duet_fold`, `verify_ood_pin_eq`, `verify_stage_pow_mask`, `verify_ext4_univariate_at_base_pin` | `aeneas/lean-whir/QsagWhirVerified/Proofs.lean` |

`RealSpecFieldWeld.lean` proves Goldilocks inverse refinement and the nonzero multiplicative-inverse law. `RealSpecKeccakWeld.lean` proves the 24-round permutation refinement. Sponge totality/phase results cover arbitrary slices; full SHAKE emitted-byte refinement still needs the rate-block XOR, padding and squeeze bridge. `bdoz_verify_arbitrary_batch` proves slice acceptance under its tag-execution premise; commitment-before-challenge and freshness need state-level binding. Multi-turn guard invariants do not by themselves establish complete mediation of every raw-secret caller.

`SydTvTranslationValidation.lean` provides five looping-kernel functional certificates, including `tower128_bdoz_mac_vpclmul_sydtv_refines_all_n`. `SimdBinaryEquiv.lean` covers decoded PCLMUL/VPCLMUL and transpose noninterference. The later certified fixture inventory contains 19 x86-64 and 9 AArch64 symbols / 3,355 decoded instructions; the earlier 16/7 inventory is historical. Archive, ELF-member and deterministic-wrapper hashes are separate identifiers in `CompiledRlibFixtures.lean`. RFLAGS validity masks and edge-vector theorems supersede the historical fixed eight-mismatch description; a fresh silicon-run result must identify its artifact.

`SpirvSimtGpuEquiv.lean` supplies modeled codec roundtrip/injectivity, race-conditioned multi-wave schedule confluence, bank-layout arithmetic and SIMT noninterference, with missing-barrier/wiping/leakage counterexamples. Runtime Vulkan shaders target SPIR-V 1.5; an enum named `SpirV15` does not establish exact shader-to-model equivalence. Driver-reported Wave32 and zero scratch, byte-output comparisons, keyed receipts and universal functional refinement are distinct evidence. See [the measurement ledger](../PROJECT.md#c-06-publication-evidence-and-follow-up).

## From component statements to actual construction security

The [construction obligation ledger](../PROJECT.md#construction-proof-obligations) names the outstanding reductions and implementation refinements. Three distinctions are especially important:

- The compact hierarchy's outer AIR proves a public commitment chain. `VerifiedHierarchicalHemEvidence` is obtained by verifying the actual children and is required for authorization. `SuccinctRecursiveHemEnv.outerRelationSound` still assumes the missing recursive relation; it cannot certify first-time verification from a compact proof alone.
- `QromMerkleOnlineExtraction.lean` has a constructive classical-table classifier and a conditional local-target union bound. The latter leaves `hLocal`, `hCard` and `hCover` to the caller and does not itself provide an extractor for coherent quantum queries. `QromExtractionBoundary.lean` supplies exact measured-query branch masses, observed-response consistency and a bridge to `merkleQueryConsistent`; its locality and coherent-recording counterexamples identify the scope of that interface. Its five new theorems passed a scoped Lean 4.35 check and constructive audit. A numerical compiler bound becomes protocol security after the remaining coherent-extraction premises and actual RBR/query event bounds are instantiated.
- Poseidon symbolic evaluation and degree upper bounds, active-box counts, and rational trail-factor arithmetic are different statements from actual reduced degree, Gröbner complexity or a differential probability bound for the fixed permutation. Likewise, primitive-break predicates must describe outputs of a reduction from the actual adversary, rather than unrestricted existential collisions.

The acceptance target is a theorem about the implemented key generation, messages, signature/proof verifier, corruption view and abort/retry law. An ideal functionality with an abstract signer is an interface for that proof, not a substitute for it.
