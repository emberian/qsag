# Security invariants, specification tests and constant-time proofs

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
The current documentation update does not claim a fresh all-module proof run.

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
The default `Habr24Qrom128` has $q=(128,64,43,32)$; the unconditional Johnson
coding-bound regime `BciksJohnsonQrom128` has $q=(258,130,88,66)$.
The first regime uses conjectural agreement. The aggregate verifier enforces a
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
Ed25519 ownership proofs. Its live ZKBoo default is 438 repetitions, giving interactive error `(2/3)^438 < 2^-256` and nominal generic Grover search exponent 128.1068. The large-prime pre-open multiplication checks use `<30/p<2^-249`; the cubic-Goldilocks checks use `<30/p^3<2^-186`. These are separate field-check errors, not a classical/quantum pair. Full FS/QROM extraction remains a separate reduction.
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
| RLWE OR-Sigma | `C={±X^k:0≤k<1024}`, 2,048 choices; 13 × 11 = 143 joint bits. Nominal exhaustive-search exponents: 143 classical / 71.5 generic Grover. | `preprocessing.rs`: `RLWE_ZKPOK_REPS`, `RLWE_ZKPOK_CHAL_BITS`, `poly_from_chal11` |
| RLWE response sampler | Truncated Gaussian σ=700, masks in `[-3072,3071]`, accepted responses in `[-3070,3069]`; acceptance `min(1, exp((‖y‖²−‖z‖²)/980000)/M)`, `M=exp(3114493/980000)≈24`. This is the live sampler, not the proposed bimodal cosh sampler at M≈1.08. | `crates/qsag-core/src/preprocessing.rs` |
| RLWE extraction | For degree `2^ν` and odd `q≥3`, distinct signed monomials satisfy `(c−c′)g=2` and their difference is a unit. Isometric extraction yields `A s_iso+e_iso=(1−c⁻¹c′)u`; at q=12289 the infinity norms are ≤6140. Secret recovery or a nonzero short-SIS relation has bound ≤6142. This is a relaxed relation, not unconditional recovery of the original CBD witness. | `RlweCyclotomicExtraction.lean`: `signedMonomial_challenge_set_pairwise_invertible`, `extract_rlwe_or_sigma_13_short_witness_1024_sound`, `short_monomial_witness_recovers_secret_or_breaks_short_sis` |
| WHIR query ladder | Habr24 QROM `(128,64,43,32)`; Johnson QROM `ceil(512/log₂ B)+2=(258,130,88,66)` at B=(4,16,64,256). Stage work is 16 bits under `QSAG.PCS.POW2/v1`; `maxQueryCap=512`. The 272/136 round bits are nominal query-plus-work search accounting. | `pcs.rs`, `sponge.rs`; `Aggregation.lean` |
| Multi-round budget | `multiRoundFsQromCompilerBound` is <2^-128 for Q+1≤2^40, five 256-bit Merkle roots and the deployed 24-variable geometry. Aggregated RBR numerators are `[4182,1644,824,489,792]/p⁴`, sum 7931/p⁴. The same expression fails at 2^41. Hem transcript flip bounds and quantum commitment extraction are premises still to instantiate. | `MultiRoundFsQrom.lean`: `multiRoundFsQrom_budget_bound`, `tooth_multiRoundFsQrom_budget_fails_at_2pow41` |
| WOTS+C | 128 base-four digits sum to 192. The accepted language has `[x^192](1+x+x²+x³)^128` = 3647133497298879801227908259470154861817607767728241841601287895307331452700 elements (≈251.01137 bits); uniform first-success grinding averages ≈31.7488 trials. Encoding width alone does not give 256 bits of accepted-language entropy. | `tsw_baggy.rs`; `HashSigs.lean` |
| Migration | `MIT_REPETITIONS=438`; `(2/3)^438≈2^-256.2136`. Active multiplication errors are <2^-249 over the large primes and <2^-186 over cubic Goldilocks. No one of these numbers is a complete FS/QROM acceptance theorem. | `zk_engine.rs`; `outer_mpc.rs` |

Constructive Guruswami–Sudan interpolation produces nonzero Hasse-vanishing witnesses; arbitrary-multiplicity factor and formal-polynomial list bounds are proved in `AffineProximityGaps.lean`. The interpolation-to-Taylor multiplicity bridge and the full trivariate affine explainer remain necessary for the mechanized Johnson-radius argument. `MultiRoundFsQrom.lean` also proves adaptive unitary oracle-dependent measure-and-reprogram and multi-round union results; the numerical compiler budget has the explicit protocol premises above.

`CeremonyAtomicityAndAbort.lean` establishes batch disjointness, unique ceremony/message per leaf, spend caps and persistent poison or fail-closed behavior for valid multi-ledger crash/interleaving traces. Its pre-open masked-view selective-abort theorem gives statistical-distance numerator zero with positive survival count. Arbitrary post-output withholding is outside that conditioning theorem. `HypertreeEufCma.lean` reduces accepted fresh-message forgeries in the specified stateless signing-log model (at most 2^32 layers) to ITSR, TCR or preimage breaks; this is stronger than its legacy Type-valued extractor interface.

### Runtime consumers and extracted proofs

| Production consumer | Executed extracted interface | Proof surface |
| --- | --- | --- |
| `qsag-core`, `qsag-quorum` | `VerifiedWotsC256Guard`, `ct_eq_bytes32`, `validate_belt_quorum_config` | `PantsAndQuorumGuards.lean`, `MultiTurnMediationAndReachability.lean` |
| `qsag-policy` | `checked_velocity_spend`, `StatefulVelocityGuard::authorize_spend` | `PolicyAndAddr.lean`, multi-turn reachability |
| `qsag-agg` | `cwyz_duet_fold`, `verify_ood_pin_eq`, `verify_stage_pow_mask`, `verify_ext4_univariate_at_base_pin` | `aeneas/lean-whir/QsagWhirVerified/Proofs.lean` |

`RealSpecFieldWeld.lean` proves Goldilocks inverse refinement and the nonzero multiplicative-inverse law. `RealSpecKeccakWeld.lean` proves the 24-round permutation refinement. Sponge totality/phase results cover arbitrary slices; full SHAKE emitted-byte refinement still needs the rate-block XOR, padding and squeeze bridge. `bdoz_verify_arbitrary_batch` proves slice acceptance under its tag-execution premise; commitment-before-challenge and freshness need state-level binding. Multi-turn guard invariants do not by themselves establish complete mediation of every raw-secret caller.

`SydTvTranslationValidation.lean` provides five looping-kernel functional certificates, including `tower128_bdoz_mac_vpclmul_sydtv_refines_all_n`. `SimdBinaryEquiv.lean` covers decoded PCLMUL/VPCLMUL and transpose noninterference. Pinned ELF fixtures contain 16 x86-64 symbols / 999 instructions and 7 AArch64 symbols / 299 instructions. Archive, ELF-member and deterministic-wrapper hashes are separate identifiers in `CompiledRlibFixtures.lean`. RFLAGS validity masks and edge-vector theorems supersede the historical fixed eight-mismatch description; a fresh silicon-run result must identify its artifact.

`SpirvSimtGpuEquiv.lean` supplies modeled codec roundtrip/injectivity, race-conditioned multi-wave schedule confluence, bank-layout arithmetic and SIMT noninterference, with missing-barrier/wiping/leakage counterexamples. Runtime Vulkan shaders target SPIR-V 1.5; an enum named `SpirV16` does not establish exact shader-to-model equivalence. Driver-reported Wave32 and zero scratch, byte-output comparisons, keyed receipts and universal functional refinement are distinct evidence. See [the measurement ledger](../PROJECT.md#c-06-publication-evidence-and-follow-up).
