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
| `MirSpecBridge.lean`, `MaliciousSecurity.lean` | Stateful signing, certified BeltLatch, quorum intersection, active checks | Global latch condition is `2q > n+f`; BFT availability needs `n >= 3f+1`. QS-A deliberately uses disjoint committee custody. |
| `UcGames.lean`, `IdealTsig.lean`, `SimulationSpine.lean`, `InteractiveUcEngine.lean` | Oracle games, ideal functionality and simulation | Generic simulation premises must be instantiated with the concrete scheduler, messages and shared resources. Sequential sessions do not establish arbitrary concurrent composition. |
| `PosixCrashWal.lean` | POSIX/NVMe persistence, torn writes, recovery, genesis seals and `OpenDescriptionId` flock ownership | Per-record crash safety needs a ceremony-level reservation/release composition theorem. Host persistence and snapshot assumptions remain explicit. |
| `ConcreteSecurityBudget.lean` | Square-root-free unitary BBBV97/O2H, fiber-cardinality search reductions | A fixed-bad-set search lemma does not automatically establish adaptive multi-round Fiat–Shamir security. |
| `Aggregation.lean`, `SuccinctAggregationIop.lean` | Hem WHIR, committed traces, signer disjointness and Canopy commitments | Bind the exact GoldilocksExt4 verifier, profile and transcript to the reduction; no free independence assumptions. |
| `LatticePreprocessingFull.lean` | Lattice preprocessing and extraction | The real signed-monomial ring challenge requires difference/invertibility and norm analysis; a Boolean extractor or wider challenge is insufficient. |
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
full 256-bit WOTS+C profile has `w=4, chains=128, target_sum=192`. The 256-lane
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
coding-bound regime `BciksJohnsonQrom128` has $q=(257,129,87,65)$.
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

`aeneas/qsag-verified` is the thirteenth project crate, separate from the 12-package
root workspace. Charon + Aeneas generate `QsagVerified.Funs`; `QsagMirProofs`
provides checked arithmetic, sponge, WOTS+C, BDOZ, BeltLatch, Waistband and
poison-latch guard results under the **0 FunsExternal** extraction discipline.
See [AENEAS_VERIFICATION.md](AENEAS_VERIFICATION.md) for precise statements.

Fresh extraction, direct production linkage and universal bridges remain distinct
from finite parity tests. Complete mediation also needs private secret ownership,
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
before any useful partial share release. Single-record atomicity alone does not
establish ceremony atomicity. Policy time windows need an authoritative clock or
agreed logical epoch; authenticated caller timestamps alone are insufficient.
Channels must provide confidentiality, authenticity, replay protection and the
broadcast consistency the protocol assumes. Loopback/RAM and simulated-WAN
benchmarks do not certify this deployment boundary; MAC framing is not encryption.

Migration now implements active pre-open Boolean and prime-field multiplication
checks, including a cross-batch barrier, for three-custodian secp256k1/Taproot/
Ed25519 ownership proofs. Its live 219-repetition ZKBoo default is a classical
soundness profile; stronger QROM accounting and the exact conditional privacy
bridge remain integration work. These active checks are implemented, while the full reduction remains separate.
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
  metamorphic threshold/single-signer cases and clause-drop mutations. `KatGen`
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
