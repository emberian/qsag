#set page(paper: "us-letter", margin: (x: 0.7in, y: 0.73in), columns: 2, numbering: "1")
#set text(font: "New Computer Modern", size: 9.5pt)
#set par(justify: true, leading: 0.45em)
#set heading(numbering: "1.1")
#set math.equation(numbering: none)
#show heading: set text(hyphenate: false)
#show heading: set par(justify: false)
#show math.equation: set text(size: 8.6pt)
#set figure(gap: 6pt)
#show heading: set block(above: 1.02em, below: 0.48em)
#show raw: it => {
  let s = it.text.replace("_", "_\u{200b}")
  let s2 = if it.text.len() > 20 {
    s.replace(regex("([a-z0-9])([A-Z])"), m => m.captures.at(0) + "\u{200b}" + m.captures.at(1))
  } else {
    s
  }
  let s3 = s2.replace(regex("([a-f0-9]{16})"), m => m.captures.at(0) + "\u{200b}")
  text(font: "DejaVu Sans Mono", size: 7.3pt, hyphenate: false, s3)
}

#let tbl(cols, ..cells) = {
  set par(justify: false)
  text(size: 7.8pt, table(
    columns: cols,
    inset: (x: 3.4pt, y: 3.6pt),
    stroke: none,
    table.hline(stroke: 0.6pt),
    ..cells.pos(),
    table.hline(stroke: 0.6pt),
  ))
}
#let panel(body) = rect(width: 100%, inset: 7pt, stroke: 0.5pt, radius: 2pt, body)

#place(top + center, float: true, scope: "parent", clearance: 14pt)[
  #align(center)[
    #set par(justify: false)
    #set text(hyphenate: false)
    #text(size: 16.5pt, weight: "bold")[QSAG: Quorum-Switching Threshold Hash Signatures, Succinct Post-Quantum Aggregation, and a Four-Pillar Machine-Checked Custody Stack]
    #v(8pt)
    #text(size: 11pt)[The QSAG Authors]
  ]
  #v(10pt)
  #block(inset: (x: 16pt))[
    #set par(justify: true, leading: 0.46em)
    *Abstract.* Threshold custody of post-quantum signing keys must reconcile five competing demands: hash-based signature trees have deep circuits when evaluated naively inside multiparty computation (MPC); replicated secret sharing blows up combinatorially with committee size; stateful one-time leaves break catastrophically if switching signer quorums ever sign two messages on the same leaf; post-quantum signature batches consume tens of kilobytes per signer without bilinear pairings; and subtle flaws in share-release ordering, crash recovery, or instruction selection can silently invalidate paper proofs. We present *QSAG* (_Quorum-Switching AGgregation_ / _Quantum Succinct AGgregation_), an open-source (`Apache-2.0 OR MIT`) architecture and 14-package zero-dependency Rust 1.99.1 (`no_std` / `wasm32`-portable across all eight custody/crypto crates) and Lean 4.35 stack addressing these bottlenecks. First, a four-oracle *Cut-the-Hash* boundary confines secret MPC evaluation to message randomization, Winternitz chain steps, and FORS leaf derivations, running all public-key compressions, Merkle paths, and target-sum counter grinding in the clear so that sequential secret hash depth is independent of tree height. On this cut we build the *Pants* signing suite: stateless *Baggy* with the *Waistband* upper-layer cache, stateful *Jorts* gated by a crash-safe write-ahead latch (*BeltLatch*), generalized $(t,n)$ quorum-switching modes (*QS-A* and *QS-B*) bridged natively in `[Goldilocks; 4]` to succinct aggregation with $(t,n) -> (t',n')$ resharing, and the Poseidon2 hypertree *Corduroy*, alongside matched-input threshold FIPS 205 SLH-DSA and standard-verifier-compatible threshold FIPS 204 ML-DSA-44/65/87. Second, *Hem* aggregates batches of algebraic hash signatures via a degree-8 Sumcheck [LFKN92] and rate-escalating WHIR [ACFY25] over `GoldilocksExt4` ($p^4 approx 2^256$), incorporating affine Reed–Solomon combiners [CWYZ26] in monomial-shift form under two unconditional Johnson-radius regimes after retiring disproved capacity proximity-gap conjectures [CS25, KKH26]. Third, surrounding custody protocols provide dealerless hierarchical derivation, Bech32m hybrid addresses, authenticated policy guards, active three-party zero-knowledge migration from legacy `secp256k1`, `Ed25519`, Zcash `Pallas`, and Ethereum `BLS12-381` keys, threshold Poseidon2 OPRF credentials, and VRAM-resident Vulkan prover kernels. Four assurance pillars pair `0 Classical.choice` constructive Lean protocol, coding-theory, POSIX-WAL, and unitary QROM proofs with Aeneas-extracted Safe-Rust MIR guards, live-pinned x86-64/AArch64 ELF64 binary refinements, and bare-metal silicon cosimulation. QSAG is an active research prototype: our mechanized results establish scoped properties of named models, extracted routines, and compiled kernel slices while explicitly delineating remaining algebraic-geometry, trace-refinement, and whole-binary composition bridges (§8).
  ]
]

= Introduction

Moving institutional key custody to post-quantum primitives changes the geometry of threshold cryptography. For Schnorr and ECDSA, signing is a compact algebraic relation over a group scalar, and decades of multiparty protocols map directly onto that group structure. Hash-based signatures such as FIPS 205 SLH-DSA [FIPS205, BHKN+19] and XMSS [BDH11] offer a compelling post-quantum alternative: their security rests on symmetric tweakable hashes, and a threshold committee can emit standard signatures verified by unmodified external clients. Turning a hash-based signer into a practical, malicious-secure threshold system, however, runs into five distinct obstacles:

1. *Merkle height versus MPC depth.* A stateless hypertree hashes thousands of Winternitz chains into subtree roots and walks $d$ Merkle layers up to the public root. Evaluating that entire hash graph inside actively secure MPC turns public tree compression and counter grinding into millions of authenticated nonlinear gates.
2. *Committee scaling.* Conjunctive normal form (CNF) replicated secret sharing keeps three-party Boolean gates fast, but stores $binom(n, t-1)$ shares in general—6,435 shares at $(t,n)=(8,15)$, with 3,432 active shares per custodian. Moving to Shamir shares over binary towers or prime fields restores committee-size-independent per-seed storage, at the price of authenticated multiplication and offline preprocessing.
3. *Stateful leaves under quorum switching.* Stateful hash trees cut signature size and signing work dramatically by spending each one-time Winternitz leaf once. In a $(t,n)$ threshold deployment, however, an adversary can route concurrent signing requests to different $t$-subsets of custodians. Whenever $2t <= n+f$, two size-$t$ signing quorums need not intersect in an honest party, threatening to open two codewords on the same leaf.
4. *Post-quantum batch bandwidth.* Without pairing-friendly curves, $K$ post-quantum threshold signatures take $O(K)$ kilobytes on the wire. Compressing $K$ verifications into one succinct post-quantum proof requires an algebraic hash profile and a transparent polynomial commitment scheme whose soundness relies solely on unconditional coding bounds and survives generic quantum search over Fiat–Shamir challenges.
5. *The gap between paper models and custody artifacts.* Even a sound threshold protocol fails if a faulted share is opened before its MAC check, if power loss rewinds a leaf counter while leaving a partial signature on the network, or if vector instructions leak shares through data-dependent control flow or memory addresses.

QSAG addresses these challenges around a single organizing principle: *secret shares should cross into cleartext at the earliest point where the underlying signature scheme already makes the derived digest public.* In *Cut-the-Hash* (§2), custodians hold shares of $"SK.seed"$ and $"SK.prf"$ and evaluate just four secret operations—message randomization, Winternitz chain starts and selected chain positions, and FORS leaf derivations—behind a durable reservation and MAC-verification barrier. Once those digests are authenticated and opened, every WOTS public-key compression $T_ell$, FORS Merkle root, internal tree hash, message digest $H_"msg"$, and target-sum counter grind executes publicly. Released chain nodes have secret hash depth at most $w$ regardless of hypertree height; message absorption and parallel wave count remain separate costs.

On top of this cut, QSAG builds the *Pants* signing suite (§2) and two complementary MPC engines (§3): a 256-lane bitsliced 2-of-3 replicated Keccak engine checked by two-pass ternary Frobenius-basis distributed zero-knowledge proofs over $FF_(2^128)$ [FLNW17, BGIN19], and an arbitrary-threshold authenticated engine over Wiedemann binary towers [Wie88] and Goldilocks [GKS23] backed by 24-challenge Ring-LWE base OT, KOS/MASCOT extension [KOS15, KOS16], and depth-15 dense dual-LPN pseudorandom correlation generators [BCGI+19]. Within Pants, *Baggy* provides stateless hypertree signing accelerated by *Waistband*, a verified cache of deterministic upper-layer child-root signatures; *Jorts* provides stateful signing guarded by *BeltLatch*, a fsynced write-ahead log and pairwise-MAC echo latch; *QuorumJorts* generalizes stateful signing to $(t,n)$ committees via *QS-A* ($binom(n,t)$ committee-partitioned subtrees permitting $t$-of-$t$ online signing when $2f > t$) and *QS-B* (one global tree with bytewise or field-element Shamir shares gated by a $2q > n+f$ BFT latch certificate), bridged natively in `[Goldilocks; 4]` to `Hem` without intermediate arithmetic-to-Boolean conversions; and *Corduroy* instantiates the stateless target-sum hypertree over Poseidon2.

To compress signature batches, *Hem* (§4) proves parallel verification of `JortsPoseidon2` or `CorduroyPoseidon2` signatures in a 256-column multilinear trace using a degree-8 Sumcheck [LFKN92] and rate-escalating WHIR [ACFY25] over the quartic extension `GoldilocksExt4` ($p^4 > 2^(255.99)$), paired with Steiner-deduplicated `CanopyMultiProof` Merkle openings and disjoint signer bitmaps. Hem replaces classical scalar Reed–Solomon folding $f + alpha g$—whose $Omega(n slash q)$ proximity floor and $abs(cal(D)_i)^2 L_i^7 slash p^4$ Johnson loss [BCIKS20] bottlenecked QROM query budgets at $2^21$—with degree-1 affine combiners [CWYZ26] in monomial-shift form. Because recent counterexamples disproved correlated agreement up to capacity $1 - rho$ [CS25] and close to capacity over prime-field multiplicative subgroups [KKH26], Hem purges all capacity-conjecture regimes and enforces unconditional Johnson-radius query schedules (`BciksJohnsonQrom128` by default). Over `GoldilocksExt4` and base-field cosets, the quadratic $(n slash q)^2$ term collapses below $2^(-371)$, the per-fold witness bound exceeds $245.1$ bits with at most two overflow monomials per stage, and the multi-round QROM measure-and-reprogram expression stays below $2^(-128)$ for $Q+1 <= 2^40$ (§4).

Surrounding signing and aggregation, QSAG provides custody protocols for dealerless hierarchical derivation, Bech32m hybrid addresses, BDOZ policy and velocity guards, active three-custodian ZKBoo migration across `secp256k1`, `Ed25519`, Zcash Orchard `Pallas`/`RedPallas`, and Ethereum Beacon `BLS12-381` keys, dealerless threshold FIPS 204 ML-DSA-44/65/87 [FIPS204] with sealed-abort transcripts, threshold Poseidon2 OPRFs and QROM-composed blind credentials, and 10 Vulkan SPIR-V 1.5 kernels including VRAM-resident WHIR prover shaders (§5).

*Contributions.*
- *Cut-the-Hash, Pants, and native QS↔AG custody (§2–§3):* A four-oracle public/secret boundary yielding height-independent sequential MPC depth for FIPS 205 SLH-DSA and custom WOTS+C [HKRY23] schemes across stateless (*Baggy* with *Waistband*, *Corduroy*), stateful (*Jorts* with *BeltLatch*), few-time (`Compact1122` single-MTU 256-bit nodes), and $(t,n)$ quorum-switching (*QS-A*, *QS-B*, `hem_quorum`) custody modes, backed by 264-bit/132-bit-Grover Ring-LWE base OT and Poseidon2 subspace-hardening defenses [MRG26, BTA26].
- *Unconditional Johnson-radius aggregation with constructive `[CWYZ26]` algebra (§4):* *Hem*, a $K$-to-$1$ aggregator combining 256-column Poseidon2 traces, degree-8 Sumcheck, rate-escalating `GoldilocksExt4` WHIR, and `[CWYZ26]` monomial-shift affine folding under two unconditional Johnson-radius regimes (`BciksJohnsonClassical128` and default `BciksJohnsonQrom128`), backed by a `0 Classical.choice` Lean formalization of trivariate Guruswami–Sudan interpolation, division-free Hensel lifting over `Frac(UPoly F)`, dynamic Euclidean splitting, Hasse stratification, and persistent Johnson bounds.
- *Multi-chain post-quantum custody lifecycle (§5):* Integrated dealerless HD hierarchies, hybrid Bech32m addresses, MAC-guarded velocity policies, $< 2^(-244)$-checked 438-repetition ZKBoo migration (`secp256k1`, `Ed25519`, `Pallas`, `BLS12-381`), sealed-abort threshold ML-DSA-44/65/87, 2-of-5 Byzantine TOPRF / `BlindVC` credentials, and VRAM-resident Vulkan compute pipelines.
- *Four-pillar constructive verification and Zen 5 silicon validation (§6–§7):* `0 Classical.choice` across `62,699+` public and `.olean.private` Lean 4.35 declarations, `130` `Qsag.Apex` and `128` MIR/WHIR comparator theorems, unconditional short-nonempty `cSHAKE256` MIR refinement, `28/28` live-pinned x86-64/AArch64 assembly kernels (`3,355` decoded instructions, `26/28` whole-kernel I/O refined, `0` strict CT violations across `92` x86-64 and `65` AArch64 crypto symbols), and bare-metal `ptrace` cosimulation (`59/59`, `7,184` vectors) plus 512-bit `AVX-512`/`GFNI`/`VPCLMULQDQ`/`SHA-NI` and Seiler [Sei18] NTT benchmarks.

== Related work and assurance scope

*Related work.* Threshold ECDSA protocols distribute arithmetic inversions and MtA checks over elliptic curves, whereas generic MPC translations of hash-based signatures evaluate the entire symmetric hash tree under secret sharing. Cut-the-Hash exploits the public internal structure of SPHINCS+ [BHKN+19], XMSS [BDH11], and checksum-free WOTS+C [HKRY23] so that secret MPC stops directly above the leaf chains. Our three-party honest-majority engine builds on replicated sharing [FLNW17] with sublinear distributed zero-knowledge checks over fully linear PCPs [BBCG+19, BGIN19], while our dishonest-majority path draws on SPDZ [DPSZ12], BDOZ [BDOZ11], interactive KOS/MASCOT OT extension [KOS15, KOS16], Seiler's signed-Montgomery lattice NTT [Sei18], and silent dual-LPN PCGs [BCGI+19]. For batch verification, Hem follows the Sumcheck [LFKN92] and WHIR [ACFY25] IOPP paradigm rather than elliptic-curve SNARK recursion, combining `[CWYZ26]` affine combiners with unconditional `[BCIKS20]` Johnson-radius bounds in view of `[CS25, KKH26]` capacity counterexamples and recent Poseidon2 algebraic analyses [MRG26, BTA26]; migration and credentials use MPC-in-the-head [IKOS07, GMO16]. On the verification side, we combine Lean 4 [MU21] protocol and binary models with Aeneas functional Rust translation [HP22] and empirical leakage testing [RBV17].

*Scope and threat-model boundaries.* QSAG is an active research prototype, and we separate what is proved in a formal model, what is checked on extracted or compiled code, and what is measured in single-host benchmarks. Honest-majority protocols tolerate up to $t-1$ corruptions ($n >= 2t-1$) with abort; dishonest-majority protocols tolerate up to $n-1$ corruptions with abort rather than guaranteed output delivery. Throughout every stateful component, custodians durably commit and synchronize state transitions—and verify all gate and opening MACs—before releasing any secret-dependent share, ensuring that crashes or active faults burn capacity rather than reusing a leaf or leaking a key. Across non-interactive proofs, challenge widths and repetition counts are sized against generic Grover search using unitary query bounds [BBBV97, AHU19, DFM20] mechanized in `ConcreteSecurityBudget.lean`, `MultiRoundFsQrom.lean`, and `BlindVcQromSecurity.lean`. Both Aeneas-extracted crates (`qsag-verified` and `qsag-whir-verified`) execute directly on production paths, while bridging Hem's Rust trace-filler routine (`populate_active_signer_rows`) to Lean's proved `StepOp256` extractor and discharging `[CWYZ26]`'s nonpersistent space-curve incidence step (`NonExcludedBound`) remain explicit open obligations (§6, §8).

= Cut-the-Hash and the Pants suite

== The four-oracle public/secret cut

In both FIPS 205 SLH-DSA and custom hash-tree schemes, a signing key consists of a secret PRF key $"SK.prf"$ and a secret leaf-generation seed $"SK.seed"$, paired with a public seed $"PK.seed"$ and Merkle root $"PK.root"$. Given a framed message $mu$ and domain-separating tree/chain address $A$ (writing $A_0$ for its chain-start form), the public/secret interface exposes four operation families:

1. *Message randomization:*
   $ "evalPrfMsg"(r, mu) = "PRF"_"msg" ("SK.prf", r, mu) = R, $
   where $r$ is an optional hedging randomizer. Once $R$ is authenticated and opened, the full message digest $H_"msg" (R, "PK.seed", "PK.root", mu)$ and any target-sum counter grind run in public. Under SHAKE256 [FIPS202], absorbing $mu$ takes $floor((2n + abs(M')) slash 136) + 1$ sequential secret Keccak permutations unless prehashed.
2. *Winternitz chain positions:*
   $ "evalWotsChainEnd"(ell, tau, "kp", j, s) = F^s ("PK.seed", A, X_j), $
   $ X_j = "PRF"("PK.seed", "SK.seed", A_0), $
   evaluated only at authorized positions $s in {d_j, w-1}$, where $d_j$ is the message-selected #box[base-$w$] digit. Each chain has sequential secret hash depth $1 + s <= w$: opening $s = w-1$ yields public-key material, while opening $s = d_j$ yields the signature codeword node.
3. *Selected FORS secret leaves (depth 1):*
   $ "evalForsReveal"(tau_0, "kp"_0, u) = "PRF"("PK.seed", "SK.seed", A_"FORS" (u)), $
   opened solely at the $k$ (or $k-1$) message-selected FORS leaf indices.
4. *Unselected FORS leaf hashes (depth 2):*
   $ "evalForsLeafHash"(tau_0, "kp"_0, u) \
     quad = F("PK.seed", A, "PRF"("PK.seed", "SK.seed", A_"FORS" (u))), $
   returning the public leaf digest rather than the secret preimage so that custodians can assemble FORS authentication paths in cleartext without exposing sibling secrets.

The traits `SlhMpcOracles` and `PqHashMpcOracles` expose this narrow interface (@cutfig). Custodians retain shared seeds and authenticate each cut opening under a durable context.

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 5pt,
    panel([#smallcaps[Secret-shared MPC evaluation]\
      `SlhMpcOracles` / `PqHashMpcOracles`\
      $"SK.prf", "SK.seed"$ → $R$, authorized chain steps $F^s$, FORS leaves / leaf hashes]),
    align(center)[↓\ #smallcaps[Durable bind · MAC / DZK barrier · open]\ ↓],
    panel([#smallcaps[Public cleartext reconstruction]\
      $T_ell$ key compression · FORS & Merkle internal $H$\
      $H_"msg"$ derivation and public target-sum counter grinding]),
  )
}, caption: [Cut-the-Hash keeps secret seeds shared inside a four-oracle boundary and executes all tree compression and counter grinding publicly.]) <cutfig>

== Height-independent depth and target-sum Winternitz

A released Winternitz chain node needs one PRF evaluation plus at most $w-1$ chain steps, hence depth at most $w$: 4 in the Pants profiles and 16 in FIPS 205. Uniform chain-table generation may perform one extra trailing step ($w+1$ work). Public internal-tree compression makes this released-node depth independent of tree height. Long-message PRF absorption, the number of chains, preprocessing, and parallel waves remain separate costs; each sponge permutation has its own rounds (24 Keccak, 30 Poseidon2).

Our custom profiles adopt checksum-free target-sum Winternitz (`WOTS+C` [HKRY23]) at base $w = 4$: a 256-bit message digest is parsed most-significant-first into $ell_1 = 128$ base-4 digits $d_j in {0,1,2,3}$, and a public counter is ground until
$ sum_(j=1)^(ell_1) d_j = S, quad S = floor((ell_1 (w-1)) / 2) = 192. $
Fixing the digit sum eliminates WOTS checksum chains while guaranteeing strict componentwise incomparability between any two distinct valid digit vectors (`wotsC256_strict_incomparability`; `tooth_wotsc_without_target_sum_forges` constructs the single-hash forgery that appears if the sum check is omitted). Unlike variants that pin trailing digits to zero, `WotsCParams::V128` leaves all 128 digits free without implying 256 bits of conditional target-sum entropy. The accepted language has $[x^192](1+x+x^2+x^3)^128 approx 2^251.01137$ elements; uniform first-success grinding averages 31.7488 trials.

@params summarizes the six standard FIPS 205 SHAKE geometries alongside the Pants custody and Hem aggregation profiles (`JortsPoseidon2` at 4,328 B and `CorduroyPoseidon2` at 82,256 B).

#figure(
  {
    set par(justify: false)
    text(size: 7.0pt, table(columns: (1.75fr, auto, auto, auto, auto, auto, auto, auto, auto, auto), inset: (x: 1.5pt, y: 3.6pt), stroke: none,
      table.hline(stroke: 0.6pt),
      [Profile], [$n$], [$h$], [$d$], [$h'$], [$a$], [$k$], [$w$], [$Q_"max"$], [Sig. B], table.hline(),
      [SHAKE-128s], [16], [63], [7], [9], [12], [14], [16], [—], [7,856],
      [SHAKE-128f], [16], [66], [22], [3], [6], [33], [16], [—], [17,088],
      [SHAKE-192s], [24], [63], [7], [9], [14], [17], [16], [—], [16,224],
      [SHAKE-192f], [24], [66], [22], [3], [8], [33], [16], [—], [35,664],
      [SHAKE-256s], [32], [64], [8], [8], [14], [22], [16], [—], [29,792],
      [SHAKE-256f], [32], [68], [17], [4], [9], [35], [16], [—], [49,856], table.hline(),
      [Corduroy], [32], [28], [7], [4], [6], [33], [4], [$2^12$], [—],
      [Baggy], [32], [32], [16], [2], [6], [33], [4], [$2^16$], [—],
      [Jorts], [32], [16], [1], [16], [—], [—], [4], [$2^16$], [—], table.hline(),
      [Hem / Jorts], [32], [6], [1], [6], [—], [—], [4], [$2^6$], [4,328],
      [Hem / Corduroy], [32], [64], [16], [4], [8], [32], [4], [$2^20$], [82,256],
      table.hline(stroke: 0.6pt),
    ))
  },
  caption: [Signature geometries ($n$ = node bytes). Custom custody rows correspond to `CORDUROY_CUSTODY_128`, `BAGGY_TSW_128F`, and `JORTS_POSEIDON2` ($ell_1=128$, $S=192$). Hem rows show `JortsPoseidon2` and `CorduroyPoseidon2` aggregation geometries.],
) <params>

== Baggy and Waistband

*Baggy* (`BaggySha3`, `BaggyPoseidon2`) is QSAG's stateless hypertree signer: $d$ layers of height-$h'$ Merkle subtrees over WOTS+C leaves whose bottom layer signs a FORS+C [HKRY23] key (grinding a public counter until the $k$-th tree index vanishes so only $k-1$ FORS trees open). Its pure-hash variant runs on the 256-lane bitsliced Keccak engine (§3.1).

Signing (`baggy_sign_mpc`) executes in three phases to prevent abort-based grinding attacks. First, custodians derive $R$ deterministically under MPC from $"SK.prf"$ and the message alone; a malicious party who aborts after seeing $R$ forces every retry onto the exact same $R$, hypertree path, and FORS indices. Second, because $R$ fixes all addresses across the hypertree, the FORS leaves and every subtree along the active path are evaluated together in a single level-by-level sweep—one PRF wave and three $F$ waves regardless of layer count $d$—followed by one distributed verification barrier before chain endpoints and FORS leaf hashes open. Third, custodians reconstruct the subtree roots and target-sum child digests in cleartext and open the selected intermediate chain nodes in one final round.

Because upper hypertree layers sign deterministic child roots rather than external messages, their leaves always open the same WOTS+C digits. *Waistband* (`WaistbandCache`) caches the public subtree leaves, authentication paths, and deterministic child-root signatures of the top $L$ layers while never caching message-binding bottom leaves. To defeat corrupted-cache second-codeword attacks (`tooth_corrupted_intermediate_waistband_opens_second_ancestor_codeword`), Baggy enforces cryptographic `BaggyKeyBinding`, extracted root-guard verification (`VerifiedWaistbandRootGuard`) up to $"PK.root"$ before shares open, and a persistent `FirstSignedLedger` (`baggy_multiturn_durable_and_non_equivocating`).

== Jorts and BeltLatch

*Jorts* is the 2-of-3 stateful signer: a single height-$h$ Merkle tree over $2^h$ one-time WOTS+C leaves (epochs), instantiated over either bitsliced Keccak (`JortsSha3`) or authenticated Poseidon2 (`JortsPoseidon2`). All three custodians participate; the reconstruction threshold is 2 and the security model permits one malicious party with abort.

To guarantee that crashes, network partitions, or malicious retries never open two distinct digit vectors on the same epoch, *BeltLatch* (`belt_latch.rs`, guarded by extracted `BeltLatchKernel`) interposes a three-step barrier ahead of every share opening:
1. Each custodian persists $("epoch", "digest", "salt", "digits")$ through an `fsync`ed write-ahead log before updating RAM, sampling the retry salt via a joint coin flip after the message is fixed and bounding epoch jumps by `MAX_EPOCH_JUMP` $= 64$.
2. On any retry for a latched epoch, a custodian replays its persisted record verbatim and rejects any mismatched digest or salt; unconfirmed local binds whose coin-flip provenance peers cannot verify permanently burn the epoch.
3. Custodians exchange pairwise cSHAKE256 [SP800-185] MAC echoes of the binding; opening routines require the resulting `OpenPermit` tokens.

*Mode 3A* evaluates the 128 chains of the current epoch online, whereas *Mode 3B* pre-evaluates and verifies a sliding window of upcoming leaves in RAM so online signing reduces to the coin flip, latch echo, and one share-opening round. On disk, `durable_ledger.rs` maintains a two-slot MAC-authenticated snapshot under an exclusive genesis lock sequenced by `FsCeremonyJournal`. `PosixCrashWal.lean` models volatile page cache, drive write-back cache, torn sector writes, and `OpenDescriptionId`-keyed POSIX `flock(2)` locks, welding `BurnAppend` host steps to epoch uniqueness across arbitrary crash/reboot traces (`reserve_before_sign_multi_crash_epoch_uniqueness`, `burnAppend_sync_welds_host_reserve`).

== QuorumJorts and the native QS↔AG bridge

Scaling stateful signing to $(t,n)$ custodians introduces online MPC latency when only $t$ signers are reachable and cross-quorum equivocation when $2t <= n+f$. `qsag-quorum` pre-stages shares of the three intermediate states along each base-4 WOTS+C chain so custodians open only the share at digit $d_j$, and the combiner hashes forward to $F^(w-1)$ to catch malformed shares without online MAC checks:

*QS-A (`CommitteePartitionedJorts`).* The $2^h$ leaves are partitioned into $binom(n,t)$ disjoint contiguous ranges, one per $t$-subset, shared additively ($t$-of-$t$) within each subset. Any $t$ online custodians sign from their dedicated range in one round. For $f <= t - 1$ corruptions—even when $2f > t$—every committee contains at least one honest custodian whose durable latch locks each leaf, though per-committee capacity divides by $binom(n,t)$ and the leaf index identifies the signing subset (`qs_a_leaf_index_identifies_committee`).

*QS-B (`BftShamirJorts`).* All custodians share a single global tree whose chain states are $(t,n)$-Shamir shared (12,288 B per leaf per custodian over $FF_(2^8)$). Before releasing shares, each custodian requires an extracted-guard-verified `LatchCertificate` (`VerifiedBeltQuorumGuard`) from $q$ custodians satisfying
$ 2q > n + f. $
Quorum intersection forces any two certificates for the same leaf to overlap in $2q - n >= f + 1$ parties, at least one honest (`beltLatch_quorum_intersection_global_uniqueness`; `tooth_under_threshold_latch_quorum_switches_double_sign`). Liveness requires $n - f >= q$, hence $n >= 3f + 1$ (`beltLatch_safe_and_live_iff_n_ge_3f_plus_1`).

*Native `[Goldilocks; 4]` `Hem` bridge (`hem_quorum.rs`).* To bridge quorum-switching custody directly into succinct aggregation (`"QS"` $arrow.l.r$ `"AG"`), `qsag-quorum` provides `HemCommitteePartitionedQuorum` (QS-A), `HemDynamicShamirQuorum` (QS-B over Goldilocks Shamir shares), and dealerless `HemSpdzSeedQuorum`. Rather than converting field outputs into canonical 32-byte digests between chain steps—which would cost 760 Boolean Beaver triples per step—`poseidon2_mpc` steps chains directly over `[Goldilocks; 4]` capacity/rate elements, emitting 4,328-byte `JortsPoseidon2` signatures verified natively by `Hem` with *zero intermediate `A2B` carry circuits*. `HemDynamicShamirQuorum` supports proactive zero-Shamir refresh ($Pi_"refresh"$) and two-round $(t,n) -> (t',n')$ committee resharing ($Pi_"reshare"$) while preserving the 65-byte validator public key and carrying forward the monotone `next_unspent_leaf` floor across committee transitions; `ConfidentialWireChannel` supplies Encrypt-then-MAC transport.

== Corduroy, bit identity, and few-time signatures

*Corduroy* instantiates the stateless target-sum hypertree over Poseidon2 (`CORDUROY_CUSTODY_128`), while `CorduroyPoseidon2` ($k=32, a=8, d=16, h'=4$) supplies the 82,256-byte stateless format arithmetized inside Hem (§4).

*Matched-input bit identity.* Across all six FIPS 205 SHAKE parameter sets, `rss_thresholdSlhSign_eq_slhSignInternal` proves byte-for-byte identity with standalone `slhSignInternal` under `MatchesKey`, with strict pure/prehash domain separation (`pure_vs_preHash_disjoint`, `preHash_downgrade_rejected`), cross-checked by 43 built-in KATs. Analogous pointwise equalities hold for Baggy, Jorts, and QS-B (`rss_thresholdPqHashSign_eq_evalSingleSign`, `shamir_poseidon2_shared_thresholdSign_eq_evalSingleSign`), while `verifyProductionPqHashSig` reduces stateless and one-time-epoch stateful forgeries to `ProdForsItsrBreak`, `ProdSmTcrBreak`, or `ProdPreimageBreak` (`production_forgery_break_of_signingLog`, `uc_production_threshold_forgery_transfer`).

*Few-time signatures (`qsag-fts`).* `FrontierSumFts` maps a randomized digest bijectively onto a prefix-free binary-tree antichain of length $L$ and height $<= h$ paired with base-$w$ chain offsets summing to $S$, factoring exact `U384` ranking into $M(h,w,L,S) = N(h,L) dot D(L,S)$ (`frontierAntichain_paths_prefixFree`, `frontierSumFts_rank_unrank_bijection`) behind an extracted burn guard (`FtsEpochGuard`). In @ftsprofiles, the 16-byte-node compact profiles provide 128 classical / 64 Grover preimage bits, whereas `Compact1122` (`1,122 B`, $w=96, L=34, S=1,615, M > 2^263$, plus a `1,194 B` `RotatedEpochVote` key-rotation envelope) and `Full256Bit` (`2,338 B`) carry full 32-byte nodes and $> 256$-bit rank domains ($> 128$-bit Grover preimage width; a complete $w=96$ EUF-CMA reduction for `Compact1122` remains separate from node width)—enabling `Compact1122` plus a 96-byte consensus vote header (`1,218 B`) to fit inside a single 1,232-byte QUIC MTU (§7.4). Experimental `ParallelSeededFts` achieves height-independent sequential MPC depth $D_"parallel" = 48(1+w) + 8 = 296$ over a 48-round $x^7$ Davies–Meyer SPN on $FF_(2^128)^2$ (`parallelSeededFts_mpc_depth_independent_of_height`).

#figure(tbl((1.55fr, auto, auto, auto, auto, auto, auto, auto),
  [Profile], [B], [$n$], [$h$], [$w$], [$L$], [$S$], [Uses], table.hline(),
  [Compact514], [514], [16], [14], [5], [31], [62], [1],
  [Compact770], [770], [16], [15], [5], [47], [118], [2],
  [Compact1122], [1,122], [32], [8], [96], [34], [1,615], [1],
  [Compact1314], [1,314], [16], [15], [5], [81], [162], [2],
  [Full256Bit], [2,338], [32], [8], [5], [72], [144], [1],
), caption: [`FrontierSumFts` wire profiles ($n$ = node bytes; `Compact1122` and `Full256Bit` carry 256-bit nodes and $> 256$-bit rank space).]) <ftsprofiles>

= Secret sharing, preprocessing, and Poseidon2 hardening

== Bitsliced 2-of-3 RSS and binary-tower Shamir

For three-party custody ($t=2, n=3$, $binom(3,1) = 3$), `Rss256Engine` evaluates up to 256 independent Keccak-f[1600] sponges in lockstep by packing bit $i$ across 256 lanes into SIMD registers [FLNW17], tolerating one malicious party with abort. Outputs stay sealed until a post-wave barrier hashes the gate transcript, runs a commit-then-open coin flip, and checks every multiplication via a two-pass sublinear distributed zero-knowledge proof [BGIN19] over `Tower128` ($FF_(2^128)$) using `PassWeights` half-plane batching, `b`-bit ternary `{0, 1, slope}^b` Frobenius-basis folding ($gamma + gamma^2$), and a `tau`-masked cross-product sacrifice (`Rss256TernaryRound.lean`, `Rss256TwoPassProductProof.lean`: `rss256_two_pass_product_proof_sound` $< 2^(-217)$ per wave; `rss256_recorded_trace_integrity`). Any failure permanently poisons the engine (`rss256_sticky_poison_terminal_absorption`).

To scale beyond small CNF committees without $binom(n, t-1)$ blowup, QSAG embeds Shamir secret sharing in a Wiedemann binary tower [Wie88]:
$ cal(T)_0 = FF_2, quad cal(T)_1 = cal(T)_0[x_0] slash (x_0^2 + x_0 + 1), $
$ cal(T)_k = cal(T)_(k-1)[x_(k-1)] slash (x_(k-1)^2 + x_(k-2) x_(k-1) + 1), $
reaching $cal(T)_3 = FF_(2^8)$ (up to 255 nonzero party points; `zero_eval_point_leaks_secret_term`) and $cal(T)_7 = FF_(2^128)$ for MAC tags (`embedTowerChain_injective`, `towerMul_inv`). `ShamirSeedShare256` stores 256 `GF(2^8)` bit shares independent of committee size $n$.

== Poseidon2 cryptanalysis and 264-bit Ring-LWE preprocessing

*Poseidon2 evaluation and 2026 subspace hardening.* Algebraic profiles instantiate width-12 Poseidon2 [GKS23] over the Goldilocks prime $p = 2^64 - 2^32 + 1$ ($R_F = 8 = 4+4$ external rounds, $R_P = 22$ partial rounds, $118$ $x^7$ S-boxes). Using preprocessed Shamir mask powers $([r], ..., [r^7])$, custodians open $y = x - r$, verify its batched `GoldilocksExt2` SPDZ MAC, and evaluate $[x^7] = sum_(k=0)^7 binom(7,k) (-1)^k y^(7-k) [r^k]$ locally in one round (`power7BinomialEval_eq_sbox7`).

Recent cryptanalysis exposed structural pitfalls in naive Poseidon2 compression modes. Merz and Rodríguez García [MRG26] showed that when the external matrix $M_E = P_3 times.o M_4 = "circ"(2 M_4, M_4, M_4)$ is paired with 4-lane partial feed-forward or reducible internal matrices $M_I$, inputs in the 8-dimensional subspace ${(X, -X, 0) : X in FF_p^4}$ cancel across $M_E$ and skip initial nonlinear rounds (`tooth_poseidon2_me_std_admits_x_neg_x_subspace_skip`); simultaneously, Bhati, Tariq, and Ashur [BTA26] demonstrated partial-layer S-box skipping via subspace restriction across $1 + (t - 2k)$ internal rounds. In `Poseidon2AlgebraicAndRecursiveHem.lean`, we prove two complementary defenses: first, even after worst-case subspace skipping, $R_F = 8, R_P = 22$ retains univariate degree $7^26$ and multivariate Macaulay/Bézout degree $7^49 > 2^128$ against CICO-1 algebraic solving; second, swapping the Kronecker factor order to $tilde(M)_E = M_4 times.o P_3$ (`poseidon2_kronecker_swap_kills_subspace_skip`), shifting the internal diagonal seed to `V[0] = -64` so $chi_(M_I^k)$ is degree-12 Rabin-irreducible over $FF_p$ for $1 <= k <= 32$, and applying 8-lane Jive bilateral feed-forward eliminate invariant-subspace round-skipping at *zero extra multiplications* (while live `sponge.rs` retains KAT-pinned $P_3 times.o M_4$ vectors pending synchronized migration).

*24-challenge Ring-LWE base OT and dual-LPN PCG.* Dealerless preprocessing starts from Ring-LWE base OT over $R_q = ZZ_(12,289)[X] slash (X^1024+1)$ with centered binomial noise $eta=1$, where $norm(e_1 r_c-e_2 s_R+e_3)_infinity <= 2049 < 3072=floor(q slash 4)$ gives exact decryption (`rlwe1024_ot_decrypt_exact`) and Fujisaki–Okamoto re-encryption binds sender pads [FO99]. To achieve full 128-bit post-quantum soundness against Grover search, the receiver's cut-and-choose OR-Sigma proof (`preprocessing.rs`, `RLWE_ZKPOK_REPS = 24`) hashes *24* challenges jointly in $cal(C) = {plus.minus X^k : 0 <= k < 1024}$ (`2,048` choices = 11 bits each), providing *264 classical bits and 132 generic Grover bits*. Over $2^k$-cyclotomics and odd $q >= 3$, `signedMonomial_challenge_set_pairwise_invertible` proves $(c - c') g = 2$, yielding short isometric extraction $A s_"iso" + e_"iso" = (1 - c^(-1) c') u$ with infinity norm $<= 6,140$ ($<= 6,142$ SIS dichotomy). Crucially, bimodal BLISS-style sign flipping cannot be used here because flipping challenge signs yields $c_1 + c_2 = 0$ when $c_2 = -c_1$, breaking special soundness at $q = 12,289$; instead, `GaussianHvzkAndDualLpn.lean` proves that the unimodal fixed-point `Q192` Bernoulli rejection sampler ($sigma = 700$, witness energy $<= 1,376$, $norm(v)_2^2 <= 33,024$, $M = 40$, `RLWE_GAUSSIAN_LOG_M = 3_615_102`) achieves statistical HVZK distance and secret-independent abort bias strictly below $2^(-128)$ (`q192_gaussian_hvzk_statistical_distance`).

Above base OT, interactive KOS extension [KOS15] commits OT columns before squeezing challenges (`kos_interactive_check_sound`), and our wire-v3 dense dual-LPN PCG (`pcg_dense.rs`) [BCGI+19] expands 64 regular-noise GGM trees of depth 15 with single-use `SeedBurnTracker` enforcement and active SPCOT checks ($approx 2^(-226)$ per directed pair). `GaussianHvzkAndDualLpn.lean` proves both depth-15 piling-up bias $< 2^(-256)$ and Prange / Stern–Dumer ISD work factors $>= 2^256$ classical and $>= 2^128$ Grover (`pcg_dense_depth15_prange_and_stern_dumer_pq128`). Multi-party arithmetic and power-7 tuples ($n >= 3$) use MASCOT batch sacrifice [KOS16] (`spdz_triple_sacrifice_sound`, `pow7_sacrifice_sound`).

== Authenticated booleanity, release ordering, and resharing

In characteristic 2, bit shares satisfy the Frobenius check $b^2 + b = 0$ over authenticated shares (`verifySharedDkgFrobenius_sound`; `frobenius_unauthenticated_offset_break`). Every engine enforces *commit → MAC-verify → open* (`ConsumingOpeningGuard2Lane`), preventing pre-MAC fault leakage (`mac_before_open_blocks_faulted_cut_leakage`), with paired `Tower128` MACs ($2^(-256)$, `bdoz_2lane_mac_soundness`) and `GoldilocksExt2` MACs ($p^(-2) < 2^(-127)$, `spdz_batch_mac_soundness`). Finally, `dkg.rs` provides two-round commit-then-open DKG, proactive refresh, and cleartext-free $(t,n) -> (t',n')$ resharing with explicit old-share zeroization (`reshare_from_shares_without_cleartext_recombines_secret`).

= Hem: succinct $K$-to-$1$ aggregation

== Multilinear trace and `GoldilocksExt4`

*Hem* (`qsag-agg`) compresses $K$ `JortsPoseidon2` or `CorduroyPoseidon2` verifications into one succinct argument over a 256-column multilinear Goldilocks trace: 512 rows per Jorts signature and 8,192 rows per Corduroy signature, packing up to 128 or 8 signers per shard within the $2^24$ flattened-element cap. Each row encodes one width-12 Poseidon2 permutation (inputs and 118 $x^7$ S-box outputs), a 44-limb step-machine state, and opcode selectors for digest unpacking (`Digest5`, proved injective in `digest5FromBitVec256_injective`), WOTS+C chain walks, endpoint compression, and Merkle verification.

All verifier challenges, OOD points, and folding scalars come from the quartic extension `GoldilocksExt4`,
$ E = FF_p [v] slash (v^4 - 7), quad q = abs(E) = p^4 > 2^(255.99). $
Under unitary QROM Grover search (`qrom_fiber_search_bound`), $q_"Hash"$ oracle queries amplify single-round error $epsilon$ by up to $8(q_"Hash" + 1)^2$: a quadratic extension hits a 64-bit quantum ceiling (`ext2_error_denominator_cliff`), whereas $p^4 approx 2^256$ sustains 128-bit QROM margins (`ext4_error_denominator_bound`).

== Sumcheck, rate-escalating WHIR, and Canopy commitments

Row constraints reduce to a degree-8 Sumcheck [LFKN92] coupled with an inter-row shift claim, settled via multi-stage rate-escalating WHIR [ACFY25]: each stage folds $s_i <= 6$ variables and re-encodes over shifted base-field two-adic cosets $cal(D)_i = 7 dot H_i subset FF_p$ at escalating blowups $B = 4, 16, 64, 256$ ($rho_i = 1 slash B_i$). Each stage oracle is pinned at two independent out-of-domain Kronecker points $"pow2"(z_"ood") in E^m$ ($< 2^(-448)$ list collision; `prechallenge_fold_forgery_attack`, `terminal_check_ext4_omission_unsound`), committed in Merkle trees over `CANOPY_MIDSTATE`, and opened via Steiner-deduplicated `CanopyMultiProof` paths (`verifyCanopyMultiproof_exact_sibling_count`, `verifyCanopyMultiproof_binding`) behind 16-bit stage PoW (`QSAG.PCS.POW2/v1`, `maxQueryCap = 512`).

== Breaking the scalar folding floor with affine RS combiners

Classical scalar Reed–Solomon combiners $f(z) + alpha g(z)$ [BCIKS20] suffer an unconditional $Omega(n slash q)$ floor ([CWYZ26], Prop. 6.1) and a Johnson list-decoding loss of $s_i abs(cal(D)_i)^2 L_i^7 slash p^4$, previously capping `.hemExt4WhirPq128` at $q_"Hash" + 1 <= 2^21$ (`tooth_hem_ext4_single_challenge_qrom_folding_ceiling`). Hem (`pcs/affine.rs`, wire v6) therefore adopts the *affine Reed–Solomon combiners* of Chiesa, Weissenberg, Yogev, and Zheng [CWYZ26]:
$ w_(theta, alpha, beta)(z) = g(z) + (alpha + beta z)(f(z) + theta g(z)), $
analyzed under $s = 1$ coordinate-loss mutual correlated agreement (shifting query hit probability by $<= 1 slash n$ per fold). `AffineProximityGaps.lean` proves `#tooth` lower bounds for both scalar $Omega(n slash q)$ (`tooth_scalar_combiner_linear_n_over_q_floor`) and $s = 0$ line-root alignment (`tooth_affine_combiner_zero_loss_linear_floor`). Specializing `[CWYZ26]` to `GoldilocksExt4` and base-field cosets $cal(D)_i subset FF_p$ yields three wins:
1. *Subfield-cheap verifier folding:* Since $z = x_k^2 in FF_p$, evaluating $alpha + beta z$ inside `fold_duet_affine_ext4` (which folds each base-field coset fiber pair $(v_0, v_1)$ under $(theta, alpha, beta) in E^3$) costs one `mul_base`—four $FF_p$ multiplications rather than sixteen.
2. *Quadratic $(n slash q)^2$ collapse:* Because $q = p^4 approx 2^256 >> n^2 <= 2^52$, the nonpersistent $(n slash q)^2$ term collapses below $2^(-371)$. Per-fold persistent error drops below $1906 slash p^4 < 2^(-245.1)$, with aggregate stage numerators $[4182, 1644, 824, 489, 792] slash p^4$ totaling $7931 slash p^4$.
3. *Two-slot degree fixed point (`Monomial-Shift WHIR`):* Because $d |-> floor(d slash 2) + 1$ satisfies $d_s <= 2^(ell - s) + 1$ for $1 <= s <= ell$ (`affine_fold_degree_le_pow2_add_one`), affine folding accumulates *at most two overflow monomials* ($c_(2^m), c_(2^m + 1)$). Witness conversion into monomial basis once at Round 0 turns multiplication by $Y = Z^2$ into a zero-multiply pointer shift bridged by five linear-functional scalars, preserving power-of-two stage NTTs and Merkle depths while Round-0 asymmetric cascading bounds $S <= 16$-polynomial batch degree growth to $+1$.

== Unconditional Johnson-radius query regimes

Earlier IOPP deployments parameterized WHIR queries under conjectural proximity gaps up to capacity $1 - rho$. In 2025–2026, Crites and Stewart [CS25] disproved both correlated agreement and WHIR mutual correlated agreement at capacity $1 - rho$, and Krachun, Kazanin, and Haböck [KKH26] constructed explicit prime-field multiplicative subgroup counterexamples where proximity gaps fail arbitrarily close to capacity $1 - rho - eta$. Consequently, QSAG purges all capacity-conjecture schedules: deserializing retired wire tags `0, 1, 3` fails closed in `WhirSecurityRegime::from_u8`, leaving solely the *two unconditional Johnson-radius regimes* $1 - sqrt(rho_i) - eta_i$ (@regimes).

#figure(tbl((2.4fr, 1.8fr, 1.6fr, 0.9fr),
  [Unconditional regime], [Queries per stage], [$q$ at $B=4,16,64,256$], [Round bits], table.hline(),
  [`BciksJohnsonClassical128` (tag 2)], [$ceil(256 slash log_2 B)+1$], [129, 65, 44, 33], [144 / 72],
  [`BciksJohnsonQrom128` (default, tag 4)], [$ceil(512 slash log_2 B)+2$], [258, 130, 88, 66], [272 / 136],
), placement: top, scope: "parent", caption: [Unconditional Johnson-radius WHIR query regimes (`WhirSecurityRegime`; retired capacity wire tags `0, 1, 3` fail closed). Round bits report classical query-plus-16-bit-PoW budgets and Grover halves. Stage 4 ($B=256$) activates at 23–24 variables.]) <regimes>

By default, `verify_aggregate` accepts *only* `BciksJohnsonQrom128` (`meets_qrom_128_floor`), which adds two slack queries per stage so all 46 canonical stages across $2..=24$ variables carry an explicit upward-rounded dyadic `[CWYZ26]` Theorem 4.8 witness (`checkWhirAffineWitness`, per-fold error $< 2000 slash p^4$) and $> 256$-bit unconditional query error; `BciksJohnsonClassical128` requires explicit opt-in for raw classical PCS testing. Keeping the two QROM accounting conventions distinct is essential:
- *Bounded-query unitary QROM:* Under BBBV97 single-round Grover amplification $8(q_"Hash" + 1)^2 epsilon$ (`ConcreteSecurityBudget.lean`), `[CWYZ26]`'s 3-scalar affine fold bound $< 2000 slash p^4 approx 2^(-245.0)$ (`cwyz_duet_fold` across coset fiber pair $(v_0, v_1)$) *already certifies $< 2^(-128)$ total QROM soundness up to $q_"Hash" + 1 <= 2^56$* ($8 dot 2^112 dot 2000 slash p^4 < 2^(-129.9) < 2^(-128)$), lifting `[BCIKS20]` scalar folding's $q_"Hash" + 1 <= 2^21$ ceiling by $+35$ query bits ($+98$–$108$ classical bits). Across all rounds jointly, `MultiRoundFsQrom.lean`'s adaptive oracle-dependent measure-and-reprogram bound (`multiRoundFsQrom_budget_bound`) stays below $2^(-128)$ for $Q + 1 <= 2^40$ and five 256-bit Merkle roots (sharp at $2^41$), conditional on concrete Hem transcript flip bounds and quantum commitment extraction.
- *Unbounded-query `soundcalc` `bits // 2` ($epsilon_"rbr"^(-1 slash 2)$) convention:* Our exact-rational `ethereum/soundcalc` profile verifier (`scripts/export_soundcalc_profile.py`, passing `59/59` `--verify` checks against `affine_schedule.rs` and Lean's `hemJohnsonQromWitnessTable`) reports *`272` classical / `136` nominal Grover bits* on `whir_query` (`256` hypergeometric + `16` stage PoW), whereas `245` classical RBR bits on `whir_proximity_gaps` halves to *`122` nominal Grover bits* unless paired with fold-round PoW grinding (`+16` bits $->$ `261 / 130` bits) or a *second independent affine-combiner rail*.

== Constructive `[CWYZ26]` coding-theory stack and mechanized Hem coverage

Across independently generated proofs, `merge_aggregates` forms a binary tree (`MAX_MERGE_TREE_DEPTH` $= 16$) enforcing disjoint `SignerBitmap`s (`popcount_union_disjoint_eq_add`, `overlapping_merge_rejected`), matching regimes, and epoch/registry binding (`Poseidon2AlgebraicAndRecursiveHem.lean` mechanizes 2-layer hierarchical soundness).

On the formal side, we built a constructive (`0 Classical.choice`, `0 sorry`) algebraic-geometry and coding-theory stack in `Qsag.CodingTheory` over `RatFunc F = Frac(UPoly F)`:
- *Polynomials, resultants, and constructive splitting:* `PolyMv3.lean`, `SylvesterResultant.lean`, `BivariateGauss.lean` (`tdeg_mul` via homogenization, constructive Gauss's Lemma `isPrimY_mul`), and `DynamicGcdSplit.lean`, which replaces non-constructive `UniqueFactorizationDomain` splitting over function fields with dynamic Euclidean `gcd` splitting (`UPoly.d5_split`) whenever evaluation witnesses stumble on non-invertible denominators.
- *Formal Hensel lifting and trivariate GS interpolation:* `HenselNumerators.lean` and `UniversalHenselLift.lean` formalize division-free Hensel contraction (`henselNum_spec`, `reconCoeff_spec`), proving `[CWYZ26]` Lemma 3.11 and the exact Claim 4.9 reconstruction identity $S^(2d-1) P = "reconstructPoly"$ over `Frac(UPoly F)`. `TrivariateGsExplainer.lean` mechanizes trivariate Guruswami–Sudan affine explainer interpolation (`explainer_spec`, `explainer_vanishes`, Lemma 4.2).
- *Hasse stratification and persistent Johnson bounds:* `SimpleRootStratification.lean` and `AffineIncidenceBound.lean` prove Hasse derivative composition $partial^((1)) partial^((k)) = (k+1) partial^((k+1))$, simple-root stratification (`simple_root_of_hasse`), excluded-line and per-line root bounds, and `#tooth` witnesses (`affineMcaBound_without_field_term_fails`). `JohnsonSetSystem.lean` and `PersistentPairsBound.lean` prove pure-`Nat` Cauchy–Schwarz set-system Johnson bounds (Lemma 3.2) and persistent challenge/pair bounds (Lemmas 4.4–4.5), culminating in `Cwyz26AffineGap.lean` (`cwyz26_affineMcaBound_of_nonExcluded`), which proves `[CWYZ26]` Lemma 4.1 modulo the single residual nonpersistent space-curve incidence hypothesis `NonExcludedBound` (Lemma 4.7), alongside unconditional Welch–Berlekamp affine gaps for $delta < (1 - rho) slash 3$ (`welch_berlekamp_affine_proximity_gap`).

Complementing `Aggregation.lean` and `SuccinctAggregationIop.lean` (`stepOp256_groupA_exact`, `stepOp256_shift_iff`), `CorduroyAndHemAirCompleteness.lean` now proves active-slot witness extraction from `stepOp256TableOk` for both XMSS/Jorts and 16-layer Corduroy (`stepOp256TableOk_xmss_extract`, `stepOp256TableOk_corduroy_extract`, `stepXmssRows_roundTrip`), leaving only the MIR/FFI bridge from Rust's `populate_active_signer_rows` trace filler to `stepOp256TableOk` (§8).

= Custody, multi-chain migration, credentials, and GPU pipeline

*Dealerless HD derivation (`qsag-hd`), addresses (`qsag-addr`), and policy (`qsag-policy`).* Custodians derive root shares, child rekeys, and MAC masks from a subset-seed ceremony ($n >= 2t-1$), backed by extracted `HdCommittedZeroTest` guards, Merkle-committed watch-only inventories (`PiHdCommitInventory`), and module-LWE public shifts (`PiHdLinearModule` mod $8,380,417$). Identities use 67-character Bech32m (`qsp`, checksum `0x2bc830a3`) with extracted `HybridPinnedEnvelope` framing (`check_hybrid_domain_framing`, `derive_hybrid_transcript_digest`). Policy entrypoints evaluate 2-lane BDOZ circuits behind extracted `StatefulVelocityGuard::authorize_spend` watermarks to mint `AuthorizedSignReleaseToken`s.

*Multi-chain active co-ZK key migration (`qsag-migrate`).* To migrate legacy accounts to a `QsagAddress` without exposing the spending key to any custodian, three custodians run `co_zk_mpc`, an actively checked distributed prover for 438-repetition mixed-domain ZKBoo [GMO16] ($(2 slash 3)^438 < 2^(-256)$, Grover exponent $128.11$, `zkboo_438_gt_two_pow_256_margin`). Supported legacy credentials span four curve ecosystems:
- *Bitcoin & Ethereum EOA (`secp256k1`):* P2PKH/P2WPKH `HASH160`, Taproot x-only keys with explicit $y$-parity pinning, and 20-byte Keccak-256 Ethereum EOAs (`PrattPrimalityCert.lean` kernel-certifies primality of `SECP256K1_FIELD_P` and `SECP256K1_ORDER_N`);
- *Solana (`Ed25519`):* SLIP-0010 compressed Edwards public keys;
- *Zcash Orchard (`Pallas` / `RedPallas`):* Both direct spend-authorizing keys $"ak" = ["ask"] cal(G)$ and rerandomized keys $"rk" = ["ask" + alpha] cal(G)$ (`pallas.rs`);
- *Ethereum Beacon Validators (`BLS12-381` $G_1$):* Compressed 48-byte `0x01`/`0x02` EIP-7251 validator keys (`BeaconValidatorPubkey`) and pre-quantum unrevealed `0x00 || SHA256(pk_48)[1..32]` withdrawal credentials (`UnrevealedBls0x00Credential`, `bls12_381.rs`), proving scalar ownership inside ZKBoo without ever publishing `pk_48` on-chain.

Before any wire, base-conversion residual, or challenged view opens, coin-flipped inner-product sacrifices verify all multiplications: two-challenge `GF(2^128)` Boolean AND checks bound soundness error below $(55 slash (2^128 - 1))^2 < 2^(-244)$ per flush, paired with $<= 35 slash (p - 1) < 2^(-249)$ large-prime checks and $<= 35 slash (p^3 - 1) < 2^(-186)$ cubic-Goldilocks checks, followed by a shared output zero test (`ActiveMigrationZeroTest.lean`: `tooth_premature_residual_open_recovers_spending_key`).

*Threshold ML-DSA-44/65/87 and QROM `BlindVC` credentials (`qsag-cred`).* Dealerless threshold lattice signing now supports all three NIST FIPS 204 security levels (@mldsa) for $n <= 5, t >= 2, n >= 2t-1$, accelerated by Seiler's signed-Montgomery SIMD NTT [Sei18] ($q = 8,380,417$). Custodians rejection-sample short secret shares in $[-eta, eta]$ directly inside RSS and evaluate online norm/hint bounds (`check_mldsa44_norm_bounds`, `check_mldsa65_norm_bounds`) across $2t - 1$ active signers. Critically, `threshold_mldsa.rs` and `ThresholdMlDsaSecurity.lean` enforce *sealed-$bold(w)_1$ abort-transcript zero-knowledge* (`threshold_mldsa_abort_transcript_zk`): high bits $bold(w)_1$ and challenge $c$ remain secret-shared inside RSS until norm and hint checks pass, while `MlDsaReleaseGate` seals partial responses $bold(z)_i mod q$ under a `cSHAKE256` stream cipher and wipes buffer shares on rejection—ensuring aborted attempts leak *zero* $(bold(w)_1, c, bold(z), bold(h))$ transcripts while durably burning every nonce. For privacy-preserving credentials, `PiVoprf` implements a 2-of-5 Poseidon2 sponge TOPRF with constructive unique line decoding against one Byzantine server (`toprf_2of5_byzantine_unique_decoding`, extracted `toprf_majority_of_3_goldilocks`), backing `PiBlindVc` six-limb attribute commitments whose 438-repetition QROM Fiat–Shamir soundness ($< 2^(-128)$ for $Q <= 2^60$) reduces presentation acceptance to issuer ML-DSA unforgeability (`BlindVcQromSecurity.lean`: `blindVc_quantum128_qrom_fs_soundness`, `blindVc_presentation_reduces_to_issuer_mldsa`).

#figure(tbl((1.35fr, 0.85fr, 0.95fr, 0.95fr),
  [FIPS 204 profile], [NIST cat.], [Public key B], [Signature B], table.hline(),
  [ML-DSA-44], [2], [1,312], [2,420],
  [ML-DSA-65], [3], [1,952], [3,309],
  [ML-DSA-87], [5], [2,592], [4,627],
), caption: [Standard FIPS 204 wire sizes emitted by the dealerless sealed-abort $(t,n)$ threshold signer.]) <mldsa>

*VRAM-resident Vulkan prover pipeline (`qsag-accel`).* A zero-`crates.io`-dependency Linux Vulkan 1.3 / SPIR-V 1.5 backend executes *10 compute shaders*: six standalone primitive kernels (Keccak-f[1600], Poseidon2-12, Goldilocks NTT, Ext2 coset LDE, Poseidon2 Merkle layers, and BDOZ binary-field dot products) plus *four VRAM-resident WHIR/Hem prover shaders* (`air_row_group_a.comp`, `air_row_group_b.comp`, `whir_lde_merkle.comp`, `whir_fold_sumcheck.comp`) managed through persistent `ProverArena` / `GpuWhirSession` slots (`ProverKernelSlot`). `vulkan_ffi.rs` supports both discrete GPUs and unified-memory `VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU` APUs, enforcing Wave32 / zero-scratch pipeline audits and V5 hardware-audit-pinned `cSHAKE256` `ExecutionReceipt`s.

= Four assurance pillars

Across the `59` root-imported modules in `Qsag.lean` (plus auxiliary coding-theory and algebra modules), our constructive kernel audit (`withEnv (env.setExporting false) Lean.collectAxioms`) verifies *`62,699+` public and `.olean.private` declarations* with *`0` `sorry`, `0` custom axioms, and `0 Classical.choice`*—permitting solely `{propext, Quot.sound}` via `PSum` extractors and structural `BEq` lemmas. In `aeneas/lean`, the MIR/spec/custody closure audits `6,546` MIR + `132` spec-weld + `89` custody-weld declarations (`0` rejected axioms, `0 FunsExternal`), paired with the `aeneas/lean-whir` WHIR closure. Sandboxed six-kernel comparator replay (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) now covers *`130` `Qsag.Apex` theorems* (including 23 newly welded production-surface theorems), *`71` MIR challenge theorems*, and *`57` WHIR MIR challenge theorems*. Hardened `#verify_inhabited` (preventing unbound `List` witnesses from silently collapsing to empty `default` lists) and `#tooth_pair` (`AssuranceKit.lean`) guard theorem premises across the spine (@pillars).

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 5.5pt,
    panel([#smallcaps[Pillar 1 · `0 Classical.choice` protocol, `CodingTheory`, WAL & QROM spine]\
      `Qsag.Apex` (130 thms) · `CodingTheory` (`[CWYZ26]` GS + Hensel + Johnson) · `PosixCrashWal` · `MultiRoundFsQrom`]),
    align(center)[↓ `MirSpecBridge.lean` · `SpongeFraming.lean` · KAT parity links ↓],
    grid(columns: (1fr, 1fr), gutter: 7pt,
      panel([#smallcaps[Pillar 2 · extracted Safe-Rust MIR]\
        `qsag-verified` (71) & `qsag-whir-verified` (57)\
        Unconditional short `cSHAKE256` & live guards]),
      panel([#smallcaps[Pillar 3 · ISA, ELF64 & `McRefine`]\
        `28/28` live `qsag_asm_*` pins (`3,355` insns)\
        `92` x86-64 / `65` AArch64 strict CT (`0` viol.)]),
    ),
    align(center)[↑ complemented by bare-metal & differential gates ↑],
    panel([#smallcaps[Pillar 4 · bare-metal silicon & executable ground-truth gates]\
      Zen 5 `ptrace` cosim (`59/59`, `7,184` vecs) · `spec-oracle` (`5,416` checks) · `13/13` mutations · `dudect` · 6-kernel replay]),
  )
}, caption: [QSAG's four assurance pillars pair `0 Classical.choice` Lean proofs with live-welded MIR crates, refreshed ELF64 kernel pins, and bare-metal Zen 5 cosimulation.]) <pillars>

== Pillar 1: protocol, coding-theory, storage, and QROM spine

Foundational and protocol modules (`Goldilocks`, `BinaryTower`, `Keccak`, `Poseidon2`, `Fips205`, `HypertreeEufCma`, `BaggyAndRss256Security`, `JortsBeltLatchAndQuorumSwitching`, `InteractiveUcEngine`, `ThresholdMlDsaSecurity`, `GaussianHvzkAndDualLpn`, `BlindVcQromSecurity`) establish bijective sponge encodings, multi-turn latch safety, sealed-abort ML-DSA privacy, `Q192` Gaussian HVZK, and sequential UC composition [Can01]. The 23 production theorems welded into `Qsag.Apex` connect `verifyProductionPqHashSig` stateless/stateful EUF-CMA and UC forgery transfer, `StepOp256` XMSS/Corduroy extraction, 2-of-5 Byzantine TOPRF unique decoding, durable Baggy non-equivocation, hardened multi-wave `RSS-256` trace integrity, and `PosixCrashWal` `BurnAppend` host reservations directly to six-kernel challenge replay.

== Pillar 2: Safe-Rust MIR refinement and live runtime welds

Charon and Aeneas translate `qsag-verified` and `qsag-whir-verified` into Lean under `0 FunsExternal`. Beyond `RealSpecFieldWeld.lean` and `RealSpecKeccakWeld.lean`, `SpongeFraming.lean` now proves *unconditional short-nonempty `cSHAKE256` MIR refinement* (`sponge_new_cshake256_short_nonempty_absorbed`, `cshake256_32_short_nonempty_refines`, `cshake256_short_nonempty_xof_from_extracted_state`) for all customization strings of length $1 <= abs("cust") <= 31$, discharging the rate-block framing bridge across every 14–26-byte `"QSAG.*"` domain tag (multi-block messages $> 135$ B remain an inductive extension). Production crates invoke these extracted functions directly on live critical paths: `VerifiedWaistbandRootGuard`, `BeltLatchKernel`, and `ConsumingOpeningGuard2Lane` in `qsag-core`; `VerifiedBeltQuorumGuard` in `qsag-quorum`; `FtsEpochGuard` in `qsag-fts`; `MlDsaReleaseGate`, norm checks, and TOPRF majority decoding in `qsag-cred`; `HdCommittedZeroTest` in `qsag-hd`; `StatefulVelocityGuard` in `qsag-policy`; `HybridPinnedEnvelope` framing in `qsag-addr`; and all six WHIR folding, OOD, PoW-mask, and terminal-pin gates in `qsag-agg`.

== Pillar 3: refreshed ELF64 byte pins, `McRefine`, and strict CT screening

`ConstantTimeIsa.lean`, `ElfBinaryVerify.lean`, and `McRefine.lean` model instruction semantics and three-way leakage taint (PC/branches, memory addresses, variable-latency operands, and dirty upper-YMM state) directly over compiled `.rlib` ELF64 `.text` slices. Resolving the earlier fixture-drift gap, `CompiledRlibFixtures.lean`, `ElfFixtureVerify.lean`, and `FaultAndSpeculativeSafety.lean` now match *`28/28` live Rust 1.99.1 exported `qsag_asm_*` assembly kernels* (`19/19` x86-64 = `1,935` instructions + `9/9` AArch64 = `1,420` instructions; `3,355` decoded instructions, `0` byte drift under kernel-bytes fixture binding, plus `5/5` standalone `SimdBinaryEquiv` fixtures), while `McRefine.lean` proves *whole-kernel mathematical I/O refinement for `26/28`* exported assembly kernels (leaving the two `64×256` transpose kernels to noninterference/looping certificates). Across the entire compiled `libqsag_asm.rlib` crypto surface—including root-level dispatchers and Rust-mangled `avx512`, `gf256_simd`, `sha2_hw`, and `ntt_simd` routines whose Lean decoder coverage remains future work—our strict ELF instruction screen (`audit_elf_ct.py --strict-rust-branches`, backed by `124` `#tooth` auditor self-tests) verified *`0` constant-time violations across all `92` x86-64 and `65` AArch64 compiled crypto symbols*, and release `objdump` disassembly confirmed *`0` `xmm`/`ymm`/`zmm` stack spills* in both 8-way `AVX-512` Keccak and Seiler `AVX2`/`AVX-512` ML-DSA NTT kernels. `SpirvSimtGpuEquiv.lean` proves SPIR-V codec roundtrip, Wave32 confluence, and modeled SIMT noninterference.

== Pillar 4: bare-metal Zen 5 cosimulation, `wasm32` portability, and ground-truth gates

Replacing earlier virtualized-only runs, we executed bare-metal Linux x86-64 `ptrace` single-step silicon cosimulation (`isa_cosim_silicon.py`) on an *AMD Ryzen AI 9 HX PRO 370 (Zen 5)* (`XCR0 & 0xE6 == 0xE6`), passing *`59/59` x86-64 test cases across `7,184` random + boundary vectors with `0` skips and `0` register/memory mismatches*, alongside `8/8` mandatory-feature `AVX-512` differential suites verified on *both* native Zen 5 silicon and Intel SDE 10.13.1 (`-spr`, including exhaustive $65,536$-pair Wiedemann `GF(2^8)` parity and all NIST ACVP ML-DSA-44/65/87 KATs). All eight core custody/crypto crates (`qsag-asm`, `qsag-addr`, `qsag-policy`, `qsag-fts`, `qsag-hd`, `qsag-cred`, `qsag-quorum`, `qsag-core`) also compile with `0` errors and `0` warnings on 32-bit `wasm32-unknown-unknown --no-default-features`. Complementing silicon execution, the strict `spec-oracle` suite passed `1,952` differential vectors (`5,416` total checks, `0` mismatches) and caught `13/13` production clause-drop mutations, while six-kernel replay checks all `130 + 71 + 57` challenge theorems. Native AArch64 `ptrace` execution remains separate from cross-compiled ELF verification.

= Evaluation

== Bare-metal Zen 5 `AVX-512` and Zen 3 `AVX2` kernel throughput

We benchmarked `qsag-asm` bare-metal on an *AMD Ryzen AI 9 HX PRO 370 (Zen 5)* (`SimdBackend::X86Avx512GfniVpclmul`, verifying OS `ZMM` state via `XGETBV`) and an *AMD EPYC-Milan (Zen 3)* (`SimdBackend::X86Avx2Pclmul`), using `rdtsc + lfence` medians of 7 runs over 64 KiB resident working sets (@simdbench):
- *Zero-spill 8-way `AVX-512` `Keccak-f[1600]`:* Keeping all 25 sponge planes plus 7 scratch registers inside `zmm0..zmm31` (`0` stack spill bytes vs. 800 B L1 spills in 4-way `AVX2`) and collapsing 5-input $theta$ parity and $chi$ into single-instruction `vpternlogq` + `vprolq` reaches *`0.634 cpb` (`3.15 GB/s`, `5.31×` vs. scalar, `1.81×` vs. `AVX2`)* on Zen 5.
- *512-bit `EVEX GFNI` and register-only split-nibble `GF(2^8)`:* Full-width `vgf2p8affineqb` reaches *`73.20 GB/s` (`537.2×`)* for Shamir `mul` and *`91.46 GB/s` (`0.022 cpb`, `653.7×`)* for `mac` on Zen 5. For CPUs without `GFNI` (Zen 3), replacing stack LUTs with a register-only 4-`vpshufb` split-nibble `mac` reaches *`48.68 GB/s` (`0.049 cpb`, `561.0×`)* on Zen 3 and `69.79 GB/s` on Zen 5.
- *4-way `EVEX VPCLMULQDQ` and `SHA-NI`:* 512-bit carry-less `GF(2^128)` batch MulAcc reaches *`34.34 GB/s` (`0.058 cpb`, `291.0×` vs. portable, `2.84×` vs. 128-bit `PCLMULQDQ`)* and `Tower128` BDOZ PolyMAC reaches `6.58 GB/s` (`46.9×`) on Zen 5; hardware `SHA-NI` reaches `0.830 cpb` (`2.41 GB/s`, `5.90×`) on Zen 5 and `1.320 cpb` (`6.72×`) on Zen 3 (paired with AArch64 `FEAT_SHA256`).
- *Seiler [Sei18] signed-Montgomery FIPS 204 NTT:* Vectorizing $q = 8,380,417$ across `16×i32` (`AVX-512`) and `8×i32` (`AVX2`) executes a 256-coefficient ML-DSA forward NTT in *`243.1 ns` (`485 cyc`, `3.33×`)*, inverse NTT in *`209.8 ns` (`419 cyc`, `4.44×`)*, and pointwise multiplication in *`56.7 ns` (`113 cyc`, `18.08 GB/s`, `6.21×`)* on Zen 5 (`338.4 ns`, `322.9 ns`, `98.8 ns` on Zen 3).

Across 1,000,192 `dudect` traces on `Intel Core i9-12900 (Alder Lake)` and `AMD EPYC-Milan (Zen 3)`, all nine positive kernel harnesses remained well inside $|t| < 4.5$ (cropped max $|t| <= 1.68$, raw $<= 1.87$, vs. $> 1,600$ on the early-exit negative control).

#figure(tbl((2.15fr, 0.85fr, 0.9fr, 0.65fr, 0.85fr, 0.9fr, 0.65fr),
  [Kernel (64 KiB / 256-coeff)], table.cell(colspan: 3)[AMD Ryzen AI 9 HX PRO 370 (Zen 5)], table.cell(colspan: 3)[AMD EPYC-Milan (Zen 3)],
  [], [Scalar], [AVX-512], [Speedup], [Scalar], [AVX2], [Speedup], table.hline(),
  [Keccak-f[1600] (`cpb` / `GB/s`)], [3.366], [0.634 (`3.15`)], [5.31×], [6.437], [1.623 (`1.48`)], [3.97×],
  [SHA-256 `SHA-NI` (`cpb` / `GB/s`)], [4.900], [0.830 (`2.41`)], [5.90×], [8.876], [1.320 (`1.82`)], [6.72×],
  [`GF(2^8)` Shamir mul (`cpb` / `GB/s`)], [14.66], [0.027 (`73.2`)], [537.2×], [28.29], [0.209 (`11.5`)], [135.2×],
  [`GF(2^8)` Shamir MAC (`cpb` / `GB/s`)], [14.32], [0.022 (`91.5`)], [653.7×], [27.66], [0.049 (`48.7`)], [561.0×],
  [`GF(2^128)` MulAcc (`cpb` / `GB/s`)], [16.97], [0.058 (`34.3`)], [291.0×], [32.97], [0.250 (`9.60`)], [131.9×],
  [`Tower128` BDOZ MAC (`cpb` / `GB/s`)], [14.23], [0.303 (`6.58`)], [46.9×], [24.21], [0.653 (`3.67`)], [37.1×],
  [ML-DSA fwd NTT (`ns` / `cyc`)], [809.3], [243.1 (`485`)], [3.33×], [1,197], [338.4 (`812`)], [3.54×],
  [ML-DSA inv NTT (`ns` / `cyc`)], [931.2], [209.8 (`419`)], [4.44×], [1,401], [322.9 (`775`)], [4.34×],
  [ML-DSA ptwise mul (`ns` / `cyc`)], [352.4], [56.7 (`113`)], [6.21×], [516.7], [98.8 (`237`)], [5.23×],
), placement: top, scope: "parent", caption: [Measured bare-metal SIMD throughput (`rdtsc` medians of 7 runs; Zen 5 at 2.00 GHz nominal TSC dispatching 512-bit `AVX-512` + `EVEX GFNI/VPCLMULQDQ` + `SHA-NI`; Zen 3 at 2.40 GHz dispatching `AVX2` + split-nibble `vpshufb` + `PCLMULQDQ` + `SHA-NI`).]) <simdbench>

== Protocol latency, unconditional proof sizes, and engineering trade-offs

@protobench summarizes single-host protocol benchmarks under unconditional `BciksJohnsonQrom128` (`Intel Core i9-12900 (Alder Lake)` and `AMD EPYC-Milan (Zen 3)`). For $K = 8$ signers under wire-v6 affine-monomial folding, `JortsPoseidon2` aggregates serialize to `291,352 B` and `16`-layer stateless `CorduroyPoseidon2` aggregates serialize to `446,254 B`; with verifier path deduplication and batched extension arithmetic, multi-shard `BciksJohnsonQrom128` verification reaches *`5.84–7.47 ms`* for 64 Jorts signers (`424,430 B`) and *`7.49–7.90 ms`* for `4 × 32 = 128` subnet signers (`1,589,980 B`) on `Intel Core i9-12900 (Alder Lake)`. On the custody signing path, pre-staged Mode 3B Jorts (`≈ 1.0 ms` local RAM, `≈ 81 ms` simulated WAN) and loopback QS-A (`≈ 0.56 ms`) reduce online signing to a single opening round, whereas `ConfidentialWireChannel` over ext4 WAL `fsync` reported `4.37 ms` (QS-A 2-of-3) and `5.21 ms` (QS-B 3-of-7). Conversely, full-hypertree dishonest-majority symmetric MPC remains minutes-scale (`38,400` Boolean Beaver triples per unbatched Keccak-f[1600], and distributed ZKBoo/SPDZ full-suite runs hit 600 s CI ceilings under 12 GiB memory caps), making batched PCG/OT acceleration ongoing engineering work.

#figure(tbl((2.05fr, 1.95fr, 1.85fr),
  [Operation (`BciksJohnsonQrom128`)], [Wire / setting], [Prove / verify], table.hline(),
  [Hem Jorts ($K=8$, Alder Lake)], [`291,352 B` (1 shard)], [4.90 s / 26.69 ms#super[†]],
  [Hem Corduroy ($K=8$, Alder Lake)], [`446,254 B` (1 shard)], [48.84 s / 35.33 ms#super[†]],
  [Hem Jorts ($K=64$, Alder Lake)], [`424,430 B` (checkpoint)], [3.95 s / 5.84–7.47 ms],
  [Hem Jorts ($4 times 32$, Alder Lake)], [`1,589,980 B` (4 subnets)], [4.96–7.47 s / 7.49–7.90 ms],
  [Jorts 2-of-3, Mode 3B], [RAM / sim. WAN], [≈ 1.0 ms / 81 ms],
  [QS-A 3-of-5 / ext4 AEAD], [loopback / `fsync` WAL], [≈ 0.56 ms / 4.37 ms],
), caption: [Protocol timings under unconditional `BciksJohnsonQrom128` (`Intel Core i9-12900 (Alder Lake)`). #super[†]Earlier unbatched verifier baseline prior to fast multi-proof verification passes; `K=64` and `4×32` rows reflect current optimized verification.]) <protobench>

== GPU kernels on RDNA 2 and unified-memory APUs

On an *AMD Radeon RX 6750 XT (RDNA 2)* (Vulkan 1.3.289, RADV 24.2.8, Wave32, zero scratch, raw-log SHA-256 `9b128cfa...4fe8`), one warmed transfer-inclusive audit run verified bit-exact parity and V5 `ExecutionReceipt`s across all six primitive shaders against `CpuReferenceBackend` (@gpubench); a subsequent twiddle-validated/buffer-scrubbed run measured `21.35 ms` (Poseidon2-12) and `35.38 ms` (Merkle). Alongside discrete RDNA 2, `qsag-accel` enumerates unified-memory APUs such as `AMD Radeon 890M (RDNA 3.5)` via `VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU` and wires the four VRAM-resident WHIR shaders (`air_row_group_{a,b}`, `whir_lde_merkle`, `whir_fold_sumcheck`) into `ProverArena`, though end-to-end whole-prover GPU speedups remain open pending full host-stage offload.

#figure(tbl((2fr, 0.7fr, 0.8fr, 0.7fr),
  [Primitive shader workload], [GPU ms], [CPU ms], [Ratio], table.hline(),
  [Poseidon2-12, 262,144], [27.38], [2,138.08], [78.1×],
  [Keccak-f[1600], 262,144], [29.67], [104.30], [3.5×],
  [Goldilocks NTT, $2^20$], [21.40], [246.24], [11.5×],
  [Ext2 coset LDE, $2^18 -> 2^20$], [15.96], [819.54], [51.4×],
  [Poseidon2 Merkle, $2^20$ leaves], [38.77], [7,930.78], [204.6×],
  [BDOZ dot, 262,144 pairs], [6.25], [68.90], [11.0×],
), caption: [Measured `AMD Radeon RX 6750 XT (RDNA 2)` primitive audit run (transfer-inclusive vs. single-threaded `CpuReferenceBackend`).]) <gpubench>

== Stake-weighted consensus application geometry

Real proof-of-stake networks consist of thousands of *independent stake-weighted single-key validators*, with threshold custody (`QS-B`) deployed optionally *inside* individual institutional operators as Distributed Validator Technology (DVT) rather than across the global validator set. Our updated consensus benchmarks (`mock_solana_alpenglow.rs`, `mock_ethereum_beam.rs`) model this architecture faithfully under unconditional `BciksJohnsonQrom128`:
- *Solana Alpenglow (`Rotor` / `Votor`, $N = 1,500$ stake-weighted single-key validators):* `Votor` collects 80% stake (`1,200` votes, 150 ms target) for 1-round fast finality or 60% (`900` votes, 400 ms target) for 2-round finality. Because `Compact1122` (`1,122 B`, 32-byte nodes, $> 128$-bit Grover preimage security) plus a 96-byte Votor header totals *`1,218 B` $<= 1,232$ B*, every PQ vote fits inside *one unfragmented QUIC MTU packet*—avoiding both the 64-bit Grover ceiling of 16-byte `Compact514` (`514 B`) and the 2-packet fragmentation penalty of `Full256Bit` (`2,338 B`), `ML-DSA-44` (`2,420 B`), or `JortsPoseidon2` (`4,328 B`). Periodic 64-signer `Hem` finality checkpoints (`424,430 B`) prove in `3.95 s` and verify in *`5.84–7.47 ms`* on `Intel Core i9-12900 (Alder Lake)` (`7.06–12.64 ms` on `AMD EPYC-Milan (Zen 3)`).
- *Ethereum Beam Chain (`4 × 32` subnet `BciksJohnsonQrom128` + optional `3f+1` `QS-B` DVT):* Four 32-validator `JortsPoseidon2` subnets (`128` validators total) aggregate into a `1,589,980 B` hierarchical `BciksJohnsonQrom128` proof that proves in `4.96–7.47 s` and verifies in *`7.49–7.90 ms` median on `Intel Core i9-12900 (Alder Lake)`*—meeting Beam's `< 8.0 ms` slot verification budget under unconditional Johnson soundness (`11.52–14.10 ms` on `AMD EPYC-Milan (Zen 3)`; mixed Jorts/Corduroy: `1,648,104 B`, `8.34–10.12 ms` on Alder Lake). Individual validators backed by `3-of-4` ($f=1$) or `5-of-7` ($f=2$) `HemDynamicShamirQuorum` DVT clusters emit identical 4,328-byte signatures, adding *`0 B`* of on-chain proof overhead.

= Proved scope and remaining bridges

- *`[CWYZ26]` algebra, `soundcalc` RBR convention, and Hem trace linkage:* `Qsag.CodingTheory` constructively mechanizes trivariate GS interpolation, division-free Hensel lifting over `Frac(UPoly F)`, dynamic `gcd` splitting, Hasse stratification, and persistent Johnson bounds (`cwyz26_affineMcaBound_of_nonExcluded`), and `CorduroyAndHemAirCompleteness` proves `StepOp256` XMSS/Corduroy witness extraction. Discharging `NonExcludedBound` (`[CWYZ26]` Lemma 4.7), connecting Rust's `populate_active_signer_rows` trace filler to `stepOp256TableOk`, raising unbounded-query `bits // 2` `whir_proximity_gaps` from `245 / 122` to $>= 256$ / $128$ nominal Grover bits via fold-round PoW grinding or a second independent affine-combiner rail (while bounded-query BBBV97 QROM already holds below $2^(-128)$ up to $q_"Hash" + 1 <= 2^56$), and proving concrete transcript flip / QROM commitment-extraction reductions remain open; recursive constant-size merging likewise requires an in-circuit WHIR verifier.
- *MIR and Poseidon2 KAT synchronization:* Short-nonempty `cSHAKE256` MIR refinement ($1 <= abs("cust") <= 31$) and live caller welds across all protocol crates are complete; multi-block sponge squeezing ($> 135$ B), complete caller-secret mediation, and rotating live `sponge.rs` constants from KAT-pinned $P_3 times.o M_4$ to Kronecker-swapped $M_4 times.o P_3$ + `V[0] = -64` + Jive feed-forward remain explicit engineering tasks.
- *RLWE, migration, and custody staging:* 24-challenge RLWE (`264`b / `132`b Grover), `Q192` Gaussian HVZK ($< 2^(-128)$), depth-15 dual-LPN ISD bounds, sealed-$bold(w)_1$ ML-DSA-44/65/87 abort privacy, and `BlindVC` QROM Fiat–Shamir soundness are mechanized; multi-round QROM extraction for `co_zk_mpc` migration, sub-25 s end-to-end SPDZ/ZKBoo runtime latency, and replacing trusted-dealer initial chain staging in `stage_committee_partitioned` / `stage_bft_shamir` with `HemSpdzSeedQuorum`-style MPC staging remain open.
- *Binary, GPU, and hardware boundaries:* `28/28` exported `qsag_asm_*` assembly kernels (`3,355` instructions) match live builds (`26/28` whole-kernel I/O refined in `McRefine`, `0` strict CT violations across `92` x86-64 and `65` AArch64 crypto symbols, `59/59` bare-metal Zen 5 `ptrace` cosimulation). Extending Lean's x86-64 decoder to `EVEX` `AVX-512` and Rust-mangled SIMD symbols, native AArch64 `ptrace` execution, SPIR-V shader-to-functional refinement, whole-prover GPU speedup profiling, hardware `DOIT` / `PSTATE.DIT` enforcement, and external cryptanalysis of experimental `ParallelSeededFts` remain separate obligations.

= Conclusion

Cut-the-Hash confines secret MPC hashing to height-independent leaf chains, powering the Pants suite, native `[Goldilocks; 4]` quorum-switching custody, and multi-chain post-quantum migration and credentials. Paired with `GoldilocksExt4` WHIR, `[CWYZ26]` monomial-shift affine folding, and unconditional Johnson-radius query schedules, Hem achieves sub-8 ms 128-validator verification on modern desktop silicon without capacity conjectures. Across `62,699+` `0 Classical.choice` Lean declarations, live-welded Aeneas MIR crates, refreshed ELF64 assembly refinements, and bare-metal Zen 5 `AVX-512` cosimulation, QSAG pairs aggressive post-quantum systems engineering with explicit, machine-checked boundaries.

#heading(numbering: none)[References]
#{
  set text(size: 7.4pt)
  set par(justify: false, leading: 0.38em, spacing: 2.6pt, hanging-indent: 1.6em)
  let refs = (
    [[ACFY25] G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT 2025.],
    [[AHU19] A. Ambainis, M. Hamburg, D. Unruh, "Quantum Security Proofs Using Semi-classical Oracles", CRYPTO 2019.],
    [[BBBV97] C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM J. Comput. 26(5), 1997.],
    [[BBCG+19] D. Boneh, E. Boyle, H. Corrigan-Gibbs, N. Gilboa, Y. Ishai, "Zero-Knowledge Proofs on Secret-Shared Data via Fully Linear PCPs", CRYPTO 2019.],
    [[BCGI+19] E. Boyle, G. Couteau, N. Gilboa, Y. Ishai, L. Kohl, P. Rindal, P. Scholl, "Efficient Two-Round OT Extension and Silent Non-Interactive Secure Computation", ACM CCS 2019.],
    [[BCIKS20] E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed–Solomon Codes", FOCS 2020.],
    [[BDH11] J. Buchmann, E. Dahmen, A. Hülsing, "XMSS – A Practical Forward Secure Signature Scheme Based on Minimal Security Assumptions", PQCrypto 2011.],
    [[BDOZ11] R. Bendlin, I. Damgård, C. Orlandi, S. Zakarias, "Semi-Homomorphic Encryption and Multiparty Computation", EUROCRYPT 2011.],
    [[BGIN19] E. Boyle, N. Gilboa, Y. Ishai, A. Nof, "Practical Fully Secure Three-Party Computation via Sublinear Distributed Zero-Knowledge Proofs", ACM CCS 2019.],
    [[BHKN+19] D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, "The SPHINCS+ Signature Framework", ACM CCS 2019.],
    [[BTA26] A. S. Bhati, S. Tariq, T. Ashur, "From Round Skipping to S-Box Skipping: Attacking Poseidon's Partial Layer via Subspace Restriction", IACR ePrint 2026/1692, 2026.],
    [[Can01] R. Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols", FOCS 2001.],
    [[CS25] E. Crites, A. Stewart, "On Reed–Solomon Proximity Gaps Conjectures", IACR ePrint 2025/2046, 2025.],
    [[CWYZ26] A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng, "Affine Combiners for Reed–Solomon Proximity Gaps", IACR ePrint 2026/2863, 2026.],
    [[DFM20] J. Don, S. Fehr, C. Majenz, "The Measure-and-Reprogram Technique 2.0: Multi-Round Fiat–Shamir and More", CRYPTO 2020.],
    [[DPSZ12] I. Damgård, V. Pastro, N. Smart, S. Zakarias, "Multiparty Computation from Somewhat Homomorphic Encryption", CRYPTO 2012.],
    [[FIPS202] NIST FIPS 202, "SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions", 2015.],
    [[FIPS204] NIST FIPS 204, "Module-Lattice-Based Digital Signature Standard", 2024.],
    [[FIPS205] NIST FIPS 205, "Stateless Hash-Based Digital Signature Standard", 2024.],
    [[FLNW17] J. Furukawa, Y. Lindell, A. Nof, O. Weinstein, "High-Throughput Secure Three-Party Computation for Malicious Adversaries and an Honest Majority", EUROCRYPT 2017.],
    [[FO99] E. Fujisaki, T. Okamoto, "Secure Integration of Asymmetric and Symmetric Encryption Schemes", CRYPTO 1999.],
    [[GKS23] L. Grassi, D. Khovratovich, M. Schofnegger, "Poseidon2: A Faster Version of the Poseidon Hash Function", AFRICACRYPT 2023.],
    [[GMO16] I. Giacomelli, J. Madsen, C. Orlandi, "ZKBoo: Faster Zero-Knowledge for Boolean Circuits", USENIX Security 2016.],
    [[HKRY23] A. Hülsing, M. Kudinov, E. Ronen, E. Yogev, "SPHINCS+C: Compressing SPHINCS+ With (Almost) No Cost", IEEE S&P 2023.],
    [[HP22] S. Ho, J. Protzenko, "Aeneas: Rust Verification by Functional Translation", ICFP 2022.],
    [[IKOS07] Y. Ishai, E. Kushilevitz, R. Ostrovsky, A. Sahai, "Zero-Knowledge from Secure Multiparty Computation", STOC 2007.],
    [[ILL89] R. Impagliazzo, L. Levin, M. Luby, "Pseudo-random Generation from One-Way Functions", STOC 1989.],
    [[KKH26] D. Krachun, S. Kazanin, U. Haböck, "Failure of proximity gaps close to capacity", IACR ePrint 2026/782, 2026.],
    [[KOS15] M. Keller, E. Orsini, P. Scholl, "Actively Secure OT Extension with Optimal Overhead", CRYPTO 2015.],
    [[KOS16] M. Keller, E. Orsini, P. Scholl, "MASCOT: Faster Malicious Arithmetic Secure Computation with Oblivious Transfer", ACM CCS 2016.],
    [[LFKN92] C. Lund, L. Fortnow, H. Karloff, N. Nisan, "Algebraic Methods for Interactive Proof Systems", J. ACM 39(4), 1992.],
    [[MRG26] S.-P. Merz, À. Rodríguez García, "Skipping Class: Algebraic Attacks exploiting weak matrices and operation modes of Poseidon2(b)", IACR ePrint 2026/306, 2026.],
    [[MU21] L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021.],
    [[RBV17] O. Reparaz, J. Balasch, I. Verbauwhede, "Dude, is my code constant time?", DATE 2017.],
    [[Sei18] G. Seiler, "Faster AVX2 optimized NTT multiplication for Ring-LWE lattice cryptography", IACR ePrint 2018/039, 2018.],
    [[SP800-185] NIST SP 800-185, "SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash", 2016.],
    [[Wie88] D. Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly 26(4), 1988.],
    [[Wui20] P. Wuille, BIP-350: "Bech32m format for v1+ witness addresses", 2020.],
  )
  for r in refs {
    par(r)
  }
}
