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
  text(size: 7.9pt, table(
    columns: cols,
    inset: (x: 3.8pt, y: 3.8pt),
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
    *Abstract.* Threshold custody of post-quantum signing keys must reconcile five competing demands: hash-based signature trees have deep circuits when evaluated naively inside multiparty computation (MPC); replicated secret sharing blows up combinatorially with committee size; stateful one-time leaves break catastrophically if switching signer quorums ever sign two messages on the same leaf; post-quantum signature batches consume tens of kilobytes per signer without bilinear pairings; and subtle flaws in share-release ordering, crash recovery, or instruction selection can silently invalidate paper proofs. We present *QSAG* (_Quorum-Switching AGgregation_ / _Quantum Succinct AGgregation_), an architecture and 14-package zero-dependency Rust and Lean 4.35 stack addressing these bottlenecks. First, a four-oracle *Cut-the-Hash* boundary confines secret MPC evaluation to message randomization, Winternitz chain steps, and FORS leaf derivations, running all public-key compressions, Merkle paths, and target-sum counter grinding in the clear so that sequential secret hash depth is independent of tree height. On this cut we build the *Pants* signing suite: stateless *Baggy* with the *Waistband* upper-layer cache, stateful *Jorts* gated by a crash-safe write-ahead latch (*BeltLatch*), two $(t,n)$ quorum-switching modes (*QS-A* and *QS-B*), and the Poseidon2 hypertree *Corduroy*, alongside matched-input threshold FIPS 205 SLH-DSA and standard-verifier-compatible FIPS 204 ML-DSA-44. Second, *Hem* aggregates batches of algebraic hash signatures via a degree-8 Sumcheck [LFKN92] and rate-escalating WHIR [ACFY25] over `GoldilocksExt4` ($p^4 approx 2^256$), incorporating affine Reed–Solomon combiners [CWYZ26] in monomial-shift form to eliminate the $Omega(n slash q)$ scalar folding floor with explicit per-fold, multi-round and commitment-extraction budgets. Third, surrounding custody protocols provide dealerless hierarchical derivation, Bech32m hybrid addresses, authenticated policy guards, active three-party zero-knowledge migration from legacy elliptic-curve keys, threshold credentials, and keyed accelerator receipts. Four assurance pillars pair constructive Lean protocol, POSIX-WAL, and unitary query models with Aeneas-extracted Safe-Rust MIR proofs, decoded x86-64/AArch64 ELF taint verification, and live differential and silicon gates. QSAG is an active research prototype: our mechanized results establish scoped properties of named models, extracted routines, and pinned kernel bytes rather than end-to-end linked implementation security or multi-round QROM Fiat–Shamir extraction (§8).
  ]
]

= Introduction

Moving institutional key custody to post-quantum primitives changes the geometry of threshold cryptography. For Schnorr and ECDSA, signing is a compact algebraic relation over a group scalar, and decades of multiparty protocols map directly onto that group structure. Hash-based signatures such as FIPS 205 SLH-DSA [FIPS205, BHKN+19] and XMSS [BDH11] offer a compelling post-quantum alternative: their security rests on symmetric tweakable hashes, and a threshold committee can emit standard signatures verified by unmodified external clients. Turning a hash-based signer into a practical, malicious-secure threshold system, however, runs into five distinct obstacles:

1. *Merkle height versus MPC depth.* A stateless hypertree hashes thousands of Winternitz chains into subtree roots and walks $d$ Merkle layers up to the public root. Evaluating that entire hash graph inside actively secure MPC turns public tree compression and counter grinding into millions of authenticated nonlinear gates.
2. *Committee scaling.* Conjunctive normal form (CNF) replicated secret sharing keeps three-party Boolean gates fast, but stores $binom(n, t-1)$ shares in general—6,435 shares at $(t,n)=(8,15)$, with 3,432 active shares per custodian. Moving to Shamir shares over binary towers or prime fields restores committee-size-independent per-seed storage, at the price of authenticated multiplication and offline preprocessing.
3. *Stateful leaves under quorum switching.* Stateful hash trees cut signature size and signing work dramatically by spending each one-time Winternitz leaf once. In a $(t,n)$ threshold deployment, however, an adversary can route concurrent signing requests to different $t$-subsets of custodians. Whenever $2t <= n+f$, two size-$t$ signing quorums need not intersect in an honest party, threatening to open two codewords on the same leaf.
4. *Post-quantum batch bandwidth.* Without pairing-friendly curves, $K$ post-quantum threshold signatures take $O(K)$ kilobytes on the wire. Compressing $K$ verifications into one succinct post-quantum proof requires an algebraic hash profile and a transparent polynomial commitment scheme whose soundness survives generic quantum search over Fiat–Shamir challenges.
5. *The gap between paper models and custody artifacts.* Even a sound threshold protocol fails if a faulted share is opened before its MAC check, if power loss rewinds a leaf counter while leaving a partial signature on the network, or if vector instructions leak shares through data-dependent control flow or memory addresses.

QSAG addresses these challenges around a single organizing principle: *secret shares should cross into cleartext at the earliest point where the underlying signature scheme already makes the derived digest public.* In *Cut-the-Hash* (§2), custodians hold shares of $"SK.seed"$ and $"SK.prf"$ and evaluate just four secret operations—message randomization, Winternitz chain starts and selected chain positions, and FORS leaf derivations—behind a durable reservation and MAC-verification barrier. Once those digests are authenticated and opened, every WOTS public-key compression $T_ell$, FORS Merkle root, internal tree hash, message digest $H_"msg"$, and target-sum counter grind executes publicly. Released chain nodes have secret hash depth at most $w$ regardless of hypertree height; message absorption and parallel wave count remain separate costs.

On top of this cut, QSAG builds the *Pants* signing suite (§2) and two complementary MPC engines (§3): a 256-lane bitsliced 2-of-3 replicated Keccak engine checked by distributed zero-knowledge proofs over $FF_(2^128)$ [FLNW17, BGIN19], and an arbitrary-threshold authenticated engine over Wiedemann binary towers [Wie88] and Goldilocks [GKS23] backed by Ring-LWE base OT, KOS/MASCOT extension [KOS15, KOS16], and dense dual-LPN pseudorandom correlation generators [BCGI+19]. Within Pants, *Baggy* provides stateless hypertree signing accelerated by *Waistband*, a verified cache of deterministic upper-layer child-root signatures; *Jorts* provides stateful signing guarded by *BeltLatch*, a fsynced write-ahead log and pairwise-MAC echo latch; *QuorumJorts* generalizes stateful signing to $(t,n)$ committees via *QS-A* ($binom(n,t)$ committee-partitioned subtrees permitting $t$-of-$t$ online signing when $2f > t$) and *QS-B* (one global tree with self-verifying bytewise Shamir shares gated by a $2q > n+f$ BFT latch certificate); and *Corduroy* instantiates the stateless target-sum hypertree over Poseidon2.

To compress signature batches, *Hem* (§4) proves parallel verification of `JortsPoseidon2` or `CorduroyPoseidon2` signatures in a 256-column multilinear trace using a degree-8 Sumcheck [LFKN92] and rate-escalating WHIR [ACFY25] over the quartic extension `GoldilocksExt4` ($p^4 > 2^(255.99)$), paired with Steiner-deduplicated `CanopyMultiProof` Merkle openings and disjoint signer bitmaps. Crucially, Hem replaces classical scalar Reed–Solomon folding $f + alpha g$—whose $Omega(n slash q)$ proximity floor and $abs(cal(D)_i)^2 L_i^7 slash p^4$ Johnson loss [BCIKS20] previously bottlenecked QROM query budgets at $2^21$—with degree-1 affine combiners [CWYZ26] in monomial-shift form. Over `GoldilocksExt4` and base-field cosets, the quadratic $(n slash q)^2$ term vanishes below $2^(-371)$, the per-fold witness bound exceeds $245.1$ bits with at most two overflow monomials per stage, and the scoped single-round portfolio expression admits $q_"Hash"+1 <= 2^56$. The newer multi-round compiler expression is below $2^(-128)$ at $Q+1 <= 2^40$, conditional on Hem transcript flip bounds and quantum commitment extraction (§4).

Surrounding signing and aggregation, QSAG provides custody protocols for dealerless hierarchical derivation, Bech32m hybrid addresses, BDOZ policy and velocity guards, active three-custodian ZKBoo migration from legacy elliptic-curve keys, threshold FIPS 204 ML-DSA-44 [FIPS204], threshold Poseidon2 OPRFs and blind credentials, and keyed accelerator receipts (§5).

*Contributions.*
- *Cut-the-Hash and the Pants suite (§2–§3):* A four-oracle public/secret boundary yielding height-independent sequential MPC depth for FIPS 205 SLH-DSA and custom WOTS+C [HKRY23] schemes, instantiated across stateless (*Baggy* with *Waistband*, *Corduroy*), stateful (*Jorts* with *BeltLatch*), and generalized $(t,n)$ quorum-switching (*QS-A*, *QS-B*) custody modes over bitsliced 2-of-3 RSS and $(t,n)$ binary-tower/Goldilocks SPDZ/BDOZ engines.
- *Succinct post-quantum aggregation with affine RS combiners (§4):* *Hem*, a $K$-to-$1$ aggregator combining 256-column Poseidon2 traces, degree-8 Sumcheck, rate-escalating WHIR over `GoldilocksExt4`, Steiner-deduplicated Merkle multi-proofs, and `[CWYZ26]` monomial-shift affine folding across five explicit classical and QROM query-accounting regimes.
- *Post-quantum custody lifecycle (§5):* Integrated protocols for dealerless HD key hierarchies, hybrid-pinned Bech32m addresses, MAC-guarded policy enforcement, actively checked 438-repetition ZKBoo key migration, dealerless threshold ML-DSA-44, and 2-of-5 Poseidon2 TOPRF credentials.
- *Four-pillar constructive verification (§6):* Constructive Lean 4.35 under the `{propext, Quot.sound}` axiom allowlist across protocol/POSIX-WAL/unitary-QROM models, Aeneas-extracted Safe-Rust MIR guards, decoded x86-64 and AArch64 ELF64 taint certificates, and live Rust-to-Lean differential, mutation, `ptrace` silicon cosimulation, and `dudect` gates over a 14-package zero-dependency Rust codebase.

== Related work and assurance scope

*Related work.* Threshold ECDSA protocols distribute arithmetic inversions and MtA checks over elliptic curves, whereas generic MPC translations of hash-based signatures evaluate the entire symmetric hash tree under secret sharing. Cut-the-Hash exploits the public internal structure of SPHINCS+ [BHKN+19], XMSS [BDH11], and checksum-free WOTS+C [HKRY23] so that secret MPC stops directly above the leaf chains. Our three-party honest-majority engine builds on replicated sharing [FLNW17] with sublinear distributed zero-knowledge checks over fully linear PCPs [BBCG+19, BGIN19], while our dishonest-majority path draws on SPDZ [DPSZ12], BDOZ [BDOZ11], interactive KOS/MASCOT OT extension [KOS15, KOS16], and silent dual-LPN PCGs [BCGI+19]. For batch verification, Hem follows the Sumcheck [LFKN92] and WHIR [ACFY25] IOPP paradigm rather than elliptic-curve SNARK recursion, upgrading its Reed–Solomon proximity step from scalar `[BCIKS20]` combiners to affine `[CWYZ26]` combiners; migration and credentials instead use MPC-in-the-head [IKOS07, GMO16]. On the verification side, we combine Lean 4 [MU21] protocol and binary models with Aeneas functional Rust translation [HP22] and empirical leakage testing [RBV17].

*Scope and threat-model boundaries.* QSAG is an active research prototype, and we separate what is proved in a formal model, what is checked on extracted or compiled code, and what is measured in single-host benchmarks. Our honest-majority protocols tolerate up to $t-1$ corruptions ($n >= 2t-1$) with abort; our dishonest-majority protocols tolerate up to $n-1$ corruptions with abort rather than guaranteed output delivery. Throughout every stateful component, custodians must durably commit and synchronize state transitions—and verify all gate and opening MACs—before releasing any secret-dependent share, ensuring that crashes or active faults burn capacity rather than reusing a leaf or leaking a key. Across our non-interactive proofs, challenge widths and repetition counts are sized against generic Grover search using unitary query bounds [BBBV97, AHU19, DFM20] mechanized in `ConcreteSecurityBudget.lean`, without claiming multi-round QROM Fiat–Shamir extraction. Likewise, the two Aeneas extraction crates live in separate workspaces and are direct Cargo dependencies: `qsag-verified` in core/policy/quorum and `qsag-whir-verified` in aggregation, and the active-slot simulation connecting Hem's 256-column Rust trace filler to its Lean signature verifier remains open. Section 6 summarizes the exact reach of each assurance pillar, and §8 consolidates all remaining proof, linkage, and deployment obligations.

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

The traits `SlhMpcOracles` and `PqHashMpcOracles` expose this narrow interface (@cutfig). The intended execution retains shared seeds and authenticates each cut opening under a durable context; complete caller mediation is a separate refinement obligation.

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
Fixing the digit sum eliminates WOTS checksum chains while guaranteeing strict componentwise incomparability between any two distinct valid digit vectors (`wotsC256_strict_incomparability`; `tooth_wotsc_without_target_sum_forges` constructs the single-hash forgery that appears if the sum check is omitted). Unlike variants that pin trailing digits to zero, `WotsCParams::V128` leaves all 128 digits free without implying 256 bits of conditional target-sum entropy. The accepted language has $[x^192](1+x+x^2+x^3)^128$ elements, approximately $2^251.01137$; uniform first-success grinding averages 31.7488 trials. Security reductions must distinguish raw hash evaluations from accepted-grind samples.

@params summarizes the six standard FIPS 205 SHAKE geometries alongside the Pants custody and Hem aggregation profiles. The two Hem geometries (`JortsPoseidon2` and `CorduroyPoseidon2`) are tailored to fit `qsag-agg`'s 24-variable trace bound and use wire encodings distinct from the standalone custody profiles.

#figure(
  {
    set par(justify: false)
    text(size: 7.1pt, table(columns: (1.7fr, auto, auto, auto, auto, auto, auto, auto, auto, auto), inset: (x: 1.6pt, y: 3.8pt), stroke: none,
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
      [Hem / Jorts], [32], [6], [1], [6], [—], [—], [4], [$2^6$], [—],
      [Hem / Corduroy], [32], [64], [16], [4], [8], [32], [4], [$2^20$], [—],
      table.hline(stroke: 0.6pt),
    ))
  },
  caption: [Signature geometries ($n$ = node bytes). Custom custody rows correspond to `CORDUROY_CUSTODY_128`, `BAGGY_TSW_128F`, and `JORTS_POSEIDON2` ($ell_1=128$, $S=192$; Baggy's FORS+C omits the $k$-th tree after grinding its index to zero). Hem rows show the `JortsPoseidon2` and `CorduroyPoseidon2` aggregation geometries.],
) <params>

== Baggy and Waistband

*Baggy* (`BaggySha3`, `BaggyPoseidon2`) is QSAG's stateless hypertree signer: $d$ layers of height-$h'$ Merkle subtrees over WOTS+C leaves whose bottom layer signs a FORS+C [HKRY23] key (grinding a public counter until the $k$-th tree index vanishes so only $k-1$ FORS trees open). Its pure-hash variant runs on the 256-lane bitsliced Keccak engine (§3.1).

Signing (`baggy_sign_mpc`) executes in three phases designed to prevent abort-based grinding attacks. First, custodians derive $R$ deterministically under MPC from $"SK.prf"$ and the message alone; a malicious party who aborts after seeing $R$ forces every retry onto the exact same $R$, hypertree path, and FORS indices. Second, because $R$ fixes all addresses across the hypertree, the FORS leaves and every subtree along the active path are evaluated together in a single level-by-level sweep—one PRF wave and three $F$ waves regardless of layer count $d$—followed by one distributed verification barrier before chain endpoints and FORS leaf hashes are opened. Third, custodians reconstruct the subtree roots and target-sum child digests in cleartext and open the selected intermediate chain nodes in one final round.

Because upper hypertree layers sign deterministic child roots rather than external messages, their leaves always open the same WOTS+C digits. *Waistband* (`WaistbandCache`) caches the public subtree leaves, authentication paths, and deterministic child-root signatures of the top $L$ layers, shaving those layers off the online MPC sweep while never caching message-binding bottom leaves. Because a corrupted cache entry would feed a false child root into the first uncached layer above it and trick a static key into signing a second codeword (`tooth_corrupted_intermediate_waistband_opens_second_ancestor_codeword`), Baggy enforces three invariants prior to opening any chain node: the cache is cryptographically bound to a single `BaggyKeyBinding` (public seed, root, and parameter digest); every cached signature along the active path is verified up to $"PK.root"$ before shares open; and a persistent `FirstSignedLedger` pins the unique child root each static keypair first signed. While Baggy requires no leaf-exhaustion counter, concrete security remains bounded by $Q_"max"$, and MPC preprocessing pools and `FirstSignedLedger` still require durable storage.

== Jorts and BeltLatch

*Jorts* is the 2-of-3 stateful signer: a single height-$h$ Merkle tree over $2^h$ one-time WOTS+C leaves (epochs), instantiated over either bitsliced Keccak (`JortsSha3`) or authenticated Poseidon2 (`JortsPoseidon2`). All three custodians participate in this schedule; the reconstruction threshold is 2 and the security model permits at most one malicious party.

To guarantee that crashes, network partitions, or malicious retries never open two distinct digit vectors on the same epoch, *BeltLatch* (`belt_latch.rs`) interposes a three-step barrier ahead of every share opening:
1. Each custodian persists $("epoch", "digest", "salt", "digits")$ through a synchronized write-ahead log before updating RAM, where the retry salt is sampled via a joint coin flip after the message is fixed and new epochs must lie within `MAX_EPOCH_JUMP` $= 64$ of the high-water mark (capping how many leaves a faulty proposer can skip).
2. On any retry for a latched epoch, a custodian replays its persisted record verbatim and rejects any mismatched digest or salt; if one custodian holds an unconfirmed local bind whose coin-flip provenance its peers cannot verify, the committee permanently burns the epoch rather than trusting a peer-supplied salt.
3. Custodians exchange pairwise cSHAKE256 [SP800-185] MAC echoes of the binding (keyed per pair so the third party cannot forge an echo between the other two); opening routines require the resulting `OpenPermit` tokens.

Jorts supports two online schedules behind the same latch. *Mode 3A* evaluates the 128 chains of the current epoch online, whereas *Mode 3B* pre-evaluates and verifies a sliding window of upcoming leaves in RAM so that online signing reduces to the coin flip, latch echo, and one share-opening round (falling back cleanly to Mode 3A under the latched salt after a reboot). Initial key generation evaluates all $2^h$ leaves under MPC ($2^h dot 128 dot 4$ lane-permutations), an offline ceremony suited to moderate tree heights. On disk, `durable_ledger.rs` maintains a two-slot MAC-authenticated snapshot under an exclusive genesis lock, sequenced across multi-resource ceremonies by `FsCeremonyJournal`. `PosixCrashWal.lean` models this storage stack across volatile page cache, drive write-back cache, torn sector writes, and POSIX `flock(2)` locks keyed by `OpenDescriptionId` rather than PID, proving epoch uniqueness across arbitrary crash/reboot traces (`reserve_before_sign_multi_crash_epoch_uniqueness`).

== QuorumJorts: generalized $(t,n)$ quorum switching

Scaling stateful signing to $(t,n)$ custodians introduces two challenges: online MPC latency when only $t$ signers are reachable, and cross-quorum equivocation when $2t <= n+f$. `qsag-quorum` eliminates online secret hashing by pre-staging shares of all three intermediate states along each base-4 WOTS+C chain: at signing time, custodians simply open the share corresponding to digit $d_j$, and the combiner hashes each reconstructed node forward to the public chain endpoint $F^(w-1)$, immediately catching any malformed share without online MAC checks. To prevent corrupted custodians from switching quorums to spend a leaf twice, `qsag-quorum` provides two complementary architectures:

*QS-A (`CommitteePartitionedJorts`).* The $2^h$ leaves are partitioned into $binom(n,t)$ disjoint contiguous ranges, one per $t$-subset of custodians, and each range's chain states are shared additively ($t$-of-$t$) exclusively among that subset. Any $t$ online custodians form a unique committee and sign from their dedicated range in a single round without waiting for offline peers. For up to $f <= t - 1$ corruptions—regardless of total $n$, even when $2f > t$—every committee contains at least one honest custodian whose durable latch locks each leaf to a single message, and no outside coalition holds shares for that range. In exchange, per-committee leaf capacity scales down by $binom(n,t)$, online signing aborts if a corrupt committee member withholds its share, and the public leaf index reveals which $t$-subset signed (`qs_a_leaf_index_identifies_committee`).

*QS-B (`BftShamirJorts`).* All custodians share a single global tree whose chain states are $(t,n)$-Shamir shared bytewise over $FF_(2^8)$ using independent polynomials per step—a constant 12,288 bytes per leaf per custodian for any $(t,n)$. Before releasing shares for an epoch, each custodian requires a `LatchCertificate` carrying pairwise-MAC acknowledgements of a single binding from $q$ custodians satisfying
$ 2q > n + f. $
By quorum intersection, any two certificates for the same leaf overlap in at least $2q - n >= f + 1$ custodians, at least one of whom is honest and refuses to certify a second message (`beltLatch_quorum_intersection_global_uniqueness`; `tooth_under_threshold_latch_quorum_switches_double_sign` exhibits the double-signature attack when $2q <= n + f$). Availability of the latch requires $n - f >= q$, yielding $n >= 3f + 1$ (`beltLatch_safe_and_live_iff_n_ge_3f_plus_1`), e.g., $(n,f,q) = (7,2,5)$ with decoupled signing threshold $t$. Currently, initial chain staging (`stage_committee_partitioned`, `stage_bft_shamir`) runs as a trusted dealer routine rather than a distributed MPC ceremony, and raw `party_node` framing supplies authentication without confidentiality; `ConfidentialWireChannel` adds encrypted transport.

== Corduroy, bit identity, and few-time signatures

*Corduroy* instantiates the stateless target-sum hypertree over the algebraic Poseidon2 tweakable hash (`CORDUROY_CUSTODY_128`), signed via the authenticated-share Poseidon2 engine (§3.2). Its companion profile `CorduroyPoseidon2` ($k=32$, $a=8$ FORS below a $d=16$, $h'=4$ hypertree) supplies the stateless signature format arithmetized inside Hem (§4).

*Matched-input bit identity.* For FIPS 205 SLH-DSA across all six SHAKE parameter sets, `thresholdSlhSign_eq_slhSignInternal` and `rss_thresholdSlhSign_eq_slhSignInternal` prove that threshold evaluation emits the exact same bytes as the standalone FIPS 205 specification whenever the cut oracles match the key (`MatchesKey`, discharged constructively for RSS Keccak and, for custom profiles, across both RSS Keccak and shared Shamir Poseidon2 via `rss_thresholdPqHashSign_eq_evalSingleSign` and `shamir_poseidon2_shared_thresholdSign_eq_evalSingleSign`), with strict domain separation between pure and prehashed modes (`pure_vs_preHash_disjoint`, `preHash_downgrade_rejected`). Analogous pointwise equalities hold for Baggy, 2-of-3 Jorts, and QS-B (and per-committee schedules in QS-A): given identical key material, parameters, leaf/message, and hedging randomizer, successful threshold outputs match single-signer outputs byte-for-byte. Differential and 43 built-in known-answer tests cross-check `Fips205.lean` against `fips205.rs`. Inside upper hypertree layers, omitting external $(R, mu)$ from internal node hashing makes child-root grinding deterministic, so any fixed internal keypair reveals at most one codeword (`stateless_leaf_reuse_identical_wots_chains`).

*Few-time signatures.* For ultra-compact custody receipts, `FrontierSumFts` maps a randomized digest bijectively onto a prefix-free binary-tree antichain of length $L$ and height $<= h$ paired with base-$w$ chain offsets summing to $S$, factoring exact `U384` ranking into $M(h,w,L,S) = N(h,L) dot D(L,S)$ (`frontierAntichain_paths_prefixFree`, `frontierSumFts_rank_unrank_bijection`). Ranking runs on public digests, while secret leaf expansion is guarded by a durable burn journal (`FtsEpochGuard`). In @ftsprofiles, the 16-byte-node compact profiles provide 128 classical bits (64 Grover bits) of node-preimage width, whereas `Full256Bit` uses 32-byte nodes and a 256-bit rank for single-use `PQ128` deployment (`ConcreteSecurityBudget.lean` includes the negative witness for a narrower 122-bit rank). Separately, experimental `ParallelSeededFts` builds height-independent few-time trees over a 48-round $x^7$ Davies–Meyer SPN on $FF_(2^128)^2$ ($gcd(7, 2^128 - 1) = 1$), achieving constant sequential MPC depth $D_"parallel" = 48(1+w) + 8 = 296$ at `CUSTODY_H10_W5` ($h=10, w=5, L=68, S=136$) with mandatory pre-open MAC checks and single-use epoch journals (`parallelSeededFts_mpc_depth_independent_of_height`).

#figure(tbl((1.5fr, auto, auto, auto, auto, auto, auto, auto),
  [Profile], [B], [$n$], [$h$], [$w$], [$L$], [$S$], [Uses], table.hline(),
  [Compact514], [514], [16], [14], [5], [31], [62], [1],
  [Compact770], [770], [16], [15], [5], [47], [118], [2],
  [Compact1314], [1,314], [16], [15], [5], [81], [162], [2],
  [Full256Bit], [2,338], [32], [8], [5], [72], [144], [1],
), caption: [`FrontierSumFts` wire profiles ($n$ = node bytes; Uses = enforced `max_safe_uses`).]) <ftsprofiles>

= Secret sharing, preprocessing, and release ordering

== Bitsliced 2-of-3 RSS and binary-tower Shamir

While CNF replicated sharing requires $binom(n, t-1)$ total shares ($6,435$ at $n=15, t=8$), three-party committees ($t=2, n=3$) sit at the sweet spot $binom(3,1) = 3$. For this common custody quorum, `Rss256Engine` implements a 256-lane bitsliced 2-of-3 Keccak-f[1600] engine [FLNW17] tolerating one malicious party with abort. Each wave evaluates up to 256 independent sponges in lockstep by packing bit $i$ of all 256 lanes into one AVX2/NEON register, turning all 1,600 #box[$chi$-layer] AND gates per round into single register operations. Outputs remain sealed until a post-wave verification barrier hashes the entire gate transcript, runs a commit-then-open coin flip bound to that digest, and verifies all multiplications via a sublinear distributed zero-knowledge proof [BGIN19] over $FF_(2^128)$ under two independent challenges using carry-less `PCLMULQDQ` / `VPCLMULQDQ` / `PMULL` kernels. Any check failure permanently poisons the engine. `BaggyAndRss256Security.lean` proves perfect one-corruption view privacy (`rss256_one_corrupt_perfect_view_privacy`), $(2 deg)^2 slash 2^256$ soundness for fixed prechallenge error and independent transcript-bound challenges (`rss256_post_wave_two_challenge_bgin19_soundness`), and terminal poison absorption (`rss256_sticky_poison_terminal_absorption`), paired with `#tooth` witnesses for mask-key misassignment, premature challenge disclosure, and non-sticky error handling.

To scale beyond small CNF committees without key-share blowup, QSAG embeds Shamir secret sharing in a Wiedemann binary tower [Wie88]:
$ cal(T)_0 = FF_2, quad cal(T)_1 = cal(T)_0[x_0] slash (x_0^2 + x_0 + 1), $
$ cal(T)_k = cal(T)_(k-1)[x_(k-1)] slash (x_(k-1)^2 + x_(k-2) x_(k-1) + 1), $
reaching $cal(T)_3 = FF_(2^8)$ (up to 255 nonzero party evaluation points; `zero_eval_point_leaks_secret_term` pins the rejection of $x_i = 0$) and $cal(T)_7 = FF_(2^128)$ for MAC tags (`embedTowerChain_injective`, `towerMul_inv`). Per-seed storage is independent of committee size: `ShamirSeedShare256` stores 256 GF256 bit shares; authenticated representations add MAC arrays. RSS stores primary/secondary seed and PRF shares plus PRG state. Sessions also allocate preprocessing and transcripts.

== Algebraic S-boxes and dealerless preprocessing

For algebraic profiles, QSAG uses width-12 Poseidon2 [GKS23] over the Goldilocks prime $p = 2^64 - 2^32 + 1$, comprising $4 dot 12 + 22 dot 1 + 4 dot 12 = 118$ power-7 S-boxes per permutation. Given preprocessed, MAC-authenticated Shamir shares of random mask powers $([r], [r^2], ..., [r^7])$, custodians open $y = x - r$ (or $x + r$), check its batched SPDZ MAC over `GoldilocksExt2`, and evaluate $[x^7]$ locally in one opening round via the binomial identity (`power7BinomialEval_eq_sbox7`, `evalSharedPow7Binomial_complete`):
$ [x^7] = sum_(k=0)^7 binom(7,k) (-1)^k y^(7-k) [r^k]. $
Canonical 256-bit byte conversion at unrevealed internal steps remains the dominant algebraic cost, consuming 760 authenticated Boolean Beaver triples per dual-adder reduction.

*Lattice base OT and correlation generation.* Dealerless preprocessing starts from Ring-LWE base OT over $R_q = ZZ_(12,289)[X]/(X^1024+1)$ with centered binomial noise $eta=1$. The bound $norm(e_1 r_c-e_2 s_R+e_3)_infinity <= 2049 < 3072=floor(q/4)$ gives exact decryption (`rlwe1024_ot_decrypt_exact`). Sender messages bind randomness through Fujisaki–Okamoto re-encryption. Receiver OR-Sigma uses 13 jointly hashed challenges in $cal(C)={plus.minus X^k:0<=k<1024}$: 2,048 choices, 11 bits each, 143 joint bits. The nominal exhaustive-search exponents are 143 classical and 71.5 generic Grover, not a 128-bit quantum-active OT guarantee.

For power-of-two degree and odd $q>=3$, `signedMonomial_challenge_set_pairwise_invertible` proves $(c-c')g=2$ and unit differences. Short isometric extraction proves $A s_"iso"+e_"iso"=(1-c^(-1)c')u$, with infinity norms at most 6140 at $q=12289$; the secret-or-short-SIS dichotomy has bound 6142. This is a relaxed witness relation. The live sampler has $sigma=700$, mask box $[-3072,3071]$, response box $[-3070,3069]$, and acceptance $min(1, exp((norm(y)^2-norm(z)^2)/980000)/M)$ with $M=exp(3114493/980000) approx 24$. A bimodal cosh sampler with $M approx 1.08$ is not the inspected implementation.

Above base OT, interactive KOS extension [KOS15] commits OT columns before squeezing consistency challenges and compresses 384-bit correlations into 128-bit pads via a seeded 2-universal leftover-hash matrix [ILL89] (`kos_interactive_check_sound`). High-volume correlations come from a dense dual-LPN PCG (`pcg_dense.rs`, wire v3) [BCGI+19]: 64 regular-noise GGM trees of depth 14 or 15 with 256-bit nodes, a dense expand-accumulate parity-check matrix, single-use `SeedBurnTracker` enforcement, and a two-pass active SPCOT consistency tag check that rejects fixed discrepancies with error $approx 2^(-226)$ per directed pair at depth 15. Multi-party arithmetic and power tuples ($n >= 3$) use MASCOT multiplication and batch sacrifice [KOS16] (`spdz_triple_sacrifice_sound`, `pow7_sacrifice_sound`).

== Authenticated booleanity, release ordering, and resharing

In characteristic 2, bit shares are checked via the Frobenius identity $b^2 + b = 0$ (`towerFrobenius_eq_zero_iff_bit`), evaluated over authenticated shares so an attacker cannot inject a canceling offset (`frobenius_unauthenticated_offset_break`, `verifySharedDkgFrobenius_sound`). The authenticated engine interfaces require a strict *commit → MAC-verify → open* discipline: as `open_before_mac_leaks_faulted_cut` demonstrates, opening a candidate share before verifying its MAC leaks secret-dependent fault residuals even when the session subsequently aborts. BDOZ Boolean paths use paired `Tower128` MACs ($2^(-256)$ for fixed prechallenge error and independent hidden MAC keys, `bdoz_2lane_mac_soundness`), while Goldilocks paths use `GoldilocksExt2` MACs ($p^(-2) < 2^(-127)$, `spdz_batch_mac_soundness`). Both provide security with abort (`honest_party_never_slashed`; culprit attribution in `protocol_realizes_idealTsig_id_abort` enters as an explicit hypothesis). Finally, `dkg.rs` provides two-round commit-then-open DKG, proactive share refresh, and cleartext-free $(t,n) -> (t',n')$ resharing with explicit old-share zeroization (`reshare_from_shares_without_cleartext_recombines_secret`).

= Hem: succinct $K$-to-$1$ aggregation

== Multilinear trace and `GoldilocksExt4`

Even when threshold signing produces standard-sized hash signatures, transmitting $K$ post-quantum signatures scales linearly in $K$. *Hem* (`qsag-agg`) compresses $K$ `JortsPoseidon2` or `CorduroyPoseidon2` verifications into a single succinct argument over a 256-column multilinear Goldilocks trace: 512 rows per Jorts signature and 8,192 rows per Corduroy signature, packing up to 128 or 8 signers per shard within the commitment scheme's 24-variable ($2^24$ flattened-element) cap. Each row encodes one width-12 Poseidon2 permutation (inputs and 118 $x^7$ S-box outputs), a 44-limb step-machine state before and after the step, and selector columns driven by a fixed opcode schedule for digest unpacking, WOTS+C chain walks, endpoint compression, and Merkle path verification. Full 256-bit digests are represented losslessly as four 56-bit limbs plus one 32-bit limb (`Digest5`, all strictly below $p$, proved collision-free in `digest5FromBitVec256_injective`).

All verifier challenges, OOD points, and folding scalars are drawn from the quartic extension `GoldilocksExt4`,
$ E = FF_p [v] slash (v^4 - 7), quad q = abs(E) = p^4 > 2^(255.99), $
constructed as a quadratic tower over `GoldilocksExt2` (`mul_inv_cancel` in `Aggregation.lean`). Moving from a 128-bit quadratic extension to `GoldilocksExt4` is essential for post-quantum soundness: under unitary QROM Grover search (`qrom_fiber_search_bound`), an adversary making $q_"Hash"$ random-oracle queries amplifies a single-round interactive soundness error $epsilon$ by up to $8(q_"Hash" + 1)^2$. Over a quadratic extension ($p^(-2) approx 2^(-128)$), any single-challenge check hits a 64-bit quantum ceiling (`ext2_error_denominator_cliff`), whereas $p^4 approx 2^256$ provides the 256-bit denominator needed to sustain 128-bit QROM margins at high query budgets (`ext4_error_denominator_bound`).

== Sumcheck, rate-escalating WHIR, and Canopy commitments

Proving that every row constraint vanishes reduces to a degree-8 Sumcheck [LFKN92] (a degree-1 #box[random-$tau$] equality kernel multiplying degree-7 Poseidon2 gates, batched across constraint columns by powers of $gamma$), coupled with an ungated inter-row shift claim equating each step's output state to the next row's input state. The resulting multilinear column evaluations are opened via multi-stage rate-escalating WHIR [ACFY25]: rather than folding a high-rate Reed–Solomon codeword passively at fixed rate across every round, each stage folds up to $s_i <= 6$ variables and re-encodes the folded polynomial over shifted base-field two-adic cosets $cal(D)_i = 7 dot H_i subset FF_p$ at escalating blowups $B = 4, 16, 64, 256$ ($rho_i = 1 slash B_i$). At $ell = 20$ ($K = 8$ Jorts signers), intermediate evaluation domains stay bounded by $2^19$ and $2^18$.

Before any folding challenges are squeezed, each committed stage oracle is pinned at two independent out-of-domain Kronecker points $"pow2"(z_"ood") in E^m$ (driving list-collision probability to $binom(L_i, 2) (abs(cal(D)_i) slash p^4)^2 < 2^(-448)$), and opened coset fibers fold into shift claims batched into the next stage (`prechallenge_fold_forgery_attack` and `terminal_check_omission_unsound` capture the attacks enabled if commitment order or terminal verification is relaxed). Stage oracles are committed in Merkle trees over a precomputed `CANOPY_MIDSTATE` using 4-way SIMD Keccak and opened via `CanopyMultiProof`—canonical bottom-up Steiner-deduplicated multi-proofs that transmit each shared internal sibling exactly once (`verifyCanopyMultiproof_exact_sibling_count`, `verifyCanopyMultiproof_binding`)—preceded by 16-bit cSHAKE256 stage work under `QSAG.PCS.POW2/v1`; `maxQueryCap = 512`.

== Breaking the scalar folding floor with affine RS combiners

A subtle coding-theoretic bottleneck arises when instantiating WHIR for 128-bit QROM security. Classical Reed–Solomon proximity-gap theorems [BCIKS20] batch and fold two functions $f, g : cal(D)_i -> E$ via a *scalar* linear combination $f(z) + alpha g(z)$ ($alpha <- E$). Even in unique decoding, scalar combiners suffer an unconditional block-length floor of $Omega(n slash q)$ ([CWYZ26], Prop. 6.1), and up to the Johnson radius $1 - sqrt(rho_i) - eta_i$, `[BCIKS20]` Theorem 4.1 incurs a per-stage commit-folding error of $s_i abs(cal(D)_i)^2 L_i^7 slash p^4$. Over `GoldilocksExt4` at $abs(cal(D)_0) <= 2^26$ and list size $L_0 <= 2^9$, that numerator sacrifices $80$ to $119$ bits, leaving only $137$–$176$ interactive bits before QROM Grover amplification. Consequently, scalar folding previously capped `.hemExt4WhirPq128` at $q_"Hash" + 1 <= 2^21$ random-oracle queries (`tooth_hem_ext4_single_challenge_qrom_folding_ceiling`), even as all other 11 `PQ128` profiles in `ConcreteSecurityBudget.lean` reached $2^56$.

To remove this bottleneck, Hem (`pcs/affine.rs`, wire v6) adopts the *affine Reed–Solomon combiners* introduced by Chiesa, Weissenberg, Yogev, and Zheng [CWYZ26] (`ia.cr/2026/2863`). Given equal-degree words ($deg F, deg G <= d - 1$), each binary fold samples $(theta, alpha, beta) <- E^3$ and forms
$ w_(theta, alpha, beta)(z) = g(z) + (alpha + beta z)(f(z) + theta g(z)), $
analyzed under a relaxed mutual correlated agreement (MCA) condition permitting at most $s = 1$ discarded coordinate per fold (shifting fiber-query hit probability by at most $1 slash n$ per fold). Both changes are strictly necessary, and `AffineProximityGaps.lean` mechanizes constructive `#tooth` witnesses for both lower bounds: scalar combiners incur $>= (1 + floor((n - A) slash (s + 1))) slash q = Omega(n slash q)$ for every fixed loss $s$ (`tooth_scalar_combiner_linear_n_over_q_floor`, Prop. 6.1), while demanding $s = 0$ exact inheritance on $S_(alpha, beta)(P)$ lets an adversary align the line root $z_0 = -alpha slash beta$ with an arbitrary disagreement point and reverts affine combiners to $Omega(n slash q)$ (`tooth_affine_combiner_zero_loss_linear_floor`, Prop. 6.2).

Specializing `[CWYZ26]` Theorems 4.8 and 5.1 to `GoldilocksExt4` and Hem's base-field cosets $cal(D)_i subset FF_p subset E$ yields three concrete wins:
1. *Subfield-cheap verifier folding:* Because every coset coordinate $z = x_k^2$ lies in the prime base field $FF_p$, evaluating $alpha + beta z$ inside `fold_duet_affine_ext4` costs one `mul_base` (four $FF_p$ multiplications rather than sixteen).
2. *Quadratic $(n slash q)^2$ collapse:* Because $q = p^4 approx 2^256 >> n^2 <= 2^52$, the nonpersistent $(n slash q)^2$ algebraic-geometry error term in `[CWYZ26]` Theorem 4.8 collapses below $2^(-371)$. Across every deployed stage of $ell = 20$ and $ell = 24$, the leading persistent error reduces to $(ell + 2 ell_0) slash p^4 < 1906 slash p^4 < 2^(-245.1)$. These are per-fold witness bounds; round batching and fold counts enter the aggregate numerators $[4182,1644,824,489,792]/p^4$, totaling $7931/p^4$. The earlier $2^56$ portfolio limit is scoped single-round arithmetic. Stage PoW does not multiply every folding, binding or OOD guarantee.
3. *Two-slot degree fixed point (`Monomial-Shift WHIR`):* Equal-degree affine folding raises degree by $+1$, yet binary coset folding halves degree at every step ($d |-> floor(d slash 2) + 1$). Starting from $d_0 = 2^ell - 1$ (or $2^ell$ after Round-0 batching), the degree sequence satisfies the invariant
   $ d_s <= 2^(ell - s) + 1 quad "for " 1 <= s <= ell $
   (`affine_fold_degree_le_pow2_add_one`), accumulating *at most two overflow monomials* ($c_(2^m), c_(2^m + 1)$) regardless of how many variables are folded. Converting the witness once into monomial basis eliminates intermediate Möbius transforms, turns multiplication by $Y = Z^2$ into a zero-multiply pointer shift bridged per fold by five linear-functional scalars (`sigma_even`, `tau_01`, `tau_10`, `c_F`, `c_G`), and reuses the exact power-of-two stage NTT by adding the two overflow monomials on the same coset without enlarging evaluation domains or Merkle tree depths. Similarly, Round-0 batching of $S <= 16$ committed trace polynomials applies the equal-degree combiner to the first pair and an asymmetric cascade $W_(i-1)(z) + (alpha_i + beta_i z) W_i(z)$ to $i >= 2$, bounding total batch degree growth by $+1$.

== The five-regime query ladder

`WhirSecurityRegime` parameterizes stage query counts directly from $log_2 B$ (@regimes). The `Habr24*` regimes assume conjectural capacity-proximity agreement $rho_i = 1 slash B_i$ (whose scalar $Omega(n slash q)$ floor is likewise eliminated by affine folding), whereas the `BciksJohnson*` regimes rely solely on the proven Johnson bound $sqrt(rho_i) + eta_i$ at roughly twice the query count: `BciksJohnsonClassical128` uses $ceil(256/log_2 B)+1$ queries, while `BciksJohnsonQrom128` adds two slack queries per stage ($ceil(512 slash log_2 B) + 2$) so all 46 non-exhaustive canonical stages across $2..=24$ variables carry an explicit upward-rounded dyadic `[CWYZ26]` Theorem 4.8 witness (`checkWhirAffineWitness`, per-fold affine witness error $< 2000 slash p^4$) and $> 256$-bit unconditional query error.

#figure(tbl((2.35fr, 1.85fr, 1.6fr, 0.85fr),
  [Regime], [Queries per stage], [$q$ at $B=4,16,64,256$], [Round bits], table.hline(),
  [`Habr24Classical128`], [$ceil(112 / log_2 B)$], [56, 28, 19, 14], [128 / 64],
  [`Habr24Interactive128`], [$ceil(128 / log_2 B)$], [64, 32, 22, 16], [144 / 72],
  [`BciksJohnsonClassical128`], [$ceil(256 / log_2 B)+1$], [129, 65, 44, 33], [144 / 72],
  [`Habr24Qrom128` (default)], [$ceil(256 / log_2 B)$], [128, 64, 43, 32], [272 / 136],
  [`BciksJohnsonQrom128`], [$ceil(512 / log_2 B)+2$], [258, 130, 88, 66], [272 / 136],
), placement: top, scope: "parent", caption: [Hem WHIR query-accounting regimes. Round bits show classical query-plus-16-bit-PoW budgets and their Grover halves (`classical_fs_round_bits`, `qrom_grover_round_bits`). Stage 4 ($B=256$) activates only at 23–24 variables.]) <regimes>

By default, `verify_aggregate` accepts only the two QROM-128 regimes (`meets_qrom_128_floor`). Weaker classical regimes require `verify_aggregate_with_regime` with an explicit expectation; the regime byte is transcript-bound. The 272/136 figures are nominal query-plus-work round-search accounting. `MultiRoundFsQrom.lean` proves adaptive unitary oracle-dependent measure-and-reprogram and multi-round union bounds. Its `multiRoundFsQrom_budget_bound` is below $2^(-128)$ for $Q+1<=2^40$, five 256-bit Merkle roots, and the deployed 24-variable geometry; the same expression fails at $2^41$. Turning this arithmetic into Hem acceptance security requires its concrete transcript flip bounds and quantum commitment-extraction reduction.

== Disjoint merging and mechanized coverage

Within a single aggregation call, multiple shards share one Round-0 Merkle-Canopy tree and settle all column evaluations in one batched WHIR opening. Across independently generated proofs, `merge_aggregates` forms a binary tree (up to `MAX_MERGE_TREE_DEPTH` $= 16$) whose internal nodes concatenate child proofs while enforcing disjoint `SignerBitmap`s (`popcount_union_disjoint_eq_add`, `overlapping_merge_rejected`), matching regimes, and canonical child ordering without a recursive SNARK verifier circuit; proof size therefore amortizes sublinearly within a prover batch and scales linearly across merged batches.

On the formal side, three Lean modules cover complementary slices of Hem. `Aggregation.lean` formalizes `GoldilocksExt4`, the 5-regime schedules, the multi-stage WHIR + OOD + PoW + merge-tree verifier (`succinct_aggregation_knowledge_soundness`, `succinct_merge_tree_knowledge_soundness`), and a concrete 2-stage Reed–Solomon trace-decoding instance (`rsSbox7TraceArith_lawful`). `AffineProximityGaps.lean` proves the two-slot degree fixed point, two-point Vandermonde line pruning (`committed_polynomial_pair_bad_lines_le_choose2`), the Prop. 6.1 and Prop. 6.2 lower-bound `#tooth` witnesses, an elementary constructive Welch–Berlekamp affine proximity-gap theorem for $delta < (1 - rho) slash 3$ (`welch_berlekamp_affine_proximity_gap`), and finite Theorem 4.8 witness checks. Constructive Guruswami–Sudan interpolation produces nonzero Hasse-vanishing coefficient witnesses; arbitrary-multiplicity factor and formal-polynomial list bounds are proved over decidable fields. The interpolation-to-Taylor multiplicity bridge and full trivariate affine explainer remain necessary for full Johnson-radius mechanization. `SuccinctAggregationIop.lean` proves completeness and Type-valued hash-break extraction for the packed 4-limb signature verifier (`aggNativeSig_completeness`, `aggNativeSig_wots_merkle_soundness`, `forsNodeAddr_injective`), exactness of the 256-column Poseidon2 permutation and shift constraints (`stepOp256_groupA_exact`, `stepOp256_shift_iff`), and `CanopyMultiProof` binding. Connecting active-slot satisfaction of the 256-column step table (`populate_active_signer_rows`) to signature acceptance—currently proved for a separate row-committed layout (`trace_satisfies_constraints_iff_all_k_sigs_valid`) and for inactive padding slots (`stepOp256_inactive_table_complete`)—remains open (§8).

= Custody, migration, and credentials

*Dealerless HD derivation (`qsag-hd`).* Custodians derive root shares, child rekeys, MAC keys, and opening masks from a one-time subset-seed ceremony in an honest-majority model ($n >= 2t-1$, security with abort). `PiHdCommitInventory` builds a Merkle-committed watch-only table of independent child public keys (whose batch enrollment reveals selected child seeds without exposing parent or subset seeds). Experimental `PiHdLinearModule` supports local public-shift derivation under $bold(t) = bold(A) bold(s)_1 + bold(s)_2 mod 8,380,417$ with secret-derived chain codes, fresh per-child MAC keys, and a durable poison journal that quarantines any faulted derivation family.

*Addresses (`qsag-addr`).* External identities use a 67-character Bech32m encoding for the three-character HRP `qsp`, using [Wui20] checksum (`0x2bc830a3`) over versioned cSHAKE256 or Poseidon2 script/key commitments (`bech32m_rejects_bech32_and_detects_single_subst`). `SingleOrThreshold` gives both custody modes the same identity encoding; surrounding registries and messages can still disclose the mode, while `HybridPinnedEnvelope` cryptographically pins the post-quantum key inside hybrid classical/PQ envelopes so an attacker cannot substitute a weaker companion key.

*Policy guards (`qsag-policy`).* The policy authorization entrypoints use a pairwise 2-lane BDOZ circuit to check suite and chain IDs, recipient allowlists, per-transaction and rolling-window velocity caps, timestamp bounds, self-approval bans, and tiered quorum thresholds behind a committed MAC barrier, minting an `AuthorizedSignReleaseToken` upon acceptance. Monotonic nonce and session watermarks ride inside a MAC-authenticated snapshot that callers must persist atomically alongside an external generation fence and trusted epoch clock.

*Active co-ZK key migration (`qsag-migrate`).* To migrate legacy `secp256k1` (HASH160 and x-only Taproot with explicit $y$-parity pinning) and SLIP-0010 `Ed25519` accounts to a `QsagAddress` without exposing the legacy spending key to any single party, three custodians run `co_zk_mpc`, an actively checked distributed prover for 438-repetition mixed-domain ZKBoo [GMO16]:
$ (2 / 3)^438 < 2^(-256), $
giving interactive error below $2^(-256)$ and nominal generic Grover search exponent 128.1068, with concrete FS/QROM extraction separate (`zkboo_438_gt_two_pow_256_margin`). Over confidential authenticated pairwise channels, every Boolean AND and prime-field multiplication is batch-verified via coin-flipped inner-product sacrifices [BBCG+19] before any wire, base-conversion residual, view commitment, or challenged repetition opens, and circuit outputs undergo a shared zero test (`all_outputs_zero`) before reconstruction. Large-prime multiplication checks have error $<30/p<2^(-249)$; cubic-Goldilocks checks have error $<30/p^3<2^(-186)$. These are different field-check bounds, not classical/Grover versions. `ActiveMigrationZeroTest.lean` formalizes the exact `SECP_N` and `ED_ORDER` scalar semantics, 64-lane RSS sharing, and pre-open barriers, alongside `tooth_premature_residual_open_recovers_spending_key`, which shows how opening a faulted residual ahead of the zero test leaks the 256-bit spending key across 256 aborted queries.

*Threshold ML-DSA-44 and TOPRF credentials (`qsag-cred`).* Threshold lattice signing targets standard FIPS 204 ML-DSA-44 (@mldsa) for $n <= 5, t >= 2, n >= 2t-1$. Custodians sample short secret vectors $bold(s)_1, bold(s)_2 in [-2, 2]$ directly on replicated shares via FIPS 204 rejection sampling and open $bold(t)$ only after shared matrix multiplication, so no dealer ever sees the secret key and no corrupt party can bias secret coefficients outside $[-2, 2]$. Online signing requires an honest majority of $2t-1$ active signers to evaluate the norm/hint rejection check under verified multiplications: the response $bold(z)$ opens only behind a shared accept bit, leaving rejected attempts with $(bold(w)_1, "reject")$ under the standard Fiat–Shamir-with-aborts heuristic while durably burning every nonce (`threshold_mldsa_nonce_reuse_extracts_sk_and_typestate_prevents`). For privacy-preserving credentials, `PiVoprf` implements a 2-of-5 threshold Poseidon2 sponge OPRF with majority error correction against one malicious server and durable pre-evaluation counter locks, powering `PiBlindVc` six-limb Poseidon2 attribute commitments with 438-repetition `Quantum128` membership proofs.

#figure(tbl((1.4fr, 1fr, 1fr),
  [FIPS 204 profile], [Public key B], [Signature B], table.hline(),
  [ML-DSA-44], [1,312], [2,420],
), caption: [Standard FIPS 204 ML-DSA-44 wire sizes produced by the dealerless $(t,n)$ threshold signer.]) <mldsa>

*Accelerator execution and receipts (`qsag-accel`).* A Linux/std zero-crates.io-dependency Vulkan FFI backend executes six SPIR-V kernels: Keccak-f[1600], Poseidon2-12, Goldilocks NTT, Ext2 coset LDE, Poseidon2 Merkle layers and BDOZ binary-field dot products. Strict audited loading requires reported Wave32 and zero scratch/spills. The runtime modules target SPIR-V 1.5. Keyed cSHAKE256 `ExecutionReceipt`s authenticate reports under a software key; the optional audit-state anchor identifies device/telemetry evidence. This does not establish hardware attestation or exact shader-to-model functional refinement.

= Four assurance pillars

QSAG organizes assurance into four complementary surfaces (@pillars). Protocol models, extracted functions, pinned binary slices and finite executions have distinct contracts. The constructive policy permits only `{propext, Quot.sound}`, with no `sorry`, custom axioms or `Classical.choice`; MIR extraction additionally requires no `FunsExternal`. `AuditAxioms` and `AuditMirAxioms` check their loaded closures. Declaration counts and module counts are not proof-coverage measurements; every release must bind imports, extraction and replay results to the integrated revision. `#tooth_pair` checks constructive declarations and structural pairing, while individual attack witnesses establish particular guard-removal failures.

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 6pt,
    panel([#smallcaps[Pillar 1 · constructive protocol, WAL, and QROM spine]\
      `Fips205` · `ThresholdMpc` · `JortsBeltLatchAndQuorumSwitching` · `PosixCrashWal`\
      `SuccinctAggregationIop` · `AffineProximityGaps` · `ConcreteSecurityBudget`]),
    align(center)[↓ `MirSpecBridge.lean` & differential / KAT parity links ↓],
    grid(columns: (1fr, 1fr), gutter: 7pt,
      panel([#smallcaps[Pillar 2 · extracted Safe-Rust MIR]\
        Both extracted crates → production callers\
        Field/sponge specs & multi-turn release guards]),
      panel([#smallcaps[Pillar 3 · ISA & compiled ELF64]\
        `ConstantTimeIsa` · `ElfBinaryVerify`\
        x86-64 / AArch64 3-way NI & vector hygiene]),
    ),
    align(center)[↑ complemented by executable checks ↑],
    panel([#smallcaps[Pillar 4 · executable ground-truth gates]\
      `spec-oracle` · clause-drop mutations · `isa-cosim` · `dudect` · configured 6-kernel replay]),
  )
}, caption: [QSAG's four assurance pillars provide complementary, scoped guarantees across specifications, extracted MIR, compiled kernel bytes, and live execution.]) <pillars>

== Pillar 1: protocol, storage, and query-bound spine

Foundational modules (`Goldilocks.lean`, `BinaryTower.lean`, `Keccak.lean`, `Poseidon2.lean`) prove field invertibility, injective multi-frame domain encoding (`encodeMultiFrame_injective`), Poseidon2 permutation bijectivity (`poseidon2Perm12_bijective`), and canonical 56-bit limb packing. Above them, `Fips205.lean`, `HashSigs.lean`, `HypertreeEufCma.lean`, `BaggyAndRss256Security.lean`, and `JortsBeltLatchAndQuorumSwitching.lean` formalize single-signer and threshold hash signing, multi-turn latch state machines matching byte-level Rust domain tags, and a constructive Type-valued one-use WOTS+C reduction (`wotsC256_one_use_euf_cma_sound`). `ThresholdMpc.lean`, `Preprocessing.lean`, `MaliciousSecurity.lean`, `IdealTsig.lean`, and `UcGames.lean` cover share-level Shamir Poseidon2 and RSS Keccak evaluation, Frobenius and sacrifice checks, commit-verify-open barriers, and sequential UC composition [Can01] (`multi_session_uc_realizes`).

`PosixCrashWal.lean` models three storage tiers—volatile kernel descriptors/page cache, drive write-back cache, and sector-atomic non-volatile media—proving multi-crash epoch uniqueness under `OpenDescriptionId` lock semantics and parent-directory fsync. `ConcreteSecurityBudget.lean` builds exact rational bit-margin arithmetic and a Gaussian-integer unitary query model, proving square-root-free BBBV97 hybrid and O2H disturbance bounds [BBBV97, AHU19] (`qrom_o2h_telescoping_disturbance_le`, `qrom_fiber_search_bound`) coupled to named protocol encoding fibers. `MultiRoundFsQrom.lean` supplies the more specific multi-round budget described in §4. `CeremonyAtomicityAndAbort.lean` proves multi-ledger crash/interleaving safety for valid events, and pre-open abort-conditioned SD numerator zero under its masked-view specification and positive survival count. `HypertreeEufCma.lean` proves an actual-signing-log reduction for fresh-message forgery in the specified stateless geometries with at most $2^32$ layers to ITSR, TCR or preimage breaks. Finally, `MirSpecBridge.lean` connects nine kernel refinements (`compiled_rlib_nine_kernels_verified`) and fixed-width guard invariants back to protocol-level predicates.

== Pillar 2: Safe-Rust MIR refinement

Charon and Aeneas translate two separately rooted Rust crates into Lean under the `0 FunsExternal` discipline. Production core/policy/quorum call `qsag-verified` guards and arithmetic; aggregation calls `qsag-whir-verified` folding, OOD, PoW-mask and terminal polynomial checks. Examples include `VerifiedWotsC256Guard`, `validate_belt_quorum_config`, `StatefulVelocityGuard::authorize_spend`, `cwyz_duet_fold` and `verify_ood_pin_eq`.

`RealSpecFieldWeld.lean` proves Goldilocks inverse refinement and nonzero inverse multiplication. `RealSpecKeccakWeld.lean` proves 24-round permutation refinement; arbitrary-slice sponge totality and phase laws are separate from full emitted-byte SHAKE refinement, which still needs rate-block XOR/padding/squeeze linkage. `MultiTurnMediationAndReachability.lean` proves multi-turn guard invariants and `bdoz_verify_arbitrary_batch` under its tag-execution premise. Fresh extraction, challenge freshness and complete mediation of caller-held secrets remain release obligations.

== Pillar 3: ISA semantics and compiled ELF64

`ConstantTimeIsa.lean` formalizes instruction-level semantics and three-way leakage taint (program counter/branches, memory addresses, and variable-latency operands, plus dirty upper-YMM state) for x86-64 (`AVX2`, `GFNI`, `PCLMULQDQ`, `VPCLMULQDQ`) and AArch64 (`SHA3`, `PMULL`), proving both functional equivalences (`gfni_isomorphism_homomorphic`, `gf256ShamirMulGfni_32lane_correct`, `goldilocksMulCt_x86_eq_arm`) and relational taint soundness (`x86_ct_checker_sound`, `arm_ct_checker_sound`).

Rather than trusting source-level assembly macros, `ElfBinaryVerify.lean` parses SHA-256-pinned `.rlib` ELF64 archives directly (`CompiledRlibFixtures.lean`), extracts `.text` symbol slices (`extractElfFuncBytes_in_text_section`), decodes raw machine bytes—including audited fixes for VEX-length `VZEROUPPER` vs. `VZEROALL`, base-less SIB absolute displacements (`tooth_sib_absolute_decode`), and AArch64 `UBFM` bitfield semantics—and verifies kernel-checked abstract-interpretation certificates across 16 x86-64 symbols (999 instructions) and 7 AArch64 symbols (299 instructions) (`rlib_x86_every_symbol_three_way_ni_sound`, `rlib_aarch64_every_symbol_three_way_ni_sound`). Byte-level mutation tests (`mutant_secret_branch_rejected`, `mutant_secret_lut_rejected`, `mutant_udiv_rejected`, `mutant_missing_vzeroupper_rejected`) confirm that injected timing hazards fail verification; whole-program dispatch and linked-artifact closure remain separate. `SydTvTranslationValidation.lean` supplies five looping-kernel functional certificates; `SimdBinaryEquiv.lean` adds decoded carryless multiply and transpose noninterference. RFLAGS validity masks and edge-vector theorems replace the historical fixed mismatch count. `SpirvSimtGpuEquiv.lean` establishes codec roundtrip, race-conditioned multi-wave confluence and modeled SIMT leakage properties; these require a separate bridge to exact runtime shader words and driver lowering.

== Pillar 4: executable ground-truth gates

Four executable gates complement the proofs: native Lean/Rust differential and clause-drop tests, Linux x86-64 `ptrace` ISA cosimulation, `dudect` timing tests, and configured six-checker replay. Counts require a dated run and artifact identity. The historical poster inventory is 1,200 + 100 + 1,000 positive comparisons and 500 mutant schedules: 2,800 total, not 2,800 positive plus 500. It does not certify the current concurrent edits. Silicon tests cover sampled instructions and states; configured replay does not imply a successful pinned replay. The six configured checkers are `lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche` and `con-ron`.

= Evaluation

== SIMD kernel throughput and empirical timing

Historical kernel measurements evaluated `qsag-asm` kernels on two Linux x86-64 platforms: an Intel Core i9-12900 (Alder Lake, dispatching `AVX2`, `GFNI`, and `VPCLMULQDQ`) and a virtualized AMD EPYC-Milan (Zen 3, dispatching `AVX2` and `PCLMULQDQ`); AArch64 `SHA3`/`PMULL` kernels are covered statically by Pillar 3. In @simdbench, hardware instructions reshape finite-field MPC bottlenecks dramatically: `GFNI` affine/multiply instructions accelerate $FF_(2^8)$ Shamir and MAC operations by >500× on Alder Lake (0.038–0.039 cycles/byte vs. ≈19.5 portable), while carry-less `VPCLMULQDQ`/`PCLMULQDQ` speeds up `Tower128` polynomial MACs by 10–12× and 4-way `AVX2` Keccak accelerates sponge commitments by 2.4–4.3×. Across 1,000,192 traces on both CPUs, the nine positive kernel harnesses stayed inside the $abs(t) < 4.5$ `dudect` threshold (cropped rows: max $abs(t) <= 1.68$; AMD raw rows reach 1.87), whereas the deliberate early-exit negative control trips immediately ($abs(t) > 1,600$). All eight protocol crates (`qsag-core`, `qsag-quorum`, `qsag-agg`, `qsag-cred`, `qsag-migrate`, `qsag-hd`, `qsag-policy`, `qsag-accel`) now dispatch directly into `qsag-asm` for bitsliced RSS Keccak, PCG tree expansion, Merkle-Canopy hashing, and carry-less MACs.

#figure(tbl((2.1fr, 0.8fr, 0.8fr, 0.65fr, 0.65fr, 0.8fr, 0.8fr, 0.65fr, 0.65fr),
  [Kernel / unit], table.cell(colspan: 4)[Intel Core i9-12900], table.cell(colspan: 4)[AMD EPYC-Milan (virtualized)],
  [], [Portable], [SIMD], [Speedup], [max $abs(t)$], [Portable], [SIMD], [Speedup], [max $abs(t)$], table.hline(),
  [Keccak-f / sponge], [652.66], [272.52], [2.39×], [1.12], [1,193.16], [279.99], [4.26×], [1.44],
  [RSS $chi$ / 256-way], [—], [—], [—], [0.81], [—], [—], [—], [1.03],
  [Tower GF256 mul / B], [19.890], [0.039], [505.20×], [1.16], [28.274], [0.551], [51.30×], [1.19],
  [Tower GF256 MAC / B], [19.498], [0.038], [517.00×], [0.95], [27.637], [0.076], [365.00×], [0.16],
  [Tower128 poly MAC / pair], [603.00], [50.11], [12.00×], [0.84], [774.31], [76.59], [10.10×], [0.56],
  [Tower128 LUT-free / pair], [3,392.88], [707.07], [4.80×], [1.68], [4,792.90], [1,122.72], [4.30×], [0.72],
  [Goldilocks mul; dot2 test], [11.56], [7.66], [1.51×], [1.02], [10.63], [9.75], [1.09×], [1.00],
  [Goldilocks pow7 test], [—], [—], [—], [1.33], [—], [—], [—], [0.45],
  [32-byte tag equality], [—], [—], [—], [1.00], [—], [—], [—], [0.16],
  [Leaking negative control], [—], [—], [—], [21,874.51], [—], [—], [—], [1,607.56],
), placement: top, scope: "parent", caption: [Historical kernel cycle counts per unit and cropped `dudect` Welch $abs(t)$-statistics over 1,000,192 traces (baseline run, not current-head validation; later 100,096-sample hardening runs are separate).]) <simdbench>

== Protocol latency, proof sizes, and engineering trade-offs

@protobench retains historical wire-v6 host reports; original raw calibration was not recovered for this edit. Under wire-v6 affine-monomial folding (`bench_affine_regimes`, $K = 8$, default shard sizing on Intel Core i9-12900), full serialized `JortsPoseidon2` aggregates measure `161,112 B` (`13.55 ms` verify) under `Habr24Qrom128` and `291,352 B` (`26.69 ms` verify) under `BciksJohnsonQrom128`, while 16-layer stateless `CorduroyPoseidon2` aggregates ($K = 8$) verify in `18.88 ms` (`240,014 B`) and `35.33 ms` (`446,254 B`) against ≈49 s single-host proving. Because WHIR proof size is dominated by Merkle-Canopy query openings that grow polylogarithmically in trace height while raw post-quantum signatures grow linearly in $K$, Hem reduces bandwidth once batch size $K$ amortizes the fixed opening overhead within a shard batch (whereas cross-batch merge trees concatenate proofs without further compression).

#figure(tbl((1.95fr, 1.95fr, 1.95fr),
  [Operation], [Setting], [Reported], table.hline(),
  [Hem Jorts v6 ($K=8$)], [`Habr24` (`161.1 kB`)], [4.30 s / 13.55 ms],
  [], [`Johnson` (`291.4 kB`)], [4.90 s / 26.69 ms],
  [Hem Corduroy v6 ($K=8$)], [`Habr24` (`240.0 kB`)], [49.20 s / 18.88 ms],
  [], [`Johnson` (`446.3 kB`)], [48.84 s / 35.33 ms],
  [Jorts 2-of-3, Mode 3B], [local / sim. WAN], [≈ 1.0 ms / 81 ms],
  [QS-A, 3-of-5], [loopback, 2 offline], [≈ 0.56 ms],
), caption: [Historical single-host protocol reports (`prove / verify` for v6 affine-monomial `bench_affine_regimes` on Intel Core i9-12900, 12 GiB cap). Jorts Mode 3B and QS-A timings measure online opening after offline chain staging and exclude disk `fsync` latency.]) <protobench>

On the signing path, Mode 3B Jorts (`≈ 1.0 ms` local compute, `≈ 81 ms` simulated WAN) and 3-of-5 QS-A (`≈ 0.56 ms` loopback TCP with two custodians offline) measure approximately millisecond online compute by moving symmetric chain evaluation into offline staging, leaving a single online round. Conversely, dishonest-majority symmetric MPC remains expensive: an unbatched Keccak-f[1600] permutation consumes 38,400 authenticated Boolean Beaver triples, keeping full-hypertree FIPS 205 dishonest-majority signing at minutes-scale. In our bounded Linux quickstart check (12 GiB RAM cap, 600 s timeout per Cargo command), 12 of 13 CLI and example workflows passed—including all 43 KATs, Hem aggregation/merge, few-time burn enforcement, policy guards, and DKG fault rejection—while the combined `threshold_slh_dsa_quickstart` example completed RSS signing and stock verification before hitting the 600 s ceiling during Shamir DKG and SPDZ preprocessing. Optimizing Ring-LWE base-OT and SPDZ preprocessing throughput is ongoing engineering work.

== GPU kernels and durable quorum measurements

The inspected 2026-11-14 RX 6750 XT raw run used RADV NAVI22, Vulkan 1.3.289, RADV 24.2.8 and the benchmark's `CpuReferenceBackend`. One warmed sample includes host transfers/submission. All six output comparisons and the keyed receipt passed (13 submissions); all pipelines reported Wave32 and zero scratch. Raw-log SHA-256: `c33c8856ef15dea3b8667e75fdcafee5e173721911e87b29cb13ab8594e5e777`.

#figure(tbl((2fr, 0.7fr, 0.8fr, 0.7fr),
  [Workload], [GPU ms], [CPU ms], [Ratio], table.hline(),
  [Poseidon2-12, 262,144], [22.11], [3027.45], [136.9×],
  [Keccak-f, 262,144], [21.49], [76.14], [3.5×],
  [NTT, $2^20$], [10.02], [183.41], [18.3×],
  [Ext2 LDE, $2^18 -> 2^20$], [11.97], [581.34], [48.6×],
  [Merkle, $2^20$ leaves], [39.45], [14184.10], [359.5×],
  [BDOZ dot, 262,144 pairs], [8.65], [746.83], [86.3×],
), caption: [One raw GPU audit run; ratios compare the paired CPU reference only.])

A later hardening report, after twiddle validation and buffer scrubbing, gives GPU/CPU ms of 21.35/1822, 20.04/67, 12.29/161, 10.95/476, 35.38/7185 and 6.30/71 in the same order. The earlier requested headlines (Merkle 19.03 ms / 432.1×, Poseidon2 12.50 ms / 173.0×, LDE 8.32 ms / 65.9×, NTT 6.94 ms / 26.6×, BDOZ 4.34 ms / 17.5×, Keccak 19.27 ms / 4.1×) remain historical reports pending their original measurement record. None measures end-to-end Hem proving.

`quorum_threaded_bench.rs` implements `ConfidentialWireChannel<TcpEndpoint>` Encrypt-then-MAC AEAD with filesystem WAL, poison journal and seed-ledger synchronization. Reported ext4 online timings are 4.37 ms for QS-A 2-of-3 and 5.21 ms for QS-B 3-of-7; their raw execution records were not recovered here. They must remain separate from the RAM/loopback results in @protobench. Offline staging and WAN latency are separate costs.

== Consensus application geometry

The Alpenglow mock implements 1,000 FrontierSumFts votes, a QS-A hot path and a 64-signer Hem checkpoint using in-memory storage and CPU reference primitives. The Beam mock implements four 32-validator Jorts subnets with minimum quorum 24, plus mixed Jorts/Corduroy workloads. These are application workloads, not live network integrations or measured 150 ms finality / sub-8 ms Beam verification. Compact514 has 16-byte nodes (128 classical / roughly 64 generic quantum preimage bits); 514 signature bytes exclude vote fields, certificates and transport.

Hierarchical Hem binds epoch, registry, quorum and non-overlap while retaining constituent proofs. Constant-size recursive verification requires a separate verifier circuit. `docs/QUORUM_AND_CONSENSUS_SCALING.md` records conditional bandwidth/work arithmetic: a maximum 128-signer Jorts shard already needs 128 MiB for base witness elements, excluding extension buffers and Merkle scratch. GPU kernel speedups require whole-prover profiling before applying Amdahl's law.

= Proved scope and remaining bridges

- *Runtime and extraction:* Both extracted Rust crates execute in production paths. Fresh source-to-extraction comparison, complete mediation of secrets and release construction, and pinned final build/import/axiom/replay evidence remain required.
- *Hem:* Active-slot trace-to-signature refinement, the Hasse-to-Taylor and full trivariate Johnson bridges, concrete transcript flip bounds and quantum commitment extraction remain open. Habr24 capacity agreement is conjectural. The $2^40$ compiler expression and $2^56$ single-round portfolio arithmetic are distinct results.
- *RLWE and migration:* Pairwise unit differences and short relaxed extraction are proved. The current 143-bit RLWE challenge width has generic Grover exponent 71.5. Migration's 438 repetitions and field-check errors do not establish a complete concrete FS/QROM reduction.
- *Storage and transport:* Multi-ledger crash/interleaving safety is proved for valid modeled events. Runtime events must refine that model with durable reservations before release, an external rollback anchor, authenticated confidential channels, consistent broadcast and an authoritative policy epoch. QS-A/QS-B staging currently uses a trusted dealer; distributed staging is separate work.
- *Hardware:* Named architectural leakage contracts require actual DOIT or PSTATE.DIT state. Pinned CPU bytes and modeled GPU semantics do not cover every caller spill, driver transformation, speculative effect or physical side channel. Software-keyed receipts authenticate reports. The experimental ParallelSeededFts SPN still requires independent cryptanalysis.

= Conclusion

QSAG's four-oracle cut makes released-chain secret depth independent of tree height. The Pants suite implements stateless, stateful and quorum-switching custody; Hem combines Ext4 WHIR, affine folding and shared Merkle openings for algebraic signature batches. Production callers execute extracted guards and WHIR routines. Constructive protocol, crash, algebra and query theorems, pinned CPU-byte certificates, GPU SIMT models and measured kernel executions provide distinct, composable evidence. The exact outstanding reductions and runtime refinements above define the next integration work.

#heading(numbering: none)[References]
#block[
#set text(size: 7.5pt)
#set par(justify: false, leading: 0.39em, hanging-indent: 1.6em)
#stack(dir: ttb, spacing: 2.8pt,
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
  [[Can01] R. Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols", FOCS 2001.],
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
  [[KOS15] M. Keller, E. Orsini, P. Scholl, "Actively Secure OT Extension with Optimal Overhead", CRYPTO 2015.],
  [[KOS16] M. Keller, E. Orsini, P. Scholl, "MASCOT: Faster Malicious Arithmetic Secure Computation with Oblivious Transfer", ACM CCS 2016.],
  [[LFKN92] C. Lund, L. Fortnow, H. Karloff, N. Nisan, "Algebraic Methods for Interactive Proof Systems", J. ACM 39(4), 1992.],
  [[MU21] L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021.],
  [[RBV17] O. Reparaz, J. Balasch, I. Verbauwhede, "Dude, is my code constant time?", DATE 2017.],
  [[SP800-185] NIST SP 800-185, "SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash", 2016.],
  [[Wie88] D. Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly 26(4), 1988.],
  [[Wui20] P. Wuille, BIP-350: "Bech32m format for v1+ witness addresses", 2020.],
)
]
