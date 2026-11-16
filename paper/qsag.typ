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

// Formal statements. `src` names the Lean declaration or the Rust item that carries it.
#let stmt(kind, name, body, src: none) = block(
  width: 100%, inset: (x: 6.5pt, y: 5.5pt), above: 0.9em, below: 0.9em,
  stroke: (left: 1.4pt + luma(70)), fill: luma(246), breakable: true,
)[
  *#kind#if name != none [ (#name)].* #body
  #if src != none {
    v(-0.25em)
    align(right, text(size: 7pt, fill: luma(60))[#src])
  }
]
#let theorem(name, body, src: none) = stmt("Theorem", name, body, src: src)
#let definition(name, body, src: none) = stmt("Definition", name, body, src: src)
#let protocol(name, body, src: none) = stmt("Protocol", name, body, src: src)
#let model(body) = text(size: 7pt, fill: luma(60))[#body]

#place(top + center, float: true, scope: "parent", clearance: 14pt)[
  #align(center)[
    #set par(justify: false)
    #set text(hyphenate: false)
    #text(size: 16.5pt, weight: "bold")[QSAG: Quorum-Switching Threshold Hash Signatures and Succinct Post-Quantum Aggregation, from Three-Party Vaults to Million-Validator Certificates]
    #v(7pt)
    #text(size: 11pt)[ember arlynx]
    #v(2pt)
    #text(size: 8.5pt, fill: luma(60))[`ember@lunar.town`]
  ]
  #v(9pt)
  #block(inset: (x: 16pt))[
    #set par(justify: true, leading: 0.46em)
    *Abstract.* QSAG is a post-quantum replacement for the elliptic-curve layer beneath wallets, custodians and validators: threshold signing (the role of FROST [KG20]), hierarchical derivation (BIP-32), signature aggregation (BLS [BLS01]), key migration, and delegable capabilities. Its security rests on hash functions, with lattices only where a standard demands them. Three ideas carry the design. _Cut-the-Hash_ observes that a hash-based signature publishes almost every digest its signer computes, so custodians evaluate only four secret operations under multiparty computation and build the tree in the clear; secret depth is then independent of tree height, and the output for FIPS 205 is byte-identical to a single signer's, whether run on a bitsliced three-party engine, an isolated per-custodian CNF engine for honest-majority thresholds [CGH+18], or an authenticated dishonest-majority engine with 31 µs pooled blinded MAC checks. _Quorum switching_ lets any authorized set of custodians sign with a stateful key without ever spending a one-time leaf twice; we state its safety for arbitrary asymmetric quorum systems and monotone access structures, of which $(t,n)$ thresholds are one case. _Hem_ proves that $K$ signatures verify, using a sumcheck over the Goldilocks field and an eight-regime WHIR polynomial commitment whose query counts follow from the Johnson bound and affine Reed–Solomon combiners [CWYZ26], with no proximity conjecture; holographic and contractive split recursion fold trees of any depth into constant-verifier-state certificates checked against a 32-byte roster root. We give a complete custody lifecycle (including hardware anti-rollback anchors and threshold four-curve key migration), a GPU prover, a scaling model from 1,500 to 1,048,576 validators and $88 times 10^9$ principals, a constructive Lean 4.35 library of 269 modules (407,223 lines) welded to extracted Rust MIR and 28 assembly kernels, a verifier coprocessor (_QSAG-NI_) synthesized and formally checked at 832.0–908.7 kGE across four ASIC libraries and two FPGA families, and a physical custody enclave (_Dregg-180_) in 180 nm 5 V CMOS.
  ]
]

= Introduction

Validators, custodians and rollups share one cryptographic substrate. FROST [KG20] or threshold ECDSA splits a signing key among $t$-of-$n$ hosts; BIP-32 derives accounts; BLS [BLS01] compresses thousands of votes into 96 bytes; capability tokens delegate narrowed authority. Every one of these leans on the algebra of elliptic-curve groups, and Shor's algorithm removes that algebra. The standardized replacements, SLH-DSA [FIPS205, BHKN+19] and ML-DSA [FIPS204], are single-signer schemes: they offer no threshold mode, no aggregation, no public derivation, and signatures two orders of magnitude larger.

Hash-based signatures are the conservative foundation, since they assume only what every other scheme already assumes. Building the full substrate on them meets five obstacles.

1. *Tree height against MPC depth.* A hypertree signature hashes thousands of Winternitz chains into roots and climbs $d$ Merkle layers. Evaluated naively under actively secure MPC, public compression becomes millions of secret gates.
2. *Committee scaling.* Replicated sharing keeps three-party Boolean gates fast but stores $binom(n, t-1)$ shares. Shamir sharing is compact but multiplies in a field where Keccak is expensive.
3. *State under quorum switching.* Stateful trees are small and fast because each one-time leaf signs once. When any $t$ of $n$ custodians may sign, two quorums can each believe a leaf is fresh, most easily after a crash, a restored snapshot or a partition; one reuse forges.
4. *Aggregation without pairings.* $K$ post-quantum signatures cost $O(K)$ kilobytes. Compressing them needs a proof system whose own soundness does not rest on a conjecture, and a certificate whose size does not grow with $K$.
5. *The distance from model to artifact.* A sound protocol still fails if a faulted share opens before its MAC is checked, if power loss rewinds a counter, or if a vector instruction leaks an operand.

*Approach.* The organizing principle is that secret shares should cross into cleartext at the earliest point where the signature scheme itself makes the value public. _Cut-the-Hash_ (§2) isolates four secret oracles and evaluates everything else publicly. On that boundary we build the _Pants_ signature suite: stateless _Baggy_ and _Corduroy_, stateful _Jorts_, and single-datagram few-time signatures. Three MPC engines serve it (§3): a 256-lane bitsliced replicated engine for three parties, an isolated per-custodian CNF engine [CGH+18] over encrypted wire channels for honest-majority $(t,n)$ committees ($2(t-1) < n$), and an authenticated engine for dishonest majorities whose pooled blinded MAC check runs in 31 µs online and reveals nothing about a long-lived authentication key on abort.

Stateful signing is made safe by a durable latch, hardware anti-rollback anchors, and a quorum rule. We state the rule in its general form: any two quorums that can certify the same leaf must intersect in a custodian outside every admissible fault set. Symmetric thresholds, weighted and tree-composed policies, and asymmetric or personal quorum systems [CT19, LGM19] are instances, and their custody shares are instances of one monotone span program released over an encrypted wire ceremony that never exposes one custodian's lanes to another.

_Hem_ (§4) proves $K$ signature verifications in a 256-column trace. Its polynomial commitment is WHIR [ACFY25] across eight wire profiles—spanning `cSHAKE256`, 12-round `TurboSHAKE256` [RFC9861], and Poseidon2 outer commitments—with affine Reed–Solomon combiners [CWYZ26] and query counts set from the Johnson radius; the capacity conjectures many deployed systems rely on were refuted in 2025–26 [CS25, KKH26]. Holographic verification makes the verifier sublinear in its own constraint system, supporting both full in-circuit subtree merges and contractive binary split recursion (`SplitSubtreeAggregate`, $<= 2^20$ rows per merge with one folded WHIR cascade per tree level). The same prover has a hiding mode for credentials, private multisignatures and capabilities.

§5 covers the lifecycle around signing (derivation, addresses, policy and capabilities, TPM 2.0 and hypervisor anti-rollback anchors, local and threshold key migration across four curve ecosystems, threshold ML-DSA, oblivious PRFs) and the GPU prover. §6 describes the formal development. §7 evaluates the system, models its scaling to 1,048,576 validators and $88 times 10^9$ principals, and presents two silicon designs: the _QSAG-NI_ verifier coprocessor across four ASIC PDKs and two FPGA families, and _Dregg-180_, a physical custody enclave in 180 nm CMOS. §8 states the trusted base.

*Contributions.*
- *Cut-the-Hash and Pants (§2).* A four-oracle boundary giving height-independent secret depth; byte-identical threshold SLH-DSA; stateless Baggy with a pruned PORS few-time layer; stateful Jorts with $2^6$ to $2^20$ signatures per key; 1,122-byte single-use signatures that fit one datagram.
- *Isolated CNF, personal release, and general access structures (§2.4–2.5, §3.1).* Leaf uniqueness from pairwise honest intersection, isolated per-custodian honest-majority signing over wire channels, encrypted personal MSP release with no coordinator, and self-contained blocklace equivocation evidence.
- *Pooled blinded MAC openings (§3.3).* A zero test on $w = (sum r_i)(sum d_j)$ backed by single-use OLE blinding triples that keeps a persistent authentication key information-theoretically hidden on abort at 31 µs per online check.
- *Hem (§4).* Eight-profile Johnson-radius WHIR with [CWYZ26] folding, constructive certificates, `TurboSHAKE256` outer commitments, holographic and contractive split recursion against a 32-byte roster root, and hiding relations for credentials and capabilities.
- *Assurance (§6).* A 269-module Lean 4.35 library with no `sorry`, no `Classical.choice` and no `import all`; Aeneas MIR proofs (`8,674` declarations, `114/114` six-kernel WHIR comparator theorems); and machine-code noninterference and `ELF ≃ Math ≃ MIR` triangles across 28 assembly kernels.
- *Scaling and silicon (§7).* Measurements on Zen 5 and an RX 6750 XT, scaling models to $2^20$ validators and $88 times 10^9$ principals, synthesized and formally verified _QSAG-NI_ RTL (`832.0–908.7 kGE`, `99/99` LEC miters), and the _Dregg-180_ 180 nm custody enclave.

*Related work.* PRAWNS [BBD+26] thresholdizes hash-based signatures through lattice-based threshold PRFs, placing a lattice assumption on the signing path; QSAG keeps leaf derivation inside symmetric MPC [FLNW17, CGH+18, BGIN19, BDOZ11, DPSZ12] and emits standard FIPS 205 signatures. Lifetime-capped SPHINCS variants trade signature size for a bound on signatures per key; QSAG instead enforces anchored reservation before release. LaBRADOR [BS23] attains smaller proofs from Module-SIS; Hem assumes only hash functions. Recent XMSS aggregators adopt capacity-regime parameters and Poseidon2 modes exposed to [MRG26, BTA26]; Hem refuses capacity tags and deploys one hardened Poseidon2 profile alongside standard byte sponges [FIPS202, SP800-185, RFC9861]. For consensus, distributed quorum signatures [KSW26] and QUASI [IM26] study post-quantum attestations that avoid signer bitmaps; our dual-path design (§7.4) is complementary. Asymmetric trust [CT19, ACTZ21, ACKV26], personal quorum systems [LGM19] and the blocklace [KLST26] supply the quorum and ordering models we instantiate. Migration and credentials build on MPC-in-the-head [IKOS07, GMO16].

= Cut-the-Hash, Pants, and Quorum Switching

== The four-oracle boundary

A hash-based signing key is a PRF key $"SK.prf"$ and a seed $"SK.seed"$, with public $"PK.seed"$ and root $"PK.root"$. Let $mu$ be the framed message, $A$ a tree or chain address, and $A_0$ its chain-start form.

#definition("secret oracles", src: [`SlhMpcOracles`, `PqHashMpcOracles`])[
  The secret interface of a signer consists of four families.
  1. _Message randomizer._ $R = "PRF"_"msg" ("SK.prf", r, mu)$ for an optional hedge $r$.
  2. _Chain position._ $F^s ("PK.seed", A, X_j)$ with $X_j = "PRF"("PK.seed", "SK.seed", A_0)$, only at $s in {d_j, w-1}$, where $d_j$ is the message-selected base-$w$ digit.
  3. _Selected few-time leaf._ $"PRF"("PK.seed", "SK.seed", A_"fts" (u))$ at the message-selected indices $u$.
  4. _Unselected few-time leaf hash._ $F("PK.seed", A, "PRF"("PK.seed", "SK.seed", A_"fts" (u)))$, the public digest of a leaf whose preimage stays secret.
]

Everything else is a function of oracle outputs and public data: the digest $H_"msg" (R, "PK.seed", "PK.root", mu)$, counter grinding, the compression $T_ell$ of chain ends, and every internal Merkle node. Custodians hold shares of the two seeds, authenticate each oracle output, and open it (@cutfig).

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 5pt,
    panel([#smallcaps[Secret-shared evaluation]\
      $"SK.prf", "SK.seed"$ #sym.arrow.r $R$, chain steps $F^s$, few-time leaves and leaf hashes]),
    align(center)[#sym.arrow.b\ #smallcaps[durable bind · MAC or proof barrier · open]\ #sym.arrow.b],
    panel([#smallcaps[Public reconstruction]\
      $T_ell$ compression · few-time and Merkle internal nodes · $H_"msg"$ and counter grinding]),
  )
}, caption: [Cut-the-Hash. Seeds stay shared behind four oracles; all tree compression is public.]) <cutfig>

#theorem("height independence", src: [`rss_thresholdSlhSign_eq_slhSignInternal`])[
  A released chain node has sequential secret depth at most $w$ hash evaluations (one PRF and at most $w-1$ steps), and a few-time leaf at most 2, for every tree height and layer count. For each of the six FIPS 205 SHAKE parameter sets, the threshold signer's output equals that of the single-key signer on matched key and randomness, byte for byte.
]

The depth is 16 for FIPS 205 and 4 for the Pants profiles. Message absorption contributes $floor((2n + abs(M')) slash 136) + 1$ sequential Keccak permutations [FIPS202] unless the message is prehashed; pure and prehash modes are domain-separated.

== Target-sum Winternitz

The Pants profiles use checksum-free Winternitz signatures (WOTS+C [HKRY23]) at $w = 4$. A 256-bit digest is read as $ell = 128$ digits $d_j in {0,1,2,3}$, and a public counter is ground until
$ sum_(j=1)^(ell) d_j = S, quad S = ell (w-1) slash 2 = 192. $

#theorem("incomparability", src: [`wotsC256_strict_incomparability`])[
  If $d != d'$ are digit vectors with $sum_j d_j = sum_j d'_j$, there are indices $j_1, j_2$ with $d_(j_1) < d'_(j_1)$ and $d'_(j_2) < d_(j_2)$.
]

So no valid signature can be advanced along its chains into another, which is what the checksum chains of ordinary Winternitz buy at the cost of extra chains. Omitting the sum check admits a one-hash forgery (`tooth_wotsc_without_target_sum_forges`). The accepted set has $[x^192](1+x+x^2+x^3)^128 approx 2^(251.01)$ elements, and grinding takes 31.7 trials on average. Verification walks exactly $ell(w-1) - S = 192$ chain steps.

#figure(
  {
    set par(justify: false)
    text(size: 7.0pt, table(columns: (1.75fr, auto, auto, auto, auto, auto, auto, auto, auto, auto), inset: (x: 1.5pt, y: 3.6pt), stroke: none,
      table.hline(stroke: 0.6pt),
      [Profile], [$n$], [$h$], [$d$], [$h'$], [$a$], [$k$], [$w$], [Sigs/key], [Sig. B], table.hline(),
      [SLH-DSA-128s], [16], [63], [7], [9], [12], [14], [16], [$2^64$], [7,856],
      [SLH-DSA-128f], [16], [66], [22], [3], [6], [33], [16], [$2^64$], [17,088],
      [SLH-DSA-192s], [24], [63], [7], [9], [14], [17], [16], [$2^64$], [16,224],
      [SLH-DSA-192f], [24], [66], [22], [3], [8], [33], [16], [$2^64$], [35,664],
      [SLH-DSA-256s], [32], [64], [8], [8], [14], [22], [16], [$2^64$], [29,792],
      [SLH-DSA-256f], [32], [68], [17], [4], [9], [35], [16], [$2^64$], [49,856], table.hline(),
      [Baggy], [32], [32], [16], [2], [11#super[‡]], [28#super[‡]], [4], [$2^16$], [≤ 71,654],
      [Corduroy], [32], [64], [16], [4], [8], [32], [4], [$2^20$], [76,896],
      [Jorts (custody)], [32], [16], [1], [16], [—], [—], [4], [$2^16$], [4,652],
      [Jorts (Hem)], [32], [6–20], [1], [6–20], [—], [—], [4], [$2^6$–$2^20$], [4,328–4,776],
      table.hline(stroke: 0.6pt),
    ))
  },
  caption: [Signature geometries: $n$ node bytes, $h$ total height in $d$ layers of height $h'$, few-time parameters $a, k$. Pants rows use $ell = 128$, $S = 192$. #super[‡]One PORS tree of $2^11$ leaves revealing 28, not $k$ trees of height $a$.],
) <params>

== Stateless signing: Baggy, Waistband, Corduroy

*Baggy* is a hypertree of $d$ layers of WOTS+C leaves whose bottom layer signs a few-time key. Over Keccak it runs on the bitsliced and isolated CNF engines of §3.1; *Corduroy* is the same shape over Poseidon2, and `CorduroyPoseidon2` is the stateless format Hem aggregates.

*Few-time layer.* Baggy uses a PORS tree [AE18] with forced pruning: one Merkle tree of $2^11$ secret leaves, of which a signature reveals 28 distinct message-selected leaves with one deduplicated multiproof. A subset is accepted only if its multiproof has at most 128 nodes (about one subset in $2^10$), and the signer grinds the public counter until one is. The layer takes at most 4,994 bytes and the signature at most 71,654.

#theorem("PORS+FP subset cover", src: [`PorsFpSecurity.sha3_128f_forgery_bound`])[
  After $g$ signatures under one tree, a fixed hash evaluation selects a subset inside the revealed leaves with probability at most $binom(28 g, 28) slash binom(2048, 28)$, for every acceptance predicate on subsets. At the deployed parameters this is at most $2^(-209)$, $2^(-157)$, $2^(-136)$, $2^(-122)$ for $g = 1, dots, 4$.
]

Because the bound holds for every acceptance predicate, pruning cannot weaken it.

*Signing* proceeds in three phases. Custodians first derive $R$ under MPC from $"SK.prf"$ and the message alone, so an abort after seeing $R$ forces any retry onto the same path. Since $R$ fixes every address, the few-time leaves and all subtrees on the path are then evaluated in one sweep (one PRF wave and three $F$ waves, whatever $d$ is) behind a single verification barrier. Finally the selected chain nodes open in one round.

*Waistband.* Upper layers sign child roots, which never change, so their leaves always open the same digits. Waistband caches the public material of the top $L$ layers and never a message-binding leaf. A corrupted cache could otherwise open a second codeword on an upper leaf; Baggy binds the cache to the key, verifies it up to $"PK.root"$ before any share opens, and records the first value signed at each cached leaf (`baggy_multiturn_durable_and_non_equivocating`).

*General $(t,n)$ committees.* Seeds are held in a CNF replicated sharing (`CnfRssKeyShare256`). Under an honest majority, $2(t-1) < n$, isolated custodians sign `Baggy` and all six FIPS 205 SHAKE parameter sets directly over encrypted pairwise channels without reconstructing shares or trusting a coordinator (`IsolatedCnfParty`, §3.1). For arbitrary $(t,n)$, a signing quorum of $t$ custodians converts locally by a public linear map into an additive $t$-of-$t$ sharing and runs the dishonest-majority engine (§3.2). Committees refresh or reshare from $(t,n)$ to $(t',n')$ without reconstructing the key or changing the public key.

== Stateful signing: Jorts and BeltLatch

*Jorts* is one Merkle tree of height $h$ over $2^h$ one-time WOTS+C leaves, in the manner of XMSS [BDH11]. A signature is a randomizer, a leaf index, a counter, 128 chain nodes and $h$ authentication nodes: $4,136 + 32 h$ bytes in the Poseidon2 format Hem consumes. Signing touches four oracle families only at their cheapest: the 128 chains of one leaf. In prepared mode the chains of upcoming leaves are evaluated and verified ahead of time, so the online protocol is one round of authenticated openings.

The scheme is secure only if no leaf signs two digests. *BeltLatch* enforces this locally.

#protocol("BeltLatch", src: [`belt_latch.rs`; extracted `BeltLatchKernel`])[
  Before releasing any share for leaf $e$ a custodian:
  1. persists $(e, "digest", "salt", "digits")$ behind a 72-byte anchored header (`generation || reservation || nonce`, tagged `QSAG.BELT.LATCH.WAL.MAC/v3`) and syncs it, the salt coming from a joint coin flipped after the message is fixed;
  2. on any later request for $e$, replays the persisted record and refuses a different digest or salt;
  3. exchanges SHAKE256/cSHAKE256 [SP800-185] custodian acknowledgments (`QSAG.BELT.ACK.v1`) of the record with its peers and requires the resulting permits to open.
  An unconfirmed local bind burns the leaf.
]

A crash can therefore waste a leaf and cannot reuse one. The journals keep their two high-water-mark slots on separate 4,096-byte pages, with the record chain starting at the third page.

#theorem("paged two-slot recovery", src: [`TwoSlotHwmCrashModel.paged_layout_safe`, `append_tear_truncate_recovers`])[
  In a crash model where any one sector under an unsynced write is arbitrary, the paged layout never recovers below an acknowledged counter, for every sector size dividing the page; recovery truncates an unauthenticated tail when the two slots hold $(c, c)$ or $(c, c-1)$ and the committed chain has length in ${c, c+1}$, and refuses otherwise. A layout with both slots in one sector loses state to a single tear.
]

No journal can detect that the whole disk or virtual machine was restored. §5.2 anchors the journals outside their rollback domain.

== Quorum switching over general access structures

With $n$ custodians, the local latch is not enough: two disjoint quorums could each latch a different message at one leaf. QSAG offers two disciplines.

*QS-A (partitioned leaves).* The $2^h$ leaves are split into $binom(n,t)$ disjoint ranges, one per $t$-subset, each shared additively within its subset. Any $t$ custodians sign from their own range in one round. Every committee contains an honest custodian whenever at most $t-1$ are corrupt, so each leaf is latched by someone honest. Capacity is divided by $binom(n,t)$ and the leaf index reveals the subset.

*QS-B (certified leaves).* All custodians share one tree, with chain states Shamir-shared. Before releasing a share for leaf $e$, a custodian requires a _latch certificate_: acknowledgments from a quorum that each has latched the same message at $e$. The classical condition is $2q > n + f$; it is one instance of the following.

#definition("asymmetric quorum system", src: [`qsag_quorum::access::AsymmetricQuorumSystem`])[
  Each participant $i$ chooses a family $cal(Q)_i$ of quorums and a downward-closed family $cal(F)_i$ of fault sets it is prepared to tolerate. The system satisfies $B^3$ [CT19] if for all $i, j$, all $Q_1 in cal(Q)_i$, $Q_2 in cal(Q)_j$, and every $F$ in both $cal(F)_i$ and $cal(F)_j$,
  $ (Q_1 inter Q_2) without F != emptyset. $
  A participant is _wise_ in an execution if the actual fault set lies in its family.
]

#theorem("leaf uniqueness", src: [symmetric case: `beltLatch_quorum_intersection_global_uniqueness`; general check: `verify_b3`])[
  Let the quorum system satisfy $B^3$, let honest custodians follow BeltLatch, and let $i, j$ be wise. If $Q_1 in cal(Q)_i$ certifies message $m_1$ at leaf $e$ and $Q_2 in cal(Q)_j$ certifies $m_2$ at $e$, then $m_1 = m_2$.
]

_Proof._ The actual fault set $F$ lies in both families, so some $h in Q_1 inter Q_2$ is honest. Its latch holds one record for $e$, and it acknowledged both certificates. $square$

With $cal(Q)_i = {Q : abs(Q) >= q}$ and $cal(F)_i = {F : abs(F) <= f}$ the condition reads $2q - n > f$; liveness under $f$ silent custodians adds $n - f >= q$, hence $n >= 3f+1$ (`beltLatch_safe_and_live_iff_n_ge_3f_plus_1`). Weighted quorums replace cardinalities by stake. Tree-composed policies, such as two chambers that must both approve, inherit $B^3$ from their components [ACTZ21]. Personal quorum systems in the style of Stellar [LGM19] are the case where each $cal(Q)_i$ is generated by slices, and the compilation of [ACKV26] reduces any $B^3$ system to a symmetric one for protocols of depth at least two. The library checks $B^3$ and availability constructively on explicit set families, and rejects a committee handoff (`verify_handoff_safety`) unless every old quorum meets every new quorum outside the fault sets common to both, since two individually safe configurations can fail across a boundary.

*Custody over monotone span programs.* Independently of who may _certify_, the key must be shared so that exactly the authorized sets can _sign_.

#definition("0/1 monotone span program", src: [`qsag_core::access::MonotoneSpanProgram`])[
  A matrix $M in {0,1}^(m times c)$ over $FF_p$ with a row-owner map $rho : [m] -> cal(P)$. A secret $s$ is shared by sampling $v = (s, r_2, dots, r_c)$ and giving $y_r = (M v)_r$ to $rho(r)$. A set $Q$ is authorized if $e_1 = (1, 0, dots, 0)$ lies in the row span of $M_Q$, the rows owned by $Q$.
]

#theorem("additive collapse")[
  If $Q$ is authorized there are public $lambda_r$, $rho(r) in Q$, with $lambda^top M_Q = e_1$; then the values $s_i = sum_(r : rho(r) = i) lambda_r y_r$ for $i in Q$ are an additive sharing of $s$. If $Q$ is not authorized, its shares are independent of $s$.
]

Shamir sharing is the Vandermonde case, CNF sharing the indicator case, and threshold trees compile by the Benaloh–Leichter construction. Because every authorized set collapses to an additive sharing by a public linear map, the signing circuit of §3 is unchanged: only the round-zero share conversion depends on the access structure. Entries in ${0,1}$ make that conversion additions only.

#protocol("isolated personal release", src: [`PersonalReleaseContext`, `PersonalReleaseParty`])[
  Over a framed wire transport, each custodian `PersonalReleaseParty` holds only its own `PersonalBeltLatch`, write-ahead log and span-program rows.
  1. Verify that `PersonalReleaseContext` matches the enrolled policy, span program, key context, epoch and signer set $Q$, persist the context digest in the WAL, and exchange receiver-authenticated acknowledgments over encrypted pairwise links.
  2. Upon assembling a valid $B^3$ certificate for $Q$, collapse owned rows to four `Goldilocks` lanes locally, reshare them point-to-point, establish pairwise Ring-LWE and KOS OT channels, authenticate inputs and 118 $x^7$ S-box tuples under a dealerless `GoldilocksExt2` MAC key, evaluate Poseidon2 compression, and run the two-stage blinded MAC test before opening the PRF-check digest alone.
]

No coordinator, driver or peer ever observes another custodian's released lanes.

*Equivocation evidence and grassroots blocklace.* Prevention can fail when a key is held by one party, or when more custodians are corrupt than any fault set allows. Then misuse is at least provable. By the incomparability theorem, two valid signatures under one key at one leaf on distinct digests exhibit a chain on which one signature reveals an earlier node than the other; together they let anyone forge, and together they are the evidence.

#theorem("equivocation evidence", src: [`JortsEquivocationEvidence::verify`, `BlocklaceLeafAnchor`])[
  The tuple $("pk", e, mu_1, sigma_1, mu_2, sigma_2)$ with $mu_1 != mu_2$ and both signatures valid at leaf $e$ is verifiable from the public key alone, needs no history or timestamps, and cannot be produced without two signing operations at $e$ by the key holder or a forgery of the scheme.
]

Both signatures are necessary: a pair of nodes on one chain, without the rest, can be manufactured from a single signature by hashing forward. The evidence is two signatures and a header: 8,800 bytes at height 6 and 9,440 bytes for a height-16 custody tree. `BlocklaceLeafAnchor` binds a constitutional root, epoch, sequence number, causal-tips digest and payload digest in a 120-byte frame enforcing $"seq" = e$, so in a grassroots blocklace [KLST26] a fork at sequence $e$ is identically a same-leaf equivocation, gossiped and acted on without replaying the lace. Rosters stay fixed between explicit reconfigurations; equivocators are excluded by causal past, so honest participants never disagree about quorum sizes.

*Aggregation bridge.* Poseidon2 Jorts chains are stepped under MPC directly on four-limb Goldilocks states, so a threshold committee emits the same `JortsPoseidon2` signature a single validator would, and Hem (§4) consumes it unchanged. A committee adds no bytes to an aggregate.

== Single-datagram few-time signatures

A validator voting every slot wants a signature that fits one datagram. `FrontierSumFts` maps a randomized digest bijectively onto a pair: a prefix-free antichain of $L$ nodes in a binary tree of height $h$, and chain offsets in $[0, w)$ summing to $S$. The number of codewords factors as $M(h,w,L,S) = N(h,L) dot D(L,S)$, and ranking is exact in 384-bit arithmetic (`frontierSumFts_rank_unrank_bijection`).

#figure(tbl((1.55fr, auto, auto, auto, auto, auto, auto, auto),
  [Profile], [B], [$n$], [$h$], [$w$], [$L$], [$S$], [Uses], table.hline(),
  [Compact1122], [1,122], [32], [8], [96], [34], [1,615], [1],
  [Full256Bit], [2,338], [32], [8], [5], [72], [144], [1],
), caption: [Few-time profiles. Both have 32-byte nodes and more than $2^256$ codewords.]) <ftsprofiles>

`Compact1122` with a 96-byte vote header is 1,218 bytes, inside the 1,232-byte payload of a minimum-MTU IPv6 datagram. Each key signs once; use is recorded durably first, through the paged journal of §2.4.

*Threshold few-time keys.* A threshold key is generated without a dealer over a 48-round $x^7$ block cipher on $FF_(2^128)^2$, whose MPC depth $48(1+w) + 8 = 296$ is independent of tree height. The ceremony consumes authenticated power tuples $(a, dots, a^7)$. Three observations make it practical: all products in a tuple share the factor $a$, so one batch of 128 oblivious transfers on the bits of $a$ serves three products (256 transfers per tuple instead of 7,552); a MAC is a product with a fixed key, so each MAC lane runs its transfers once and thereafter costs stream output; and squaring is additive in characteristic 2, so $a^2, a^4, a^6$ need a linear check, not triples (9 authenticated values per tuple instead of 25). The product phase for 1,024 tuples fell from 67.5 s to 0.31 s. The unspent preprocessing of a ceremony is serialized in an authenticated _reservoir_, so signing after a restart needs no second ceremony.

= Authenticated Multiparty Engines and Blinded MAC Openings

== Three-party bitslicing and isolated CNF committees

For $(2,3)$ custody, the bitsliced engine evaluates up to 256 independent Keccak-f[1600] instances in lockstep, packing bit $i$ of every instance into one SIMD lane [FLNW17], over replicated shares and against one malicious party with abort. Outputs stay sealed until a barrier after each wave: the gate transcript is hashed, a coin is flipped by commit-and-open, and every AND gate is checked by a sublinear distributed zero-knowledge proof [BGIN19] over $FF_(2^128)$. The proof folds in two passes, with ternary challenges in ${0, 1, gamma}^b$ expressed in a Frobenius basis so that folding is linear over $FF_2$.

#theorem("wave soundness", src: [`rss256_two_pass_product_proof_sound`, `rss256_sticky_poison_terminal_absorption`])[
  If any multiplication in a wave is incorrect, the two-pass proof accepts with probability below $2^(-217)$, and after any rejection the engine releases no further output.
]

For larger honest-majority committees ($2(t-1) < n$, such as 2-of-3, 3-of-5 and 4-of-7), `IsolatedCnfParty` generalizes replicated Boolean evaluation to one isolated custodian state per party over encrypted pairwise `WireTransport` links, without a coordinator or preprocessing ceremony.

#protocol("isolated CNF party", src: [`IsolatedCnfParty`, `IsolatedCnfSlhOracles`])[
  Each $(t-1)$-subset $S$ defines a slot held by the parties outside $S$, together with a 32-byte PRSS seed known only to those holders.
  1. _Maurer multiplication._ Each ordered pair $(S, S')$ is assigned to the smallest party outside $S union S'$ (nonempty since $2(t-1) < n$), which reshare-masks its local sum across PRSS streams and sends a single correction only to fellow holders of one designated slot.
  2. _Dual `GF(2^128)` authentication [CGH+18]._ Every wire $w$ carries a dual sharing $[r dot w]$ under a never-opened PRSS key $[r] in FF_(2^128)$. Before any opening, pairs of holders compare digests of every shared slot, toss a commit-and-open coin $(alpha_k)$, form $[T] = sum_k alpha_k ([r z_k] + [r][z_k])$ and $[rho dot T]$ for a fresh $[rho]$, compare slot digests again over the coin transcript, and open $rho dot T = 0$ (error $approx 2^(-126)$ per barrier).
  3. _Cut-the-Hash release._ After a two-round `QSAG.R_COMMIT/v1` hedged randomizer coin toss with commitment-echo verification, the party implements both `BaggyEngine` and `IsolatedCnfSlhOracles` (`slh_keygen`, `slh_sign`), poisoning its durable journal on any mismatch.
]

*Binary towers.* Larger stateful committees use Shamir sharing in Wiedemann's tower [Wie88],
$ cal(T)_0 = FF_2, quad cal(T)_(k) = cal(T)_(k-1)[x_(k-1)] slash (x_(k-1)^2 + x_(k-2) x_(k-1) + 1), $
with $cal(T)_3 = FF_(2^8)$ for share points (up to 255 parties, share size independent of $n$) and $cal(T)_7 = FF_(2^128)$ for MACs. Hardware multiplies in the polynomial basis $FF_2[z] slash (z^128 + z^7 + z^2 + z + 1)$.

#theorem("tower isomorphism", src: [`ringIsoTower128ToPoly`, `gf128FieldMul_eq_rustGf128Mul`])[
  There is an explicit ring isomorphism $cal(T)_7 tilde.equiv FF_2[z] slash (z^128 + z^7 + z^2 + z + 1)$ under which tower multiplication equals the shift-and-reduce loop of the Rust implementation, and hence the `PCLMULQDQ`, `VPCLMULQDQ` and `PMULL` kernels proved equal to that loop.
]

== The arbitrary-threshold engine

For general $(t,n)$, and for algebraic hashes, shares are Shamir shares over Goldilocks, $p = 2^64 - 2^32 + 1$, authenticated by SPDZ-style MACs [DPSZ12] in the quadratic extension. Poseidon2's S-box $x^7$ is evaluated in one round from a preprocessed mask with its powers: parties open $y = x - r$ and compute
$ [x^7] = sum_(k=0)^7 binom(7,k) y^(7-k) [r^k] $
locally (`power7BinomialEval_eq_sbox7`). Preprocessing has three layers.

*Base oblivious transfer* is built on Ring-LWE over $ZZ_(12289)[X] slash (X^1024 + 1)$ with a Fujisaki–Okamoto re-encryption check [FO99]. The receiver proves knowledge of its secret by an OR-proof with 24 challenges drawn from ${plus.minus X^k}$ (11 bits each: 264 classical bits, 132 under Grover search), and the public matrix $a$ is absorbed into the Fiat–Shamir hash. Differences of distinct challenges divide 2 in this ring, which gives special soundness (`signedMonomial_challenge_set_pairwise_invertible`). An $ell_infinity$ bound alone would not bind extraction to a hard problem, since the short-solution relation it yields admits a public unit solution for most $a$; prover and verifier therefore enforce a Euclidean bound under which that solution is excluded (`extract_rlwe_or_sigma_24_euclidean_sis_dichotomy`). Responses are sampled by rejection from a discrete Gaussian with statistical distance below $2^(-128)$ from a simulation.

*Extension and correlation.* KOS extension [KOS15] commits its columns before challenges are drawn. A dual-LPN correlation generator [BCGI+19] expands 64 regular-noise trees of depth 15, each seed usable once. Its tap matrix is generated by SHAKE256, and the bias of the deployed matrix is computed in the Lean kernel, not assumed: row 0 has bias strictly between $2^(-118)$ and $2^(-117)$ (`prodRow0_bias_bracket`), and a uniformly sampled row has second moment below $2^(-148)$.

*Triples.* Arithmetic and power tuples use sacrifice [KOS16]. Boolean triples are combined in buckets after a random permutation; the bucket size is the least $f$ with $n slash binom(f(n+1), f) <= 2^(-40)$ for a pool of $n$ bits ($f = 3$ at 8,192 words), and one bucket per pass is discarded so that the pool's parity is never revealed. A sacrifice whose transcript is frozen before the challenge accepts a wrong transcript on at most one challenge vector in $abs(FF)^tau$, whereas sampling first accepts always (`SacrificeFreezeSample`).

== Blinded MAC openings

A MAC check tests whether $d = m - alpha x$ is zero for an opened value $x$ with tag $m$ under key $alpha$. Opening $d$ is standard and safe when the key dies with the session. Here $alpha$ persists across sessions and across resharing, and an adversary that shifts an opening by a known $Delta$ obtains $d = -alpha Delta$ in the abort transcript: the key. Two situations make the shift reachable without tripping an earlier check, namely unanimous committees ($t = n$), which have no redundant share, and a malicious reshare dealer whose polynomial is degree-consistent but violates the MAC relation.

#protocol("blinded zero test", src: [`mac_blind.rs`])[
  Parties hold additive shares $d_j$ of the residual and each draws a private randomizer $r_i$.
  1. Commit to all value shares.
  2. Compute additive shares of $w = (sum_i r_i)(sum_j d_j)$ by oblivious linear evaluation in which the residual share is always the _sender_ input and the receiver's choice bits are fresh random masks.
  3. Commit to every share of $w$; then open $w$ alone and accept if and only if $w = 0$.
]

No bit of a residual or of a key is ever an OT choice, and no authenticated triple bootstraps the product, so the check is not circular. On a retained `OtMesh`, an offline batched OLE pre-populates a pool of single-use blinding triples $(r, a, c = r dot a)$ over $cal(T)_7$ with monotone per-mesh serials: each online check pops a triple, commit-opens $e = d + a$, and commit-opens $w = r dot e + c = r dot d$, cutting the three-party online MAC check from 13.75 ms (two inline 4,608-OT rounds) to 31 µs (4.04 ms amortized offline refill) and permanently poisoning and wiping the pool on any failure.

#theorem("zero leakage on abort", src: [`macBlind_abort_independent_of_alpha`, `macBlind_spdz_alpha_zero_leakage`, `macBlind_tower128_two_round_256bit_sound`])[
  In the ideal-OLE model, fix the corrupt inputs and let one honest randomizer be uniform in a field $FF$. If $d = 0$ then $w = 0$. If $d != 0$ then $w$ is uniform in $FF$; conditioned on abort it is uniform in $FF^times$ and independent of $alpha$; and the test accepts with probability $1 slash abs(FF)$. Over $FF_(p^2)$ this is $p^(-2) < 2^(-127)$; over $FF_(2^128)$ with two independent randomizers it is $2^(-256)$.
]

The proof is one line: for $d != 0$, $r |-> r d$ is a bijection of $FF$. Without blinding the residual determines $alpha$ (`tooth_unblinded_mac_residual_recovers_alpha`), and a zero randomizer accepts any forgery (`tooth_zero_randomizer_always_accepts_forged_mac`), which is why every party contributes one. Additive Boolean openings commit the whole residual vector and pass three transcript-bound linear projections through the same test, bounded by $(q^(-1) + (1 - q^(-1)) q^(-2))^3 < q^(-2)$ at $q = 2^128$ (`three_projection_mac_blind_bound`). For Shamir-shared values each degree syndrome and the constant term are blinded with independent randomizers.

*Refresh and resharing.* Shares are refreshed in place by adding a jointly generated sharing of zero, and reshared from $(t,n)$ to $(t',n')$ in two rounds without reconstructing the secret; old shares are erased and the monotone leaf mark carries across the transition. Resharing is where a persistent key is most exposed, since the dealer of a sub-share chooses its polynomial: the new committee verifies against all $n'$ members while dealing at the true threshold $t'$, so degree checks keep their redundancy, and every residual it opens goes through the blinded test.

All engines enforce the order _commit, verify, open_ in the type of their opening functions: an opening requires a token that only a successful check mints, so a faulted value cannot leak ahead of its MAC (`mac_before_open_blocks_faulted_cut_leakage`).

= Hem: Johnson-Radius WHIR and Holographic Recursion

== Arithmetization

Hem proves that $K$ signatures verify. The witness is a multilinear table over Goldilocks with 256 columns. Each row holds one width-12 Poseidon2 permutation (its inputs and 118 S-box outputs), a 44-limb machine state, and selectors for digest unpacking, chain steps, endpoint compression and Merkle steps. Row constraints have degree 8 and are reduced by one sumcheck [LFKN92] coupled with a shift claim between consecutive rows. All challenges come from the quartic extension
$ E = FF_p [v] slash (v^4 - 7), quad abs(E) = p^4 > 2^(255.99), $
because a quadratic extension caps Grover-amplified error at 64 bits (`ext2_error_denominator_cliff`).

A Jorts signer occupies 512 rows. Its program is 8 message rows, $1 + 64 dot 7 + 1$ chain rows, and two rows per tree level: $470 + 2(h - 6)$.

#theorem("height at no cost", src: [`test_jorts_configurable_heights_7_and_20_shard_aggregation`])[
  For every $6 <= h <= 20$ the signer program has at most $498 < 512$ rows and fits the existing columns. A key of $2^20$ one-time leaves is aggregated in the same trace cells, prover time and memory as a key of $2^6$.
]

*Corduroy in the trace.* The stateless format ($k = 32$ few-time trees of height 8 under 16 layers of height-4 subtrees, 76,896 bytes) verifies in 8,192 rows: its signers need no state and no rotation, at sixteen times the trace of a Jorts signer.

A shard of $2^24$ cells holds 128 Jorts signers or 8 Corduroy signers (8,192 rows each); the commitment admits up to $2^28$ cells.

*One Poseidon2.* Width-12 Poseidon2 [GKS23] over Goldilocks has 8 external and 22 internal rounds. Two 2026 analyses matter. With the external matrix $P_3 times.o M_4$ and a one-sided feed-forward, inputs in ${(X, -X, 0)}$ cancel across the linear layer and skip rounds [MRG26]; and subspace restriction skips internal S-boxes [BTA26]. QSAG deploys one profile everywhere (signatures, MPC, prover, shaders, silicon, and the Lean specification): external layer $M_4 times.o P_3$, which removes the cancellation (`poseidon2_kronecker_swap_kills_subspace_skip`); internal layer $M_I = J + "diag"(-64, 1, 2, 4, dots, 1024)$, for which the characteristic polynomial of $M_I^k$ is irreducible for $1 <= k <= 32$, so no power has an invariant subspace; and a compression that binds all twelve input lanes,
$ H(x_0, x_1, tau) = pi(x_0 || x_1 || tau)_(0..4) + x_0 + 2 x_1 + 4 tau. $

== WHIR with affine combiners

The table is committed and opened with WHIR [ACFY25] in stages. Stage $i$ folds up to six variables and re-encodes on a base-field coset $cal(D)_i subset FF_p$ at rate $rho_i in {1/4, 1/16, 1/64, 1/256}$. Each stage oracle is pinned at two out-of-domain points and committed in a salted Merkle tree (_Canopy_), opened by multiproofs with shared paths.

A scalar combination $f + alpha g$ of two Reed–Solomon words has proximity error $Omega(n slash q)$ over a field of size $q$, and a Johnson-regime analysis loses a further $n^2 L^7$ factor. Hem folds with the affine combiner of [CWYZ26],
$ w_(theta, alpha, beta)(z) = g(z) + (alpha + beta z)(f(z) + theta g(z)), $
whose error has no linear term in $n slash q$. Two properties make it cheap here. Since $z in FF_p$, the factor $alpha + beta z$ costs four base multiplications, not sixteen. And the degree map $d |-> floor(d slash 2) + 1$ has the fixed point $d_s <= 2^(ell - s) + 1$ (`affine_fold_degree_le_pow2_add_one`), so folding accumulates at most two overflow monomials; in monomial basis, multiplication by $z^2$ is a shift, and stage sizes stay powers of two.

*Eight wire regimes.* `WhirSecurityRegime` decodes eight wire tags (@regimes) across three outer hash functions: 24-round `cSHAKE256` [SP800-185], Role-1 12-round `TurboSHAKE256` [RFC9861] from precomputed customization midstates (`QSAG.PCS.TURBOCANOPY/v1`), and algebraic width-12 Poseidon2 for in-circuit recursion. Nothing is assumed beyond the Johnson radius $1 - sqrt(rho_i) - eta_i$: correlated agreement up to capacity is false [CS25], and proximity gaps fail arbitrarily close to it [KKH26]. Retired capacity-regime tags (`0, 1, 3`) do not deserialize, and classical-only `BciksJohnsonClassical128` (tag `2`, 72 nominal Grover bits) is confined to lower-level PCS tests and refused for aggregates.

#figure(tbl((2.55fr, 1.3fr, 0.45fr, 1.05fr, 1.15fr),
  [Regime (wire tag)], [Queries at rates $1/4$–$1/256$], [PoW], [Tree hash], [Oracle queries $Q$], table.hline(),
  [`BciksJohnsonQrom128` (4, default)], [258, 130, 88, 66], [16], [cSHAKE256], [unbounded (136b)],
  [`Cdhz25JohnsonQrom128` (5)], [202, 102, 70, 52], [16], [cSHAKE256], [$Q <= 2^38$ (108b)],
  [`Cdhz25ZeroPowQrom128` (6)], [216, 109, 74, 56], [0], [cSHAKE256], [$Q + 1 <= 2^40$ (107b)],
  [`Poseidon2Cdhz25JohnsonQrom128` (7)], [202, 102, 70, 52], [16], [Poseidon2], [$Q <= 2^38$ (108b)],
  [`Poseidon2Cdhz25ZeroPowQrom128` (8)], [216, 109, 74, 56], [0], [Poseidon2], [$Q + 1 <= 2^40$ (107b)],
  [`TurboShakeBciksJohnsonQrom128` (9)], [258, 130, 88, 66], [16], [TurboSHAKE256], [unbounded (136b)],
  [`TurboShakeCdhz25JohnsonQrom128` (10)], [202, 102, 70, 52], [16], [TurboSHAKE256], [$Q <= 2^38$ (108b)],
), placement: top, scope: "parent", caption: [Authorized WHIR aggregate regimes (7 of the 8 wire-decodable tags; classical tag 2 is test-only, and capacity tags 0, 1, 3 are rejected). Tags 4 and 9 use $ceil(512 slash log_2 (1 slash rho)) + 2$ queries per stage, giving 136 nominal bits of per-round Grover work with no bound on $Q$ (`meets_unconditional_grover_128_floor`). Tags 5–8 and 10 open 16–21% fewer positions (107–108 nominal per-round Grover bits) and achieve 128-bit security under [CDHZ25] salted-Merkle state restoration up to the stated $Q$; verifiers accept a bounded-query regime only when the caller names it.]) <regimes>

#theorem("constructive Johnson certificates", src: [`hemCwyz26JohnsonCert_sliced`, `HemSlicedFoldBudget.dfm184_budget_at_2pow27`])[
  For each of the 46 non-exhaustive stages of the default regime with $2 <= n_v <= 24$ variables, a binary affine fold of two words, at least one outside the Johnson radius, yields a word inside it with probability at most $2^(-184)$ over the challenges; the worst stage is $n_v = 22$, and the bound reaches $2^(-235)$ at small stages. Under measure-and-reprogram accounting [DFM20] this sustains error below $2^(-128)$ for $Q + 1 <= 2^27$ oracle queries.
]

The certificate is obtained by slicing the trivariate interpolant of [CWYZ26] along cylinders, which bounds non-excluded roots by a term linear in the agreement set plus a persistent term below $1906 slash p^4$. The sharper constant of [CWYZ26, Claim 4.8], below $2000 slash p^4$ per fold in total, would extend the same accounting to $Q + 1 <= 2^40$ over five Merkle roots; the schedules for $25 <= n_v <= 28$ are certified by finite witness tables checked in Rust. With salted trees, compressed-oracle state restoration [Zha19, CDHZ25] loses a factor linear in $Q$ in place of quadratic, which is what the bounded-query profiles account for.

*Three accountings, kept apart.* A round-by-round error $epsilon$ becomes a non-interactive bound differently in each quantum model, and conflating them is the usual source of overclaimed parameters. Under a single-round search bound [BBBV97, AHU19] the loss is $8(Q+1)^2 epsilon$. Under multi-round measure-and-reprogram [DFM20] it is $(2Q+1)^2$ per round, which is where the $2^27$ above comes from. Under compressed-oracle state restoration for salted Merkle commitments [CDHZ25] it is $O(Q^2 slash 2^256) + Q epsilon$, linear in $Q$, and at that rate the proved 184-bit fold bound stays below $2^(-128)$ beyond $Q = 2^50$. Tags 4 and 9 do not depend on which accounting one accepts for their query phase: with two slack queries per stage every stage has query error below $2^(-256)$, so the classical proximity analysis of [BCIKS20], halved for Grover search, already gives 128 bits.

The supporting mathematics is formalized constructively over the fraction field of univariate polynomials: Sylvester resultants and Gauss's lemma, division-free Hensel lifting, trivariate Guruswami–Sudan interpolation, Hasse-derivative stratification, the Johnson set-system bound, and a Welch–Berlekamp decoder that is sound without hypotheses, complete for $k + 2e <= n$, and runs in at most $2(n+2)^3 + 5(n+2)^2$ field operations (`WelchBerlekampDecoder`). Unique factorization, which is not constructive over a function field, is replaced by gcd splitting on demand.

== Holographic verification and recursion

A Hem verifier evaluates the multilinear extension of its constraint system at a random point. For a signature shard that system is uniform and the evaluation is cheap. For a relation that _verifies another proof_ it is millions of irregular entries, so the verifier is linear in the relation and cannot economically be placed inside itself.

#definition("shape hologram", src: [`ShapeHologram`, `ShapeVerifierKey`])[
  For a relation with sparse constraint matrices, the _hologram_ is a commitment to their row, column and value tables. Its _verifier key_ is the commitment roots and dimensions, under 256 bytes. A proof for the relation carries, in addition to its sumchecks, a lookup argument (LogUp with a GKR evaluation) that the matrix evaluation it used is consistent with the committed tables. Poseidon2 blocks, which dominate a recursive verifier, are not committed at all: their contribution has a closed form evaluated in $O(log)$ time.
]

Verification then depends on the relation only through its key: 11.5 ms on one core for the relations below, against 190–820 ms for direct evaluation.

#protocol("subtree recursion", src: [`SubtreeLeafMergeRelation`, `SubtreeInternalMergeRelation`, `SuccinctSubtreeAggregate`])[
  Fix an arity $b in {2, 4, 8, 16}$.
  - A _recursive shard_ is a signature shard proved with a Poseidon2 transcript and fixed-path openings, so that its verifier is a circuit of fixed shape.
  - A _leaf merge_ verifies up to $b$ recursive shards: their sumchecks, the row constraints at the opened point, and the openings. It checks that the witnessed keys hash to the shard's roster subtree, that each signer bit is Boolean, and that every signer signed the bound message.
  - An _internal merge_ verifies up to $b$ merge proofs against the fixed verifier key of the child relation.
  Every merge exposes the same public statement of 14 field elements:
  $ ("root"_(0..4), "epoch", "msg"_(0..5), k_min, k_max, "count", "weight"), $
  and an internal merge requires $k_max$ of each child to be less than $k_min$ of the next, sums counts and weights, and equates epochs and messages.
]

#theorem("interval disjointness")[
  In any merge tree, the key-index intervals $[k_min, k_max]$ of the leaves are pairwise disjoint. Hence no signer is counted twice, at any depth, without a bitmap.
]

_Proof._ Each leaf's interval contains its signers' indices. An internal node's interval is the hull of its children's, which are strictly ordered; induct on depth. $square$

In `SuccinctSubtreeAggregate`, the root is one proof for a relation of fixed size, so its length depends on $b$ alone: about 312 KiB at $b = 2$ and 340 KiB at $b = 16$. Checking child WHIR Merkle openings inside every internal circuit is what dominates internal relation size; separating the algebraic hologram IOP from the polynomial commitment cascade yields a contractive binary recursion that fits within $2^20$ rows per merge.

#protocol("contractive split recursion", src: [`SplitSubtreeRelation`, `SplitSubtreeAggregate`, `FoldedLevelWhirProof`])[
  Each binary internal circuit ($<= 1,048,576$ padded rows; `524,288` at depth 3) verifies both children's Spark/LogUp-GKR hologram sumchecks and roster/interval transitions, and commits to each child's `DeferredPcsClaim` digest and prior ledger root inside an 18-word public statement (`14` subtree words plus `4` `accumulator_root` words). At the root, `prove_root` groups all $M_ell$ homogeneous deferred claims at each tree level $ell in {0, dots, "depth" - 1}$ and folds them via a `[CWYZ26]` multilinear point-reduction sumcheck and correlated codeword combination into a single `FoldedLevelWhirProof` per level ($O("depth")$ WHIR cascades in place of $O(N)$), authenticated against the committed child roots by Steiner-deduplicated multiproofs.
]

The verifier's entire state is the 32-byte roster root, the epoch, the message, and a verifier key; the common roster-root verifier (`verify_succinct_subtree_aggregate_against_roster_root`) accepts either carrier through a sealed trait. In _dense_ mode a leaf merge hashes its shard's contiguous keys into a subtree root and internal merges hash upward. In _sparse_ mode each signer's path to a directory root of height up to 40 is opened inside the leaf merge, in the structured Poseidon2 region, and every merge carries the same root; a few hundred signers scattered through a directory of $2^37$ keys are certified in the same proof shape.

A merge has no private witness, so it is proved in _public_ mode: one committed table in place of five, no masking, and a public-input check weighted by powers of a challenge, with error at most $(m+1) slash p^4$ for $m$ public values. Its prover exploits structure: the selector is a prefix indicator carried as three words of state, the first sumcheck round runs on base-field tables, and S-box inputs are affine along a row pair, so the weighted S-box residual is a degree-7 polynomial costing about 24 extension multiplications per S-box where the direct form costs 34.

== Hiding relations

The same prover has a zero-knowledge mode (_zk-Hem_): five committed tables in place of one, sumcheck masking polynomials, and blinded openings. Three relations use it.

- *Credential presentation.* The holder's commitment lies under an accumulator root, the presented commitment rerandomizes it, the scope tag is well formed, and disclosed attributes and range predicates hold. For 32 attributes the proof is 239 kB.
- *Private multisignature.* For a policy address and a message, enough members signed. A hidden activity bit per slot, a prefix rule, increasing member indices and a range check on $sum "active" - t$ make the statement identical for every threshold, member count and signing subset.
- *Capabilities.* A bearer capability is $("id", "audience", "tag"_0, c_1, dots, c_n)$ with tags chained by $"tag"_(k+1) = H("tag"_k, c_k, k)$. A batch of up to 32 presentations proves for each: every caveat (expiry, not-before, resource, actions, amount) is satisfied by the public request; the capability's leaf, which binds $n$ and the final tag, lies under the issuer's root; a per-context presentation tag is correctly derived; and the identifier is not revoked.

#theorem("sorted-tree non-revocation", src: [`capability.rs`: `slot_gadget`, `enforce_gated_cmp_limbs32`])[
  Let the revocation tree hold strictly sorted identifiers between two sentinels. If adjacent leaves $r_"lo", r_"hi"$ at indices $(i, i+1)$ open under the epoch-bound root and $r_"lo" < "id" < r_"hi"$ as 256-bit integers on canonical limbs, then the identifier is not in the tree. The relation enforces canonicity of every limb and decomposes both indices into bits with $i_"hi" = i_"lo" + 1$, so neither comparison nor increment can wrap modulo $p$.
]

A holder cannot drop or alter a caveat (the result is a leaf that does not exist) and cannot open an ancestor's leaf (attenuation replaces the root tag by a one-way image). In _registered_ mode the issuer enrolls each attenuated leaf. In _delegated_ mode each attenuation is authenticated by a one-time target-sum signature under an ephemeral key carried in the chain, and the relation verifies the whole chain and possession of the terminal secret; only the first key is enrolled, and later hops need no contact with the issuer. Revocation is per identifier and covers a lineage.


= The Custody Lifecycle and the GPU Prover

== Derivation, addresses, policy and capabilities

*Hierarchical derivation.* Hash-based keys have no homomorphism, so a parent public key cannot derive child public keys. Custodians instead derive root shares and child keys from a ceremony over subset seeds ($n >= 2t - 1$) and publish a Merkle-committed inventory of child public keys for watch-only use; for module-lattice keys (`qsag-hd`), a public linear shift lets a watch-only party derive child keys alone. In the three-party case each custodian projects its replicated share of a child signing key directly from the subset seeds it already holds, so no host ever assembles a child secret. Each derivation consumes a slot of a durable, anchored query budget.

*Addresses.* Addresses are 67-character Bech32m strings [Wui20] that commit to a signature suite and a key, including hybrid keys pairing a classical with a post-quantum scheme under one pinned envelope. One function derives the policy key identifier from the suite and public key in every crate.

*Policy.* Spending rules (allowlists, per-transaction and rolling limits, approval tiers, separation of initiator and approver) are evaluated on MAC-authenticated shared state before any custodian releases a share. A successful evaluation mints a move-only release token for the exact key, message, context and quorum, which is split into one token per quorum member; a signer accepts only the token bound to its own party identifier, so a custodian holding two tokens cannot use both.

*Capabilities.* Three constructions cover the trade-off between size, offline delegation and privacy (@caps). A _SpongeMacaroon_ is a chained-MAC bearer token: each caveat rekeys the tag, and third-party discharges are bound to the presenting token. Appending a caveat can only narrow the authorized set, and any accepted alteration of a caveat chain yields a forgery of the chained MAC (`MacaroonAttenuation`). A _PqBiscuit_ replaces the shared key with public-key verification: each hop carries the root of the next one-time key and a `Compact1122` signature by the previous one, 1,154 bytes per hop, and a holder attenuates offline. The hop key is a value consumed by signing, and an authority key bundles up to 256 one-time roots under one 105-byte public key. The zero-knowledge capabilities of §4.4 hide the token and its caveats from the verifier. The policy engine evaluates any of the three against the trusted facts of a request before latching preprocessing.

#figure(tbl((1.5fr, 1.1fr, 0.9fr, 0.9fr, 0.8fr),
  [Capability], [Size], [Verifier holds], [Offline hop], [Hidden], table.hline(),
  [SpongeMacaroon, 3 caveats], [161 B], [secret key], [yes], [no],
  [PqBiscuit], [1,154 B per hop], [public key], [yes], [no],
  [zk capability, registered], [239 kB per batch], [two roots], [no], [yes],
  [zk capability, delegated], [one proof], [two roots], [yes], [yes],
), caption: [Capability forms. All share one caveat language.]) <caps>

== Anti-rollback anchors

The journals of §2.4 are crash-safe but cannot notice that their whole volume was restored from a snapshot. Every stateful object therefore reserves, then consumes, a single-use ticket from an _external monotone anchor_; replay, a failed persist, either crash point, and double consumption are all refused. Three concrete anchors are implemented in safe Rust (`#![forbid(unsafe_code)]`) and compose (`anti_rollback.rs`):

- `Tpm2NvMonotoneAnchor`: speaks raw ISO/IEC 11889 TPM 2.0 command/response frames (`TPM2_NV_Increment`, `TPM2_NV_Read` under `TPM_RS_PW`) directly over `/dev/tpmrm0` with zero C library dependencies, binding ledger checkpoints to a 64-bit hardware `TPM_NT_COUNTER` index through a crash-safe two-phase `(committed, pending)` seal;
- `VmGenIdForkGuard` and `HypervisorGenerationAnchor`: bind every checkpoint to the hypervisor's 128-bit ACPI `VMGENID` (`/sys/devices/virtual/misc/vmgenid`), Linux `boot_id`, and the guarded WAL file's `(st_dev, st_ino, st_ctime)` tuple, halting on any snapshot restore or volume clone;
- `FsDirectoryMonotoneAnchor`: a mirrored two-slot directory anchor on a separate mounted device (`st_dev` verified distinct unless explicitly waived), surviving the loss of either slot.

The command-line tool refuses to create or use stateful custody without an anchor unless the key is declared ephemeral, and a key enrolled with an anchor cannot later be used without it. After a committee is reshared, the old vault is retired at the anchor, so a restored copy of it is permanently refused. All records go through `LockedRecord`, which takes its lock on the held open-file description, refuses files with group or world permission bits, and opens without following links.

== Collaborative ZKBoo migration from elliptic-curve keys

To move an existing account to a post-quantum address, its owner must prove knowledge of the old spending scalar, bound to the new address and a Poseidon2 nullifier, in a way a quantum adversary cannot forge before the legacy public key is exposed. `qsag-migrate` runs both a local single-holder prover and a distributed collaborative ZKBoo (`CoZK`) prover (`CoZkCustodianShare`) for a 438-repetition mixed-domain proof [GMO16], $(2 slash 3)^438 < 2^(-256)$ classically and $(2 slash 3)^219 < 2^(-128.10)$ under generic Grover search, without reconstructing the legacy key on any host. Two actively secure outer MPC backends serve all four curve ecosystems: replicated 2-of-3 sharing (`outer_mpc`, no preprocessing, tolerating one malicious custodian) and MAC-authenticated $(t, n)$ Shamir or $n$-of-$n$ additive custody (`threshold_mpc`, `< 2^(-126)` batch MAC check on witness-independent `threshold_prep` material).

- *secp256k1*: Bitcoin P2PKH and P2WPKH, Taproot keys with pinned even-$y$ parity, and Ethereum `keccak256` accounts;
- *Ed25519*: Solana keys under SLIP-0010;
- *Pallas*: Zcash Orchard spend-authorizing keys, direct and rerandomized;
- *BLS12-381*: Ethereum `0x00` validator withdrawal credentials, proving ownership of the G1 scalar without publishing the public key.

When a chain has only ever seen a hash of the public key, the proof keeps that key hidden from Shor's algorithm. Prover throughput comes from batched XOR sub-seed clear tape expansion, zero-reallocation arena buffers, and 12-round `TurboSHAKE256` view-tree commitments (`COZK_VIEW_MAGIC_V4`). Before any wire or challenged ZKBoo view opens, every multiplication and Boolean-arithmetic conversion is checked by transcript-bound coin-flipped sacrifices: two-challenge Boolean checks with error below $(63 slash (2^128 - 1))^2 < 2^(-244)$ per flush, curve-field checks below $2^(-249)$, and cubic-Goldilocks checks below $2^(-186)$. Opening a residual early would recover the spending key (`tooth_premature_residual_open_recovers_spending_key`). Field tapes are sampled by rejection with zero modular bias.

== Threshold ML-DSA and oblivious PRFs

*Threshold ML-DSA.* For compatibility with FIPS 204 verifiers, QSAG threshold-signs ML-DSA-44, -65 and -87 with no dealer. Key material is Shamir-shared among $n <= 64$ custodians with $n >= 2t - 1$; a quorum of $2t - 1 <= 16$ converts to the replicated engine under checked multiplications and conversions. The difficulty peculiar to lattice signatures is rejection sampling: a rejected attempt's partial response, if seen, leaks the key. The high bits $bold(w)_1$ and the challenge stay shared until the norm and hint checks pass, and partial responses are one-time-padded until release.

#theorem("sealed abort", src: [`threshold_mldsa_abort_transcript_zk`])[
  At ML-DSA-44 dimensions, the view of a corrupt minority in an aborted attempt is identically distributed for any two keys consistent with the public accept/reject outcome.
]

Every attempt burns a nonce durably before it starts. The nonce ledger stores each session once: 33 bytes for a session whose burned attempts form a prefix, with further attempts of the same session recorded in place, and its generation counter must equal the number of attempts recorded, so a ledger with missing history cannot be opened.

*Oblivious PRF and credentials.* A $(t,n)$ threshold oblivious PRF over Poseidon2 serves rate-limited derivation and blind credential issuance. A 2-of-5 replicated form corrects one malicious server by unique decoding when all five servers participate online (`toprf_2of5_byzantine_unique_decoding`). The general SPDZ form, $2 <= t <= n <= 64$ with $t$ servers online, runs on the authenticated engine of §3.2 from a non-cloneable reservoir of preprocessed power tuples; a cursor advances before a range is returned, so no tuple is used twice. Input binding, one batched check over every S-box opening, and the output are each MAC-checked in that order through the blinded test of §3.3, and outputs are padded by client masks no server knows. A malformed client request costs one reservation; a failed MAC check poisons the reservoir. With the OT mesh retained, a $(2,3)$ evaluation takes 4.3 ms online. The reservation logic is modelled as a state machine whose counters ratchet on every server before any state changes and never recycle after a partial failure (`ToprfMachine.partial_reserve_burns_without_recycle`).

Blind issuance proves the blinded commitment with 438 repetitions of three-party ZKBoo over Goldilocks; soundness below $2^(-128)$ holds for $Q <= 2^60$ quantum queries (`blindVc_quantum128_qrom_fs_soundness`), with a constructive extractor that returns a witness or an explicit commitment collision. Selective-disclosure presentation is proved either as a 33-repetition, 256-party seed-tree MPC-in-the-head protocol over $FF_(p^5)$ ($256^(-33) = 2^(-264)$ classical soundness) or succinctly through the zk-Hem relation of §4.4 (239,507 B).

== GPU prover

The prover's cost is dominated by Reed–Solomon encoding, Merkle hashing and the row sumcheck, all data-parallel. A Vulkan compute backend with no external dependencies runs ten SPIR-V 1.5 shaders: six primitives (Keccak-f[1600], Poseidon2, Goldilocks NTT, coset extension, Poseidon2 Merkle layers, binary-field inner products) and four prover stages (two for row evaluation, one for encoding and tree commitment, one for folding and sumcheck). Prover stages keep the witness resident in VRAM across the whole proof; the host stages it in 32 MiB chunks and holds under 1 GiB.

*Twenty-six variables in 12 GiB.* A single storage buffer is limited to 4 GiB. The arena is split so that the largest buffer at $2^26$ cells is exactly 3.00 GiB: work buffers alternate between a full and a half extent, and stage buffers are indexed by parity. Kronecker tables for evaluation points use four byte-indexed factors, covering $2^32$ positions. A shard of 256 or 512 signers is then committed entirely on a 12 GiB card (5.3 and 9.9 GiB).

*One Merkle shader, four modes.* The Poseidon2 Merkle shader builds the signature scheme's weighted-compression trees, its two-block node sponge, the commitment's Canopy trees, and the fixed-tweak compression of the recursive verifier, each in one submission, so every tree in §4 has a device path.

*Admission.* Provers are admitted against a memory budget, so sixteen subnets of 128 signers queue through one device with about 3 GiB of host memory where an unconstrained CPU run needs 67 GiB. A batch too large for the arena falls back to the CPU prover and reports that it did; proof bytes are the same either way.

*Receipts and determinism.* CPU and GPU provers emit identical bytes. Every one of the ten shader slots can return a keyed receipt binding the pinned SPIR-V 1.5 digest, hardware pipeline audit digest, job descriptor, and digests of its inputs and outputs under cSHAKE256; the digest of a committed witness is independent of how the upload was chunked. A receipt is evidence for the party holding the key that a specific module ran, not hardware attestation. The compiled pipelines use no scratch memory and spill no registers on the measured driver, and session buffers are scrubbed between jobs. On Apple portability drivers (`MoltenVK`) lacking executable-property inspection, witness-bearing prover arenas remain gated until audited.

= End-to-End Constructive Formalization

The claims above are supported at four levels, each covering what the others cannot: protocol models, the Rust source, compiled machine code, and execution on hardware and silicon (@pillars).

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 5.5pt,
    panel([#smallcaps[Specification and protocol (`lean/Qsag/`, 269 modules)]\
      ideal functionalities · query-bounded assumptions · signing, custody, aggregation, coding theory]),
    align(center)[#sym.arrow.b refinement (`ErrSyncDataRefines`, `GuardedMachineSim`) #sym.arrow.b],
    grid(columns: (1fr, 1fr), gutter: 7pt,
      panel([#smallcaps[Extracted Rust MIR (`aeneas/`)]\
        8,674 audited decls · 114/114 6-kernel WHIR comparator · sponge & release guards]),
      panel([#smallcaps[Machine code & RTL (`Machine/`, `hardware/`)]\
        28 ELF kernels, ELF–Math–MIR triangles · 99/99 ASIC LEC miters + Obend Lean 4]),
    ),
    align(center)[#sym.arrow.t differential and physical checks #sym.arrow.t],
    panel([#smallcaps[Execution]\
      single-step cosimulation on Zen 5 · 74 differential/E2E suites · Verilator & BSIM4 SPICE]),
  )
}, caption: [Four levels of assurance and the direction of the links between them.]) <pillars>

== The Lean library

The protocol library is in Lean 4.35 [MU21] and comprises 269 modules (407,223 lines across `Tactic`, `Spec`, `Math`, `Coding`, `Oracle`, `Protocol`, `Custody`, `Exec`, `Machine`, `Top` and `Tests`). Three invariants are enforced mechanically by `scripts/check_lean_policy.py` and `audit-axioms`.

- *No `sorry` and no axioms beyond `propext` and `Quot.sound`.* An audit walks every declaration, public and private (`setExporting false`), and rejects anything else, including `Classical.choice` and `native_decide`. Excluded middle is unavailable, so an existence proof is a program: a reduction _computes_ the collision or forgery it promises, and a decoder _is_ the algorithm.
- *No `import all` and strict layering.* Every module begins with `module`, exposes at most 12 definitions (`LAW-M1`), and obeys a strict rank order from `Tactic` and `Spec` up to `Top` and `Tests` with zero `import all` edges anywhere in the library. Proofs cannot depend on another module's private representation.
- *Teeth.* Guards are paired across 43 `Tests/` modules with counterexample theorems (`#tooth`) exhibiting the attack that appears when a check is removed, alongside inhabitedness checks ensuring hypotheses are non-vacuous.

Six independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, and `con-ron`) replay 127 top-level theorems in `lean/comparator.json` from source-regenerated statements.

*Ideal functionalities and simulation kit.* `Spec/` defines five ideal state machines: `IdealSign`, `IdealCustody`, `IdealMigrate`, `IdealCred`, and `IdealAggregate`. `Exec/RefinesBridges.lean` introduces `ErrSyncDataRefines`, an error-synchronizing forward simulation that keeps state burned on failure (such as an epoch consumed by an aborted signature) in lockstep between concrete and ideal machines, while `Exec/GuardedMachineSim.lean` provides `GuardedMachine` combinators (`zoom`, `seq`, `prod`) composing the release guards.

#theorem("refinement of signing and distributed custody", src: [`Spec.latchedSigner_refines_ideal`, `distributedCustody_refines_idealCustody`])[
  The latched signer refines `IdealSign` unconditionally across arbitrary crashes and retries, and the distributed $(t,n)$ Shamir custody network (`DistCustody.distMachine`: per-custodian state, network buffer, adaptive corruption below threshold, and coordinator ledger) refines `IdealCustody` for its deployment identifier.
]

*Query-bounded assumptions.* Hardness quantified over all adversaries is false for a finite hash, since exhaustive search wins. Each game is built from a primitive, a sampler and an adversary with separated coins, and hardness is stated for the class of adversaries `Within` $q$ oracle queries.

#theorem("random-oracle bounds", src: [`Spec/Assumptions.lean`, §2i])[
  In the random-oracle model with $n$-bit outputs, every adversary `Within` $q$ queries wins the target-collision, preimage and interleaved-target-subset games with probability bounded by an explicit function of $q$ and $2^(-n)$, and the corresponding hardness classes are inhabited. Removing the query bound refutes each statement on the same game.
]

Forgery of a Pants signature is bounded by $Pr["forgery"] <= Pr["ITSR"] + Pr["TCR"] + Pr["PRE"]$ via a constructive extractor (`production_forgery_extract`). For WHIR (`ClosedWhirSchedule.lean`), the executable Fiat–Shamir QROM reduction (`whir_exec_closed_qrom_soundness`) has an unconditional one-stage non-vacuity certificate (`sampledQueryCert`), while the four-stage `nv = 24` statement (`deployed_whir_exec_closed_qrom_128`) remains parameterized by an open `WhirScheduleCert` hypothesis and the `whirAffineStageSimpleNum` MCA gap.

*Coding theory, oracles, and storage.* Over function fields, gcd splitting replaces non-constructive unique factorization. For quantum adversaries, Zhandry's block-compressed Fourier step [Zha19] is formalized for 256-bit blocks alongside a two-phase Merkle extractor failing on at most $(d + Q_2 + Q_1)(3 Q_1 + 1) slash 2^w$ of oracles. `Exec/PosixCrashWal.lean` models a volatile page cache, drive write-back cache, torn sector writes and open-file-description locks (`walModel_contract` in `Exec/PlatformContractInstances.lean`), proving epoch uniqueness across multi-crash traces (`reserve_before_sign_multi_crash_epoch_uniqueness`) at the deployed page offsets (`qsburn05_paged_offsets_match`).

== Extracted Rust

The checks on which secret release and WHIR verification depend live in two `#![no_std]`, `#![forbid(unsafe_code)]` crates translated from MIR to Lean by Charon and Aeneas [HP22] with zero `FunsExternal` axioms.

- *`aeneas/qsag-verified` #sym.arrow.r `aeneas/lean` (6,805 audited declarations, 0 rejected; 71 comparator theorems):* Weakest-precondition rules over the Aeneas `Result` monad (`MirWpKit.lean`) discharge Goldilocks and Wiedemann-tower arithmetic (`RealSpecFieldWeld`, `RealSpecTowerWeld`), Keccak-f[1600] (`RealSpecKeccakWeld`), byte-level sponge framing, and the session guards (`BeltLatchKernel`, `BdozOpeningGuard2Lane`, `VerifiedBeltQuorumGuard`, `MlDsaReleaseGate`, `StatefulVelocityGuard`). `aeneas/qsag-verified/extraction-coverage.json` classifies all 235 public functions: 63 lie on production call paths (the session guards and sponge), while 172 are `spec-welded`, `proof-only`, `test-only`, or unreferenced library items.
- *`aeneas/qsag-whir-verified` #sym.arrow.r `aeneas/lean-whir` (1,869 audited declarations, 0 rejected; 114/114 comparator theorems):* Covers all 37 `Funs.lean` definitions called by `qsag-agg` for canonical `Goldilocks`/`Ext4` decoding, `[CWYZ26]` affine and bridge folding, Horner evaluation, OOD pins, PoW masks, Merkle pair ordering, and quorum summation, welded to `Qsag.Exec.WhirKernels` (`QsagWhirVerified.Canonical`) and accepted by all six paranoid comparator kernels (`comparator-bwrap.py`).

#theorem("sponge framing and phase safety", src: [`SpongeFraming.lean`: `absorbBlocks_append_block`, `cshake256_32_refines`, `cshake256_squeeze_refines`; `RealSpecKeccakWeld.lean`: `shake256_absorb_after_squeezing_fails`])[
  For every nonempty customization string and every chunked input split, the extracted `Shake256Sponge` emits bytes identical to `Qsag.shake256Xof` and `Qsag.cshake256Xof` across arbitrary multi-block squeezes, and calling `absorb` after `finalize` deterministically fails with `.assertionFailure`.
]

== Machine code

The 28 hand-written assembly kernels (19 for x86-64, 9 for AArch64; 3,355 decoded instructions) are verified directly from compiled `.rlib` archive bytes. A Lean model of each ISA defines execution and a three-way leakage trace over program counters, memory addresses, variable-latency operands, and dirty upper-vector / NEON scratch state.

#theorem("kernel noninterference, DIT contracts, and ELF–Math–MIR triangles", src: [`McRefine.lean`, `ElfVerify.lean`, `PlatformContractInstances.lean`, `ElfMirTriangles.lean`])[
  All 19 x86-64 and 9 AArch64 compiled `.rlib` symbols satisfy `Spec.DitHardwareContract` (`rlib_x86_all19_dit_trace_data_independent`, `rlib_aarch64_all9_dit_trace_data_independent`), producing identical leakage traces from public-equivalent initial states; 26 of the 28 kernels are proved functionally equal to their mathematical specifications (the remaining two being bit-matrix transposes covered by noninterference and loop certificates); and seven end-to-end composition theorems (`elf_mir_goldilocks_{add,sub,mul}_x86_64`, `elf_mir_goldilocks_mul_aarch64`, `elf_mir_keccak_f1600_avx2_4x`, `elf_mir_gf256_gfni`, `elf_mir_tower128_pclmul`) equate decoded ELF execution with extracted Aeneas MIR through the canonical mathematical algebra.
]

A binary dataflow screen (`scripts/audit_elf_ct.py`) checks the four single-codegen-unit release archives (`x86_64` and `aarch64`, `std` and `no_std`) with 124 negative self-tests and zero violations. On the GPU side, `Machine/SpirvSimt.lean` and `Machine/PlatformContractInstances.lean` formalize Wave32 SIMT barrier-epoch noninterference (`simtEpochContract`) for the decoded Poseidon2 shader alongside an explicit address-disjointness formula check (`nttStageAddressModel`) for the nine fused stages of `goldilocks_ntt.comp`.

== Execution

Models are checked against hardware in both directions. The x86-64 kernels are single-stepped under `ptrace` on an AMD Zen 5 processor and compared register by register against the Lean ISA semantics: 59 cases and 7,184 vectors with zero mismatches. Executable Lean specifications match Rust across 277 shared known-answer vectors (`ExternalSpecOracle.lean`), and 74 standalone differential and end-to-end tests (`0` ignored) cross-check the workspace against 17 independent implementations, including full subtree recursion, threshold credential issuance to zk presentation, capability-gated custody, and journal fault injection. Empirical `dudect` timing tests [RBV17] stay within $abs(t) < 4.5$ against $> 1,600$ on a leaky control, and five sanitizer fuzz harnesses exercise wire decoders with canonical re-encoding (@matrix).

#figure(tbl((2.05fr, 1.95fr),
  [Gate], [Result], table.hline(),
  [`lean/Qsag` policy and build], [269 modules, 407,223 lines, 0 `import all`],
  [Extracted-MIR axiom audits (`lean` + `lean-whir`)], [6,805 + 1,869 decls, 0 rejected],
  [Six-kernel paranoid comparator (`Top` / MIR / WHIR)], [127 + 71 + 114 = 312 theorems],
  [Lean–Rust cross-language KATs], [277 vectors, 279 mutation checks],
  [Differential and end-to-end validation], [74 passed, 0 ignored],
  [Compiled `.rlib` DIT & CT archive screen], [28 kernels (19 x86-64, 9 AArch64), 0 errors],
  [Zen 5 single-step ISA cosimulation], [59 cases, 7,184 vectors, 0 mismatches],
  [Statistical timing (`dudect`) & fuzzing], [0 leak flags; 5 harnesses, 0 crashes],
  [SPIR-V 1.5 pins and GPU–CPU parity], [10 modules, bit-exact],
  [QSAG-NI ASIC formal LEC + Obend Lean 4], [99/99 miters, 5 ANF + 32 CSA certs, 0 `sorryAx`],
), caption: [Assurance gates. Sampled tests refute implementation bugs; they do not extend formal theorems.]) <matrix>

= Evaluation and Scaling

Measurements are single release runs on named hardware: an AMD Ryzen AI 9 HX PRO 370 (Zen 5), an AMD Ryzen 9 9950X, an Intel Core i9-12900, an AMD EPYC Milan (Zen 3), and an AMD Radeon RX 6750 XT (12 GiB, Mesa RADV). Consensus scaling projections are marked #model[model] and reproduced by `scripts/quorum_and_consensus_scaling.py`, whose self-test fails if any figure drifts. Silicon synthesis and formal-equivalence figures come from Yosys 0.71 / ABC, Z3, Bitwuzla, `nextpnr-ecp5`, and `ngspice` 45 (`sm141064.ngspice`) runs on `bb2` and `persvati`.

== Kernels

#figure(tbl((2.15fr, 0.85fr, 0.9fr, 0.65fr, 0.85fr, 0.9fr, 0.65fr),
  [Kernel (64 KiB / 256 coefficients)], table.cell(colspan: 3)[Zen 5, AVX-512], table.cell(colspan: 3)[Zen 3, AVX2],
  [], [Scalar], [Vector], [Ratio], [Scalar], [Vector], [Ratio], table.hline(),
  [Keccak-f[1600] (cpb; GB/s)], [3.366], [0.634 (3.15)], [5.31×], [6.437], [1.623 (1.48)], [3.97×],
  [SHA-256 (cpb; GB/s)], [4.900], [0.830 (2.41)], [5.90×], [8.876], [1.320 (1.82)], [6.72×],
  [$FF_(2^8)$ Shamir multiply (cpb; GB/s)], [14.66], [0.027 (73.2)], [537×], [28.29], [0.209 (11.5)], [135×],
  [$FF_(2^8)$ Shamir MAC (cpb; GB/s)], [14.32], [0.022 (91.5)], [654×], [27.66], [0.049 (48.7)], [561×],
  [$FF_(2^128)$ multiply-accumulate (cpb; GB/s)], [16.97], [0.058 (34.3)], [291×], [32.97], [0.250 (9.60)], [132×],
  [Tower MAC (cpb; GB/s)], [14.23], [0.303 (6.58)], [46.9×], [24.21], [0.653 (3.67)], [37.1×],
  [ML-DSA forward NTT (ns; cycles)], [809.3], [243.1 (485)], [3.33×], [1,197], [338.4 (812)], [3.54×],
  [ML-DSA inverse NTT (ns; cycles)], [931.2], [209.8 (419)], [4.44×], [1,401], [322.9 (775)], [4.34×],
  [ML-DSA pointwise multiply (ns; cycles)], [352.4], [56.7 (113)], [6.21×], [516.7], [98.8 (237)], [5.23×],
), placement: top, scope: "parent", caption: [Kernel throughput, medians of seven runs. Zen 5 uses 512-bit vectors with GFNI and VPCLMULQDQ; Zen 3 uses 256-bit vectors with a register-only split-nibble multiply.]) <simdbench>

The eight-way Keccak keeps all 25 lanes and its temporaries in registers, with no stack traffic, and reaches 0.634 cycles per byte (@simdbench). Across eight Merkle lanes one core hashes an internal commitment node in 111 ns and a 2,071-byte batch leaf in 778 ns. The ML-DSA transform follows [Sei18].

== Protocols

#figure(tbl((2.2fr, 1.7fr, 1.9fr),
  [Operation], [Setting], [Result], table.hline(),
  [Jorts, 2-of-3, prepared], [in memory / simulated WAN], [1.0 ms / 81 ms],
  [QS-A 2-of-3 / QS-B 3-of-7 ($q = 5$)], [encrypted channels, synced journal], [4.37 ms / 5.21 ms],
  [Pooled blinded MAC check (`OtMesh`)], [3 parties: online / offline refill], [31 µs / 4.04 ms],
  [Baggy or SLH-DSA, 2-of-3 bitsliced], [one wave of 256 hashes with check], [54 ms],
  [Isolated CNF Keccak wave (`cnf_party`)], [2-of-3 / 3-of-5 over `WireTransport`], [39.5 ms / 96.2 ms],
  [Compact1122, 1,200 votes], [one core / eight threads], [1.23 s / 158–187 ms],
  [Threshold few-time ceremony], [height 3, 418,560 tuples, 3 parties], [153 s],
  [Oblivious PRF, 2-of-3 / 3-of-5 ($q=3$)], [4 evaluations: offline / online each], [7.4 s, 4.3 ms / 21.6 s, 11.7 ms],
  [SpongeMacaroon, 3 caveats], [161 B], [1.8 µs verify], table.hline(),
  [Hem shard, 128 signers, CPU], [445,566 B; i9-12900 / 9950X], [3.67 s / 2.94 s; verify 3.0 ms],
  [Hem shard, 128 signers, GPU], [445,566 B, identical bytes], [1.33–1.56 s],
  [Hem shard, 256 / 512 signers, CPU], [480,342 B / 556,830 B], [5.68 s / 11.08 s],
  [Recursive shard, 128 / 512 signers], [9950X, child of a merge], [4.44 s / 17.02 s],
  [Hologram root proof], [one core], [11.5 ms verify],
  [zk credential, 32 attributes], [239,507 B (tag 7)], [0.28 s; verify 19.6 ms (one core)],
  [zk multisignature, 4 / 16 slots], [424,675 B / 700,491 B], [1.12 s / 3.48 s],
  [zk capability, batch 1 / 4], [238,747 B / 396,491 B], [0.26 s / 0.39 s; verify 4.0 / 8.7 ms],
), caption: [Protocol measurements. Hem shards use default tag 4; zk rows use tag 7. Pooled `OtMesh` blinding cuts the retained-mesh online MAC check from 13.75 ms to 31 µs.]) <protobench>

Signing with a prepared stateful key is one round, and its cost on durable media is the synced write (@protobench). Stateless signing runs either in 256-lane bitsliced waves or across isolated per-custodian CNF parties over encrypted channels. Proving is linear in signers, 15–23 ms each on a 16-core CPU and about 8 ms on the GPU, and a batch of 128-signer shards is cheaper in time and memory than one large polynomial.

== GPU

#figure(tbl((2.3fr, 0.8fr, 0.9fr, 0.7fr),
  [Workload], [GPU ms], [CPU ms], [Ratio], table.hline(),
  [Poseidon2, 262,144 permutations], [27.4], [2,138], [78×],
  [Keccak-f[1600], 262,144], [29.7], [104], [3.5×],
  [Goldilocks NTT, $2^20$], [21.4], [246], [11.5×],
  [Coset extension, $2^18 -> 2^20$], [16.0], [820], [51×],
  [Two-block Merkle tree, $2^18$ leaves], [23.3], [2,315], [99×],
  [Canopy tree, $2^20$ leaves], [81.6], [4,712], [58×],
  [Binary-field inner product, 262,144], [6.3], [68.9], [11×], table.hline(),
  [Round-0 commit, $2^25$ cells (256 signers)], [1,649], [—], [5.3 GiB],
  [Round-0 commit, $2^26$ cells (512 signers)], [3,401], [—], [9.9 GiB],
  [Four fold rounds, $2^25$ cells, 12 receipts], [191], [—], [—],
), caption: [RX 6750 XT, transfers included, against one CPU thread. The last column of the lower rows is VRAM in use.]) <gpubench>

Tree building gains two orders of magnitude and is where recursion spends its time (@gpubench). At $n_v = 25$ and $26$, native GPU openings complete in 624 ms and 1,098 ms after 1.14 s and 2.61 s commits (2.89 ms and 3.18 ms verify, zero CPU fallback). A 128-signer shard proves in 1.33 s with 0.2 GiB of host memory; for a subnet of 2,048 validators with one aggregator per 128-signer shard, the slowest stage completes in 1.14 s.

== Consensus scaling

A consensus protocol needs two things from signatures that pull in opposite directions: a vote small and fast enough for the live path, and a certificate that a third party can check later without the votes.

*Live path.* With an aggregate signature and a signer bitmap, the bitmap alone outgrows a 1,232-byte datagram beyond 9,088 validators, which is the observation behind distributed quorum signatures [KSW26]. A `Compact1122` vote with its header is 1,218 bytes at any validator count, so a sampled quorum of single-datagram votes scales where a bitmap certificate does not. Verification is the price: 1.03 ms per vote on one core, so 1,200 votes inside 150 ms need about nine cores (@live). Batching verifies independent signatures across the lanes of the eight-way Keccak kernel, a factor of 6.1 over scalar verification.

#figure(tbl((1fr, 1.2fr, 0.8fr, 1.1fr, 1fr),
  [Validators], [BLS + bitmap B], [One datagram], [Sampled votes], [One-core verify], table.hline(),
  [1,500], [284], [yes], [512], [0.52 s],
  [9,088], [1,232], [yes], [1,000], [1.03 s],
  [10,000], [1,346], [no], [1,200], [1.23 s],
  [1,048,576], [131,168], [no], [1,500], [1.54 s],
), caption: [Live path. Left: a bitmap certificate against the 1,232-byte limit (exact). Right: verifying a sampled quorum of 1,218-byte `Compact1122` votes with SIMD batching (measured rate).]) <live>

*Finality path.* Each validator also signs the checkpoint with a `JortsPoseidon2` key, whose $2^20$ leaves last a year of 30-second checkpoints, and aggregators fold the signatures into one certificate by the recursion of §4.3. The certificate is transferable: a bridge, light client or archive verifies it in 11.5 ms against the roster root.

#figure(tbl((0.95fr, 0.85fr, 0.85fr, 0.55fr, 0.75fr, 0.7fr, 0.65fr, 0.75fr, 0.75fr, 0.7fr, 0.65fr),
  table.cell(rowspan: 2)[Validators], table.cell(rowspan: 2)[Raw sigs.], table.cell(rowspan: 2)[Direct proofs],
  table.cell(colspan: 4)[LAN: 128-signer shards, arity 4], table.cell(colspan: 4)[WAN: 512-signer shards, arity ≤ 16],
  [Shards], [Levels], [Root], [Path], [Shards], [Schedule], [Root], [Path], table.hline(),
  [1,500], [6.8 MiB], [5.1 MiB], [12], [2], [321 KiB], [2.38 s], [3], [4], [321 KiB], [6.73 s],
  [2,048], [9.3 MiB], [6.8 MiB], [16], [2], [321 KiB], [2.38 s], [4], [4], [321 KiB], [6.73 s],
  [8,192], [37.3 MiB], [27.2 MiB], [64], [3], [321 KiB], [2.76 s], [16], [16], [340 KiB], [7.60 s],
  [16,384], [74.6 MiB], [54.4 MiB], [128], [4], [321 KiB], [3.14 s], [32], [8 · 4], [321 KiB], [7.41 s],
  [100,000], [455.5 MiB], [332.3 MiB], [782], [5], [321 KiB], [3.52 s], [196], [16 · 16], [340 KiB], [8.85 s],
  [1,048,576], [4.66 GiB], [3.40 GiB], [8,192], [7], [321 KiB], [4.28 s], [2,048], [16 · 16 · 8], [331 KiB], [9.53 s],
), placement: top, scope: "parent", caption: [One certificate for a validator set. Raw signatures and direct shard proofs are exact and measured; root sizes and critical paths are #model[model] (`SuccinctSubtreeAggregate`, one GPU per tree node, no network transfer). Verification is 11.5 ms (measured) in every row.]) <planetary>

@planetary gives the cost model for full in-circuit subtree merges. Its inputs are the measured shard and commit times of @protobench and @gpubench, a per-node merge time linear in the padded size of the merge relation (0.22, 0.38, 0.68, 1.25 s on a GPU at arity 2, 4, 8, 16), and a root size that is an exact count of sumcheck and lookup elements plus a fitted term for three openings. Two conclusions do not depend on the fitted constants.

_Arity is a latency–hop trade._ Root size grows by under 10 KiB when arity doubles while merge time doubles, so two quaternary levels (0.76 s) beat one 16-ary level (1.25 s). On a local network the fastest tree is narrow and deep: a million validators in seven levels, 4.28 s. Across a wide-area network each level is a round trip, and the best tree has 512-signer shards and three levels: 9.53 s, with a quarter as many leaf provers.

_Verifier cost is constant._ Without recursion, a certificate for $2^20$ validators is 8,192 shard proofs: 3.40 GiB and 51 core-seconds. The root proof is four orders of magnitude smaller and its verifier holds 32 bytes of roster. Building the roster tree is linear, 0.66 s for $2^20$ keys #model[model], and happens once per epoch. On the contractive binary split path (`SplitSubtreeAggregate`), depth-2 and depth-3 trees over dense and depth-37 sparse rosters execute end to end within $2^20$ internal rows (`524,288` at the depth-3 root) on both CPU and RX 6750 XT Vulkan.

The first row is the size of Solana's Alpenglow validator set, the next three are Ethereum Beam subnets and attester windows. For a four-second slot the model gives 3.83 s at 2,048 validators with 256-signer shards and one 8-ary merge, GPUs at every node; larger sets pipeline across slots.

== A certified causal web

The same statement extends from validator sets, which are dense and agreed in advance, to agreements among arbitrary subsets of a very large population. Consider $8 times 10^9$ people and $8 times 10^10$ software agents: $88 times 10^9 approx 2^(36.36)$ principals entering bilateral and multilateral agreements. Four costs rule out a global ledger at this scale: a total order over all agreements; signer bitmaps (16 GiB at $2^37$ bits) or key lists; a global revocation list, which requires agreement among all its verifiers; and delegation that needs the issuer online. The design that follows is a sizing exercise on components that exist, not a deployed system.

- *No global order.* Agreements are vertices of a blocklace [KLST26], each naming the causal tips of its participants, and each participant's safety rests on its own quorum system (§2.5). A _cut_ is certified by a merge proof whose statement adds the digest of the cut's tips to the roster and revocation roots. Proofs for cuts compose exactly as merges do, so a cut carries one constant-size certificate for its entire causal past.
- *No bitmap.* A directory of height 37 holds $1.37 times 10^11$ keys (@depths). A signer's membership path is 1,184 bytes of witness inside a sparse leaf merge and adds nothing to the proof.
- *Scoped revocation.* Each issuer keeps its own sorted revocation tree at its own tip. Non-membership at depth 37 is 74 permutations, and since $2^37 + 1 < p$ the index increment cannot wrap.
- *Offline delegation.* A PqBiscuit hop or a delegated zero-knowledge capability (§4.4) attenuates without contacting the issuer.

#figure(tbl((0.6fr, 1fr, 0.9fr, 0.9fr, 1.2fr),
  [Depth], [Capacity], [Bitmap], [Path B], [Non-membership], table.hline(),
  [20], [$1.05 times 10^6$], [128 KiB], [640], [40 perm.],
  [37], [$1.37 times 10^11$], [16 GiB], [1,184], [74 perm.],
  [40], [$1.10 times 10^12$], [128 GiB], [1,280], [80 perm.],
), caption: [Directory and revocation trees. A permutation is 118 S-box constraints in the relation.]) <depths>

Checkpoints of 320 KiB are too heavy for a stream of small agreements between two agents, so the design has three tiers (@tiers). The middle tier folds each step into a running claim with the affine combiner and defers the opening: 16 sumcheck rounds, a running commitment, a folded point and the cut statement, 3,104 bytes per step. Its folding relation exists in the prover; the streaming accumulator around it does not, and it is sized, not measured.

#figure(tbl((0.9fr, 1.9fr, 1.2fr, 1.1fr),
  [Tier], [Object], [Bytes], [Verify], table.hline(),
  [Session], [SpongeMacaroon; Compact1122 with key], [161; 1,218], [1.8 µs; 1.0 ms],
  [Edge], [deferred-opening affine fold #model[model]], [3,104 per step], [—],
  [Checkpoint], [root proof over a causal cut], [312–340 KiB], [11.5 ms],
), caption: [Three accumulation tiers for a causal web.]) <tiers>

== QSAG-NI: verified verifier silicon across ASIC and FPGA

Every verification in this paper (signatures, capabilities, and the recursive proof) reduces to five primitives on 64-bit words: Goldilocks arithmetic, where reduction is shifts and adds since $2^64 equiv 2^32 - 1$ and $2^96 equiv -1$; its quartic extension; width-12 Poseidon2; Keccak-p[1600]; and carry-less multiplication in $FF_(2^128)$. There are no pairings, no multi-precision multipliers, no Gaussian samplers and no division. That is the profile of an instruction-set extension, not an accelerator card.

#figure(tbl((2.6fr, 0.6fr, 0.6fr),
  [Block], [kGE], [Share], table.hline(),
  [Four-lane extension-field array, 36 multipliers], [524], [54.9%],
  [Poseidon2, 30-stage pipeline, one permutation per clock], [245], [25.7%],
  [Keccak-f[1600], two rounds per clock], [82], [8.6%],
  [Decode, canonical-range checks, transcript control], [65], [6.8%],
  [Carry-less multiplier and tower map], [38], [4.0%], table.hline(),
  [Total logic], [954], [],
), caption: [Analytical QSAG-NI unrolled logic budget #model[model], from published cores [CDK+26] and multiplier counts.]) <silicon>

#figure(tbl((0.7fr, 1.1fr, 0.6fr, 0.6fr, 1fr, 1fr, 0.7fr),
  [Node], [Area mm#super[2]], [GHz], [mW], [Verify µs], [Energy µJ], [Fold µs], table.hline(),
  [28 nm], [0.89 / 1.52], [1.0], [185], [34.0 / 15.0], [6.29 / 2.77], [180],
  [7 nm], [0.17 / 0.30], [1.6], [110], [21.2 / 9.4], [2.34 / 1.03], [112],
  [5 nm], [0.11 / 0.19], [2.0], [85], [17.0 / 7.5], [1.45 / 0.64], [90],
  [3 nm], [0.08 / 0.14], [2.2], [72], [15.5 / 6.8], [1.11 / 0.49], [82],
), caption: [Analytical 30-stage pipelined projection by node #model[model]: area with 128 / 512 KiB SRAM; root verify (Keccak / Poseidon2); $2^16$-row edge fold.]) <nodes>

@silicon and @nodes size an unrolled 30-stage pipeline (954 kGE, 15,000–34,000 cycles per root proof). To test that budget against real cell libraries and equivalence solvers, we implemented synthesizable SystemVerilog RTL for both standard-cell ASICs (`qsag_ni_asic_top` in `hardware/asic/`) and FPGAs (`qsag_ni_fpga_top` in `hardware/fpga/`).

*Synthesized ASIC (`hardware/asic/`).* Rather than 36 separate multipliers, `qsag_ni_asic_top` shares twelve 64×64 Dadda trees (with carry-save `2^64` and `2^96` Goldilocks folding and compound canonicalizers) across all twelve lanes of a Poseidon2 full round, a 4-way C-slowed Canopy batch engine (`P2_CANOPY4_BATCH`), and a single-cycle 9-product tower Karatsuba `GoldilocksExt4` multiply-add (`EMULADD`), paired with a 2-round/clock Keccak/`TurboSHAKE256` Canopy engine (`TS_CANOPY_BATCH`), single-cycle Karatsuba `GF(2^128)` and Wiedemann $cal(T)_7$ multipliers, and a 4-bank dual-port SRAM interface. Under delay-driven hierarchical Liberty synthesis (`synth/run_hier.py`, SRAM black-boxed), mapped logic stays below the 954 kGE budget across all four open PDKs (@asicsynth): *832.0 kGE* on `ASAP7` (7 nm predictive RVT), *832.6 kGE* on `IHP SG13G2` (130 nm), *862.9 kGE* on `Nangate45`, and *908.7 kGE* on `Sky130 HD`. Sharing multipliers trades single-chain latency (a serial permutation is iterated rather than 1 perm/clock) for area below 910 kGE while keeping parallel Canopy batches saturated.

#figure(tbl((1.35fr, 0.85fr, 1.45fr, 1.55fr),
  [Target], [Logic / LUT], [Multipliers / FFs], [Verification], table.hline(),
  [`ASAP7` 7 nm RVT], [832.0 kGE], [12 shared Dadda CSA], [99/99 LEC, 8/8 `QSAGSTA1`],
  [`IHP SG13G2` 130 nm], [832.6 kGE], [12 shared Dadda CSA], [99/99 LEC, 32 CSA certs],
  [`Nangate45` 45 nm], [862.9 kGE], [12 shared Dadda CSA], [99/99 LEC, 5 ANF certs],
  [`Sky130 HD` 130 nm], [908.7 kGE], [12 shared Dadda CSA], [Obend Lean 4 (`0 sorryAx`)], table.hline(),
  [UltraScale+ (`XCUP_RING`)], [86,496 LUT], [768 `DSP48E2`, 88.8k FF], [Z3 tiled DSP + ANF `GF(2^128)`],
  [Lattice `ECP5-85F`], [compact fit], [80 `MULT18X18D` (16 in P2)], [1.70M Verilator checks],
), caption: [Synthesized QSAG-NI silicon (`hardware/asic/`, `hardware/fpga/`). ASIC kGE excludes SRAM macros.]) <asicsynth>

*Formal hardware verification.* Monolithic bit-blasting of 12-lane 64-bit linear layers and 128-bit polynomial multipliers times out in SMT solvers. Decomposing the datapath along carry-save boundaries yields *99/99 decided Yosys + Z3/Bitwuzla equivalence miters* (`0` undecided, `0` failed, every positive miter paired with a `sat` fault mutant), backed by *32 carry-save adder certificates* (`lec_csa.json`), *5 exact algebraic-normal-form (ANF) certificates* (`check_anf.py`, proving bilinearity and monomial-for-monomial equality across all 128 output bits of `qsag_clmul64`, `qsag_gf128_mul`, `qsag_tower128_mul` and the basis maps), and a read-only *Obend Lean 4* hardware proof (`QsagNi.lean`, `0 sorryAx`) discharging the `2^64`/`2^96` folding congruences, `M_4`/`M_E`/`M_I` invertibility (Sherman–Morrison determinant numerator `3055`), and equivalence of 9-product tower Karatsuba `Ext4` to 16-product schoolbook multiplication. Verilator passes 70,724 unit checks and all 8 top-level workloads, including bit-exact replays of exported `QSAGSTA1` proofs under both Poseidon2 and `TurboSHAKE256` Canopy regimes.

*Synthesized FPGA (`hardware/fpga/`).* `qsag_ni_fpga_top` exposes one AXI4-Lite and 512-bit AXI4-Stream ISA across three parameterizations: `VU9P_TURBO` (unrolled 1 perm/clock Poseidon2, 511k LUT / 5,664 `DSP48E2`), `XCUP_RING` (21-slot C-slowed ring on Xilinx UltraScale+, 86,496 LUT and 768 `DSP48E2`, 7% LUT and 11% DSP of a VU9P), and `ECP5_COMPACT` (`qsag_p2_compact`, rotating the 768-bit Poseidon2 state through one 16-`MULT18X18D` Goldilocks multiplier in $<= 18$ LUT4/CCU2C levels alongside compact `Ext4`, lane-sliced Keccak, and Steiner-deduplicated `TurboSHAKE256`/`cSHAKE256` Canopy verification inside a single Lattice `LFE5UM5G-85F`). Z3 proves both `26×17` and `16×16` DSP multiplier tilings and the 136-bit Goldilocks reducer over all $2^128$ and $2^136$ inputs, and ANF verification checks all 40,832 monomials of the 3-stage Karatsuba `GF(2^128)` multiplier.

== Dregg-180: a physical custody enclave in 180 nm CMOS

Software journals and TPM counters still trust the host CPU assembling a signing request. _Dregg-180_ (`hardware/gf180mcu/`) moves Cut-the-Hash custody, verifier stream checking, and physical capability enforcement onto a standalone 5.0 V CMOS enclave for the `wafer.space` GlobalFoundries `GF180MCU` Run 3 shuttle (`gf180mcuD`, `gf180mcu_fd_sc_mcu7t5v0` cells and `gf180mcu_fd_io` 24 mA pads, `SLOT_0P5X0P5`: `1,936 × 2,531 µm` die, `1,052 × 1,647 µm = 1.733 mm²` core, 56 pads, zero hard SRAM macros).

*GALS shell and serial datapath.* The core clocks from an external pad or a 32-tap DCRO (registered one-hot tap select, tunable replica critical path, LFSR-dithered jitter) behind a glitch-free mux, speaking `QSAG-Wire v1` over x1/x4/x8 SPI, dual-simplex source-synchronous lanes, and a clockless Sutherland micropipeline on an `aoi222_1` Muller C-element. A word-serial datapath (4-clock Booth Karatsuba Goldilocks multiplier with parallel-prefix canonicalizer, 122-clock `Ext4` multiply, 3,074-clock Poseidon2, word-serial Keccak/`TurboSHAKE256`, digit-serial `GF(2^128)` MAC, and an external SPI FRAM two-slot monotone counter) shares one 25-lane sponge file. Five hardware capability organs govern key use:

1. *CapTP `SpongeMacaroon` vat (`dregg_captp_vat`).* Root $K_"vat"$ never signs raw host digests. Capabilities bind rights, guard flags, epoch window, spend ceiling, proximity ceiling, and a 256-bit key or ZK root under `TurboSHAKE256`, attenuated word-by-word through one 64-bit comparator across the sponge. Asynchronous-clear `latrnq_1` latches wipe metadata in zero clocks on tamper even if `clk_core` stops; sequencing uses 125 punctured `[12,7,4]` Hamming codewords (distance $>= 4$ from `0x000`, `0xFFF`, and one another) plus a non-bricking `OP_BIST`.
2. *64-RO PUF and `BCH(63,36,t=5)` (`dregg_ro_puf_bch`).* Sixty-four 5-stage `nand2_1` rings behind `RSZ-3006`-safe isolation buffers reconstruct $K_"vat"$ at boot via margin screening and a serial `GF(2^6)` Berlekamp–Massey/Chien decoder (zero nonvolatile secret bits on die), requiring 60 screened pairs per block (480 bits, $> 256$ bits min-entropy) against FRAM mask-starvation attacks.
3. *13.56 MHz HF-NFC and Direct-RF `NCO` (`dregg_nfc_nco`).* A hardware `÷16` (`847.5 kHz`) ISO/IEC 14443 subcarrier prescaler ahead of CDC prevents Nyquist aliasing at low core clocks, decoding CRC-16 Manchester co-approval frames, driving resistive load-modulation TX, and synthesizing phase-continuous CW, 2-FSK, or chirp beacons.
4. *Sub-5 ns `Brands–Chaum` responder and Vernier TDC (`dregg_distance_tdc`).* Shift-out 64-round $(r_0, r_1)$ masks feed one `mux2_4` between a `CS=0` CMOS input and an adjacent `SL=0` 24 mA output straddling `DVDD`/`DVSS` (`~2.9 ns` TT, `~4.6 ns` SS), while `.IE=1` `PAD2CORE` loopback cancels outbound pad delay into a reflection-locked 32-tap Vernier TDC with bubble-immune population count.
5. *Staggered `WOTS+C` self-check, `Metal5` shield, BSIM4 SPICE, and NFC PCB.* Before releasing $Y_j = F^(d_j)(X_j)$, the enclave reads $Y_j$ back from the egress buffer and checks $F^(w-1-d_j)(Y_j) = "PK"_("end", j)$ across two staggered cycles, zeroizing on mismatch. Four-quadrant glitch canaries and a 16-span `Metal5` serpentine shield (`dregg_shield_canaries`) guard the core; turnaround, TDC resolution, and 4-pad ground bounce are simulated in `ngspice` 45 (`sm141064.ngspice`, `brands_chaum_and_vernier_tdc.sp`, `pdn_ssn_ground_bounce.sp`) alongside a 4-layer `JLC04161H-7628` coil model (`planar_nfc_coil_calc.py`: $40 times 40$ mm 4-turn spiral over a $46 times 46$ mm `L2–L4` keepout, $L_2 = 1.47$ µH, $R_"ac" = 0.99 thin Omega$, $Q_"loaded" = 17.9$, $-3$ dB BW $759$ kHz).

*Status boundary.* `Dregg-180` passes Verilator `-Wall` (`0` warnings), all 593 datapath vectors across three register/latch configs, multi-link regressions (clock switch-overs, tamper/glitch wipe, FRAM rollback refusal), and Z3 Booth/parallel-prefix Goldilocks and `GF(2^128)` LEC. Baseline flat synthesis maps to $835,495$ µm#super[2] (48.2% of `SLOT_0P5X0P5`, before a sequential diet reclaiming $> 226,000$ µm#super[2]) and completes detailed placement; post-CTS LibreLane routing, multi-corner OpenSTA `Fmax`, DRC/LVS, and silicon entropy tests remain in flight before shuttle ordering.

#set page(columns: 1)

= Trusted Base and Scope

*Cryptographic assumptions.* (i) Keccak-p[1600] in its SHAKE256, cSHAKE256 and 12-round TurboSHAKE256 modes, and width-12 Poseidon2 in the single profile of §4.1, behave as random oracles within the adversary's query budget (target-collision, preimage and interleaved-subset resistance at 256-bit output, plus absence of sub-generic algebraic attacks on the hardened Poseidon2 profile). (ii) For dealerless SPDZ preprocessing only: Ring-LWE at dimension 1,024 and modulus 12,289, the Euclidean Ring-SIS relation extracted by the 24-challenge base-OT proof, and regular dual-LPN at the kernel-bracketed bias. (iii) For FIPS 204 compatibility only: the assumptions of ML-DSA. Three-party bitsliced signing, isolated honest-majority CNF signing, and Hem aggregation use (i) alone.

*Proof-system soundness.* Hem's query counts follow from the Johnson bound across all seven aggregate-authorized `WhirSecurityRegime` tags (`4–10`). Tags `4` (`cSHAKE256`) and `9` (`TurboSHAKE256`) sustain 136 nominal bits of per-round Grover search work with no query bound; tags `5, 7, 10` ($Q <= 2^38$) and `6, 8` ($Q + 1 <= 2^40$) are bounded-query [CDHZ25] profiles accepted only when named. Per-fold `[CWYZ26]` certificates are kernel-checked in Lean for all 46 stages with $2 <= n_v <= 24$ and checked by finite witnesses in Rust for $25 <= n_v <= 28$. In `ClosedWhirSchedule.lean`, the executable Fiat–Shamir QROM reduction (`whir_exec_closed_qrom_soundness`) has an unconditional one-stage non-vacuity certificate (`sampledQueryCert`), while the four-stage `nv = 24` theorem (`deployed_whir_exec_closed_qrom_128`) takes an open `WhirScheduleCert` hypothesis (with `whirAffineStageSimpleNum` exceeding the proved sliced MCA count), and the joint five-table hiding simulator is stated via its component lemmas rather than a single end-to-end composition theorem.

*Protocol and custody models.* Threshold engines provide active security with abort (not fairness): honest-majority engines (`Rss256Engine`, `IsolatedCnfParty`) tolerate $t - 1$ corruptions with $2(t-1) < n$, and SPDZ engines tolerate $n - 1$. The blinded MAC zero-leakage theorem is proved in Lean in the ideal-OLE model; security of the `OtMesh` triple pool and concrete KOS/MASCOT amplification rests on written reductions and fault-injection tests. `PersonalReleaseParty` runs over encrypted `WireTransport` links from dealer-enrolled span-program shares. `IdealSign` and distributed Shamir `IdealCustody` (`distributedCustody_refines_idealCustody`) are refined in Lean; `IdealCred` (`piToprfCredService`), `IdealMigrate` (under `SettlementCircuitSound`), and `IdealAggregate` (256-column AIR) are refined by protocol-level Lean state machines rather than MIR-extracted whole binaries. Single-state `rssSharedReleaseMachine_eq_reference`, `thresholdServiceShared_eq_ideal`, and Clause II of `Top/SecurityBounds.lean` are function equalities and closed-form rational evaluations, as documented in their module headers.

*Software and silicon artifacts.* The software TCB comprises the Lean 4.35 kernel (`{propext, Quot.sound}`, cross-checked on 312 exported theorems by five independent replay kernels), Charon/Aeneas and their 64-bit prelude semantics (with 63 of 235 `qsag-verified` functions on live production call paths and uncommitted Rust edits requiring re-extraction before release), `rustc`/LLVM outside extracted functions, single-codegen-unit archive compilation for the constant-time binary screen, OS entropy, and host storage `fsync` semantics. ISA noninterference covers decoded instruction timing, addresses, and named vector/NEON registers under x86-64 DOIT and AArch64 `PSTATE.DIT` assumptions (verified from compiled bytes on AArch64 and single-stepped on Zen 5). For silicon, `QSAG-NI` is synthesized pre-layout across four ASIC Liberty libraries (`832.0–908.7 kGE`, SRAM black-boxed) and two FPGA families with 99/99 compositional LEC miters and Obend Lean 4 proofs (`0 sorryAx`), without full-chip GDS signoff or vendor Vivado STA; `Dregg-180` is RTL-, LEC-, Verilator-, SPICE-, and placement-verified on `GF180MCU` `SLOT_0P5X0P5`, with post-CTS LibreLane routing, multi-corner OpenSTA `Fmax`, DRC/LVS, and silicon entropy characterization remaining before fabrication.

*Measured, synthesized, modelled.* All single-host software timings (§7.1–7.3), split subtree recursion runs through depth 3, ASIC/FPGA synthesis and LEC counts (§7.6), and `Dregg-180` RTL/SPICE/PCB figures (§7.7) are measured on the named artifacts. Multi-node WAN/LAN critical paths in @planetary, the streaming edge tier of §7.5, and the 30-stage pipelined 3–28 nm projection of @silicon–@nodes are reproducible analytical models (`scripts/quorum_and_consensus_scaling.py`). QSAG is a research prototype and has had no external audit.

#set page(columns: 2)

= Conclusion

Hash-based signatures publish nearly everything their signer computes, and QSAG is what follows from taking that seriously: threshold signing whose secret depth ignores tree height, stateful keys that any quorum system with honest intersections can use safely, and an aggregation proof whose verifier is small enough to verify itself—and small enough to synthesize below 910 thousand gates—so that a certificate for a million signers has the size and verification cost of a certificate for a hundred. Around these it supplies the unglamorous parts a custody system needs, from hardware-anchored journals and four-curve key migration down to a 180 nm capability enclave, and holds each of them either to a constructive, machine-checked statement or to an explicit accounting of where the proof stops.

#heading(numbering: none)[References]
#{
  set text(size: 7.4pt)
  set par(justify: false, leading: 0.38em, spacing: 2.6pt, hanging-indent: 1.6em)
  let refs = (
    [[ACFY25] G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT 2025.],
    [[ACKV26] I. Amores-Sesar, C. Cachin, S. H. Kamp, J. Villacis, "Symmetry all the way down", arXiv:2607.04887, 2026.],
    [[ACTZ21] O. Alpos, C. Cachin, L. Zanolini, "How to Trust Strangers: Composition of Byzantine Quorum Systems", SRDS 2021.],
    [[AE18] J.-P. Aumasson, G. Endignoux, "Improving Stateless Hash-Based Signatures", CT-RSA 2018.],
    [[AHU19] A. Ambainis, M. Hamburg, D. Unruh, "Quantum Security Proofs Using Semi-classical Oracles", CRYPTO 2019.],
    [[BBBV97] C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM J. Comput. 26(5), 1997.],
    [[BBD+26] D. Boneh, B. Bünz, Justin D., Y. Litchev, K. Nazirkhanova, "PRAWNS: Threshold Hash-Based Signatures from Threshold PRFs", IACR ePrint 2026/2142, 2026.],
    [[BCGI+19] E. Boyle, G. Couteau, N. Gilboa, Y. Ishai, L. Kohl, P. Rindal, P. Scholl, "Efficient Two-Round OT Extension and Silent Non-Interactive Secure Computation", ACM CCS 2019.],
    [[BCIKS20] E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed–Solomon Codes", FOCS 2020.],
    [[BDH11] J. Buchmann, E. Dahmen, A. Hülsing, "XMSS – A Practical Forward Secure Signature Scheme Based on Minimal Security Assumptions", PQCrypto 2011.],
    [[BDOZ11] R. Bendlin, I. Damgård, C. Orlandi, S. Zakarias, "Semi-Homomorphic Encryption and Multiparty Computation", EUROCRYPT 2011.],
    [[BGIN19] E. Boyle, N. Gilboa, Y. Ishai, A. Nof, "Practical Fully Secure Three-Party Computation via Sublinear Distributed Zero-Knowledge Proofs", ACM CCS 2019.],
    [[BHKN+19] D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, "The SPHINCS+ Signature Framework", ACM CCS 2019.],
    [[BLS01] D. Boneh, B. Lynn, H. Shacham, "Short Signatures from the Weil Pairing", ASIACRYPT 2001.],
    [[BS23] W. Beullens, G. Seiler, "LaBRADOR: Compact Proofs for R1CS from Module-SIS", CRYPTO 2023.],
    [[BTA26] A. S. Bhati, S. Tariq, T. Ashur, "From Round Skipping to S-Box Skipping: Attacking Poseidon's Partial Layer via Subspace Restriction", IACR ePrint 2026/1692, 2026.],
    [[Can01] R. Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols", FOCS 2001.],
    [[CDHZ25] A. Chiesa, Z. Di, Z. Hu, Y. Zheng, "How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions", IACR ePrint 2025/2166, 2025.],
    [[CDK+26] L. Campa, T. De Cnudde, A. Kindi, A. Roy, F. Schmid, M. Schofnegger, S. Trevisani, "BenX: Resource-Sharing Permutations for Computational Integrity", arXiv:2609.31087, 2026.],
    [[CGH+18] K. Chida, D. Genkin, K. Hamada, D. Ikarashi, R. Kikuchi, Y. Lindell, A. Nof, "Fast Large-Scale Honest-Majority MPC for Malicious Adversaries", CRYPTO 2018.],
    [[CS25] E. Crites, A. Stewart, "On Reed–Solomon Proximity Gaps Conjectures", IACR ePrint 2025/2046, 2025.],
    [[CT19] C. Cachin, B. Tackmann, "Asymmetric Distributed Trust", OPODIS 2019; extended version with O. Alpos and L. Zanolini, arXiv:1906.09314.],
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
    [[IM26] M. Ioffe, D. Malkhi, "QUASI: Post-Quantum Quorum Attestation of Pre-Validated Statements", arXiv:2611.10403, 2026.],
    [[KG20] C. Komlo, I. Goldberg, "FROST: Flexible Round-Optimized Schnorr Threshold Signatures", SAC 2020.],
    [[KKH26] D. Krachun, S. Kazanin, U. Haböck, "Failure of proximity gaps close to capacity", IACR ePrint 2026/782, 2026.],
    [[KLST26] I. Keidar, A. Lewis-Pye, E. Shapiro, N. Talmon, "Constitutional Consensus for Democratic Governance", arXiv:2505.19216, 2026.],
    [[KOS15] M. Keller, E. Orsini, P. Scholl, "Actively Secure OT Extension with Optimal Overhead", CRYPTO 2015.],
    [[KOS16] M. Keller, E. Orsini, P. Scholl, "MASCOT: Faster Malicious Arithmetic Secure Computation with Oblivious Transfer", ACM CCS 2016.],
    [[KSW26] Q. Kniep, J. Sliwinski, R. Wattenhofer, "Byzantine Fault-Tolerant Post-Quantum Distributed Quorum Signatures", arXiv:2607.17700, 2026.],
    [[LFKN92] C. Lund, L. Fortnow, H. Karloff, N. Nisan, "Algebraic Methods for Interactive Proof Systems", J. ACM 39(4), 1992.],
    [[LGM19] G. Losa, E. Gafni, D. Mazières, "Stellar Consensus by Instantiation", DISC 2019.],
    [[MRG26] S.-P. Merz, À. Rodríguez García, "Skipping Class: Algebraic Attacks exploiting weak matrices and operation modes of Poseidon2(b)", IACR ePrint 2026/306, 2026.],
    [[MU21] L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021.],
    [[RBV17] O. Reparaz, J. Balasch, I. Verbauwhede, "Dude, is my code constant time?", DATE 2017.],
    [[RFC9861] B. Viguier, D. Wong, "KangarooTwelve and TurboSHAKE", IETF RFC 9861, 2025.],
    [[Sei18] G. Seiler, "Faster AVX2 optimized NTT multiplication for Ring-LWE lattice cryptography", IACR ePrint 2018/039, 2018.],
    [[SP800-185] NIST SP 800-185, "SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash", 2016.],
    [[Wie88] D. Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly 26(4), 1988.],
    [[Wui20] P. Wuille, BIP-350: "Bech32m format for v1+ witness addresses", 2020.],
    [[Zha19] M. Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO 2019.],
  )
  for r in refs {
    par(r)
  }
}
