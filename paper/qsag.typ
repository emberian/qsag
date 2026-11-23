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

#place(top + center, float: true, scope: "parent", clearance: 14pt)[
  #align(center)[
    #set par(justify: false)
    #set text(hyphenate: false)
    #text(size: 16.5pt, weight: "bold")[QSAG: Quorum-Switching Threshold Hash Signatures and Succinct Post-Quantum Aggregation]
    #v(7pt)
    #text(size: 11pt)[ember arlynx]
    #v(2pt)
    #text(size: 8.5pt, fill: luma(60))[`ember@lunar.town`]
  ]
  #v(9pt)
  #block(inset: (x: 16pt))[
    #set par(justify: true, leading: 0.46em)
    *Abstract.* QSAG lets a changing quorum of custodians sign with one hash-based key and lets a verifier check a committee’s signatures in one proof. Cut-the-Hash evaluates four secret oracle families inside multiparty computation and builds the public Merkle layers in the clear. On matched inputs, threshold SLH-DSA produces the single signer’s FIPS 205 signature bytes. Durable reservations and quorum intersection prevent a stateful key from spending the same leaf twice. Hem aggregates signatures with sumcheck and Johnson-radius WHIR over the quintic Goldilocks field. For a four-key committee with three active signers, the public proof occupies 360,391 B with TurboSHAKE256 or 381,661 B with Poseidon2. The binary recursive construction fixes the [DKT26] root at 639,673 B independent of depth. Lean also bounds straight-line tree extraction for a recursive margin schedule through depth 16 at $Q <= 2^64$ quantum queries. We describe the migration and credential protocols, the Lean and extracted Rust assurance evidence, and autonomous proof verification in RTL, with mapped area on two 130 nm libraries and routed timing on an ECP5 FPGA.
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

_Hem_ (§4) encodes signature verification in a 256-column trace. Sumcheck reduces the constraints to an evaluation claim, which WHIR [ACFY25] opens over the quintic extension of Goldilocks. Regional verifiers can check each public shard against their registry. A verifier of a contiguous binary tree of Jorts shards can instead check one fixed-size recursive root. Hiding relations use zk-Hem v2 for credentials, private multisignatures, capabilities and migration.

§5 describes the custody lifecycle and GPU primitives. §6 gives the scope of the protocol proofs, extracted Rust kernels and machine-code checks. §7 reports signing measurements, validator-set proof sizes, and the evidence for each hardware target. §8 states the assumptions needed to apply these results.

#block(sticky: true)[*Contributions.*]
- *Cut-the-Hash and Pants (§2).* A four-oracle boundary giving height-independent secret depth; byte-identical threshold SLH-DSA; stateless Baggy with a pruned PORS few-time layer; stateful Jorts with $2^6$ to $2^20$ signatures per key; 1,122-byte single-use signatures; and a four-hop full-adversary EUF-CMA reduction (`< 2^(-128)` classical and QROM).
- *Isolated CNF, dealerless personal release, and general access structures (§2.4–2.5, §3.1).* Leaf uniqueness from pairwise honest intersection, isolated per-custodian honest-majority signing over deployment-bound wire channels, dealerless personal MSP enrollment and release with no coordinator, and self-contained blocklace equivocation evidence.
- *Active-sacrifice pooled blinded MAC openings and `SoftSpokenOT` (§3.2–3.3).* Subfield VOLE OT extension (`k = 2`, 512 Ring-LWE base OTs [Roy22]) and a zero test on $w = (sum r_i)(sum d_j)$ backed by Beaver-sacrificed single-use OLE blinding triples that keeps a persistent authentication key information-theoretically hidden on abort at 31 µs per online check.
- *Aggregation (§4).* Across 13 schedules, the public and hiding proof systems have modeled QROM soundness error below $2^(-128)$ for $Q <= 2^64$. Binary recursion uses a degree-two sumcheck to carry a fixed public-matrix evaluation claim between levels.
- *Formalization (§6).* Lean 4.35 and two Aeneas MIR packages contain 148,052 audited declarations. Six kernels replay 326 challenge theorems and 35 definitions across the three packages.
- *Hardware (§7).* QSAG-NI v2 autonomously verifies serialized public and hiding proofs. We report its open-foundry logic area and routed FPGA frequencies, the physical custody boundary of ASS2-0P5, and the AWS F2 shell’s end-to-end cosimulation.

*Related work.* PRAWNS [BBD+26] thresholdizes hash-based signatures through lattice-based threshold PRFs, placing a lattice assumption on the signing path; QSAG keeps leaf derivation inside symmetric MPC [FLNW17, CGH+18, BGIN19, BDOZ11, DPSZ12] and emits standard FIPS 205 signatures. Lifetime-capped SPHINCS variants trade signature size for a bound on signatures per key; QSAG instead enforces anchored reservation before release. LaBRADOR [BS23] attains smaller proofs from Module-SIS; Hem assumes only hash functions. Recent XMSS aggregators adopt capacity-regime parameters and Poseidon2 modes exposed to [MRG26, BTA26]; Hem uses Johnson-radius query schedules and distinct commitment profiles for public and hiding proofs. For consensus, distributed quorum signatures [KSW26] and QUASI [IM26] study post-quantum attestations that avoid signer bitmaps; our dual-path design (§7.4) is complementary. Asymmetric trust [CT19, ACTZ21, ACKV26], personal quorum systems [LGM19] and the blocklace [KLST26] supply the quorum and ordering models we instantiate. Blind credential issuance builds on MPC-in-the-head [IKOS07, GMO16].

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

*Extension and correlation.* Both KOS extension [KOS15] and interactive `SoftSpokenOT` ($n_C = 256, k = 2$, 512 Ring-LWE base OTs for 128-bit Grover resistance on $Delta in FF_2^256$, consistency error $<= 2^(-241) + B^2 slash 2^256$ [Roy22], `softspoken_consistency_simulation_budget`) commit their columns before challenges are drawn. A dual-LPN correlation generator [BCGI+19] expands 64 regular-noise trees of depth 15, each seed usable once. Its tap matrix is generated by SHAKE256, and the bias of the deployed matrix is computed in the Lean kernel, not assumed: row 0 has bias strictly between $2^(-118)$ and $2^(-117)$ (`prodRow0_bias_bracket`), and a uniformly sampled row has second moment below $2^(-148)$.

*Triples.* Arithmetic and power tuples use sacrifice [KOS16]. Boolean triples are combined in buckets after a random permutation; the bucket size is the least $f$ with $n slash binom(f(n+1), f) <= 2^(-40)$ for a pool of $n$ bits ($f = 3$ at 8,192 words), and one bucket per pass is discarded so that the pool's parity is never revealed. A sacrifice whose transcript is frozen before the challenge accepts a wrong transcript on at most one challenge vector in $abs(FF)^tau$, whereas sampling first accepts always (`SacrificeFreezeSample`).

== Blinded MAC openings

A MAC check tests whether $d = m - alpha x$ is zero for an opened value $x$ with tag $m$ under key $alpha$. Opening $d$ is standard and safe when the key dies with the session. Here $alpha$ persists across sessions and across resharing, and an adversary that shifts an opening by a known $Delta$ obtains $d = -alpha Delta$ in the abort transcript: the key. Two situations make the shift reachable without tripping an earlier check, namely unanimous committees ($t = n$), which have no redundant share, and a malicious reshare dealer whose polynomial is degree-consistent but violates the MAC relation.

#protocol("blinded zero test", src: [`mac_blind.rs`])[
  Parties hold additive shares $d_j$ of the residual and each draws a private randomizer $r_i$.
  1. Commit to all value shares.
  2. Compute additive shares of $w = (sum_i r_i)(sum_j d_j)$ by oblivious linear evaluation in which the residual share is always the _sender_ input and the receiver's choice bits are fresh random masks.
  3. Commit to every share of $w$; then open $w$ alone and accept if and only if $w = 0$.
]

No bit of a residual or of a key is ever an OT choice, and no authenticated triple bootstraps the product, so the check is not circular. On a retained `OtMesh` (and wire `PartyOtEndpoint`), an offline batched OLE generates live single-use blinding triples $(r, a, c = r dot a)$ alongside companion sacrifice triples over $cal(T)_7$ or $FF_(p^2)$, executes a two-round echo-committed Beaver sacrifice check before sealing any triple into the pool (error $< 2^(-255)$ per staged triple), and assigns monotone per-mesh serials: each online check pops a triple, commit-opens $e = d + a$, and commit-opens $w = r dot e + c = r dot d$, cutting the three-party online MAC check from 13.75 ms to 31 µs (4.04 ms amortized offline refill) and permanently poisoning and wiping the pool on any failure.

#theorem("zero leakage on abort", src: [`macBlind_abort_independent_of_alpha`, `macBlind_spdz_alpha_zero_leakage`, `macBlind_tower128_two_round_256bit_sound`])[
  In the ideal-OLE model, fix the corrupt inputs and let one honest randomizer be uniform in a field $FF$. If $d = 0$ then $w = 0$. If $d != 0$ then $w$ is uniform in $FF$; conditioned on abort it is uniform in $FF^times$ and independent of $alpha$; and the test accepts with probability $1 slash abs(FF)$. Over $FF_(p^2)$ this is $p^(-2) < 2^(-127)$; over $FF_(2^128)$ with two independent randomizers it is $2^(-256)$.
]

The proof is one line: for $d != 0$, $r |-> r d$ is a bijection of $FF$. Without blinding the residual determines $alpha$ (`tooth_unblinded_mac_residual_recovers_alpha`), and a zero randomizer accepts any forgery (`tooth_zero_randomizer_always_accepts_forged_mac`), which is why every party contributes one. Additive Boolean openings commit the whole residual vector and pass three transcript-bound linear projections through the same test, bounded by $(q^(-1) + (1 - q^(-1)) q^(-2))^3 < q^(-2)$ at $q = 2^128$ (`three_projection_mac_blind_bound`). For Shamir-shared values each degree syndrome and the constant term are blinded with independent randomizers.

*Refresh and resharing.* Shares are refreshed in place by adding a jointly generated sharing of zero, and reshared from $(t,n)$ to $(t',n')$ in two rounds without reconstructing the secret; old shares are erased and the monotone leaf mark carries across the transition. Resharing is where a persistent key is most exposed, since the dealer of a sub-share chooses its polynomial: the new committee verifies against all $n'$ members while dealing at the true threshold $t'$, so degree checks keep their redundancy, and every residual it opens goes through the blinded test.

All engines enforce the order _commit, verify, open_ in the type of their opening functions: an opening requires a token that only a successful check mints, so a faulted value cannot leak ahead of its MAC (`mac_before_open_blocks_faulted_cut_leakage`).

= Hem: Johnson-Radius Quintic WHIR and Depth-Independent Recursion

== Signature traces and the challenge field

The public trace encodes `JortsPoseidon2` or `CorduroyPoseidon2` verification over Goldilocks. Each row has 256 columns, including the 118 S-box outputs of a width-12 Poseidon2 permutation. A public bitmap identifies the signing slots. In `hem_quintic/rows.rs` the verifier pins all 138 non-S-box columns of each inactive padding slot to canonical zero. The permutation equations then determine its S-box outputs. Padding therefore gives the prover no free state at the boundary between signers.

Base-field rows keep the witness compact. Sumcheck and WHIR draw challenges from the extension
$ E = FF_(p^5) = FF_p[X] slash (X^5 - 3), quad p = 2^64 - 2^32 + 1. $
Its size exceeds $2^(319.99)$. In the power basis, Frobenius scales coefficient $i$ by $zeta_5^i$, since $X^p = zeta_5 X$. Here $zeta_5 = 3^((p-1)/5) mod p$ equals 1,041,288,259,238,279,555. A canonical `Fp5` value has five base-field limbs.

== Public committee aggregation

`prove_hem_quintic_128` proves the active signatures for the committee keys and signing mode. `verify_hem_quintic_128` takes those public inputs and checks the `HemQuintic128` proof (`QSAGHQM2`). Sumcheck [LFKN92] reduces the trace constraints to an opening. WHIR folds the resulting Reed–Solomon words using affine challenges [CWYZ26]. For a domain point $z$ and words $f, g$, the combiner is
$ g(z) + (alpha + beta z)(f(z) + theta g(z)). $
The verifier checks sampled fibers against their Canopy commitments. The two `HemQuinticProfile` variants differ in their digest representation (@publicprofiles).

#figure(tbl((1.15fr, 1.4fr, 1fr),
  [Profile], [Canopy digest], [Proof bytes], table.hline(),
  [`TurboShake400`], [TurboSHAKE256, 50 bytes], [360,391],
  [`Poseidon2Gl24`], [Poseidon2-GL-w24, 7 limbs], [381,661],
), caption: [Serialized public proofs for the same four Jorts keys, shared message and active slots 0, 2 and 3. The digests are 400 and 448 bits, respectively.]) <publicprofiles>

#theorem("public committee soundness", src: [`PublicHemQuintic128.lean`, `publicHemQuintic_qrom_soundness_128`])[
  For each of the 13 schedules with $16 <= "logCells" <= 28$ and $Q <= 2^64$, the public profile’s QROM soundness error under the [CDHZ25] reduction and ideal-hash model is below $2^(-128)$. Stage 0 takes 267 queries for $2^16$ through $2^23$ cells and 266 for $2^24$ through $2^28$ cells under the [DKT26] schedule.
]

== Regional composition and binary recursive IVC

`HierarchicalHemAggregate` (`QSAGHEM\x04`) carries one `QSAGHQM2` proof per regional shard. `prove_hierarchical_hem_prepared` binds the shards to a `PreparedPolicyRegistry`. The verifier, `verify_hierarchical_hem_prepared`, checks the regional policies and proofs against an independently supplied registry. Adding a region adds its proof and framing to the wire.

The binary IVC API in `crates/qsag-agg/src/zk_hem/recursive_ivc/` proves a power-of-two run of contiguous Jorts shards. `prove_ivc_tree` returns a `SuccinctIvcProof`. Its public statement names the policy registry root, message digest, half-open shard interval and total quorum count. A parent must join adjacent child intervals under the same registry and message.

#protocol("binary recursive step", src: [`IvcTreeStepRelation`, `FixedPathWhirW24` (`QSAGIW24`)])[
  Each internal step checks both child WHIR openings and their row and column sumchecks over $FF_(p^5)$ using Poseidon2-GL-w24. A degree-two sumcheck folds the public-matrix evaluation claims to one claim for the parent. `verify_ivc_tree` discharges the final claim against the fixed matrices at the root.
]

The Lean native $x^7$ census gives 315,150 rows including closing padding, within $2^19$. The production [DKT26] two-child step uses 7,652,354 rows before closing and fits within $2^23$. At this fixed geometry the canonical `QSAGIVC1` root occupies *639,673 B* with strict profile tag `0x00`, independent of depth (`ivcRootProof_byteSize_independent_of_depth`).

#theorem("recursive extraction budget", src: [`MultiDepthRecursiveQromExtractor.lean`, `multidepth_recursive_qrom_lt_2_neg_128`])[
  Straight-line extraction uses the recorded oracle transcript for both children. The node errors compose over the tree without a $2^d$ rewinding loss in the query budget. For $d <= 16$ (up to 65,536 shards) and $Q <= 2^64$, the tree bound for the three-stage recursive margin schedule is below $2^(-128)$.
]

The margin schedule uses $2^20$ cells and query counts 304, 148 and 100. The Rust root fixes its schedule to `IvcStepConfig::dkt26(23)`, with 267 Stage-0 queries. The numerical tree theorem applies to the former schedule. A depth-16 bound for the serialized root still requires composition for its own parameters.

== Hiding relations

In zk-Hem v2 the single prover serializes `QSAGZKH2` and collaborative provers serialize the split-share form `QSAGZKS2`. Both decoders accept tag 16 (cSHAKE256) or 17 (TurboSHAKE256) with 400-bit digests. Stage 0 commits the packed base-field assignment table $Z$ and a folded-domain mask word $R$ over $E$. Five out-of-domain points mask the fold scalars. Each tree uses a 32-byte `tree_nonce` and each Stage-0 leaf has a fresh 32-byte salt. Relations with lookups add a helper commitment and a `LookupV2Proof` whose openings are jointly masked with the assignment over $E$.

The affine folds [CWYZ26] and the line-folding bound of [DKT26, Theorem 5.12] give the packed-fiber schedule certified in `ZkHemV2PackedFiberCerts.lean`. The theorem `zkHemV2_packed_all13_qrom_lt_128_at_2pow64` bounds QROM error below $2^(-128)$ across all 13 sizes $2^16$ through $2^28$ at $Q <= 2^64$.

- *Credential presentation.* A `BlindVC` holder proves accumulator membership, selective disclosure and the requested predicates while hiding the remaining attributes.
- *Private multisignature.* For a policy address and a message, enough members signed. A hidden activity bit per slot, a prefix rule, increasing member indices and a range check on $sum "active" - t$ make the statement identical for every threshold, member count and signing subset.
- *Capabilities.* The `QSAGCAU1` unlinkable presentation hides its witness. A bearer capability is $("id", "audience", "tag"_0, c_1, dots, c_n)$ with tags chained by $"tag"_(k+1) = H("tag"_k, c_k, k)$. A batch of up to 32 presentations proves for each: every caveat (expiry, not-before, resource, actions, amount) is satisfied by the public request; the capability's leaf, which binds $n$ and the final tag, lies under the issuer's root; a per-context presentation tag is correctly derived; and the identifier is not revoked.

#theorem("sorted-tree non-revocation", src: [`capability.rs`: `slot_gadget`, `enforce_gated_cmp_limbs32`])[
  Let the revocation tree hold strictly sorted identifiers between two sentinels. If adjacent leaves $r_"lo", r_"hi"$ at indices $(i, i+1)$ open under the epoch-bound root and $r_"lo" < "id" < r_"hi"$ as 256-bit integers on canonical limbs, then the identifier is not in the tree. The relation enforces canonicity of every limb and decomposes both indices into bits with $i_"hi" = i_"lo" + 1$, so neither comparison nor increment can wrap modulo $p$.
]

A holder cannot drop or alter a caveat (the result is a leaf that does not exist) and cannot open an ancestor's leaf (attenuation replaces the root tag by a one-way image). In _registered_ mode the issuer enrolls each attenuated leaf. In _delegated_ mode each attenuation is authenticated by a one-time target-sum signature under an ephemeral key carried in the chain, and the relation verifies the whole chain and possession of the terminal secret; only the first key is enrolled, and later hops need no contact with the issuer. Revocation is per identifier and covers a lineage.


= The Custody Lifecycle and GPU Primitives

== Derivation, addresses, policy and capabilities

*Hierarchical derivation.* Hash-based keys have no homomorphism, so a parent public key cannot derive child public keys. Custodians instead derive root shares and child keys from a ceremony over subset seeds ($n >= 2t - 1$) and publish a Merkle-committed inventory of child public keys for watch-only use; for module-lattice keys (`qsag-hd`), a public linear shift lets a watch-only party derive child keys alone. In the three-party case each custodian projects its replicated share of a child signing key directly from the subset seeds it already holds, so no host ever assembles a child secret. Each derivation consumes a slot of a durable, anchored query budget.

*Addresses.* Addresses are 67-character Bech32m strings [Wui20] that commit to a signature suite and a key, including hybrid keys pairing a classical with a post-quantum scheme under one pinned envelope. One function derives the policy key identifier from the suite and public key in every crate.

*Policy.* Spending rules (allowlists, per-transaction and rolling limits, approval tiers, separation of initiator and approver) are evaluated on MAC-authenticated shared state before any custodian releases a share. A successful evaluation mints a move-only release token for the exact key, message, context and quorum, which is split into one token per quorum member; a signer accepts only the token bound to its own party identifier, so a custodian holding two tokens cannot use both.

*Capabilities.* Three constructions cover the trade-off between size, offline delegation and privacy (@caps). A _SpongeMacaroon_ is a chained-MAC bearer token: each caveat rekeys the tag, and third-party discharges are bound to the presenting token. Appending a caveat can only narrow the authorized set, and any accepted alteration of a caveat chain yields a forgery of the chained MAC (`MacaroonAttenuation`). A _PqBiscuit_ replaces the shared key with public-key verification: each hop carries the root of the next one-time key and a `Compact1122` signature by the previous one, 1,154 bytes per hop, and a holder attenuates offline. The hop key is a value consumed by signing, and an authority key bundles up to 256 one-time roots under one 105-byte public key. The zero-knowledge capabilities of §4.4 hide the token and its caveats from the verifier. The policy engine evaluates any of the three against the trusted facts of a request before latching preprocessing.

#figure(tbl((1.5fr, 1.1fr, 0.9fr, 0.9fr, 0.8fr),
  [Capability], [Size], [Verifier holds], [Offline hop], [Hidden], table.hline(),
  [SpongeMacaroon, 3 caveats], [161 B], [secret key], [yes], [no],
  [PqBiscuit], [1,154 B per hop], [public key], [yes], [no],
  [zk capability, registered], [one proof per batch], [two roots], [no], [yes],
  [zk capability, delegated], [one proof], [two roots], [yes], [yes],
), caption: [Capability forms. All share one caveat language.]) <caps>

== Anti-rollback anchors

The journals of §2.4 are crash-safe but cannot notice that their whole volume was restored from a snapshot. Every stateful object therefore reserves, then consumes, a single-use ticket from an _external monotone anchor_; replay, a failed persist, either crash point, and double consumption are all refused. Three concrete anchors are implemented in safe Rust (`#![forbid(unsafe_code)]`) and compose (`anti_rollback.rs`):

- `Tpm2NvMonotoneAnchor`: speaks raw ISO/IEC 11889 TPM 2.0 command/response frames (`TPM2_NV_Increment`, `TPM2_NV_Read` under `TPM_RS_PW`) directly over `/dev/tpmrm0` with zero C library dependencies, binding ledger checkpoints to a 64-bit hardware `TPM_NT_COUNTER` index through a crash-safe two-phase `(committed, pending)` seal;
- `VmGenIdForkGuard` and `HypervisorGenerationAnchor`: bind every checkpoint to the hypervisor's 128-bit ACPI `VMGENID` (`/sys/devices/virtual/misc/vmgenid`), Linux `boot_id`, and the guarded WAL file's `(st_dev, st_ino, st_ctime)` tuple, halting on any snapshot restore or volume clone;
- `FsDirectoryMonotoneAnchor`: a mirrored two-slot directory anchor on a separate mounted device (`st_dev` verified distinct unless explicitly waived), surviving the loss of either slot.

The command-line tool refuses to create or use stateful custody without an anchor unless the key is declared ephemeral, and a key enrolled with an anchor cannot later be used without it. After a committee is reshared, the old vault is retired at the anchor, so a restored copy of it is permanently refused. All records go through `LockedRecord`, which takes its lock on the held open-file description, refuses files with group or world permission bits, and opens without following links.

== Anchored Collaborative Key Migration across 19 Classical Ecosystems

A migration statement binds a source commitment, the destination post-quantum address and a nullifier. The 19 CLI kinds cover Bitcoin, including Taproot, and Ethereum on secp256k1, Solana Ed25519, BLS12-381 withdrawal credentials, and Zcash NU7 Sapling, Orchard, ZIP-2005 Ironwood and ZIP-2007 Transparent. Each kind selects an ownership relation and specifies which source data may be public. `ClassicalCommitmentKind` and `ClassicalOwnershipWitness` in `crates/qsag-migrate/src/classical.rs` implement the classical commitment and witness primitives.

A single holder proves the relation locally with zk-Hem v2 (`QSAGZKH2`). Distributed custodians evaluate it on authenticated shares through `hem::collab` and emit `QSAGZKS2`. To multiply two quintic shared elements, the engine uses nine base-field Beaver triples in a Toom-3 product. Before round 1, `Engine::new_anchored` burns the preprocessing `tape_id()` against an `ExternalMonotoneAnchor`. A stale tape therefore fails before a custodian transmits a round message. The Ironwood recovery branch without a spending scalar uses an external randomized signature to establish spend authority.

== Threshold ML-DSA and oblivious PRFs

*Threshold ML-DSA.* For compatibility with FIPS 204 verifiers, QSAG threshold-signs ML-DSA-44, -65 and -87 with no dealer. Key material is Shamir-shared among $n <= 64$ custodians with $n >= 2t - 1$; a quorum of $2t - 1 <= 16$ converts to the replicated engine under checked multiplications and conversions. The difficulty peculiar to lattice signatures is rejection sampling: a rejected attempt's partial response, if seen, leaks the key. The high bits $bold(w)_1$ and the challenge stay shared until the norm and hint checks pass, and partial responses are one-time-padded until release.

#theorem("sealed abort", src: [`threshold_mldsa_abort_transcript_zk`])[
  At ML-DSA-44 dimensions, the view of a corrupt minority in an aborted attempt is identically distributed for any two keys consistent with the public accept/reject outcome.
]

Every attempt burns a nonce durably before it starts. The nonce ledger stores each session once: 33 bytes for a session whose burned attempts form a prefix, with further attempts of the same session recorded in place, and its generation counter must equal the number of attempts recorded, so a ledger with missing history cannot be opened.

*Oblivious PRF and credentials.* A $(t,n)$ threshold oblivious PRF over Poseidon2 serves rate-limited derivation and blind credential issuance. A 2-of-5 replicated form corrects one malicious server by unique decoding when all five servers participate online (`toprf_2of5_byzantine_unique_decoding`). The general SPDZ form, $2 <= t <= n <= 64$ with $t$ servers online, runs on the authenticated engine of §3.2 from a non-cloneable reservoir of preprocessed power tuples; a cursor advances before a range is returned, so no tuple is used twice. Input binding, one batched check over every S-box opening, and the output are each MAC-checked in that order through the blinded test of §3.3, and outputs are padded by client masks no server knows. A malformed client request costs one reservation; a failed MAC check poisons the reservoir. With the OT mesh retained, a $(2,3)$ evaluation takes 4.3 ms online. The reservation logic is modelled as a state machine whose counters ratchet on every server before any state changes and never recycle after a partial failure (`ToprfMachine.partial_reserve_burns_without_recycle`).

Blind issuance uses 438 repetitions of three-party Goldilocks MPC-in-the-head [IKOS07, GMO16] in `crates/qsag-cred/src/blind_vc.rs`. A `BlindVC` holder subsequently proves selective disclosure with the zk-Hem v2 presentation relation (§4.4).

== GPU primitives

The Vulkan backend has six compute shaders for Keccak-f[1600], Poseidon2, Goldilocks NTT, coset extension, Poseidon2 Merkle layers and binary-field inner products. A dispatch receipt binds the job descriptor, module digest and input and output digests. The planted-fault audit compares results on a Radeon RX 6750 XT with the CPU reference and checks the pinned shader identity. §7.3 reports primitive timings.

= End-to-End Constructive Formalization

== The Lean library

Lean 4.35 [MU21] checks the protocol models in `lean/`. The library contains 340 layered `Qsag` modules. The axiom audit accepts all 139,005 declarations, including 74,363 theorems, with dependencies confined to `propext` and `Quot.sound`. There are zero occurrences of `Classical.choice`, `sorry` or `import all` in the library. Across 432 source files, `scripts/check_lean_policy.py` checks layering and proof policy, rejects constant-true verifier definitions, and checks coverage of all 54 extracted WHIR symbols.

The signing reduction in `HulsingMultiHopReduction.lean` connects an adaptive signature forgery to the primitive games. The quantitative bounds depend on their query and hardness assumptions. For custody, `productionLatchedRandomizedSigner_refines_idealSign` relates the latched signer to the ideal signing machine across retries. The distributed model in `Top/DistributedAuthRunBound.lean` accounts for deployment-authenticated frames and durable reservations.

For aggregation, `QuinticMultiStageWhir.lean` relates quintic folding on cosets to coefficient evaluation and supplies an inhabited three-stage, 256-point round-by-round proof. `ConcreteIvcWhir.lean` executes the recursive WHIR checks alongside R1CS sumcheck verification. The extraction argument follows accepted child statements using the recorded query table. The numerical bounds for the 13 deployed schedules and for the recursive tree appear in §4. Their application to serialized Rust proofs also depends on decoding, transcript framing and correspondence with the modeled verifier.

== Extracted Rust

Charon and Aeneas [HP22] translate Rust MIR into Lean. The custody package includes `QsagCustodyWeld` and verifies field arithmetic, sponge framing and release guards. Its `extraction-coverage.json` classifies all 238 public functions. Of the 87 on production call paths, 57 are direct calls, 16 are classified as direct by lexical analysis and 14 are reached transitively. The other 151 serve standalone library, specification, proof or test uses. All 238 have extractions.

The pure-quintic WHIR package connects its extracted `Funs.lean` definitions to the canonical `Qsag` specification through `QsagWhirSpecWeld`. Its 173 anchored theorems cover all 54 definitions with zero external model files. This checks the extracted arithmetic and verifier operations used by Rust. The callers that assemble the full wire transcript are a separate implementation boundary.

#figure(tbl((1fr, 0.7fr, 1fr, 0.95fr),
  [Package], [Modules], [Declarations], [Theorems], table.hline(),
  [Qsag], [340], [139,005], [74,363],
  [Custody MIR], [52], [6,887], [2,917],
  [WHIR MIR], [9], [2,160], [1,185], table.hline(),
  [Total], [401], [148,052], [78,465],
), caption: [Axiom census for the protocol and two MIR packages. All three audits recorded zero rejected declarations.]) <census>

Six kernels replay each package’s comparator challenge. For `lean/comparator.json` the export has 16,829 declarations and the challenge selects 152 `Qsag.Top` theorems. For `aeneas/lean/comparator.json` the export has 4,145 declarations and the challenge selects 71 theorems and 25 definitions. For `aeneas/lean-whir/comparator.json` the corresponding counts are 4,154, 103 and 10. All 18 package/kernel runs accepted, covering 326 challenge theorems and 35 definitions across the three packages in @census.

== Machine code

The 28 hand-written assembly kernels (19 for x86-64, 9 for AArch64; 3,355 decoded instructions) are verified directly from compiled `.rlib` archive bytes. A Lean model of each ISA defines execution and a three-way leakage trace over program counters, memory addresses, variable-latency operands, and dirty upper-vector / NEON scratch state.

#theorem("kernel noninterference, DIT contracts, and ELF–Math–MIR triangles", src: [`McRefine.lean`, `ElfVerify.lean`, `PlatformContractInstances.lean`, `ElfMirTriangles.lean`])[
  All 19 x86-64 and 9 AArch64 compiled `.rlib` symbols satisfy `Spec.DitHardwareContract` (`rlib_x86_all19_dit_trace_data_independent`, `rlib_aarch64_all9_dit_trace_data_independent`), producing identical leakage traces from public-equivalent initial states; 26 of the 28 kernels are proved functionally equal to their mathematical specifications (the remaining two being bit-matrix transposes covered by noninterference and loop certificates); and seven end-to-end composition theorems (`elf_mir_goldilocks_{add,sub,mul}_x86_64`, `elf_mir_goldilocks_mul_aarch64`, `elf_mir_keccak_f1600_avx2_4x`, `elf_mir_gf256_gfni`, `elf_mir_tower128_pclmul`) equate decoded ELF execution with extracted Aeneas MIR through the canonical mathematical algebra.
]

A binary dataflow screen (`scripts/audit_elf_ct.py`) checks the linked `target/release/qsag` binary and single-codegen-unit release archives (`x86_64` and `aarch64`, `std` and `no_std`, including 25 wiped SIMD kernels and flat `SecretBuffer` destructors) with 175 negative `#tooth` self-tests and zero violations. On the GPU side, `Machine/SpirvPoseidon2UniversalEntry.lean` proves universal functional equivalence (`spirv_poseidon2_perm12_entry_universal`) of the embedded 5,478-word `poseidon2_perm12.spv` binary against `Qsag.poseidon2Perm12` across all `Fin 12 -> Goldilocks` states alongside Wave32 SIMT barrier-epoch noninterference (`simtEpochContract`).

== Execution

The Lean–Rust runner checks 317 cross-language known-answer vectors and rejects 319 mutations. A separate test removes clauses from the compiled implementation and catches all 18 mutants. The domain-label inventory contains 952 labels across 14 crates, with 13 shared and zero drift. These gates exercise encodings, rejection and domain separation at implementation boundaries where the formal results depend on correct inputs.

The Zen 5 single-step harness compared 7,184 register-state vectors against the modeled ISA. The Vulkan suite `vulkan_planted_fault_audit.rs`, enabled by `fault-injection-audit`, checks corrupted shader binaries and executes planted semantic faults against CPU references. §7.5 gives the serialized proof fixtures exercised by autonomous RTL.

= Evaluation and Scaling

The signing and arithmetic measurements below use AMD Zen 5, AMD EPYC Milan (Zen 3) and a Radeon RX 6750 XT with Mesa RADV. The hardware tables distinguish resident RTL simulation cycles, mapped ASIC logic area and routed FPGA clock estimates.

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
), caption: [Protocol measurements. The offline refill and online check are timed separately for the three-party blinding pool.]) <protobench>

A prepared stateful signature takes one online round. On durable media the synchronized journal write contributes to latency (@protobench).

== GPU

#figure(tbl((2.3fr, 0.8fr, 0.9fr, 0.7fr),
  [Workload], [GPU ms], [CPU ms], [Ratio], table.hline(),
  [Poseidon2, 262,144 permutations], [27.4], [2,138], [78×],
  [Keccak-f[1600], 262,144], [29.7], [104], [3.5×],
  [Goldilocks NTT, $2^20$], [21.4], [246], [11.5×],
  [Coset extension, $2^18 -> 2^20$], [16.0], [820], [51×],
  [Two-block Merkle tree, $2^18$ leaves], [23.3], [2,315], [99×],
  [Binary-field inner product, 262,144], [6.3], [68.9], [11×], table.hline(),
), caption: [Primitive timings on a Radeon RX 6750 XT, including transfers, against one CPU thread.]) <gpubench>

The largest speedup in @gpubench is for a two-block Merkle tree, where many independent nodes can be hashed in parallel. The unit of measurement in this table is a single primitive workload.

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

*Finality path.* Regional committees sign the checkpoint message. With `HierarchicalHemAggregate`, a new verifier checks the included `QSAGHQM2` shards against its prepared registry. For $s$ regions the payload includes the sum of the $s$ serialized shard lengths, plus registry, commitment and shard framing. The 360,391 B and 381,661 B examples in @publicprofiles give two concrete lengths for the same sparse committee. Committee size, signer activity and proof profile matter when sizing other shards.

For a power-of-two sequence of contiguous Jorts shards, `QSAGIVC1` verifies one 639,673 B root against the public interval, quorum count, message and registry root. Doubling the shard count adds one level of proving work while leaving the root length fixed. The current leaf circuit admits at most two active signers per shard. The depth-16 margin-schedule theorem counts 65,536 shards. Neither the fixed wire size nor this modeled bound measures network latency.

== QSAG-NI v2: autonomous verifier silicon across 130 nm CMOS, ECP5, and AWS F2

After loading a proof and its public descriptor into SRAM, the host issues `OP_VERIFY_PROOF_AUTO` (`0x50`). The hardware parses the proof and executes the quintic WHIR and sumcheck verifier from a synchronous $4096 times 64$-bit (32 KiB) ROM. For a windowed upload, `OP_PAGE_CONTINUE` (`0x51`) resumes at the requested offset. In public committee mode the engine computes `compute_message_mu` on chip with Poseidon2-12 for each active key and message. The autonomous ABI supports the non-lookup tag-17 hiding fixture and the tag-1 public profile. The descriptor’s row program is trusted verification-key material. A streaming micro-command port also exposes the datapath.

#figure(tbl((1.55fr, 1fr, 1fr),
  [Resident proof fixture], [Bytes], [RTL cycles], table.hline(),
  [`QSAGZKH2`], [258,104], [54.91 M],
  [`QSAGHQM2`, one signer], [307,531], [89.63 M],
  [`QSAGHQM2`, multiple signers], [331,221], [94.42 M],
), caption: [Autonomous Verilator runs after preload. The first two fixtures rejected 288/288 and 300/300 proof-bit mutations respectively.]) <autoverify>

The streaming port rejected 194/194 injected faults. The RTL verification suite includes 105+ Z3/Bitwuzla equivalence miters (UNSAT for mismatches) and the Obend Lean 4 checks (zero `sorryAx`). These component checks complement the complete proof replays in @autoverify.

#figure(tbl((1.25fr, 1fr, 1fr),
  [130 nm library], [Autonomous], [`AUTO_VERIFY=0`], table.hline(),
  [IHP SG13G2], [709.61 kGE], [661.00 kGE],
  [Sky130 HD], [784.54 kGE], [734.23 kGE],
), caption: [Yosys mapped logic area in thousands of library NAND2 equivalents. Four 128 KiB SRAM banks are black boxes.]) <foundry>

Across the unbuffered pre-layout OpenSTA runs, worst slack against the 100 ns reference clock ranges from −202.93 ns to −645.59 ns. Tapeout requires physical buffering, clock-tree synthesis, characterized SRAM Liberty models, extracted interconnect and multi-corner signoff. The area measurements in @foundry and the corresponding timing configurations are documented in `hardware/asic/synth/RESULTS.md`.

*ECP5-85F.* All eight routed `.pnr.bit` bitstreams on `LFE5U-85F-6BG381C` meet their respective constraints with zero overused wires. The six primitive wrappers reach 34.72–71.34 MHz. Both full cores meet a 20 MHz target (@ecp5). The synchronous ROM infers 16 `DP16KD` blocks with zero LUTs. The FPGA regression records 461 formal/ANF obligations and over 1.90 million Verilator checks.

#figure(tbl((1fr, 1fr, 1fr, 0.7fr, 0.7fr),
  [Core], [MHz], [LUT4], [DSP], [BRAM], table.hline(),
  [Compact], [33.62], [23,576], [18], [79],
  [Full rate], [29.86], [35,153], [81], [77],
), caption: [Routed tops in `hardware/fpga/RESULTS.md`, `fmax_compact_top.pnr.bit` and `fmax_ecp5_fullrate_top.pnr.bit`.]) <ecp5>

*AWS EC2 F2.* The `CL_QSAG_F2` HDK 2.3.5 wrapper targets `xcvu47p-fsvh2892-2-e`. It integrates two verifier engines, each with eight `RAMB36E2` autonomous ROM blocks, and three isolated ASS2 vats. The mapped HDK wrapper uses 314,047 LUT1–6, 290 `DSP48E2` and 315 `RAMB36E2`. Strongly connected component checks found zero combinational loops before and after mapping. A `BUFGCE_DIV` divides the vat clock by two. The design mixes `DNA_PORTE2` identity and `SYSMONE4` entropy with RCT/APT health checks for per-session sealing. Cloud AFI deployment requires AWS-supported replacements for customer `DNA_PORT` and `SYSMON`. Rust-to-Verilator OCL and PCIS cosimulation exercises `verify_proof_auto` on the 258,104 B `QSAGZKH2` fixture and function-level reset zeroization over 32,768 cycles.

== ASS2-0P5 / Dregg-64: Two-Ring W^X physical custody enclave in 180 nm 5 V CMOS

The 64-bit GF180MCU-D design targets the wafer.space `SLOT_0P5X0P5` shuttle slot. Its 1,936 × 2,531 µm die has 56 pads and a 1,052 × 1,647 µm core (1.733 mm²). Ring 0 executes from an immutable 4 KiB instruction ROM. Ring 3 executes owner WOTS+C-signed SRAM applets of at most 64 instructions. A hardware fence checks the privilege of `SYS_MMIO` accesses, including after an applet branches into resident code. The design uses foundry `gf180mcu_fd_ip_sram__sram512x8m8wm1` memory.

The PUF pairs 512 ring oscillators into 256 disjoint pairs. Four BCH(63,36,5) blocks use 252 pairs, yielding a modeled 144 bits of post-helper entropy. The CoSO TRNG implements the SP 800-90B repetition-count and adaptive-proportion health tests. `LC_PROVISIONED` locks out debug and BIST access. Gate-level simulation clears the secret latches in 0.60 ns with the clock stopped. BSIM4 decks run in ngspice 45.

The four-layer KiCad 8 carrier has zero schematic ERC violations and zero footprint-fixture DRC violations. Its planar NFC coil model gives 1.47 µH and loaded $Q = 17.9$. Wafer entropy measurements, board routing checks and populated-coil measurements remain physical qualification steps.

= Trusted Base and Scope

*Cryptographic assumptions.* (i) Keccak-p[1600] in its SHAKE256, cSHAKE256 and 12-round TurboSHAKE256 modes, and width-12 / width-24 Poseidon2 in their hardened profiles, behave as random oracles within the adversary's query budget (PRF, target-collision, preimage, undetectable-distribution and interleaved-subset resistance, plus absence of sub-generic algebraic attacks on Poseidon2). (ii) For dealerless SPDZ / `SoftSpokenOT` preprocessing only: Ring-LWE at dimension 1,024 and modulus 12,289, the Euclidean Ring-SIS relation extracted by the 24-challenge base-OT proof, correlation-robust OT pad hashing [Roy22], and regular dual-LPN at the kernel-bracketed bias. (iii) For FIPS 204 compatibility only: the assumptions of ML-DSA. Three-party bitsliced signing, isolated honest-majority CNF signing, and Hem / `HemQuintic128` / `QSAGIVC1` aggregation use (i) alone.

*Proof systems.* For public and hiding proofs the modeled QROM bound applies through $Q <= 2^64$ at each of 13 deployed table sizes. For the recursive construction, the 639,673 B wire size is independent of depth, while the stated depth-16 tree bound uses its own $2^20$-cell margin schedule. The public-matrix, WHIR and R1CS verification steps have executable Lean models. Applying their theorems to arbitrary bytes also requires the Rust callers and parsers to enforce canonical decoding and bind the same transcript and statement.

*Custody and migration.* Release safety depends on the assumed corruption threshold, authenticated channels, and persistence of the reservation before a signature share or migration message is sent. The migration refinement starts from a checked R1CS assignment. Receipt of a serialized proof requires a sound verifier, and Ironwood recovery without the spending scalar additionally checks an external randomized signature. The operating system, entropy sources, storage synchronization and external monotone anchor are part of the deployment’s trusted base.

*Software.* The Lean kernel and allowed axioms, the Charon/Aeneas MIR translation and its preludes, and the semantics used for the ISA and SPIR-V proofs enter at different boundaries. Six-kernel replay checks the exported challenges. Rust callers of extracted kernels, the remaining compiler and linker pipeline, and the host GPU driver still require assurance.

*Hardware.* Autonomous RTL replay assumes an authentic public descriptor. ASIC tapeout timing and ASS2 routing and physical qualification remain open. The ECP5 results are routed bitstream timings. F2 cosimulation checks the host interface and scrub sequence, while deployment needs supported identity and entropy sources and a timed AFI. QSAG is a research prototype with no external audit.

= Conclusion

Cut-the-Hash keeps the secret portion of threshold signing independent of tree height. Quorum intersection and durable leaf reservations let committees change while preserving the stateful signing key. Public quintic Hem proofs let regions verify committees independently. Where a verifier needs one certificate for a contiguous tree of shards, the binary IVC fixes the root at 639,673 B. The distinction between format size, modeled extraction error and physical implementation evidence determines which guarantee each verifier can rely on.

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
    [[CGH+18] K. Chida, D. Genkin, K. Hamada, D. Ikarashi, R. Kikuchi, Y. Lindell, A. Nof, "Fast Large-Scale Honest-Majority MPC for Malicious Adversaries", CRYPTO 2018.],
    [[CS25] E. Crites, A. Stewart, "On Reed–Solomon Proximity Gaps Conjectures", IACR ePrint 2025/2046, 2025.],
    [[CT19] C. Cachin, B. Tackmann, "Asymmetric Distributed Trust", OPODIS 2019; extended version with O. Alpos and L. Zanolini, arXiv:1906.09314.],
    [[CWYZ26] A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng, "Affine Combiners for Reed–Solomon Proximity Gaps", IACR ePrint 2026/2863, 2026.],
    [[DFM20] J. Don, S. Fehr, C. Majenz, "The Measure-and-Reprogram Technique 2.0: Multi-Round Fiat–Shamir and More", CRYPTO 2020.],
    [[DKT26] Q. Dao, S. Kominers, J. Thaler, "Tighter Post-Quantum Security for Reed–Solomon Proximity Testing and WHIR", IACR ePrint 2026/2056, 2026.],
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
    [[Roy22] L. Roy, "SoftSpokenOT: Quieter OT Extension from Small-Field Silent VOLE in the Minicrypt Model", CRYPTO 2022.],
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
