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
    #text(size: 16.2pt, weight: "bold")[Cut-the-Hash: Post-Quantum Threshold Hash Signing and Stateful Quorum Custody]
    #v(7pt)
    #text(size: 11pt)[ember arlynx]
    #v(2pt)
    #text(size: 8.5pt, fill: luma(60))[`ember@lunar.town`]
  ]
  #v(9pt)
  #block(inset: (x: 16pt))[
    #set par(justify: true, leading: 0.46em)
    *Abstract.* A threshold hash signer need only compute the values that depend on a shared secret. Cut-the-Hash opens four families of such values behind an integrity check, after which anyone can assemble the signature. A Winternitz chain requires at most 16 sequential secret hash calls for FIPS 205 SLH-DSA and four for Jorts, Baggy and Corduroy, independent of tree height. For honest-majority committees we describe the order of masking, challenge sampling and opening in the replicated multiplication check. For stateful keys we give the intersection and persistence conditions under which distinct signing quorums can share one tree. The Hem interface preserves the validator public key through a change of custodians. Lean relates replicated SLH-DSA oracles to the single-signer specification and reduces forgery in modeled signing games to explicit primitive-hardness bounds. We distinguish these results from the behavior measured on Rust signing paths and from the assumptions on storage, channels and hardware.

  ]
]

= Introduction

Validators, institutional custodians, and consensus committees rely on threshold signing over algebraic groups: FROST [KG20] and threshold ECDSA distribute a signing key across $t$-of-$n$ hosts, while BLS [BLS01] aggregates committee attestations. Shor's algorithm breaks the discrete-logarithm assumption underlying these protocols. Standardized post-quantum replacements—SLH-DSA [FIPS205, BHKN+19] and ML-DSA [FIPS204]—specify single-signer algorithms with no native threshold mode, stateful leaf coordination, or quorum reconfiguration.

Hash-based signatures rest on symmetric assumptions alone, avoiding structured lattice assumptions on the signing path. Turning single-signer hash trees into a threshold custody substrate faces four technical obstacles:

1. *Hypertree height against MPC depth.* A stateless hypertree signature hashes thousands of Winternitz chains into leaf roots and climbs $d$ Merkle layers of total height $h <= 68$. Evaluating internal compressions inside actively secure MPC turns public tree hashing into millions of authenticated non-linear gates.
2. *Committee scaling without trusted coordinators.* Replicated secret sharing keeps three-party Boolean Keccak fast [FLNW17, BGIN19] at $binom(n, t-1)$ storage, whereas dishonest-majority $(t,n)$ committees require authenticated shares [BDOZ11, DPSZ12] over fields suited to both binary sponges and algebraic permutations [GKS23]. Practical custody further requires peer-to-peer execution over forward-secret post-quantum channels and proactive share refresh without reconstructing the key.
3. *State safety under crashes, snapshots, and quorum switching.* Stateful Merkle trees [BDH11] eliminate hypertree overhead because each one-time leaf signs at most once, but a single leaf reuse across two quorums—after power loss, VM snapshot rollback, consensus slot skips, or a $(t,n) -> (t',n')$ handoff—exposes chain values at two positions and invalidates the one-time security argument.
4. *Persistent MAC exposure and implementation gaps.* When an authenticated MPC engine retains a global MAC key $alpha$ across sessions and resharings, opening raw MAC residuals $d = m - alpha x$ allows an adversary who shifts an opening by a known $Delta$ to recover $d = -alpha Delta$ on abort—fatal in unanimous ($t = n$) quorums and malicious-dealer resharings. Even a sound protocol fails if Rust callers release shares before durable synchronization or if SIMD assembly leaks secret operands through timing or vector register residue.

*Approach.* Our design principle is that secret shares cross into cleartext at the earliest boundary where the single-signer specification already exposes the value publicly. _Cut-the-Hash_ (§2) isolates four secret oracle families inside MPC and reconstructs $T_ell$ compressions, message digests, counter grinds, and Merkle authentication paths in the clear. This boundary supports the six FIPS 205 SHAKE profiles, stateless Baggy (Keccak with pruned PORS) and Corduroy (Poseidon2), and stateful Jorts. Section 2 also describes the separate one-use Frontier construction for live votes.

The computation below the cut depends on the hash and corruption threshold. Replicated Boolean shares support batched Keccak evaluation [FLNW17, BGIN19]. An honest-majority CNF party checks randomized products before releasing outputs [CGH+18]. The SPDZ cluster implements the SLH-DSA oracles with authenticated Boolean operations. An arithmetic backend supports Poseidon2 over Goldilocks. Both draw on oblivious-transfer preprocessing [DPSZ12, Roy22]. Section 3 gives the trust and interaction requirements of each path.

The central stateful question is when a custodian may release a chain value. Section 4 relates the durability of each acknowledgment to honest intersection between quorums [CT19]. Section 5 gives the hypotheses of the signing and custody theorems and the scope of the extracted Rust and assembly results. Section 6 reports signing and verification costs. The companion paper, _Quintic Hem_, treats public aggregation and private proofs.

*Related work.* PRAWNS [BBD+26] thresholdizes hash-based signatures by replacing symmetric leaf derivation with lattice-based threshold PRFs, introducing a lattice hardness assumption onto the signing path and departing from standard FIPS 205 key derivation; Cut-the-Hash evaluates standard symmetric PRFs and chains inside actively secure MPC [FLNW17, CGH+18, BGIN19, BDOZ11, DPSZ12] and emits exact FIPS 205 bytes. Lifetime-capped SPHINCS variants trade signature size for a cap on signatures per key; BeltLatch enforces anchored monotone reservation before share release on stateful XMSS-style trees [BDH11] with WOTS+C [HKRY23] and pruned PORS [AE18]. Actively secure OT extension and silent VOLE build on KOS [KOS15], MASCOT [KOS16], dual-LPN PCGs [BCGI+19], and `SoftSpokenOT` [Roy22]. For consensus, distributed quorum signatures [KSW26] and QUASI [IM26] eliminate signer bitmaps on live voting paths; `Compact1122` addresses the same 1,232-byte IPv6 MTU constraint with hash-only single-use votes. Asymmetric Byzantine quorum systems [CT19, ACTZ21, ACKV26], personal quorums [LGM19], and the blocklace [KLST26] provide the trust and causal-ordering models instantiated in §4.

= Cut-the-Hash and the Pants Signature Suite

== The four-oracle MPC boundary

A hash-based key pair comprises secret seeds $("SK.prf", "SK.seed")$ and public parameters $("PK.seed", "PK.root")$. Let $mu$ denote the domain-framed message, $A$ a 32-byte tree or chain address (`ADRS`), and $A_0$ its chain-start address.

#definition("secret oracles", src: [`SlhMpcOracles`, `PqHashMpcOracles`])[
  The secret interface evaluated under MPC consists of four oracle families:
  1. _Message randomizer._ $R = "PRF"_"msg" ("SK.prf", r, mu)$ for an optional hedge $r$.
  2. _Selected chain output._ $F^s ("PK.seed", A, X_j)$ with $X_j = "PRF"("PK.seed", "SK.seed", A_0)$, evaluated solely at $s in {d_j, w-1}$ for message-selected base-$w$ digit $d_j$.
  3. _Selected few-time preimage._ $"PRF"("PK.seed", "SK.seed", A_"fts" (u))$ at message-selected indices $u$.
  4. _Unselected few-time leaf digest._ $F("PK.seed", A, "PRF"("PK.seed", "SK.seed", A_"fts" (u)))$, opening only the public digest of each unrevealed leaf.
]

Every remaining step of signature generation is a deterministic public function of $(R, "PK.seed", "PK.root", mu)$ and the opened oracle outputs: message hashing $H_"msg"$, counter grinding, $T_ell$ chain-end compression, few-time internal nodes, and every hypertree Merkle layer (@cutfig). Custodians hold secret shares of $("SK.prf", "SK.seed")$, bind the signing request durably, pass a MAC or distributed zero-knowledge barrier, and open only the four oracle outputs.

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 5pt,
    panel([#smallcaps[Secret-shared MPC evaluation]\
      $"SK.prf", "SK.seed"$ #sym.arrow.r $R$, chain steps $F^s$ ($s in {d_j, w-1}$), few-time preimages & leaf digests]),
    align(center)[#sym.arrow.b\ #smallcaps[durable WAL bind · MAC / DZK barrier · authenticated open]\ #sym.arrow.b],
    panel([#smallcaps[Public cleartext reconstruction]\
      $H_"msg"$ & counter grind · $T_ell$ leaf compression · PORS/FORS & hypertree Merkle paths]),
  )
}, caption: [Cut-the-Hash boundary. Secret seeds never leave MPC; all tree compression runs publicly.]) <cutfig>

#theorem("height independence and FIPS 205 byte identity", src: [`rss_thresholdSlhSign_eq_slhSignInternal`])[
  Every released Winternitz chain node requires sequential secret depth at most $w$ tweakable hash calls (one PRF call plus at most $w-1$ chain steps), and every few-time leaf at most 2, independent of total tree height $h$ and layer count $d$. In the Lean replicated-sharing oracle model, public assembly yields the same SLH-DSA signature as the single-signer specification on matched keys, message and randomness. Each concrete backend must separately implement that oracle interface.
]

Sequential secret depth per chain is therefore at most 16 for FIPS 205 (`SLH-DSA-SHAKE-{128,192,256}{s,f}`) and at most 4 for the native Pants profiles (@params). Message randomization absorbs $floor((2n + abs(M')) slash 136) + 1$ sequential Keccak-f[1600] permutations [FIPS202] in pure mode, or a constant-size digest in domain-separated prehash mode.

== Target-sum Winternitz (`WOTS+C`)

Native Pants profiles replace explicit Winternitz checksum chains with checksum-free target-sum encoding (WOTS+C [HKRY23]) at radix $w = 4$. A 256-bit message digest is parsed into $ell = 128$ base-4 digits $d_j in {0,1,2,3}$, and a public 32-bit counter is ground publicly after opening $R$ until
$ sum_(j=1)^(ell) d_j = S, quad S = ell (w-1) slash 2 = 192. $

#theorem("strict codeword incomparability", src: [`wotsC256_strict_incomparability`])[
  For any distinct digit vectors $d != d'$ in ${0,1,2,3}^128$ satisfying $sum_j d_j = sum_j d'_j = 192$, there exist coordinates $j_1, j_2$ such that $d_(j_1) < d'_(j_1)$ and $d'_(j_2) < d_(j_2)$.
]

Forward hashing alone cannot turn one valid digit vector into a distinct valid vector. Omitting the sum check admits a single-hash advancement forgery (`tooth_wotsc_without_target_sum_forges`). The balanced sphere has $[x^192](1+x+x^2+x^3)^128 approx 2^(251.01)$ valid codewords, requiring 31.7 public counter trials in expectation, and every verifier executes exactly $ell(w-1) - S = 192$ hash steps.

#figure(
  {
    set par(justify: false)
    text(size: 8.1pt, table(columns: (1.78fr, auto, auto, auto, auto, auto, auto, auto, auto, auto), inset: (x: 5pt, y: 3.2pt), stroke: none,
      table.hline(stroke: 0.6pt),
      [Profile], [$n$], [$h$], [$d$], [$h'$], [$a$], [$k$], [$w$], [Sigs/key], [Sig. B], table.hline(),
      [SLH-DSA-128s], [16], [63], [7], [9], [12], [14], [16], [$2^64$], [7,856],
      [SLH-DSA-128f], [16], [66], [22], [3], [6], [33], [16], [$2^64$], [17,088],
      [SLH-DSA-192s], [24], [63], [7], [9], [14], [17], [16], [$2^64$], [16,224],
      [SLH-DSA-192f], [24], [66], [22], [3], [8], [33], [16], [$2^64$], [35,664],
      [SLH-DSA-256s], [32], [64], [8], [8], [14], [22], [16], [$2^64$], [29,792],
      [SLH-DSA-256f], [32], [68], [17], [4], [9], [35], [16], [$2^64$], [49,856], table.hline(),
      [Baggy (Keccak)], [32], [32], [16], [2], [11#super[‡]], [28#super[‡]], [4], [$2^16$], [$<=$ 71,654],
      [Corduroy (Poseidon2)], [32], [64], [16], [4], [8], [32], [4], [$2^20$], [76,896],
      [Jorts (custody)], [32], [16], [1], [16], [—], [—], [4], [$2^16$], [4,652],
      [Jorts (consensus)], [32], [6–20], [1], [6–20], [—], [—], [4], [$2^6$–$2^20$], [4,328–4,776],
      [Compact1122 (FTS)], [32], [8], [1], [8], [—], [34#super[§]], [96], [1], [1,122],
      [Full256Bit (FTS)], [32], [8], [1], [8], [—], [72#super[§]], [5], [1], [2,338],
      table.hline(stroke: 0.6pt),
    ))
  },
  placement: top, scope: "parent",
  caption: [Supported signature geometries: $n$ node bytes, total height $h$ across $d$ layers of height $h'$, few-time parameters $(a, k)$, and Winternitz radix $w$. Baggy/Corduroy/Jorts use $ell = 128, S = 192$. #super[‡]Single PORS+FP tree of $2^11$ leaves revealing 28 leaves with $<= 128$ multiproof nodes. #super[§]`FrontierSumFts` antichain size $L$ with target sums $S = "1,615"$ and $S = 144$.],
) <params>

== Stateless hypertrees: Baggy, PORS+FP, Waistband, and Corduroy

*Baggy* is a $d = 16$ hypertree of WOTS+C layers over Keccak/cSHAKE256 [SP800-185] whose bottom layer signs a pruned PORS few-time public key [AE18]. *Corduroy* mirrors this hypertree over width-12 Goldilocks Poseidon2 [GKS23] ($h = 64, d = 16$, FORS $a = 8, k = 32$) for algebraic signature aggregation.

*PORS with forced pruning (`PORS+FP`).* Instead of $k$ separate FORS trees, Baggy commits one Merkle tree of $2^11 = "2,048"$ secret leaves and reveals $k = 28$ distinct message-selected leaves accompanied by a canonical deduplicated Steiner multiproof. During public grinding, a candidate counter is accepted only if the induced 28-leaf multiproof contains at most 128 sibling digests (occurring with probability $approx 2^(-10)$). The few-time layer occupies at most 4,994 B and the complete signature at most 71,654 B; verifiers reject unsorted, duplicate, or oversized openings before size arithmetic.

#theorem("PORS+FP subset-cover security", src: [`PorsFpSecurity.forgery_fraction_bound`, `sha3_128f_binomial_bits`])[
  After $g$ signatures hit the same bottom-layer PORS tree, any fixed hash query lands entirely inside the union of revealed leaves with probability at most $binom(28 g, 28) slash binom(2048, 28)$, uniformly across every public subset-acceptance predicate. At $(2048, 28)$ this bound is at most $2^(-209), 2^(-157), 2^(-136), 2^(-122)$ for $g = 1, 2, 3, 4$.
]

The denominator counts all 28-subsets. An acceptance predicate can only remove winning subsets from the numerator. This is a bound per uniform candidate before grinding. Conditioning on an accepted candidate changes the sampling distribution. The Baggy-specific corollary `baggySha3_128f_pors_itsr_lt_2_neg_131` budgets at most 16 attempts when at most three signatures hit the same tree.

*Three-phase signing and Waistband.* Signing executes in three phases: (1) custodians jointly evaluate $R$ under MPC from $"SK.prf"$ and $mu$, locking the hypertree path so an abort after seeing $R$ forces any retry onto identical addresses; (2) all few-time leaves and all $d$ path subtrees evaluate in one batched sweep (one PRF batch plus three $F$ batches regardless of $d$) behind a single verification barrier; and (3) only the message-selected chain positions open in one round. Because upper hypertree layers sign static child roots, *Waistband* caches verified public material of the top $L$ layers while never caching message-binding bottom leaves. The extracted `VerifiedWaistbandRootGuard` models binding the cache to $"PK.root"$ and locking the first codeword signed at each ancestor leaf. The modeled cache then refuses a second codeword for the same leaf (`baggy_multiturn_durable_and_non_equivocating`).

== Stateful Jorts and single-datagram `FrontierSumFts`

*Jorts* instantiates a single-layer Merkle tree of height $h in [6, 20]$ over $2^h$ one-time WOTS+C leaves [BDH11], occupying 4,652 B at custody height $h = 16$ (Keccak) and $"4,136" + 32 h$ B in Goldilocks Poseidon2 format. Signing touches only the 128 chains of one leaf; in prepared mode, upcoming leaf chains are evaluated and MAC-checked offline, reducing online signing to a single round of authenticated openings gated by BeltLatch (§4.1).

*Single-datagram few-time votes.* For live consensus voting under the 1,232-byte IPv6 minimum-MTU payload limit, `FrontierSumFts` uses a public randomized message digest as the rank of a prefix-free binary-tree antichain of $L$ nodes at height $h = 8$ paired with chain offsets in $[0, w)$ summing to $S$. The codeword space factors as $M(h,w,L,S) = N(h,L) dot D(L,S) > 2^256$, ranked and unranked exactly in 384-bit integer arithmetic (`frontierSumFts_rank_unrank_bijection`). `Compact1122` ($w = 96, L = 34, S = "1,615"$) occupies 1,122 B—1,218 B with a 96-byte consensus vote header.

`FrontierSumFts` is the sole few-time signature construction. Its canonical voting profile is `Compact1122`. On the durable signing path the signer reserves the key's single use before computing secret chain values in `FtsEpochWal`. Exact rank and unrank concern the public codeword space. The one-use rule concerns the secret key and must survive a restart.

= Actively Secure Multiparty Engines and Blinded MACs

== 256-way bitsliced 3PC with Frobenius ternary DZK

For $(2,3)$ honest-majority custody, `rss256` evaluates 256 independent Keccak-f[1600] instances in lockstep, bitslicing bit $i$ of each instance into a 256-bit SIMD register over replicated shares [FLNW17]. Every $chi$-layer AND gate remains sealed behind a post-batch barrier: parties hash the gate transcript, run a commit-and-open coin toss, and verify all multiplications simultaneously via a two-pass sublinear distributed zero-knowledge proof [BGIN19] over $FF_(2^128)$. Ternary challenges in ${0, 1, gamma}^b$ are represented in a Frobenius normal basis so challenge folding reduces to $FF_2$-linear XORs.

#theorem("bitsliced batch soundness and sticky poison", src: [`rss256_two_pass_product_proof_sound`, `rss256_sticky_poison_terminal_absorption`])[
  For a recorded batch with a nonzero error block, the model bounds the fraction of accepting coin pairs in the two-pass check [BGIN19]. At 614,400 blocks and six fold levels the bound is below $2^(-217)$. In the modeled poison latch a barrier failure makes subsequent openings inadmissible.
]

== Coordinator-free `IsolatedCnfParty`, PQ-hybrid channels, and proactive refresh

For general honest-majority committees ($2(t-1) < n$, including 2-of-3, 3-of-5, and 4-of-7), `IsolatedCnfParty` eliminates central coordinators and offline preprocessing by executing replicated CNF Boolean evaluation [CGH+18] directly over pairwise post-quantum hybrid encrypted links.

*PQ-hybrid forward-secret wire channels.* Pairwise links (`ConfidentialWireChannel` / `pq_handshake.rs`) establish ephemeral forward secrecy by combining `X25519` Diffie–Hellman with `ML-KEM-768` [FIPS203] key encapsulation, authenticated under out-of-band pairwise 32-byte pre-shared keys and bilateral transcript confirmation (`QSAG.QUORUM.WIRE_PQ_TRANSCRIPT/v1`; only the lower-indexed party holds a decapsulation key). Session traffic uses per-direction ratcheted cSHAKE256 [SP800-185] keystreams with predecessor key erasure, 32-byte encrypt-then-MAC tags over `"QSWF"` headers binding deployment ID, session ID, directed endpoints, round tag, and strict monotonic sequence numbers. Replayed, reordered, reflected, or cross-deployment frames fail authentication in constant time without advancing channel state.

#protocol("coordinator-free CNF signing and proactive refresh", src: [`IsolatedCnfParty`, `cnf_party/refresh.rs`])[
  Each $(t-1)$-subset $S subset [n]$ defines a replication slot held by all custodians $i in.not S$, seeded with a shared 32-byte PRSS key (`CnfRssKeyShare256`).
  1. _Chida et al. multiplication check [CGH+18]._ In characteristic two, let $[z_k]$ be a gate value, $[u_k]$ its randomized sharing, and $[r]$ the secret check key. Before drawing the public coin, each party derives a fresh shared PRSS mask $[s]$, computes $[r s]$ (`rs = self.mul_field(&r, &mask)?` in Rust), and exchanges consistency digests. The coin then supplies weights for $[w] = sum_k alpha_k [z_k]$ and $[u] = sum_k alpha_k [u_k]$. Parties open $hat(w) = w + s$ and compute $[T] = [u] + [r s] + hat(w) [r]$ locally. The check has zero post-coin secret $r w$ multiplications. Fixing the product correction before the weights are known closes that selective-failure channel. A separate PRSS blind $[rho]$ masks the final residual. Parties multiply $[rho][T]$, cross-check consistency again, and accept only an opening of zero.
  2. _Hedged Cut-the-Hash release._ After a two-round echo-verified `QSAG.R_COMMIT/v1` randomizer coin toss, custodians execute `BaggyEngine` or `IsolatedCnfSlhOracles` (`slh_keygen`, `slh_sign`), poisoning their durable journal on any mismatch.
  3. _Proactive zero-sum CNF refresh._ In `refresh_share`, each dealer samples 112-byte slot rows whose first 80 bytes XOR to zero across all $binom(n, t-1)$ slots (32-byte seed mask, 32-byte PRF mask, 16-byte $FF_(2^128)$ blind) plus 32 bytes of fresh PRSS entropy, commits per-peer payloads (`QSAG.QUORUM.REFRESH.COMMIT/v1`) before opening, verifies peer commitments and slot consistency digests, and opens a degree-4 Horner evaluation over $FF_(2^128)$ at a joint coin challenge (detecting any non-zero mask sum with error $<= 4 slash 2^128$). Updated `QSCNFK01` shares install after peers acknowledge preparation with `confirm_refresh_prepared`. An honest peer sends this acknowledgment after persisting its staged bytes.
]

== Dishonest-majority SPDZ, binary towers, and Ring-LWE + `SoftSpokenOT`

For arbitrary thresholds $t <= n$ (and for $(t,n)$ committees converting CNF shares via a public 0/1 linear map into $t$-of-$t$ additive shares), QSAG runs actively secure SPDZ [DPSZ12] over two algebraic rings:
- *Goldilocks ($p = 2^64 - 2^32 + 1$)* with MACs in the quadratic extension $FF_(p^2)$ for algebraic Poseidon2 [GKS23] chains (`CorduroyPoseidon2`, `JortsPoseidon2`), evaluating each $x^7$ S-box in one online round from a preprocessed power tuple $([r], [r^2], dots, [r^7])$ by opening $y = x - r$ and computing $[x^7] = sum_(k=0)^7 binom(7,k) y^(7-k) [r^k]$ locally (`power7BinomialEval_eq_sbox7`).
- *Wiedemann's binary tower [Wie88]*, $cal(T)_0 = FF_2$, $cal(T)_k = cal(T)_(k-1)[x_(k-1)] slash (x_(k-1)^2 + x_(k-2) x_(k-1) + 1)$, using $cal(T)_3 = FF_(2^8)$ for Shamir evaluation points (up to 255 custodians) and $cal(T)_7 = FF_(2^128)$ for MACs.

#theorem("tower-to-polynomial hardware isomorphism", src: [`ringIsoTower128ToPoly`, `gf128FieldMul_eq_rustGf128Mul`])[
  An explicit constructive ring isomorphism $cal(T)_7 tilde.equiv FF_2[z] slash (z^128 + z^7 + z^2 + z + 1)$ maps tower multiplication to the Rust shift-and-reduce loop and to the verified `PCLMULQDQ`, `VPCLMULQDQ`, and `PMULL` carryless multiplication kernels.
]

*Dealerless preprocessing.* Base oblivious transfer runs over Ring-LWE in $ZZ_(12289)[X] slash (X^1024 + 1)$ with a Fujisaki–Okamoto re-encryption check [FO99] and a 24-challenge signed-monomial OR-proof (${plus.minus X^k}$: 264 bits of challenge space, 132-bit generic Grover search exponent; pairwise challenge differences divide 2, `signedMonomial_challenge_set_pairwise_invertible`). Because an $ell_infinity$ norm check alone admits the trivial public unit solution $(s = 1, e = -a)$ for most public polynomials $a$, prover and verifier enforce an exact Euclidean norm bound $norm(z_s)_2^2 + norm(z_e)_2^2 <= 1.5 times 10^9$ that refutes the unit solution and forces extraction into a non-vacuous Euclidean Ring-SIS relation (`extract_rlwe_or_sigma_24_euclidean_sis_dichotomy`, `tooth_rlweUnitSis_refuted_by_euclidean_bound`). The fixed-point `Q192` sampler has a modeled rational-base error budget across 49,152 coordinates (`q192_rlwe_batch_tvd_bound_rational_base`). Applying it to production sampling requires the finite-precision and normalized Gaussian hypotheses.

OT extension supports both KOS [KOS15] and subfield-VOLE `SoftSpokenOT` ($n_C = 256, k = 2$, 512 Ring-LWE base OTs for 128-bit Grover security on $Delta in FF_2^256$, consistency error $<= 2^(-241) + B^2 slash 2^256$ [Roy22], `softspoken_consistency_simulation_budget`). Correlation expansion uses a depth-15, 64-tree regular dual-LPN PCG [BCGI+19]. Lean brackets bias for a specified row (`prodRow0_bias_bracket` in $(2^(-118), 2^(-117))$; balanced 11-tap fixture in $(2^(-220), 2^(-219))$ with a Stern–Dumer work estimate $> 2^256$). Arithmetic and Boolean triples use MASCOT sacrifice [KOS16] and post-permutation bucketing ($f = 3$ at 8,192 words, $< 2^(-40)$ leakage, one parity-hiding bucket discarded per pass), with transcript commitments frozen strictly before challenge sampling (`SacrificeFreezeSample`).

== 31 µs active-sacrifice pooled blinded MAC openings

In standard SPDZ, verifying an opened value $x$ with MAC share $[m]$ tests whether $d = m - alpha x = 0$ by opening $d$. That is safe only when the global MAC key $alpha$ is discarded on abort. In threshold custody, $alpha$ persists across signing sessions and $(t,n) -> (t',n')$ resharings: an adversary who shifts an opened share by $Delta != 0$ observes $d = -alpha Delta$ in the abort transcript and recovers $alpha = -d Delta^(-1)$ (`tooth_unblinded_mac_residual_recovers_alpha`). Degree checks do not block this attack in unanimous quorums ($t = n$, zero redundancy) or when a corrupt reshare dealer distributes a degree-$t'$ polynomial violating the constant-term MAC relation.

#protocol("active-sacrifice pooled blinded MAC zero test", src: [`mac_blind.rs`])[
  Parties hold additive shares $d_j$ of the MAC residual $d = sum_j d_j$ over $FF in {FF_(p^2), cal(T)_7}$.
  1. _Unpooled OLE baseline._ Parties commit to value shares, draw private randomizers $r_i in FF$, and evaluate additive shares of $w = (sum_i r_i)(sum_j d_j)$ via oblivious linear evaluation in which $d_j$ is strictly the _sender_ input and receiver choice bits are fresh disposable masks (preventing selective-failure bit tests on $d_j$). Parties commit to all shares of $w$, open $w$ alone, and accept iff $w = 0$.
  2. _Offline Beaver-sacrificed blinding pool._ Over a retained `OtMesh` (or `PartyOtEndpoint`), batched offline OLE generates single-use blinding triples $([r], [a], [c = r dot a])$ paired with companion sacrifice triples $([r], [a'], [c'])$, runs a two-round echo-committed Beaver sacrifice check before sealing triples into a monotone-serial pool (sacrifice soundness error $< 2^(-255)$ per triple over $cal(T)_7$), and wipes/poisons the pool on any discrepancy.
  3. _31 µs online opening._ Each online MAC barrier pops one certified triple, commit-opens $e = d + a$, and commit-opens $w = r dot e - c = r dot d$, accepting iff $w = 0$.
]

#theorem("zero key leakage on abort", src: [`macBlind_abort_independent_of_alpha`, `macBlind_spdz_alpha_zero_leakage`, `macBlind_tower128_two_round_256bit_sound`])[
  In the ideal-OLE hybrid with corrupt inputs fixed and at least one honest party contributing a uniform $r_i in FF$: if $d = 0$ then $w = 0$; if $d != 0$ then $w$ is uniform over $FF$, hence conditioned on abort ($w != 0$) the opened value is uniform over $FF^times$ for every key producing a nonzero defect. False acceptance occurs with probability $1 slash abs(FF)$ ($p^(-2) < 2^(-127)$ over $FF_(p^2)$, and $2^(-256)$ over $cal(T)_7$ across two independent randomizers).
]

_Proof._ With corrupt shares fixed, $r = sum_i r_i$ is uniform in $FF$. For any $d != 0$, multiplication $r |-> r d$ is a bijection on $FF$ mapping $0 |-> 0$ and $FF^times -> FF^times$ uniformly without reference to $alpha$. $square$

A zero randomizer would accept every forgery (`tooth_zero_randomizer_always_accepts_forged_mac`), which is why every party contributes $r_i$. Additive Boolean openings commit the full residual vector and pass three transcript-bound $FF_(2^128)$ projections through `blind_open_tower128` under independent projection and blinding challenges. The resulting error budget is $(q^(-1) + (1 - q^(-1)) q^(-2))^3 < 2^(-256)$ at $q = 2^128$. Lean checks the integer inequality after clearing denominators (`three_projection_mac_blind_bound_gf128`). In Shamir resharings $(t,n) -> (t',n')$, all $n'$ recipients verify degree-$< t'$ syndromes and constant-term MAC relations through independent blinded zero tests before retiring old shares. The Rust release guards use consuming permits to enforce the order of checks and openings at their call sites.

*Threshold ML-DSA.* In `threshold_mldsa`, signing tolerates up to $t-1$ statically corrupt custodians with abort and requires at least $2t-1$ online. For ML-DSA-44/65/87 [FIPS204], the high bits $w_1$ of $A y$ remain sealed during rejection sampling. Authenticated daBits convert the high bits to binary replicated shares. The parties run SHAKE256 with shared Keccak-f[1600] and generate the sparse challenge on shares. A blinded joint check over $FF_(q^6)$ covers sampling completion and the norm and hint predicates. An unsuccessful attempt exposes masked openings and one verdict. Only acceptance permits opening the signature material. This abort-transcript ZK argument assumes fresh masks and the protocol's authenticated broadcast and sharing guarantees.

*Threshold oblivious PRF.* In `voprf_spdz`, all $n$ servers enroll Shamir shares of a width-12 Poseidon2 key and its SPDZ authentication material. Any selected $t$ can evaluate ($2 <= t <= n <= 64$). The online job binds the roster and a durably reserved counter. The parties authenticate the masked client input, check the permutation openings and return masked outputs to the client. Enrollment and local CLI orchestration can hold several parties' state on one host. Isolation requires distinct custodians and confidential authenticated links. Blind credential issuance separately uses a three-party MPC-in-the-head proof [IKOS07, GMO16].

*One transport interface.* The shared `no_std` `WireTransport` carries round-tagged frames. CNF signing, Shamir-SPDZ evaluation and Hem custody use it directly. The ML-DSA round adapter implements `MpcTransport` on the same interface. A concrete channel must enforce the protocol's session, endpoint, sequencing and confidentiality requirements.

= BeltLatch, Anti-Rollback Anchors, and Quorum Custody

== Crash-atomic paged WAL and `SlotIndexed` leaf binding

Stateful Jorts security reduces to a single invariant: no leaf index $e$ may ever open WOTS+C chain shares for two distinct `(digest, salt)` tuples. _BeltLatch_ enforces this invariant locally at each custodian before any share leaves memory.

#protocol("BeltLatch durable reservation", src: [`belt_latch.rs`; MIR `BeltLatchKernel`])[
  Before releasing any WOTS+C share at leaf $e$, custodian $i$:
  1. validates $e < 2^h$ under its active `BeltIndexingMode` (`SequentialBounded` wallet mode bounding jumps by `MAX_EPOCH_JUMP = 64`, or `SlotIndexed` consensus mode mapping BFT slot $s$ directly to leaf $e = s$ via `bind_consensus_slot` and permanently burning skipped leaves $< s$);
  2. persists $(e, "digest", "salt", "digits")$ behind a 72-byte MAC-sealed header (`QSAG.BELT.LATCH.WAL.MAC/v3`) and `fsync`s file and directory descriptors under an `OpenDescriptionId`-bound `LockedRecord` (`mode & 0o077 == 0`);
  3. replays the exact persisted record on any retry for $e$ and rejects any differing digest, salt, or digit vector;
  4. exchanges cSHAKE256 acknowledgments (`QSAG.BELT.ACK.v1`) with peers and requires a valid quorum permit (`VerifiedBeltQuorumGuard`) to open shares.
]

#theorem("paged two-slot torn-sector recovery", src: [`TwoSlotHwmCrashModel.paged_layout_safe`, `append_tear_truncate_recovers`])[
  Placing the genesis seal on page 0, the two high-water-mark slots on separate 4,096-byte pages (offsets 4,096 and 8,192), and the authenticated record chain from offset 12,288 gives the following model-level guarantee. Assuming authenticated seals cannot be forged (`NoForge`) and at most one unsynced sector tears per crash (sector size dividing 4,096), recovery never rewinds below an acknowledged counter, deterministically truncating an unauthenticated tail when slots hold $(c, c)$ or $(c, c-1)$ and failing closed otherwise. Co-locating both slots in one sector loses state under a single tear.
]

== Hardware and hypervisor anti-rollback anchors

Filesystem `fsync` cannot detect whole-disk or virtual-machine snapshot restoration. An anchored journal brackets a reservation with a single-use two-phase `(committed, pending)` `AnchorTicket` against an `ExternalMonotoneAnchor` (`anti_rollback.rs`, `#![forbid(unsafe_code)]`):
- *`Tpm2NvMonotoneAnchor`*: speaks raw ISO/IEC 11889 TPM 2.0 command/response frames (`TPM2_NV_Increment`, `TPM2_NV_Read`) over `/dev/tpmrm0` with zero C dependencies, binding WAL checkpoints to a 64-bit hardware `TPM_NT_COUNTER`.
- *`VmGenIdForkGuard` & `HypervisorGenerationAnchor`*: bind checkpoints to the hypervisor's 128-bit ACPI `VMGENID`, Linux `boot_id`, and the WAL's `(st_dev, st_ino, st_ctime)` tuple, halting immediately on VM clone or snapshot revert (paired with a disjoint-mount or TPM counter).
- *`FsDirectoryMonotoneAnchor`*: a mirrored, fsynced two-slot checkpoint. Independence from the journal is a deployment requirement. The CLI mount anchor checks device identifiers.

The sealed Hem vault authenticates its anchor requirement. Its CLI refuses `--ephemeral-unanchored` for an anchored enrollment, and resharing retires the superseded generation at the anchor.

== Switching custodians without changing the validator key

`HemDynamicShamirQuorum` bridges signing custody (QS) and public aggregation (AG). Custodians share one height-six JortsPoseidon2 tree. Its 65-byte validator key and 4,328-byte signatures pass directly to the Hem verifier. Changing the roster or threshold preserves that key and carries forward the first usable leaf.

On the detached signing path, each acknowledger binds the message, leaf, generation and ordered rosters in its authenticated local journal, advances its durable leaf floor, and persists its share state. The signers release only after every member of the chosen acknowledgment quorum confirms this reservation. A signing subset needs $t$ shares. Two acknowledgment quorums must intersect in an honest custodian.

Handoff consumes predecessor custody. Every old endpoint reserves past the last leaf in its generation, persists retirement for the handoff binding, and acknowledges it before an old dealer may send a resharing packet. The successor starts at the agreed floor. In the vault path the successor remains staged until durable predecessor retirement releases its key. Losing an acknowledgment can stop service. Safety depends on the durability and rollback protection of the old generation's records.

The symmetric threshold rule $2q > n + f$ (with liveness $q <= n - f$, yielding tight BFT optimality $n >= 3f + 1$, `beltLatch_safe_and_live_iff_n_ge_3f_plus_1`) is a special case of Cachin–Tackmann asymmetric trust [CT19]:

#definition("asymmetric B³ quorum system", src: [`qsag_quorum::access::AsymmetricQuorumSystem`])[
  Each participant $i$ specifies a quorum family $cal(Q)_i$ and a downward-closed tolerated fault family $cal(F)_i$. The system satisfies $B^3$ [CT19] if for all $i, j$, all $Q_1 in cal(Q)_i$, $Q_2 in cal(Q)_j$, and all $F in cal(F)_i inter cal(F)_j$,
  $ (Q_1 inter Q_2) without F != emptyset. $
  Participant $i$ is _wise_ in an execution with actual fault set $F^*$ if $F^* in cal(F)_i$.
]

#theorem("global leaf uniqueness under B³", src: [`abqs_belt_latch_unique_msg`, `beltLatch_quorum_intersection_global_uniqueness`, `verify_b3`])[
  If the quorum system satisfies $B^3$, honest custodians enforce BeltLatch, and $i, j$ are wise, then any two certificates $Q_1 in cal(Q)_i$ for $m_1$ and $Q_2 in cal(Q)_j$ for $m_2$ at leaf $e$ satisfy $m_1 = m_2$.
]

_Proof._ Since $F^* in cal(F)_i inter cal(F)_j$, some custodian $h in (Q_1 inter Q_2) without F^*$ is honest, persisted a unique record at leaf $e$, and acknowledged both $Q_1$ and $Q_2$. $square$

Weighted stake quorums, tree-composed bicameral policies [ACTZ21], and Stellar-style personal quorum slices [LGM19] instantiate the intersection condition above (and compile to symmetric depth-2 protocols via [ACKV26]). During reconfiguration, `verify_handoff_safety` enforces cross-system intersection $(Q_"old" inter Q_"new") without F != emptyset$ across all common fault sets so safety holds across epoch boundaries.

== Dealerless 0/1 monotone span programs and equivocation evidence

Independently of certification quorums, signing authority is governed by a binary monotone span program (`MonotoneSpanProgram`): a matrix $M in {0,1}^(m times c)$ over $FF_p$ with row-owner map $rho : [m] -> [n]$. Sampling $v = (s, r_2, dots, r_c)$ distributes row share $y_r = (M v)_r$ to $rho(r)$. Any authorized set $Q$ owns rows spanning $e_1 = (1, 0, dots, 0)$ via public reconstruction weights $lambda^top M_Q = e_1$, collapsing locally to additive shares $s_i = sum_(rho(r) = i) lambda_r y_r$ via additions alone while unauthorized sets hold shares independent of $s$.

In `PersonalReleaseParty`, each custodian holds only its own `PersonalBeltLatch`, WAL, and MSP rows: after assembling a $B^3$ certificate over encrypted pairwise links, parties locally collapse owned rows to four Goldilocks elements, establish pairwise Ring-LWE/KOS OT channels, authenticate inputs and 118 Poseidon2 $x^7$ S-box tuples under a dealerless `GoldilocksExt2` MAC key, and pass the two-stage blinded MAC test before opening the digest—never exposing raw MSP shares to any coordinator or peer.

When fault thresholds are exceeded (or a single host holds a key), WOTS+C incomparability makes double-signing publicly slashable:

#theorem("self-contained equivocation evidence", src: [`JortsEquivocationEvidence::verify`, `BlocklaceLeafAnchor`])[
  Any tuple $("pk", e, mu_1, sigma_1, mu_2, sigma_2)$ with $mu_1 != mu_2$ and both Jorts signatures valid at leaf $e$ (8,800 B at $h = 6$; 9,440 B at $h = 16$) is publicly verifiable from $"pk"$ alone without timestamps or state history, and is unforgeable unless the key holder signed twice at $e$ or broke WOTS+C/Merkle security. Binding `"seq" = e` inside the 120-byte `BlocklaceLeafAnchor` equates any grassroots blocklace fork [KLST26] with same-leaf equivocation.
]

== Watch-only wallets and delegated authority

`PiHdCommitInventory` is the watch-only PQ wallet. At enrollment the custodians derive a finite batch of child keys from shared subset seeds. The public inventory binds each index and child public key under a 32-byte master commitment. Given the inventory, a wallet can return the enrolled address and authentication path with zero online MPC rounds. Deriving private child material still requires custody shares.

The capability ladder offers three verification interfaces. A `SpongeMacaroon` holder appends caveats to a keyed sponge chain that a verifier checks with a shared secret. A `PqBiscuit` verifier needs only the authority public key to check signatures. Each delegation authenticates the next step key and caveats with a one-use `Compact1122` signature, and a terminal seal closes the chain. At the third rung, a `QSAGCAU1` holder presents a fresh challenge-bound zk-Hem proof of issuer enrollment, caveat satisfaction and non-revocation. Public inputs include the request and registry roots. The presentation omits a stable token identifier. These interfaces have distinct wire formats.

= What the verification establishes

== Signing reductions and their hypotheses

In `lean/Qsag`, `hulsing_closed_multihop_euf_cma_bound` relates an executable adaptive forgery experiment to primitive games for the message randomizer, seed PRF, chain and hash targets. `SigningPrimitiveBounds` supplies advantage bounds for the relevant adversaries and, where applicable, subset cover. Lean [MU21] checks the game hops and the final arithmetic. The $< 2^(-128)$ conclusions have the logical form `*_of_primitive_bounds`: instantiating them requires explicit ROM or QROM primitive-hardness bounds. The quantum query estimates draw on search, recording and one-way-to-hiding arguments [BBBV97, Zha19, AHU19]. The executable signing game itself is classical. Using its primitive error parameter for a concrete hash against quantum queries requires a separate instantiation.

For example, `Top/Signing.lean` gives Jorts up to $2^16$ signing queries and $2^48$ evaluations in its QROM-sized primitive term. For Baggy these caps are $2^16$ and $2^40$ with an additional $2^(-131)$ cover premise. Corduroy and the modeled radix-16 SLH profile have their own caps. The evaluation cap parameterizes the primitive-hardness premise. The executable signing trace counts signing queries only.

== Custody models, extracted Rust and ISA evidence

The latch refinement relates visible epoch and signing events under the model's signing oracle. Distributed custody models reason about accepted acknowledgments, ledger transitions and unsafe release subject to authentication and durability premises. A visible-trace result alone gives no secrecy theorem for internal messages. A UC transfer in the sense of [Can01] requires its real/ideal distinguishing premise. The two-slot crash theorem concerns the modeled log under the tear and seal assumptions in §4. Whole-device rollback, TPM 2.0, VMGENID, slot-indexed deployment, proactive refresh and the X25519 + ML-KEM handshake are implementation or platform boundaries.

Charon and Aeneas [HP22] translate selected Rust MIR into Lean using a modeled prelude. Examples with specification lemmas include field operations, the Keccak permutation and individual release guards. For SLH-DSA the byte-identity theorem concerns the replicated oracle model (§2). The network scheduler, share storage, compiler and link step require separate evidence. A lexical call-site count and an axiom audit measure neither whole-program reachability nor binary correctness.

For the 28 hand-written assembly kernels, `ElfFunctionalEquiv.lean` identifies 12/28 live functional bindings. For constant time the 26/28 non-transpose kernels have ISA trace evidence within the public-state and DOIT/DIT contracts. The full fixture inventory contains 19 x86-64 and nine AArch64 entries. The x86 multi-call trace theorem fixes a default public state. Its AArch64 counterpart takes the public state as a parameter. Functional bindings relate results to mathematical operations. Trace checks concern observations such as program counters, addresses and variable-latency operands. Their interpretation as timing requires an adequate hardware leakage model [RBV17]. Fixture freshness is checked outside Lean. Seven assembly/MIR comparisons meet at shared mathematical specifications under their input preconditions, including single-block cases.

Pairwise authenticated channels, fresh entropy, bounds on corruption, persistent storage and an independent rollback anchor enter the deployment trust base. SPDZ preprocessing additionally assumes security of the underlying Ring-LWE OT and correlation expansion. The standalone #link("https://github.com/emberian/qsag-chip")[qsag-chip hardware repository] contains the silicon and FPGA designs and their evidence.

= Evaluation

Measurements were collected on AMD Zen 5 (AVX-512, GFNI, VPCLMULQDQ), AMD EPYC-Milan Zen 3 (16 cores / 32 threads, AVX2, `rustc 1.99.1`, `opt-level = 3`, `lto = "thin"`, `codegen-units = 1`), and encrypted `WireTransport` sockets.

== Constant-time SIMD cryptographic kernels

#figure(tbl((2.15fr, 0.85fr, 0.9fr, 0.65fr, 0.85fr, 0.9fr, 0.65fr),
  [Kernel (64 KiB / 256 coeffs)], table.cell(colspan: 3)[Zen 5, AVX-512], table.cell(colspan: 3)[Zen 3, AVX2],
  [], [Scalar], [Vector], [Speedup], [Scalar], [Vector], [Speedup], table.hline(),
  [Keccak-f[1600] (cpb; GB/s)], [3.366], [0.634 (3.15)], [5.31×], [6.437], [1.623 (1.48)], [3.97×],
  [SHA-256 (cpb; GB/s)], [4.900], [0.830 (2.41)], [5.90×], [8.876], [1.320 (1.82)], [6.72×],
  [$FF_(2^8)$ Shamir mul (cpb; GB/s)], [14.66], [0.027 (73.2)], [537×], [28.29], [0.209 (11.5)], [135×],
  [$FF_(2^8)$ Shamir MAC (cpb; GB/s)], [14.32], [0.022 (91.5)], [654×], [27.66], [0.049 (48.7)], [561×],
  [$FF_(2^128)$ mul-acc (cpb; GB/s)], [16.97], [0.058 (34.3)], [291×], [32.97], [0.250 (9.60)], [132×],
  [Tower $cal(T)_7$ MAC (cpb; GB/s)], [14.23], [0.303 (6.58)], [46.9×], [24.21], [0.653 (3.67)], [37.1×],
  [ML-DSA fwd NTT [Sei18] (ns, cycles)], [809.3], [243.1 (485)], [3.33×], [1,197], [338.4 (812)], [3.54×],
  [ML-DSA inv NTT (ns; cyc)], [931.2], [209.8 (419)], [4.44×], [1,401], [322.9 (775)], [4.34×],
  [ML-DSA ptwise mul (ns; cyc)], [352.4], [56.7 (113)], [6.21×], [516.7], [98.8 (237)], [5.23×],
), placement: top, scope: "parent", caption: [Constant-time kernel throughput (medians of 7 runs). Zen 5 uses 512-bit vectors with GFNI and VPCLMULQDQ; Zen 3 uses 256-bit register-only split-nibble tables.]) <simdbench>

Eight-way register-resident Keccak-f[1600] eliminates stack spills and achieves 0.634 cycles/byte (3.15 GB/s) on Zen 5 (@simdbench), hashing an internal Merkle node in 111 ns per instance. Hardware GFNI and `VPCLMULQDQ` accelerate $FF_(2^8)$ Shamir inner products by 654× (91.5 GB/s) and $FF_(2^128)$ MAC folding by 291× (34.3 GB/s), removing linear algebra from the MPC critical path.

== Threshold signing, quorum switching, and MPC batches

#figure(tbl((2.25fr, 1.65fr, 1.85fr),
  [Protocol operation], [Configuration & channel], [Latency / cost], table.hline(),
  [Jorts 2-of-3 prepared sign], [in-memory / simulated WAN], [1.0 ms / 81 ms],
  [`BftShamirJorts` 3-of-4 DVT ($f=1, q=3$)], [Shamir + BeltLatch (`4,172 B`)], [2.44 ms],
  [Unpooled vs. pooled blinded MAC], [3PC `OtMesh`: baseline / online (refill)], [13.75 ms / *31 µs* (4.04 ms)],
  [256-way bitsliced 3PC batch], [256 Keccak-f[1600] + [BGIN19] DZK], [54.0 ms],
  [`IsolatedCnfParty` Keccak batch], [2-of-3 / 3-of-5 over PQ `WireTransport`], [39.5 ms / 96.2 ms],
  [Poseidon2 TOPRF ($t$-of-$n$ SPDZ)], [2-of-3 / 3-of-5: offline; online/eval], [7.4 s, 4.3 ms / 21.6 s, 11.7 ms],
), caption: [End-to-end threshold signing, quorum-switching, MPC batch, and preprocessing measurements.]) <protobench>

@protobench separates online signing from precomputation. In the three-party MAC benchmark the pooled path used 31 µs online plus 4.04 ms amortized refill time. The prepared Jorts figure likewise excludes preparation. The historical CNF timings precede the pre-coin product and final blinding changes.

== Consensus live-path batch verification

In BFT slot voting, an aggregate signature paired with a 1-bit-per-validator participation bitmap exceeds the 1,232-byte IPv6 minimum-MTU UDP payload once the registry surpasses 9,088 validators (`96 + ceil(N / 8) > 1,232`) [KSW26]. `Compact1122` keeps every individual vote plus its 96-byte consensus header at a constant 1,218 B regardless of total validator count $N$, allowing a committee of 512–1,500 sampled voters to fit one datagram per vote at $N = 10^6$ (@live).

#figure(tbl((1.05fr, 1.25fr, 0.85fr, 1.1fr, 1.35fr),
  [Validators $N$], [96 B sig + bitmap], [Fits 1 MTU], [Sampled votes], [Verify (1c / 8t)], table.hline(),
  [1,500], [284 B], [yes], [512], [0.52 s / 68 ms],
  [9,088], [1,232 B], [yes], [1,000], [1.03 s / 132 ms],
  [10,000], [1,346 B], [no], [1,200], [1.23 s / 158–187 ms],
  [1,048,576], [131,168 B], [no], [1,500], [1.54 s / 198 ms],
), caption: [Live-path consensus voting: exact byte size of a hypothetical 96 B signature + $N$-bit bitmap vs. 1,232 B IPv6 MTU ceiling, alongside measured 8-way SIMD Keccak batch verification of 1,218 B `Compact1122` votes.]) <live>

Batching independent `Compact1122` verifications across the 8-way SIMD Keccak-f[1600] kernel yields a 6.1× speedup over scalar verification (1.03 ms per vote on one core; 158–187 ms for 1,200 votes across 8 threads), comfortably within sub-second BFT slot budgets while relying solely on symmetric hash assumptions.

= Conclusion

Threshold signers can share the secret work at the leaves while a public assembler handles the tree. The replicated multiplication barrier fixes its check product before the coin, and stateful custody fixes the leaf reservation before release. The former protects secret computation on abort. The latter preserves the signing history when a quorum changes. The Lean results describe modeled signing games and state transitions under explicit primitive and durability assumptions.

#heading(numbering: none)[References]
#{
  set text(size: 7.4pt)
  set par(justify: false, leading: 0.38em, spacing: 2.6pt, hanging-indent: 1.6em)
  let refs = (
    [[ACKV26] I. Amores-Sesar, C. Cachin, S. H. Kamp, J. Villacis, "Symmetry all the way down", arXiv:2607.04887, 2026.],
    [[ACTZ21] O. Alpos, C. Cachin, L. Zanolini, "How to Trust Strangers: Composition of Byzantine Quorum Systems", SRDS 2021.],
    [[AE18] J.-P. Aumasson, G. Endignoux, "Improving Stateless Hash-Based Signatures", CT-RSA 2018.],
    [[AHU19] A. Ambainis, M. Hamburg, D. Unruh, "Quantum Security Proofs Using Semi-classical Oracles", CRYPTO 2019.],
    [[BBBV97] C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM J. Comput. 26(5), 1997.],
    [[BBD+26] D. Boneh, B. Bünz, Justin D., Y. Litchev, K. Nazirkhanova, "PRAWNS: Threshold Hash-Based Signatures from Threshold PRFs", IACR ePrint 2026/2142, 2026.],
    [[BCGI+19] E. Boyle, G. Couteau, N. Gilboa, Y. Ishai, L. Kohl, P. Rindal, P. Scholl, "Efficient Two-Round OT Extension and Silent Non-Interactive Secure Computation", ACM CCS 2019.],
    [[BDH11] J. Buchmann, E. Dahmen, A. Hülsing, "XMSS – A Practical Forward Secure Signature Scheme Based on Minimal Security Assumptions", PQCrypto 2011.],
    [[BDOZ11] R. Bendlin, I. Damgård, C. Orlandi, S. Zakarias, "Semi-Homomorphic Encryption and Multiparty Computation", EUROCRYPT 2011.],
    [[BGIN19] E. Boyle, N. Gilboa, Y. Ishai, A. Nof, "Practical Fully Secure Three-Party Computation via Sublinear Distributed Zero-Knowledge Proofs", ACM CCS 2019.],
    [[BHKN+19] D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, "The SPHINCS+ Signature Framework", ACM CCS 2019.],
    [[BLS01] D. Boneh, B. Lynn, H. Shacham, "Short Signatures from the Weil Pairing", ASIACRYPT 2001.],
    [[Can01] R. Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols", FOCS 2001.],
    [[CGH+18] K. Chida, D. Genkin, K. Hamada, D. Ikarashi, R. Kikuchi, Y. Lindell, A. Nof, "Fast Large-Scale Honest-Majority MPC for Malicious Adversaries", #link("https://eprint.iacr.org/2018/570")[CRYPTO 2018].],
    [[CT19] C. Cachin, B. Tackmann, "Asymmetric Distributed Trust", OPODIS 2019; extended version with O. Alpos and L. Zanolini, arXiv:1906.09314.],
    [[DPSZ12] I. Damgård, V. Pastro, N. Smart, S. Zakarias, "Multiparty Computation from Somewhat Homomorphic Encryption", CRYPTO 2012.],
    [[FIPS202] NIST FIPS 202, "SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions", 2015.],
    [[FIPS203] NIST FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", 2024.],
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
    [[KLST26] I. Keidar, A. Lewis-Pye, E. Shapiro, N. Talmon, "Constitutional Consensus for Democratic Governance", arXiv:2505.19216, 2026.],
    [[KOS15] M. Keller, E. Orsini, P. Scholl, "Actively Secure OT Extension with Optimal Overhead", CRYPTO 2015.],
    [[KOS16] M. Keller, E. Orsini, P. Scholl, "MASCOT: Faster Malicious Arithmetic Secure Computation with Oblivious Transfer", ACM CCS 2016.],
    [[KSW26] Q. Kniep, J. Sliwinski, R. Wattenhofer, "Byzantine Fault-Tolerant Post-Quantum Distributed Quorum Signatures", arXiv:2607.17700, 2026.],
    [[LGM19] G. Losa, E. Gafni, D. Mazières, "Stellar Consensus by Instantiation", DISC 2019.],
    [[MU21] L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021.],
    [[RBV17] O. Reparaz, J. Balasch, I. Verbauwhede, "Dude, is my code constant time?", DATE 2017.],
    [[Roy22] L. Roy, "SoftSpokenOT: Quieter OT Extension from Small-Field Silent VOLE in the Minicrypt Model", CRYPTO 2022.],
    [[Sei18] G. Seiler, "Faster AVX2 optimized NTT multiplication for Ring-LWE lattice cryptography", IACR ePrint 2018/039, 2018.],
    [[SP800-185] NIST SP 800-185, "SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash", 2016.],
    [[Wie88] D. Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly 26(4), 1988.],
    [[Zha19] M. Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO 2019.],
  )
  for r in refs {
    par(r)
  }
}
