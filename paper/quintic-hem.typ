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
  text(size: 7.6pt, table(
    columns: cols,
    inset: (x: 3.2pt, y: 3.4pt),
    stroke: none,
    table.hline(stroke: 0.6pt),
    ..cells.pos(),
    table.hline(stroke: 0.6pt),
  ))
}

#let stmt(kind, name, body, src: none) = block(
  width: 100%, inset: (x: 6.5pt, y: 5.5pt), above: 0.85em, below: 0.85em,
  stroke: (left: 1.4pt + luma(70)), fill: luma(246), breakable: true,
)[
  *#kind#if name != none [ (#name)].* #body
  #if src != none {
    v(-0.25em)
    align(right, text(size: 7pt, fill: luma(60))[#src])
  }
]
#let theorem(name, body, src: none) = stmt("Theorem", name, body, src: src)
#let lemma(name, body, src: none) = stmt("Lemma", name, body, src: src)
#let definition(name, body, src: none) = stmt("Definition", name, body, src: src)
#let protocol(name, body, src: none) = stmt("Protocol", name, body, src: src)

#place(top + center, float: true, scope: "parent", clearance: 14pt)[
  #align(center)[
    #set par(justify: false)
    #set text(hyphenate: false)
    #text(size: 15.8pt, weight: "bold")[Quintic Hem: Post-Quantum Signature Aggregation, Committed-Mask Zero-Knowledge WHIR, and Binary Recursive IVC]
    #v(7pt)
    #text(size: 11pt)[ember arlynx]
    #v(2pt)
    #text(size: 8.5pt, fill: luma(60))[`ember@lunar.town`]
  ]
  #v(9pt)
  #block(inset: (x: 16pt))[
    #set par(justify: true, leading: 0.46em)
    *Abstract.* Quintic Hem uses one degree-five Goldilocks challenge field for public signature aggregation, committed-mask zero-knowledge proofs, and binary recursive verification. The field admits no proper intermediate subfield. Its size allows 13 schedules with zero proof-of-work grinding whose rational error budgets are below $2^(-128)$ at $2^64$ oracle queries under the cited proximity and QROM reductions. We give a paper proof of perfect honest-verifier zero knowledge for the interactive masked protocol and identify the algebraic steps mechanized in Lean. Public committees expose a signer bitmap. A recursive root merges overlapping votes and authenticates the signer count in 639,673 bytes independent of depth. An eight-signer public proof verified in 19.49 ms on EPYC-Milan. On a Radeon RX 6750 XT, prover speedups on the measured workloads ranged from 0.88× to 2.19×. The Lean translation of selected Rust checks covers field arithmetic and proof payloads. The Fiat–Shamir transcript, Merkle authentication and outer verifier remain Rust implementation boundaries.

  ]
]

= Introduction

A committee that replaces BLS [BLS01] with independently verifiable post-quantum signatures faces a bandwidth cost. FIPS 204 and FIPS 205 specify single-signer formats [FIPS204, FIPS205]. In the stateful hash-based case [BDH11, HKRY23], 1,500 height-20 Jorts signatures occupy 6.83 MiB and one million occupy 4.78 GB. We prove an execution of the signature verifier with a hash-based interactive oracle proof [BCS16], combining sumcheck [LFKN92] with Reed–Solomon proximity testing [ACFY25].

Making hash-based aggregation simultaneously post-quantum sound at 128 bits in the quantum random oracle model (QROM), zero-knowledge without commitment bloat, and constant-size across recursive committee trees exposes four algebraic and protocol challenges:

1. *The quartic QROM barrier.* Under the multi-round QROM Fiat–Shamir and Merkle state-restoration reduction of Chiesa, Di, Hu, and Zheng [CDHZ25], achieving $< 2^(-128)$ error against $Q = 2^64$ quantum queries requires classical round-by-round (RBR) error below $2^(-264.4)$ alongside 400-bit digests ($6380 Q^3 slash 2^400$). A quartic Goldilocks challenge field ($abs(FF_(p^4)) < 2^256$) cannot reach $2^(-264.4)$ regardless of query count; compensating via Fiat–Shamir proof-of-work grinding lacks a tight multi-round quantum credit, while capacity-regime decoding parameters risk proximity-gap failures [CS25, KKH26].
2. *Zero-knowledge WHIR without companion-table blowup.* Adding zero knowledge to multilinear WHIR via naive extension-limb splitting commits five separate $N$-cell base-field Reed–Solomon tables (where four companion encodings consume $58.9%$ of proof bytes), whereas constrained interleaved-code ZK-IOPPs [CFW26] alter the commitment degree and code family. Overlaying a sparse mask on a shared tree requires a complete proof that out-of-domain (OOD) evaluations, multi-fold affine scalars, and Merkle siblings leak zero witness information.
3. *Overlapping gossip subnets in recursive IVC.* BFT finality networks aggregate overlapping partial signatures within a committee before combining adjacent committees. Fixed-leaf recursion that assumes disjoint signers double-counts gossip overlaps, while naive $2^d$-branch rewinding blows up QROM query budgets exponentially in tree depth $d$.
4. *Padding degrees of freedom and parser-to-field gaps.* In public committee traces padded to power-of-two slot counts, leaving inactive rows unconstrained lets a malicious prover stuff arbitrary auxiliary witnesses across slot boundaries. Likewise, idealized field-level verifiers remain vulnerable if Rust byte-slice decoders accept non-canonical Goldilocks limbs ($>= p$) or miscount Steiner multiproof siblings.

*Contributions.*
- *Pure-quintic field and `HemQuintic128` (`QSAGHQM2`, §2).* We instantiate sumcheck and Johnson-radius affine WHIR [CWYZ26] over $E = FF_(p^5) = FF_p[X] slash (X^5 - 3)$ ($abs(E) > 2^(319.998)$, prime extension degree 5 so Frobenius fixes $FF_p$ with zero intermediate subfields) with zero grinding, pinning all 138 non-S-box columns on inactive padding slots to canonical zero. `QSAGHQM2` supports 50-byte `TurboShake400` [RFC9861] (360,391 B on 3-of-4 sparse Jorts) and 56-byte `Poseidon2Gl24` [GKS23] (381,661 B) Canopies, composed across regions via `HierarchicalHemAggregate` (`QSAGHEM\x04`).
- *Committed-mask zero-knowledge WHIR (`zk-Hem v2`, §3).* Stage 0 commits one packed base-field cube $Z in FF_p^N$ and one folded-domain mask codeword $R$ over $E$, blending $g = P_s + beta_R R$. Five Frobenius-disjoint OOD evaluations blind all $5s$ fold scalars through an exact $5 times 5$ Vandermonde bijection (Lemmas 3.1–3.4 and Theorem 3.1), while 32-byte per-tree nonces and per-leaf salts remove table-size birthday loss. Applying Dao–Kominers–Thaler ([DKT26], Theorem 5.12) line proximity bounds unlocks tables of $2^16 dots 2^28$ cells at 267/266 Stage-0 queries (rational QROM budget $< 2^(-128)$), extended with jointly masked LogUp [Hab22] and collaborative proving for ownership claims over authenticated $FF_(p^5)$ shares (`QSAGZKS2`). The migration CLI also supports Zcash NU7 `ZIP-2005` Ironwood.
- *Overlapping-bitfield binary recursive IVC (`QSAGIVC1`, §4).* A fixed 639,673 B root authenticates a contiguous interval of committees. Within a committee, union of the 256-bit signer masks deduplicates repeated votes. Joining adjacent intervals requires quorum completion and checked addition of signer counts. Section 4 gives separate budgets for extracting a whole tree and following one path.
- *Extracted payload checks and measured costs (§5–§6).* The Charon/Aeneas translation of `qsag-whir-verified` contains 86 definitions [HP22]. Section 5 identifies the checks the public verifier calls, the enclosing Rust code and the coverage of the GPU model [MU21]. Section 6 compares CPU and Vulkan proof times and distinguishes measured proof sizes from bandwidth projections.

*Related work.* LaBRADOR [BS23] achieves compact R1CS proofs under Module-SIS; Quintic Hem relies solely on hash functions in the ROM/QROM [BBBV97, AHU19, BCS16, CDHZ25]. Counterexamples limit some conjectured Reed–Solomon proximity gaps [CS25, KKH26]. We use affine combiners [CWYZ26] and a mutual correlated agreement bound inside the Johnson radius [DKT26]. Cryptanalysis of specific Poseidon configurations [MRG26, BTA26] also makes the choice of permutation parameters material. The public and recursive protocols use width-12 or width-24 Poseidon2 [GKS23]. The hiding profiles use 400-bit digests from cSHAKE256 [SP800-185] or TurboSHAKE256 [RFC9861]. Chiesa, Fenzi, and Weissenberg [CFW26] construct ZK-IOPPs via constrained interleaved encodings; Feneuil, Provin, and Rivain [FPR26] establish that base-field masks with fewer than $[E : FF_p]$ coordinates cannot hide an $E$-evaluation, matching Lemma 3.2 from below. PRAWNS [BBD+26] studies threshold hash signatures; our companion paper covers symmetric Cut-the-Hash threshold custody, whose `JortsPoseidon2` outputs feed `QSAGHQM2` and `QSAGIVC1` under the same validator public key. Post-quantum HD wallet seed-provenance bounds follow ZKPoSP [BPRR26]. Distributed quorum signatures [KSW26] and QUASI [IM26] target live voting; Quintic Hem serves finality and state checkpoints.

= Pure-Quintic Public Committee Aggregation (`QSAGHQM2`)

== Algebraic geometry of $FF_(p^5)$ and QROM sizing

Let $p = 2^64 - 2^32 + 1$ be the Goldilocks prime. Since $p equiv 1 mod 5$ and $3^((p-1) slash 5) mod p = "1,041,288,259,238,279,555" =: zeta_5 != 1$, $X^5 - 3$ is irreducible over $FF_p$ by Serret's criterion, defining the pure quintic challenge field
$ E = FF_(p^5) = FF_p[X] slash (X^5 - 3), quad abs(E) = p^5 > 2^(319.998). $
Every element has a unique canonical representation $(c_0, dots, c_4) in [0, p)^5$ (40 bytes little-endian) in the power basis $[1, X, X^2, X^3, X^4]$. Because $X^p = 3^((p-1) slash 5) X = zeta_5 X$, the Frobenius automorphism $sigma(u) = u^p$ acts diagonally as $sigma(sum_(i=0)^4 c_i X^i) = sum_(i=0)^4 c_i zeta_5^i X^i$ at a cost of four base-field multiplications (`fp5_frobenius`). Crucially, because $[E : FF_p] = 5$ is *prime*, $E$ contains zero proper intermediate subfields: $sigma$ fixes $FF_p$ pointwise, and every $z in E without FF_p$ has five distinct Frobenius conjugates ${sigma^i (z)}_(i=0)^4$ and minimal polynomial of degree 5 over $FF_p$.

Under the [CDHZ25] QROM transformation (Theorems 6.10, 8.3, and 11.3) for $k < 2^9$ interactive rounds and $sigma$-bit Merkle digests at $Q$ quantum oracle queries, knowledge-extraction failure is estimated for the 400-bit sizing envelope ($Q >= 2^24$) by
$ epsilon_"QROM" (Q) <= 2^(0.023) (320 (Q + k + 1)(Q + k) epsilon_"RBR" + 6380 Q^3 slash 2^sigma). $
At $Q = 2^64$ we choose $sigma = 400$ ($6380 dot 2^192 slash 2^400 < 2^(-195.3)$) and target $epsilon_"RBR" <= 2^(-264.5)$. Over $FF_(p^4)$ ($abs(FF_(p^4)) < 2^256$), a single degree-9 sumcheck round already incurs $9 slash abs(FF_(p^4)) > 2^(-252.9)$, missing the target by $> 11.5$ bits. Moving to $FF_(p^5)$ pushes algebraic round errors to $<= d l_0 slash (p^5 - 1) < 2^(-299)$, making Stage-0 fiber sampling the sole binding round at $> 264.5$ bits with *zero* proof-of-work grinding—so the sizing formula charges no grinding credit.

== 256-column trace and inactive-slot zero pinning

`HemQuintic128` (`QSAGHQM2`) encodes verification of stateful `JortsPoseidon2` (512 rows/signer for any tree height $h in [6, 20]$) or stateless `CorduroyPoseidon2` (8,192 rows/signer) into a base-field trace of $C = 256$ columns (`trace.rs`): 12 Poseidon2 state inputs (`COL_ST_IN[0..12]`), 118 intermediate $x^7$ S-box outputs (`COL_SBOX_OUT[12..130]`) of a width-12 Poseidon2 permutation [GKS23], 44 previous-row and 44 next-row carried state limbs (`COL_PREV_STATE`, `COL_NEXT_STATE`), and 38 opcode-specific auxiliary limbs (`COL_AUX[218..256]`). Keeping the witness over $FF_p$ avoids a $5 times$ commitment footprint while drawing sumcheck and WHIR challenges from $E$.

For $k_"act"$ active signers indicated by a canonical `SignerBitmap`, the trace allocates $"slots" = 2^(ceil(log_2 k_"act"))$ signer blocks (`cells` $= "slots" times "rows_per_signer" times 256 = 2^ell$). If inactive slots $[k_"act", "slots")$ were merely gated off by zeroing opcode selectors, a cheating prover could inject non-canonical `COL_AUX` values, non-zero carried states, or non-zero `COL_ST_IN` vectors paired with valid Poseidon2 trajectories.

In `hem_quintic/rows.rs`, let $"active"(r_"slot") = sum_(i < k_"act") "eq"(r_"slot", i)$ and $"INACTIVE" = 1 - "active"(r_"slot")$. During the degree-8 row sumcheck [LFKN92], the verifier adds the constraint batch
$ "eq"(tau, r_"row") dot "INACTIVE"(r_"slot") dot sum_(m=0)^(137) gamma^(M + m) C_(pi(m)) (r_"row"), $
where $pi$ enumerates all $12 + 126 = 138$ non-S-box columns (`COL_ST_IN` $union$ `COL_PREV_STATE..256`). Because each term has degree $1 + 1 + 1 = 3 <= 8$ in the active sumcheck variable, zero round overhead is incurred. The unbatched relation requires every inactive non-S-box column to vanish. The Group-A Poseidon2 equations then determine the other 118 columns. With randomized batching, a fixed nonzero residual can pass at a root of the challenge polynomial. The Rust regression `tooth_inactive_slot_noncanonical_witness_rejected_by_prover_and_verifier` tests rejection of a changed padding witness.

== Canopy profiles, soundness, and regional composition

After the row sumcheck reduces trace validity to 256 column evaluations at $r_x$, an 8-variable column fold reduces them to one multilinear evaluation claim on $Z$, combined with five OOD evaluations $hat(Z)(omega_1), dots, hat(Z)(omega_5)$ and folded across 3 or 4 WHIR stages via the affine combiner [CWYZ26]:
$ P_(i+1)(Y) = G(Y) + (alpha_i + beta_i Y)(F(Y) + theta_i G(Y)), $
where $F, G$ are the even and odd parts of $P_i$. `HemQuinticProfile` supports two unmasked commitment Canopies (@publicprofiles): `TurboShake400` (tag 1: 50-byte / 400-bit 12-round TurboSHAKE256 [RFC9861]) and `Poseidon2Gl24` (tag 2: 7 canonical Goldilocks limbs = 56 bytes / $p^7 approx 2^(448)$ via width-24 Poseidon2 Jive compression [GKS23]), initialized from a static TurboSHAKE256 midstate (`QSAG.HEM.QUINTIC.FS/v2`) capped at `FS_CALL_LIMIT = 4096` calls.

#figure(tbl((1.1fr, 1.55fr, 0.85fr, 0.9fr),
  [Profile (tag)], [Canopy hash & digest], [Bits], [3-of-4 bytes], table.hline(),
  [`TurboShake400` (`1`)], [TurboSHAKE256, 50 B], [400], [360,391],
  [`Poseidon2Gl24` (`2`)], [Poseidon2-GL-w24, 7 limbs], [$approx 448$], [381,661],
), caption: [Serialized `QSAGHQM2` proofs for the pinned 4-validator Jorts committee with active signers $\{0, 2, 3\}$ on a shared message.]) <publicprofiles>

#theorem("public committee error budget", src: [`PublicHemQuintic128.lean`, `publicHemQuintic_budget_lt_128`])[
  For either Canopy, $16 <= ell <= 28$ and $Q <= 2^64$, Lean proves the rational inequality $"publicHemError"("profile", ell, Q) < 2^(-128)$. Its terms transcribe the round and Merkle bounds of [CWYZ26, DKT26, CDHZ25]. This is a `*_budget_lt_128` result. Its statement quantifies over table size, profile and query budget.
]

At the protocol level, `whir_exec_closed_qrom_soundness` and its succinct variants reduce acceptance of a false claim to bad round or commitment events. Applying the deployed-schedule game bound requires a `WhirScheduleCert` for the verifier environment, root consistency and a bound on Merkle collisions. Evaluating the rational budget supplies none of those premises. In particular, the arithmetic theorem above has no prover, verifier or acceptance event in its conclusion.

For multi-region finality, `HierarchicalHemAggregate` (`QSAGHEM\x04`) bundles per-committee `QSAGHQM2` proofs bound to a 32-byte `PreparedPolicyRegistry` root (`hierarchical_hem_message` domain-separating registry root, committee ID, cluster tag, and epoch floor), checking committee policies and overflow-free 64-bit quorum totals via MIR-verified `checked_quorum_sum`.

= Committed-Mask Zero-Knowledge WHIR (`zk-Hem v2`)

== Single-cube packed layout and folded-domain mask line

`zk-Hem v2` (`QSAGZKH2` single-prover, `QSAGZKS2` collaborative; `CshakeJohnson400` tag 16 [SP800-185] and `TurboShakeJohnson400` tag 17 [RFC9861]) proves satisfaction of a degree-9/degree-2 R1CS-with-$x^7$ relation over $2^n$ rows ($n >= 5$) and `num_vars` variables ($>= 16$, with constant $z_0 = 1$, `num_public <= num_vars - 16`, and 15 secret corner pads in three 5-limb groups occupying 24 reserved top rows).

*Packed layout.* Instead of committing five base-field tables, `params::Layout` packs everything into a single cube $Z in FF_p^N$ ($N = 2^ell$, $ell in [16, 28]$):
#align(center)[Variables · padding · row masks · column masks · padding · blinders]
where `var_cells` aligns `num_vars` to $2^(max(4, k-8))$ ($k = ceil(log_2 "num_vars")$), row masks hold $5 n dot 16$ cells, column masks hold $5 k dot 4$ cells, and the top $b = 2^s (q_0 + 25)$ cells are uniform base-field blinders ($s = "step_vars"_0 <= 6$, so $2^s | b$ and $2^s | (N - b)$).

*Commitment and scalar mask line.* Let $c in FF_p^N$ be the multilinear monomial coefficients of $Z$ via the Möbius transform, with Reed–Solomon codeword $hat(Z)(x) = sum_(i < N) c_i x^i$ on coset $D_0$ ($abs(D_0) = 4 N$). Simultaneously, the prover samples a uniform mask polynomial $R in E[Y]$ of degree $<= N slash 2^s + 1$, evaluated on the folded domain $D' = {x^(2^s) : x in D_0}$ ($4 N slash 2^s$ fibers). Stage 0 samples a fresh 32-byte per-tree `tree_nonce`, and hashes each fiber leaf $g in [0, abs(D'))$ with a fresh 32-byte per-leaf salt, the $2^s$ base symbols of $hat(Z)$ over $y_g in D'$, and the single extension symbol $hat(R)(y_g) in E$.

After the masked degree-9 row sumcheck, masked row-value disclosures $(A z, B z, C z)(r_x)$, and masked degree-2 column sumcheck on $Z_"var"$ (decomposed into $<= k - "var_align" + 1$ dyadic tensor terms reading zero cells $>= "var_cells"$ outside the sumcheck masks), the verifier draws five OOD points $omega_1, dots, omega_5 in E$, receives $a_j = hat(Z)(omega_j)$, batches them with weights $w_1, dots, w_5$ into $chevron.l c, K + sum_(j=1)^5 w_j e_(omega_j) chevron.r = V + sum_(j=1)^5 w_j a_j$ (keeping exact geometric continuation on overflow coefficients for point kernels $e_x$), runs $s$ Stage-0 affine folds to obtain $P_s$ with kernel $v_s$ and claim $sigma_s$, receives $mu = chevron.l R, v_s chevron.r$, draws nonzero $beta_R in E^times$, and commits Stage 1 to the *scalar mask line* $g = P_s + beta_R R$ (avoiding the witness-dependent kernel rank leak that would arise from an affine blend $P_s + (a + b Y) R$).

The honest prover tests a public verifier-coin predicate *Good* before each dependent round (aborting with `MaskRankDeficient` if violated, $Pr[not "Good"] <= 15 slash p + (5 dot 2^s p + 50 dot 2^s + 5 + 6 s + 3 n) slash abs(E) < 2^(-59)$): (G1) the five equality weights $"eq"((r_(x,0), r_(x,1), r_(x,2)), c)$ ($c = 0..4$) form an $FF_p$-basis of $E$ and the three corner factors are nonzero; (G2) $z_j = omega_j^(2^s) in E without FF_p$ are pairwise Frobenius non-conjugate; and (G3) $w_j != 0$, $phi_i != 0$, and $1 + phi_i omega_j^(2^i) != 0$ for all $i < s, j <= 5$.

== Mathematical proofs of zero knowledge (Lemmas 3.1–3.4 & Theorem 3.1)

Theorem 3.1 is a paper proof for the interactive IOP. Lean mechanizes the algebraic mask-bijection and rank results used in Lemmas 3.2–3.4. In Lemma 3.2 the mechanized result is the point-interpolation form. The residue-class argument and the composition of the simulator appear below.

#stmt("Lemma 3.1", "top-cell monomial triangularity", src: [`Lemma V2.1`])[
  A hypercube table supported on the top $b$ indices $[N - b, N)$ has multilinear monomial coefficients supported bijectively on $[N - b, N)$. Hence $hat(Z)(x) = W(x) + x^(N - b) B(x)$, where $W$ depends only on cells below $N - b$ and $B in FF_p[x]$ is uniform of degree $< b$, independent of $W$.
]

#stmt("Lemma 3.2", "Frobenius CRT blinding count", src: [`v2_blinding_count`; lower bound [FPR26]])[
  Let $Q subset FF_p^times$ be distinct opened base-field points and $z_1, dots, z_t in E without FF_p$ be pairwise non-conjugate under Frobenius $sigma$. If $b >= abs(Q) + 5 t dot 2^s$, the $FF_p$-linear evaluation-and-residue map
  $ B &|-> ( (B(q))_(q in Q), (x^(N - b) B mod (x^(2^s) - z_j))_(j=1..t) ) \
      &in FF_p^(abs(Q)) times product_(j=1)^t E[x] slash (x^(2^s) - z_j) $
  is surjective, so its output is uniform for uniform $B$ of degree $< b$.
]

_Proof._ Define $m_j (x) = product_(i=0)^4 (x^(2^s) - sigma^i (z_j))$. Since $sigma$ permutes the five factors, $m_j$ has coefficients fixed by $sigma$, so $m_j in FF_p[x]$ of degree $5 dot 2^s$. Because $z_j in.not FF_p$ and $[E : FF_p] = 5$ is prime, the five conjugates $sigma^i (z_j)$ are pairwise distinct; thus an $f in FF_p[x]$ divisible by $x^(2^s) - z_j$ in $E[x]$ is divisible by all five coprime conjugate factors, hence by $m_j$. Comparing $FF_p$-dimensions ($5 dot 2^s$ on both sides), $FF_p[x] slash m_j -> E[x] slash (x^(2^s) - z_j)$ is an isomorphism. Across $q in Q$ and $j in [1, t]$, the moduli $x - q$ and $m_j$ are pairwise coprime in $FF_p[x]$ because roots of $m_j$ have $2^s$-th powers $sigma^i (z_j) in.not FF_p$ (distinct across $(i, j)$), whereas $q^(2^s) in FF_p$. All are coprime to $x$ since $q != 0, z_j != 0$, so multiplication by $x^(N-b)$ is a unit in every residue factor. By the Chinese Remainder Theorem, every residue tuple is hit by a polynomial of degree $< abs(Q) + 5 t dot 2^s <= b$. $square$

#stmt("Lemma 3.3", "fold-scalar Vandermonde bijection", src: [`v2_fold_scalar_matrix_bijective`])[
  Fix $j in {1,dots,5}$ and write $A = E[x] slash (x^(2^s) - z_j)$, $T_j = hat(Z) mod (x^(2^s) - z_j)$, and $x_(j,i) = omega_j^(2^i)$.
  1. Let $u_i = P_i (x_(j,i))$ ($u_0 = a_j$), $F_i, G_i$ be the even and odd parts of $P_i$ evaluated at $x_(j,i)^2$, and $w_(j,0) = w_j$, $w_(j,i+1) = w_(j,i)(1 + phi_i x_(j,i))$. Then $u_i = F_i + x_(j,i) G_i$, $u_(i+1) = G_i + (alpha_i + beta_i x_(j,i)^2)(F_i + theta_i G_i)$, and point $j$'s contribution to the five fold-$i$ scalars is $E$-linear in $T_j$:
     $ &(sigma_"even", tau_01, tau_10, c_F, c_G)_j \
       &= w_(j,i) (F_i, x_(j,i) F_i, G_i, (1 + phi_i x_(j,i)) x_(j,i)^2 F_i, (1 + phi_i x_(j,i)) x_(j,i)^2 G_i). $
  2. Whenever $omega_j != 0$, the $s + 1$ linear functionals $(u_0, F_0, dots, F_(s-1))$ on $A$ ($dim_E A = 2^s$) are $E$-linearly independent.
  3. Under (G2) and (G3), for every fold $i < s$ and fixed $(u_i)_(j=1..5)$, the map from $(F_i)_(j=1..5) in E^5$ to $sum_(j=1)^5 (sigma_"even", tau_01, tau_10, c_F, c_G)_j$ is an affine bijection of $E^5$.
]

_Proof._ (1) Each affine fold is a ring operation on even/odd parts compatible with reduction modulo $X^(2^(s-i)) - z_j$, and evaluation at $x_(j,i)$ factors through that quotient since $x_(j,i)^(2^(s-i)) = z_j$; exact continuation on overflow coefficients makes inner products with point kernels pure evaluations. (2) Induct downward from $i = s$, where $(u_s)$ is the identity on $A_s = E[X] slash (X - z_j) tilde.equiv E$. For $i -> i+1$, write $(F, G) in A_(i+1)^2$ and $Phi(F, G) = G + (alpha_i + beta_i Y)(F + theta_i G)$. $Phi$ surjects onto $A_(i+1)$ (set $F = -theta_i G$), so pullbacks of $u_(i+1), F_(i+1), dots, F_(s-1)$ are independent and vanish on $ker Phi$. Meanwhile $u_i, F_i$ span the two-dimensional evaluation space $(F(x_(j,i)^2), G(x_(j,i)^2))$ ($x_(j,i) != 0$), which contains $u_(i+1) compose Phi$ but is not contained in $(ker Phi)^perp$ since $(1 + theta_i (alpha_i + beta_i Y), -(alpha_i + beta_i Y)) in ker Phi$ evaluates to $(1 + theta_i e, -e) != (0, 0)$ for $e = alpha_i + beta_i x_(j,i)^2$. Hence the space meets the pullback span strictly in the line $E dot (u_(i+1) compose Phi)$, and replacing $u_(i+1) compose Phi$ by $(u_i, F_i)$ preserves independence. (3) Substituting $G_i = (u_i - F_i) slash x_(j,i)$, the homogeneous linear part has column $j$ equal to $w_(j,i) (1, x, -x^(-1), (1 + phi_i x) x^2, -(1 + phi_i x) x)^top$ at $x = x_(j,i)$. Invertible row operations at $phi_i != 0$ transform the rows to $(x^(-1), 1, x, x^2, x^3)^top$, factoring the matrix as a $5 times 5$ Vandermonde matrix on distinct nonzero points $x_(1,i), dots, x_(5,i)$ (by (G2)) times $"diag"(w_(j,i) slash x_(j,i))$ (invertible by (G3)). $square$

#stmt("Lemma 3.4", "scalar mask-line bijection", src: [`v2_mask_line_perfectly_simulated`, `v2_mask_line_view_perfectly_simulated`])[
  For any $beta_R in E^times$ and $P_s$ of degree $<= N slash 2^s + 1$, $R |-> g = P_s + beta_R R$ is a bijection on $E^(N slash 2^s + 2)$ with inverse $R = (g - P_s) slash beta_R$, uniquely determining both $mu = (chevron.l g, v_s chevron.r - sigma_s) slash beta_R$ and every opened symbol $hat(R)(y) = (g(y) - P_s (y)) slash beta_R$.
]

#stmt("Theorem 3.1", "Perfect HVZK", src: [Paper proof. Algebraic mask-bijection and rank results of Lemmas 3.2–3.4 mechanized in Lean.])[
  For every satisfying witness and independent uniform prover randomness, the interactive oracle proof of §3.1 is perfect honest-verifier zero-knowledge (reproducing exact abort prefixes outside *Good*).
]

_Proof._ Given verifier coins (in *Good*; otherwise halt at the exact public coin check where the prover aborts), the simulator (1) samples front messages (`G1`, degree-9 row polynomials on the affine space fixed by the endpoint sum, `(Az, Bz, Cz)(rx)` in $E^3$, `G2`, and degree-2 column polynomials) uniformly, fixing $(K, V)$; and (2) constructs a base-field lower table $W'$ satisfying $chevron.l c(W', 0), K chevron.r = V$, samples uniform top blinders, $R$, and salts, and runs the honest prover from round 7 on $Z' = (W', "blinders")$.

In the real execution, row-mask coefficients $a_(i, h)$ ($h >= 1$) contribute $rho_1 2^(n-i-1) a_(i, h)$ independently to non-constant coefficients, while `G1` fixes one linear combination of constant terms; on (G1), the three 5-limb corner pad groups map bijectively to $(R_0, R_1, R_2) in E^3$ with invertible disclosure matrix determinant $k_0 k_1 k_2 != 0$, making `(Az, Bz, Cz)(rx)` conditionally uniform, and likewise for the column mask. A surrogate $W'$ always exists because varying the 5 limbs of the constant, linear, or quadratic block of row-mask round 0 scales $chevron.l c, K chevron.r$ by $2^n + lambda^2$, $2^(n-1) + lambda^2 r_(x,0)$, or $2^(n-1) + lambda^2 r_(x,0)^2$, which cannot all vanish ($lambda^2 = -2^n$ and $r_(x,0) = 1 slash 2$ force the third to $2^(n-2) != 0$).

Conditioned on all cells below $N - b$, the statement kernel $K$ vanishes on $[N - b, N)$ ($2^s | (N - b)$), and each fold halves the blinder support start $L_i = (N - b) slash 2^i$ while preserving vanishing of the folded tensor kernel on $[L_i slash 2, infinity)$ including shifts by $Y$ and overflow slots. Thus blinders enter $(a, S_0, dots, S_(s-1))$ exclusively through the five OOD point kernels. By Lemmas 3.1 and 3.2 at $t = 5$ ($b = abs(Q) + 25 dot 2^s$), the opened symbols $O$ and residue tuples $(T_j)_(j=1..5)$ are jointly uniform and independent of $W$. By Lemma 3.3(1)–(3), $(u_0, F_0, dots, F_(s-1))_(j=1..5)$ maps to $(a, S_0, dots, S_(s-1))$ via a block-triangular affine map with bijective $E^5$ diagonal blocks, making $(a, S, O)$ uniform. Finally, $g = P_s + beta_R R$ is uniform and independent of $(a, S, O)$ by Lemma 3.4, determining $mu$, opened $hat(R)$ symbols, and all Stages $>= 1$. $square$

This argument uses only the projected fold scalars and queried symbols in the specified view. Revealing complete polynomial remainders changes the view and can expose coefficients. The noninteractive proof also requires commitment hiding and Fiat–Shamir simulation. Perfect HVZK here is a statement about the interactive honest-verifier experiment with independent uniform masks.

== [DKT26] QROM soundness, per-tree nonces, and LogUp

*[DKT26] Theorem 5.12 mask-line soundness.* Under [BCGM25] Lemma 9.3, the exceptional set of challenges $beta_R in E^times$ grew as $(m + 1 slash 2)^7 abs(D')^2 slash rho'^(3 slash 2)$, rejecting tables above $2^24$ cells and requiring $281..342$ Stage-0 queries. Replacing that bound with Dao, Kominers, and Thaler [DKT26] Theorem 5.12 (characteristic-free mutual correlated agreement inside the Johnson radius at $d = 1$ on $abs(D') = 4 N slash 2^s$ fibers of degree $D = N slash 2^s + 1$) reduces the bad-challenge count to
$ B_"cf" = ceil(((2 m + 1)^3 abs(D')^2) / (3 D)), $
improving the proximity-slack exponent from 7 to 3 and scaling linearly in $abs(D')$ at fixed rate. Optimizing $m in [3, 512]$ makes the mask-line round non-binding across all 13 table sizes $2^16 .. 2^28$, dropping Stage-0 fiber queries to *267* ($2^16 .. 2^23$) and *266* ($2^24 .. 2^28$) (@v2bounds), with the resulting rational error sum checked in `ZkHemV2PackedFiberCerts.lean` (`zkHemV2_packed_all13_budget_lt_128`). Beyond the Johnson radius, [DKT26] Proposition 5.10 ($L <= 2$, $delta = 2 slash 3 - k slash (3n) - 1 slash eta_"inv"$) gives an exploratory $209..220$-query estimate in the Rust calculator `dkt26_beyond_johnson_first_order`. The deployed schedules in @v2bounds use the Johnson regime.

#figure(tbl((1.25fr, 0.55fr, 1.15fr, 0.45fr, 0.85fr, 0.85fr, 0.9fr),
  [Rows, vars], [Cells], [Queries / stage], [$m$], [RBR bits], [QROM lvl], [Max B], table.hline(),
  [$2^16$, 40,000], [$2^16$], [267, 136, 92], [54], [265.230], [128.276], [288,624],
  [$2^17$, 82,000], [$2^17$], [267, 136, 92], [54], [265.183], [128.253], [347,280],
  [$2^20$, $2^20$], [$2^21$], [267, 136, 92], [145], [265.009], [128.192], [500,602],
  [$2^21$, 1,088,721], [$2^21$], [267, 136, 92], [145], [265.009], [128.192], [501,122],
  [$2^22$, $2^22$], [$2^23$], [267, 136, 92, 70], [271], [265.374], [128.317], [607,936],
  [$2^23$, $2^23$], [$2^24$], [266, 136, 92, 70], [364], [264.514], [128.001], [640,642],
  [$2^25$, $2^25$], [$2^26$], [266, 136, 92, 70], [511], [264.634], [128.048], [791,962],
  [$2^27$, $2^27$], [$2^28$], [266, 136, 92, 70], [512], [264.627], [128.050], [1,027,882],
), caption: [`zk-Hem v2` certified [DKT26] schedules (`bounds.rs`). Classical work level is 198.999 bits throughout; QROM error at $Q = 2^64$ ranges from $2^(-128.168)$ to $2^(-129.028)$.]) <v2bounds>

*Per-tree nonces and O2H leaf hiding.* Absorbing a fresh 256-bit `tree_nonce` alongside leaf index $g$ and a 256-bit leaf salt into every Stage-0 leaf ensures two proofs share a leaf domain prefix iff their `tree_nonce`s collide ($binom(P, 2) slash 2^256$, independent of $abs(D')$). By semi-classical one-way-to-hiding [AHU19], unopened Merkle preimages across $P$ proofs are hidden within $Q P slash 2^256 + binom(P, 2) slash 2^256$ classically and $2 Q sqrt(P slash 2^256) + binom(P, 2) slash 2^256$ against $Q$ quantum queries ($2^(-63)$ for one proof at $Q = 2^64$).

*Jointly masked LogUp.* Relations with table lookups [Hab22] (`LookupV2Proof`, `ZkHemV2ComposedZkAndCerts.lean`) commit a second salted Stage-0 helper cube $(H, R_H)$ holding the five extension limbs of $h_i = n_i slash (alpha - v_i)$ (after checking nonzero batch denominator product to avoid witness-dependent pole timing), degree-4 lookup sumcheck masks, an 8-entry corner supplying rank-15 base-field masking across joint disclosures, and `blind_cells_for` top blinders, incurring RBR errors $((w-1) L T l_0, (L + 2T + 1) l_0, max(d, 5) l_0 l'_0) slash abs(E)$.

== Anchored 9-triple Toom-3 collaborative proving & applications

In `ZkHemV2SplitProof` (`QSAGZKS2`), $c in [1, 255]$ custodians prove knowledge of a shared witness without reconstructing it: each custodian $p$ commits an independent salted Stage-0 share tree $(Z^((p)), R^((p)))$ with its own `tree_nonce`, so $Z = sum_p Z^((p))$ and $R = sum_p R^((p))$ remain statistically hidden whenever at least one custodian is honest.

To evaluate `zk-Hem v2` witness synthesis and sumcheck polynomials over MAC-authenticated additive shares in $E = FF_(p^5)$, `qsag_migrate::hem::collab` uses *nine base-field triples per quintic product* (`Engine::mul_ext`): degree-4 operand polynomials over $FF_p$ are evaluated locally at the nine points ${0, plus.minus 1, plus.minus 2, plus.minus 3, 4, infinity}$, multiplied in a single batched base-field Beaver round (schoolbook multiplication of two five-limb elements takes 25 base products), interpolated over $FF_p$, and reduced modulo $X^5 - 3$. Before the first online proving round, `Engine::new_anchored` hashes `tape_id = cSHAKE256("QSAG.COLLAB.TAPE.ID/v1", ...)` and advances both the in-process burned set and an `ExternalMonotoneAnchor` so restoring a consumed tape cannot replay Beaver triples or MAC masks while the anchor retains its state. Over TCP (`qsag migrate collab`), custodians run dealerless OT preprocessing and split proving across pairwise forward-secret `X25519 + ML-KEM-768` [FIPS203] channels.

Applications built on `zk-Hem v2` include: (1) *19 multi-chain key-migration statements* (`qsag-migrate`: Bitcoin P2PKH/Taproot, Ethereum EOA/`BLS12-381`, Ed25519/`SLIP-0010`, `BIP-32` respecting extended-public-key export bounds [BPRR26], and Zcash NU7 `ZIP-2005` Ironwood shielded note recovery `QSHEMZN2`, Orchard `QSHEMZA2`, Sapling `QSHEMZS2`, and `ZIP-2007` Transparent `QSHEMZT2`, gated by an append-only `NullifierRegistry`); (2) *selective-disclosure `BlindVC` presentations*; (3) *threshold-hiding policy multisignatures*; and (4) *unlinkable `QSAGCAU1` capabilities* proving non-revocation via canonical 256-bit limb strict-inequality checks $r_"lo" < "id" < r_"hi"$ on adjacent sorted Merkle leaves at bit-checked indices $(i, i+1)$.

= Overlapping-Bitfield Binary Recursive IVC (`QSAGIVC1`)

== Fixed-geometry two-child PCD and bitfield union

While `HierarchicalHemAggregate` scales linearly with the number of regional committees $S$, `prove_ivc_tree` (`crates/qsag-agg/src/zk_hem/recursive_ivc/`) compresses an arbitrary contiguous run of Jorts committees into a single *depth-independent 639,673 B* root proof (`SuccinctIvcProof`, wire prefix `QSAGIVC1\x00`, `ivcRootProof_byteSize_independent_of_depth`).

#protocol("overlapping-bitfield binary recursive step", src: [`IvcTreeStepRelation`, `tree::split`, `FixedPathWhirW24`])[
  Each `IvcSubtreeStatement` encodes 31 public 32-bit words, including registry root, half-open committee interval $[a,b)$, `total_signers`, threshold, 256-bit bitmap and message digest. The matrix accumulator adds seven limbs. The accessor `completed_shards()` returns the interval width $b-a$. A single-committee interval has width one even when its bitmap is still below threshold.
  1. _Jorts leaf._ The circuit authenticates the committee policy against the registry root and verifies the active Jorts signatures against member positions on a common message. The default geometry provisions 64 signature slots and 256 bitmap positions. At a leaf, `total_signers` equals the bitmap population.
  2. _Merge._ Children in the same single committee must agree on the threshold. For each bitmap position, the circuit enforces $B_j = l_j + r_j - l_j r_j$ and counts the union. For adjacent intervals it requires the left endpoint range to end where the right starts. Each single committee leaving bitmap form must meet threshold, enforced by a 32-bit range check on the signer surplus. The parent clears its bitmap and threshold and adds the two signer counts with checked 64-bit arithmetic. The verifier checks completion at the root.

  3. _In-circuit WHIR & matrix folding._ Verifies both children's `FixedPathWhirW24` openings (`IvcStepConfig::dkt26(23)`, routing distinct queries via a partial Fisher–Yates switching network) and their 23-round row and column sumchecks over $FF_(p^5)$, then folds the four child R1CS matrix claims into one parent accumulator via a 49-round degree-2 sumcheck. `verify_ivc_tree` discharges the root accumulator directly against the two compiled matrices.
]

== Multi-depth QROM extraction scope

A whole-tree extractor pays for every node. Following a claim about one committee visits only one node per depth. Lean formalizes the reductions in a recorded-query model and separately bounds their error terms in `MultiDepthRecursiveQromExtractor.lean` and `RecursiveIvcPublicRowQrom.lean`.

- _Whole tree._ For the three-stage margin schedule at $2^20$ cells (304/148/100 queries), the numerical budget is below $2^(-128)$ for $d <= 16$, $Q <= 2^64$. The serialized schedule is `dkt26(23)` (267/136/92/70). With 95 public sumcheck rounds per node, its whole-tree budget is below $2^(-128)$ at $d <= 7$, $Q <= 2^64$, or at $d <= 20$, $Q <= 2^57$ (`treeBudget_lt_128`). At $d=20$, $Q=2^64$ the sum lies between $2^(-116)$ and $2^(-115)$.
- _Single path._ For $d <= 64$ and $Q <= 2^64$, the $d+1$ selected nodes have combined budget below $2^(-130)$ (`spineBudget_lt_130`). Given acceptance and collision freedom in the model, `overclaimed_spine_euf_cma_forgery` locates a bad extraction step or a signed overclaim. Identifying the roster with enrolled keys gives a signature on behalf of a nonparticipant.

The Lean overclaim predicate compares the sum of authenticated bitmap weights with modeled participation. Applying it to Rust requires relating that sum to `total_signers`, including merges of overlapping bitmaps. Recovery at adaptively selected nodes must also imply a recorded commitment query. The path bound treats width-24 Poseidon2 as an ideal oracle. Internal recursive sumchecks are unmasked. Their public linear evaluations fall outside Theorem 3.1.

= Verification from wire bytes to field claims

The `no_std` crate `qsag-whir-verified` has 86 extracted definitions in `Funs.lean`, including functions, constants and generated loop bodies. Its Lean translation covers `Fp5` arithmetic and Frobenius, canonical limb and header decoding, and bounded proof payload checks. `compute_steiner_multiproof_siblings` agrees with `Qsag.steinerSiblingCount`. This fixes how many siblings an opening must carry for a given query set.

On the live public path, `hem_quintic/rows.rs` calls `verify_qsaghqm2_row_rounds_at` to replay degree-eight row messages. In `hem_quintic/whir.rs`, `verify_qsaghqm2_cwyz_folds_at` and `verify_qsaghqm2_multiproof_and_rounds` check fold and opening payloads against supplied challenges and bounds. These results concern specified slices and field operations. Rust selects the profile and statement, runs the Fiat–Shamir transcript, samples queries, computes and authenticates Merkle roots, and combines all checks into the final verdict. Extraction uses the modeled Aeneas prelude. Compiling the crate and linking this loop introduce additional trust boundaries.

The Lean Poseidon2-12 shader entry theorem ranges over input states in a fixed execution environment at invocation zero. The SIMT reasoning has scheduling and race-freedom premises. Multiple device invocations and the other pipelines have separate hardware tests (§6).

= Evaluation and Scaling

CPU benchmarks were measured on an AMD EPYC-Milan reference server (16 cores / 32 threads, Linux 6.12, `rustc 1.99.1`, `opt-level = 3`, `lto = "thin"`, `codegen-units = 1`, 16 GiB cap). GPU primitive benchmarks ran on an AMD Radeon RX 6750 XT (Mesa RADV Vulkan).

== Public committee and regional hierarchy performance

#figure(tbl((1.7fr, .93fr, .8fr, 1.15fr),
  [Workload], [Wire B], [Prove s], [Verify ms], table.hline(),
  [8 Jorts], [392,971], [4.40], [19.49],
  [16 Jorts + 2 Corduroy], [978,020], [23.87], [21.58 / 34.52],
  [4 × 32 Jorts], [2,072,874], [61.00], [32.42 / 69.00],
), caption: [EPYC-Milan, TurboShake400. Regional rows give all-worker / one-worker verification. Wire bytes include the child evidence. Proving excludes key generation and signing.]) <aggbench>

The eight-signer proof covers 34,624 B of raw signatures. The four-region verifier checks a total of 128 signers against a prepared registry (@aggbench). The first 32-signer region took 15.38 s to prove. These timings and the hardware runs below use distinct hosts and fixtures.

== Proof size vs. raw Jorts break-even and recursive IVC scaling

Comparing `QSAGHQM2` and `QSAGIVC1` wire sizes against concatenated raw signatures clarifies exact bandwidth break-even thresholds (@breakeven):
- A single-region height-6 Jorts run at 128 signers produced a 598,669 B `QSAGHQM2` proof for 553,984 B of raw signatures. The number of authenticated paths changes with the proof schedule, so extrapolating from an eight-signer proof understates the bytes needed at 128. The mixed-committee quickstart verified a complete 1,238,354 B regional aggregate for 112 Jorts and 16 Corduroy signers against 1,715,072 B of concatenated signatures, a 27.8% bandwidth saving. Both measurements include the full serialized proof.
- Against the depth-independent *639,673 B `QSAGIVC1` binary recursive root*, raw Jorts crosses break-even at *134 signers* ($h = 20$: 639,984 B) to *148 signers* ($h = 6$: 640,544 B). Beyond that point, raw signatures grow linearly while `QSAGIVC1` stays constant at 639,673 B (51.17 ms transfer over a 100 Mbit/s link), yielding *7.6×* compression at 1,024 validators, *747×* at $10^5$ validators, and *7,466×* at $10^6$ validators (639.7 KB vs. 4.78 GB, at $h=20$).

#figure(tbl((0.8fr, 0.65fr, 1.05fr, 1.05fr, 0.95fr, 0.95fr),
  [Active $K$], [Cells], [Raw Jorts ($h = 6 slash 20$)], [`QSAGHQM2` UB], [`QSAGIVC1` B], [IVC ratio ($h=20$)], table.hline(),
  [8], [$2^20$], [34.6 / 38.2 KB], [416,714 B#super[∗]], [639,673], [0.06×],
  [32], [$2^22$], [138.5 / 152.8 KB], [543,059 B], [639,673], [0.24×],
  [91], [$2^24$], [393.8 / 434.6 KB], [625,265 B], [639,673], [0.68×],
  [128], [$2^24$], [554.0 / 611.3 KB], [625,269 B], [639,673], [0.96×],
  [148], [$2^25$], [640.5 / 706.8 KB], [675,385 B], [639,673], [*1.11×*],
  [256], [$2^25$], [1.11 / 1.22 MB], [675,385 B], [639,673], [*1.91×*],
  [1,024], [$2^27$], [4.43 / 4.89 MB], [824,041 B], [639,673], [*7.65×*],
  [65,536], [$d=16$], [283.6 / 313.0 MB], [—], [639,673], [*489×*],
  [1,048,576], [$d=20$], [4.54 / 5.01 GB], [—], [639,673], [*7,829×*],
), caption: [Bandwidth scaling and break-even across validator counts $K$ (`QUORUM_AND_CONSENSUS_SCALING.md` & `hem_quintic.rs`). #super[∗]Measured 8-signer `QSAGHQM2` with Steiner deduplication is 392,971 B ($90.8 times$ one $h=6$ Jorts signature). Ratios compare serialized proof bytes with raw signature payloads and exclude the public statement.]) <breakeven>

== Vulkan prover and kernel measurements

@proofgpu gives prover wall times on an Intel Core i9-12900 and a Radeon RX 6750 XT (RADV NAVI22, Mesa 24.2.8). Both backends used identical inputs and coins under a 12 GiB host limit. Timers included host arithmetic, transfers and device execution. They excluded key generation, signing, device initialization and verification. Each accelerated proof matched the CPU serialization and passed the verifier with zero CPU fallbacks. These November 27 measurements precede integration of the wide seed stream and the current recursive committee relation. A subsequent release check reproduced byte-for-byte parity for both public profiles, both hiding profiles and the verified recursive root with zero CPU fallbacks on that root.

#figure(tbl((1.5fr, .86fr, .83fr, .83fr, .69fr),
  [Workload and hash], [Wire B], [CPU ms], [GPU⁎ ms], [CPU/GPU], table.hline(),
  [Hem 1, T], [308,531], [362.85], [297.95], [1.22×],
  [Hem 1, P], [321,381], [839.31], [383.35], [2.19×],
  [Hem 8, T], [390,171], [2,362.79], [2,047.01], [1.15×],
  [Hem 8, P], [416,205], [3,395.27], [2,155.44], [1.58×],
  [v2 1,024, C], [263,544], [137.60], [135.14], [1.02×],
  [v2 1,024, T], [261,994], [124.62], [124.85], [1.00×],
  [v2 16,384, C], [263,874], [184.80], [209.30], [0.88×],
  [v2 16,384, T], [265,374], [160.17], [177.70], [0.90×],
  [IVC 2, P], [639,673], [124,729.71], [107,235.10], [1.16×],
), caption: [⁎CPU plus GPU. Hem counts Jorts signers on a shared message, v2 counts S-box/product pairs, and IVC combines two committees. T denotes TurboShake400 for Hem and TurboShakeJohnson400 for v2. P denotes Poseidon2Gl24 and C denotes CshakeJohnson400. Hem and v2 report medians of three trials. IVC reports one pair at $2^23$ cells.]) <proofgpu>

The hardware audit covered ten SPIR-V kernels, including five quintic-field and Canopy kernels. No legacy Ext2 LDE kernel is in this set. RADV reported 32-thread subgroups, zero scratch and zero spilled registers for all ten pipelines. Planted faults produced hardware mismatches and rejected pins. @gpubench reports the five standalone timings. Kernel speedups span 0.14× to 106.91×. The 16,384-pair v2 proofs also took longer with the GPU, despite the speed of individual permutation and tree operations.

#figure(tbl((1.85fr, .8fr, .8fr, .7fr),
  [Kernel and workload], [CPU ms], [GPU ms], [CPU/GPU], table.hline(),
  [Poseidon2-12, $2^18$ states], [1,111.49], [14.20], [78.27×],
  [Keccak-f[1600], $2^18$ states], [34.56], [18.43], [1.88×],
  [Goldilocks NTT, $2^20$ points], [34.84], [8.10], [4.30×],
  [Poseidon2 Merkle, $2^20$ leaves], [4,466.55], [41.78], [106.91×],
  [BDOZ dot product, $2^18$ pairs], [0.88], [6.32], [0.14×],
), caption: [One timed invocation per backend on the same system. GPU times include transfers. All outputs matched.]) <gpubench>

= Conclusion

The quintic field provides room for the round-error terms without grinding. The public and hiding schedules target $2^(-128)$ under the cited reductions and ideal-hash assumptions. The interactive masking argument, executable extraction models, rational budget checks and extracted payload verifiers each establish a different part of that claim. On the measured hardware, the one-signer Poseidon2 proof ran 2.19× faster with Vulkan, whereas both 16,384-pair hiding workloads ran faster on the CPU.

#heading(numbering: none)[References]
#{
  set text(size: 7.4pt)
  set par(justify: false, leading: 0.38em, spacing: 2.5pt, hanging-indent: 1.6em)
  let refs = (
    [[ACFY25] G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT 2025 (full version IACR ePrint 2024/1586).],
    [[AHU19] A. Ambainis, M. Hamburg, D. Unruh, "Quantum Security Proofs Using Semi-classical Oracles", CRYPTO 2019.],
    [[BBBV97] C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM J. Comput. 26(5), 1997.],
    [[BBD+26] D. Boneh, B. Bünz, Justin D., Y. Litchev, K. Nazirkhanova, "PRAWNS: Threshold Hash-Based Signatures from Threshold PRFs", IACR ePrint 2026/2142, 2026.],
    [[BCGM25] S. Bordage, A. Chiesa, Z. Guan, I. Manzur, "All Polynomial Generators Preserve Distance with Mutual Correlated Agreement", IACR ePrint 2025/2051, 2025.],
    [[BCS16] E. Ben-Sasson, A. Chiesa, N. Spooner, "Interactive Oracle Proofs", TCC 2016.],
    [[BDH11] J. Buchmann, E. Dahmen, A. Hülsing, "XMSS – A Practical Forward Secure Signature Scheme Based on Minimal Security Assumptions", PQCrypto 2011.],
    [[BLS01] D. Boneh, B. Lynn, H. Shacham, "Short Signatures from the Weil Pairing", ASIACRYPT 2001.],
    [[BPRR26] V. Botta, M. Pospieszalski, E. Ragnoli, J. Ranvier, "ZKPoSP: Post-Quantum Zero-Knowledge Proofs for Hierarchical Deterministic Wallets", IACR ePrint 2026/1508, 2026.],
    [[BS23] W. Beullens, G. Seiler, "LaBRADOR: Compact Proofs for R1CS from Module-SIS", CRYPTO 2023.],
    [[BTA26] A. S. Bhati, S. Tariq, T. Ashur, "How to Attack Poseidon via Smart Subspace Restriction", IACR ePrint 2026/1692, 2026.],
    [[CDHZ25] A. Chiesa, Z. Di, Z. Hu, Y. Zheng, "How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions", #link("https://eprint.iacr.org/2025/2166")[IACR ePrint 2025/2166], 2025.],
    [[CFW26] A. Chiesa, G. Fenzi, G. Weissenberg, "Zero-Knowledge IOPPs for Constrained Interleaved Codes", IACR ePrint 2026/391, 2026.],
    [[CS25] E. Crites, A. Stewart, "On Reed–Solomon Proximity Gaps Conjectures", IACR ePrint 2025/2046, 2025.],
    [[CWYZ26] A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng, "Affine Combiners for Reed–Solomon Proximity Gaps", IACR ePrint 2026/2863, 2026.],
    [[DKT26] Q. Dao, S. D. Kominers, J. Thaler, "Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs", #link("https://eprint.iacr.org/2026/2056")[IACR ePrint 2026/2056], 2026.],
    [[FIPS203] NIST FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", 2024.],
    [[FIPS204] NIST FIPS 204, "Module-Lattice-Based Digital Signature Standard", 2024.],
    [[FIPS205] NIST FIPS 205, "Stateless Hash-Based Digital Signature Standard", 2024.],
    [[FPR26] T. Feneuil, K. Provin, M. Rivain, "Sum-Checking SmallWood: Smaller Hash-Based Zero-Knowledge Arguments", IACR ePrint 2026/2880, 2026.],
    [[GKS23] L. Grassi, D. Khovratovich, M. Schofnegger, "Poseidon2: A Faster Version of the Poseidon Hash Function", AFRICACRYPT 2023.],
    [[Hab22] U. Haböck, "Multivariate lookups based on logarithmic derivatives", IACR ePrint 2022/1530, 2022.],
    [[HKRY23] A. Hülsing, M. Kudinov, E. Ronen, E. Yogev, "SPHINCS+C: Compressing SPHINCS+ With (Almost) No Cost", IEEE S&P 2023.],
    [[HP22] S. Ho, J. Protzenko, "Aeneas: Rust Verification by Functional Translation", ICFP 2022.],
    [[IM26] M. Ioffe, D. Malkhi, "QUASI: Post-Quantum Quorum Attestation of Pre-Validated Statements", arXiv:2611.10403, 2026.],
    [[KKH26] D. Krachun, S. Kazanin, U. Haböck, "Failure of proximity gaps close to capacity", IACR ePrint 2026/782, 2026.],
    [[KSW26] Q. Kniep, J. Sliwinski, R. Wattenhofer, "Byzantine Fault-Tolerant Post-Quantum Distributed Quorum Signatures", arXiv:2607.17700, 2026.],
    [[LFKN92] C. Lund, L. Fortnow, H. Karloff, N. Nisan, "Algebraic Methods for Interactive Proof Systems", J. ACM 39(4), 1992.],
    [[MRG26] S.-P. Merz, À. Rodríguez García, "Skipping Class: Algebraic Attacks exploiting weak matrices and operation modes of Poseidon2(b)", IACR ePrint 2026/306, 2026.],
    [[MU21] L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021.],
    [[RFC9861] B. Viguier, D. Wong, G. Van Assche, Q. Dang, J. Daemen, "KangarooTwelve and TurboSHAKE", #link("https://www.rfc-editor.org/rfc/rfc9861")[IETF RFC 9861], 2025.],
    [[SP800-185] NIST SP 800-185, "SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash", 2016.],
  )
  for r in refs {
    par(r)
  }
}
