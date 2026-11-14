#set page(paper: "us-letter", margin: (x: 0.7in, y: 0.75in), columns: 2, numbering: "1")
#set text(font: "New Computer Modern", size: 9.5pt)
#set par(justify: false, leading: 0.45em)
#set heading(numbering: "1.1")
#set math.equation(numbering: none)
#show heading: set text(hyphenate: false)
#show heading: set par(justify: false)
#show math.equation: set text(size: 8.5pt)
#set figure(gap: 6pt)
#show heading: set block(above: 1.1em, below: 0.6em)
#show raw: it => text(font: "DejaVu Sans Mono", size: 7.5pt, hyphenate: false, it.text.replace("_", "_\u{200b}"))
#let tbl(cols, ..cells) = text(size: 8pt, table(columns: cols, inset: (x: 4pt, y: 4pt), stroke: none, table.hline(stroke: 0.6pt), ..cells.pos(), table.hline(stroke: 0.6pt)))
#let panel(body) = rect(width: 100%, inset: 7pt, stroke: 0.5pt, radius: 2pt, body)
#place(top + center, float: true, scope: "parent", clearance: 14pt)[
  #align(center)[
    #set par(justify: false)
    #set text(hyphenate: false)
    #text(size: 17pt, weight: "bold")[QSAG: Height-Independent-Depth Threshold Hash Signatures, Succinct Post-Quantum Aggregation, and a Four-Tier Machine-Checked Custody Stack]
    #v(8pt)
    #text(size: 11pt)[The QSAG Authors]
  ]
  #v(10pt)
  #block(inset: (x: 18pt))[
    #set align(left)
    *Abstract.* QSAG is a research prototype with open implementation issues in several components (§8); its mechanized results are statements about specifications. QSAG combines threshold hash signing, signature aggregation, and custody protocols with machine-checked statements about their specifications. A public/secret cut restricts secret evaluation to message randomization, chain starts and selected chain values, and FORS leaves; tree compression and target-sum grinding execute publicly. Specialized replicated sharing serves the honest-majority case, while authenticated Shamir sharing over binary towers and Goldilocks supports dishonest-majority computation with abort. A BaseFold-based [7] aggregation layer compresses batches of algebraic hash signatures. Custody components cover derivation, addresses, policy, migration, threshold ML-DSA [3], credentials, and accelerator provenance. Four verification tiers distinguish Lean specifications, extracted Safe-Rust MIR, modeled ISA correctness and leakage, and analysis of pinned compiled archive symbols. Differential and known-answer tests link specifications to code. We report measured kernel and aggregation performance and identify unresolved extractor, arithmetization, preprocessing, and ISA-model gaps. The development does not establish end-to-end implementation security or tight quantum-random-oracle extraction for its Fiat–Shamir protocols.
  ]
]

= Introduction
QSAG is a research prototype with open implementation issues in several components (§8); its mechanized results are statements about specifications.

Threshold custody must preserve a signing key across failures, membership changes, and malicious participants while remaining compatible with external verification. Hash-based signatures are attractive because the public verifier can remain unchanged when secret evaluation moves into a committee. Their large trees, however, make a literal secure-circuit translation expensive. Tree height, signature size, nonlinear circuit depth, and online communication are different costs; reducing one does not eliminate the others.

QSAG organizes the problem around the point where a secret-derived value is already permitted to become public. Secret shares need not follow that value through every subsequent compression or authentication-path computation. This observation gives a reusable cut interface for stateless and stateful hash signatures. It also exposes the obligations that a malicious-secure implementation must satisfy before opening a value: preprocessing validity, authenticated evaluation, transcript binding, and irreversible state transitions.

A second problem is verification scale. Even when threshold signing produces an ordinary signature, collecting many such signatures leaves a substantial bandwidth burden. QSAG therefore places an algebraic aggregation layer after signing. That layer proves a batch-verification relation and preserves signer-set accounting across disjoint merges. It is a distinct protocol with distinct assumptions, not an additional property of the threshold signature itself.

A third problem is the meaning of verification evidence. A theorem about a protocol specification, refinement of an extracted arithmetic routine, and a leakage check over compiled assembly answer different questions. We use a four-tier presentation to make those boundaries explicit. In particular, a constructive function returning an alleged break witness is not automatically a security reduction: the witness must express the intended break, and the function needs an adequate soundness statement.

*Contributions.*
- A unified post-quantum threshold hash-signing architecture with a four-oracle public/secret cut, specialized honest-majority RSS, and authenticated dishonest-majority field computation.
- A $K$-to-$1$ aggregation implementation using multilinear traces, Sumcheck [8], commitment-before-challenge BaseFold, and disjoint signer bitmaps; the Lean evidence covers an abstract fold/Sumcheck/bitmap layer.
- A custody suite connecting derivation, address binding, policy authorization, migration, threshold ML-DSA, credentials, and accelerator provenance to explicit state and entropy obligations.
- A four-tier Lean 4.35 [23] development (0 `sorry`, 0 custom axioms) over a Rust workspace with no external crates. “Verified” denotes the stated specification, MIR, or leakage-model property within its scope; it does not denote whole-system security.

== Mechanisms and threat models
*Related work.* CNF replicated sharing trades local simplicity for combinatorial storage. Paillier/MtA threshold ECDSA distributes an arithmetic signing relation; generic MPC evaluation of hash signatures instead hides the full hash circuit. Our cut exposes only authorized outputs and leaves tree work public. SNARK-based signature aggregation proves batch verification through a separate proof system; our transparent folding approach uses BaseFold [7] and Sumcheck [8]. MPC-in-the-head [25] supplies the distinct migration and credential proof mechanism. Hash-signature designs build on stateless hypertrees [5] and stateful Merkle trees [6].

CNF replicated secret sharing trades simple local operations for combinatorial replication as thresholds grow. Subfield-embedded Shamir sharing instead makes the per-party secret representation independent of that combinatorial family, at the cost of authenticated multiplication and preprocessing. The specialized 2-of-3 RSS path remains useful where honest majority is an acceptable assumption. The general SPDZ [10]/BDOZ [11] path addresses dishonest-majority computation with abort; identifiable-abort claims additionally require attribution evidence and adequate membership conditions.

Paillier/MtA threshold ECDSA distributes a different signing relation and arithmetic structure. QSAG's hash-signing mechanism instead distributes PRF and chain evaluation while preserving a hash-signature verifier. Sequential antichain FTS and parallel-seeded FTS likewise solve different optimization problems: compact single-signer signatures versus height-independent nonlinear MPC depth. We compare these mechanisms without treating a shared “threshold” label as evidence of equivalent cost or security.

The aggregation and migration Fiat–Shamir analyses are classical interactive-proof or random-oracle analyses over primitives selected for post-quantum use. They are not tight QROM online-extraction results. Custody statefulness introduces an additional operational assumption: a process crash must not turn an already consumed signing epoch or nonce into a reusable one.

= Cut-the-Hash
== Four secret oracles
Let the committee hold shares of $"SK.seed"$ and $"SK.prf"$, with public seed $"PK.seed"$ and root $"PK.root"$. Let $mu$ denote the framed message. Addresses bind the layer, tree, keypair, chain, and hash position. For compact notation write $A$ for the appropriate address and $A_0$ for its chain-start form. The cut interface consists of the following evaluations:

$ "evalPrfMsg"(r, mu) = "PRF"_"msg" ("SK.prf", r, mu) = R. $
Depth here counts sequential secret hash invocations, not multiplicative depth. This is one PRF call; SHAKE256 [1] absorbs the framed input sequentially, requiring $floor((2n + abs(M') )/136)+1$ secret Keccak permutations including padding, so permutation depth grows with message length unless prehashed. Here $r$ is the optional signing randomizer, not an exposed key share. Once authenticated, $R$ can enter the public message-digest computation.

$ "evalWotsChainEnd"(ell, tau, "kp", j, s) = F^s ("PK.seed", A, X_j), $
$ X_j = "PRF"("PK.seed", "SK.seed", A_0). $
The requested position is $s in {d_j, w-1}$, where $d_j$ is the message-selected chain offset. Secret hash-call depth is $1+s <= w$, with the hash-position address field advanced at each step. The endpoint is public-key material; the selected intermediate position is signature material. Arbitrary extra intermediate openings are not authorized merely because the endpoint is public.

$ "evalForsReveal"(tau_0, "kp"_0, u) \
 = "PRF"("PK.seed", "SK.seed", A_"FORS" (u)). $
This oracle reveals the signature-selected FORS secret leaf, at secret depth 1. The sibling-leaf oracle instead returns its hash:

$ "evalForsLeafHash"(tau_0, "kp"_0, u) \
 = F("PK.seed", A, "PRF"("PK.seed", "SK.seed", A_"FORS" (u))). $
Its secret depth is 2. That distinction prevents the public reconstruction of an authentication path from requiring sibling secret leaves themselves.

The interfaces `SlhMpcOracles` and `PqHashMpcOracles` encapsulate these operations. The construction never requires an omniscient reconstruction of the complete signing seed. Its security obligation is more specific than “the final signature is public”: each opening must be one permitted by the cut, produced by a valid authenticated computation, and bound to the authorized signing context.

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 5pt,
    panel([#smallcaps[Secret-shared evaluation]\
      `SlhMpcOracles` / `PqHashMpcOracles`\
      PRF keys → selected chain values / FORS outputs]),
    align(center)[↓\ #smallcaps[Commit · MAC-verify · open]\ ↓],
    panel([#smallcaps[Public reconstruction]\
      $T_ell$ compression · FORS roots · Merkle $H$\
      $H_"msg"$ and TSW grinding on authorized outputs]),
  )
}, caption: [The cut releases permitted outputs after authentication; secret seeds remain shared.])


== Depth, work, and chain tabulation
The tabulation bound is
$ N_"chain" <= 1+w $
secret hash evaluations per tabulated chain: one PRF and at most $w$ chain steps. `buildMpcChainTable` includes one further step whose output is discarded; the retained positions need only $w$ evaluations. The selected opening has sequential hash-call depth $1+s<=w$: 4 for the custom $w=4$ setting, and 16 for FIPS 205 [4]. A hash call can itself contain many nonlinear permutation rounds.

The benefit is independence from the height of the public tree above the cut. It does not assert that the number of leaf chains is independent of height, that a sponge evaluation is a single multiplication, or that preprocessing is free. Batching many independent secret operations can reduce their sequential dependency without reducing their total number.

Every WOTS public-key compression $T_ell$, FORS root compression, and binary Merkle internal hash executes in plaintext after the cut. So do $H_"msg"$ and TSW counter grinding. These operations depend only on public inputs and already opened cut digests.

TSW chooses chain offsets with a fixed sum:
$ sum_(j=1)^(ell_1) d_j = S,
quad S = floor((ell_1(w-1))/2) = 192, $
for $w=4$ and $ell_1=128$. The constant-sum restriction supports incomparability of distinct codewords in the specification. Grinding searches public candidate digests until the required sum holds.

== Parameters and encoding boundaries
@params gives the FIPS 205 SHAKE geometries and the custom profiles. The FIPS sizes are standard signature encodings. A dash for a custom wire size means no common byte count is asserted here; the custom family has different serialization and benchmark configurations. Poseidon2 [16] is the algebraic hash used by the custom aggregation profiles. The aggregation measurements later use a height-6 raw Jorts relation, while the protocol suite reports a 4,405-byte wire signature. These are not interchangeable measurements.

#figure(
  text(size: 7.1pt, table(columns: (1.7fr, auto, auto, auto, auto, auto, auto, auto, auto, auto), inset: (x: 1.6pt, y: 4pt), stroke: none,
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
    [Jorts], [32], [16], [1], [16], [—], [—], [4], [$2^16$], [—],
    table.hline(stroke: 0.6pt),
  )),
  caption: [Signature geometries; $n$ is node bytes. Custom rows are Corduroy-Custody-128, Baggy-128f, and Jorts-Poseidon2, with $ell_1=128$. Their encodings differ from FIPS 205.],
) <params>

== Bit identity and static upper layers
The strongest bit-exact result concerns FIPS 205. The declarations `thresholdSlhSign_eq_slhSignInternal` and `rss_thresholdSlhSign_eq_slhSignInternal` identify threshold evaluation with the single-signer specification, assuming the oracles compute the four cut functions (`MatchesKey`); the RSS instantiation discharges this premise in the specification. Together with differential and known-answer tests linking `Fips205.lean` and `fips205.rs`, this supports the stated threshold/single-signer equivalence for all six SHAKE sets. Equality is with matching inputs and randomness; it is not a claim that arbitrary committee transcripts are indistinguishable or that timing reveals nothing about participation.

Pure and prehashed message framing are separated by `pure_vs_preHash_disjoint` and `preHash_downgrade_rejected`.

At the custom-specification level, `evalCutBatchSignMpc_eq_evalSingleSign`, `rss_thresholdPqHashSign_eq_evalSingleSign`, and `shamir_poseidon2_thresholdSign_eq_evalSingleSign` express corresponding cut-evaluation equalities. They do not establish a bit-exact custom Lean-to-Rust wire match. The known differences in wire magic, bit windows, address layout, and leaf selection are recorded in §8.

Static upper-layer hashing omits external $R$ and $mu$ from `th_hash_internal_node`. Upper layers and stateless FORS-root signing therefore grind deterministically for their fixed internal inputs. The specification result `stateless_leaf_reuse_identical_wots_chains` expresses the intended consequence: at most one WOTS+C codeword is revealed for a fixed internal keypair across the key lifetime. This property does not authorize reuse of a stateful leaf for a different external message. The epoch mechanism is responsible for that separate boundary.

== Few-time signatures
`FrontierSumFts` maps a randomized public message digest into a decorated prefix-free binary-tree frontier. A frontier of length $L$ and height bound $h$ is paired with chain offsets whose sum is $S$. The exact ranking construction factors its counting problem as
$ M(h,w,L,S) = N(h,L) dot D(L,S). $
`frontierAntichain_paths_prefixFree` checks the frontier property, and `frontierSumFts_rank_unrank_bijection` checks the ranking correspondence. `U384` arithmetic and a `u128` fast view support exact ranking. Rank and unrank operate on public digests; secret expansion is straight-line and guarded by a monotonic 2-use latch.

#figure(tbl((1.5fr, auto, auto, auto, auto, auto, auto),
  [Profile], [B], [$n$], [$h$], [$w$], [$L$], [$S$], table.hline(),
  [Compact514], [514], [16], [14], [5], [31], [62],
  [Compact770], [770], [16], [15], [5], [47], [118],
  [Full256Bit], [1,058], [32], [8], [5], [32], [64],
  [Compact1314], [1,314], [16], [15], [5], [81], [162],
), caption: [FrontierSumFts wire profiles; $n$ is node bytes.])

The compact profiles use 16-byte nodes and therefore cap generic node-preimage strength at 128 classical bits or 64 Grover bits. The 32-byte-node `Full256Bit` profile supplies 256 classical or 128 Grover bits at that node-preimage boundary. These are node-width bounds, not a substitute for a complete few-time signature security analysis.

Sequential antichain FTS expands secrets down internal tree edges. Experimental `ParallelSeededFts` instead derives independent leaf-chain work from a shared root seed, opens authenticated endpoints, and constructs a height-$h$ Poseidon2 [16] Merkle tree publicly. Its compression primitive is a 48-round $x^7$ SPN over $FF_(2^128)^2$ with Davies–Meyer feedforward. The S-box is bijective because $gcd(7,2^128-1)=1$; the feedforward compression is not thereby a bijection. Algebraic degree growth alone is not a general cryptanalytic security argument.

The reference MPC schedule in `parallel_mpc.rs` reports
$ D_"parallel" = 48(1+w)+4 = 292 $
for `CUSTODY_H10_W5`, with $h=10$, $w=5$, $L=68$, and $S=136$. The added term accounts for the MAC barriers. Its internal-chained comparison is $24(h w+1)=1,224$, charging 24 rounds per step. This is a schedule comparison using that implementation's accounting, not the numerical instance of the generic Lean AST theorem.

Specifically, `buildParallelSeededAst_depth` gives $"rounds"(1+w)$, while `buildInternalChainedAst_depth` gives $"rounds" h w$. The theorem `parallelSeededFts_mpc_depth_independent_of_height` proves height invariance and includes the concrete instance $"rounds"=82$, $h=15$, $w=5$: 492 versus 6,150. That structural example excludes the reference runner's added barrier term and does not describe the deployed 48-round parameter choice. The distinction keeps a useful asymptotic statement from becoming a misleading latency comparison.

= Beyond the CNF barrier and dishonest majority
== Sharing and the binary tower
In the CNF replication accounting, a general threshold construction carries a family of $binom(n,t-1)$ shares, with $binom(n-1,t-1)$ active terms per party. At $n=15$, $t=8$, the former is $binom(15,7)=6,435$, with $binom(14,7)=3,432$ active terms per party. Such replication can be useful for small committees but does not scale like a single field share.

QSAG uses an active 2-of-3 RSS Keccak path [12, 13]: at most one corrupted party, with security with abort. Keccak's linear steps are local XOR and rotations; its nonlinear $chi$ step requires distributed evaluation. The implementation batches 64 lanes in `eval_rss_keccak_f1600_batch64`. `reconstructRssKState_mpcKeccakF1600Rss` relates the shared computation to the permutation specification, and `rss_flnw_active_open_sound` supplies specification-level active-opening evidence. We do not attach a full-signature latency to those local results.

The arbitrary-threshold path uses Shamir sharing embedded in a Wiedemann tower [17]:
$ cal(T)_0 = FF_2, quad
  cal(T)_1 = cal(T)_0[x_0] slash (x_0^2+x_0+1), $
$ cal(T)_k = cal(T)_(k-1)[x_(k-1)] slash
  (x_(k-1)^2+x_(k-2)x_(k-1)+1). $
The construction reaches $cal(T)_3=FF_(2^8)$ and $cal(T)_7=FF_(2^128)$. The former supports up to 255 distinct nonzero evaluation points. Injective embeddings preserve the Boolean subfield's addition and multiplication; `embedTowerChain_injective` and `towerMul_inv` state relevant algebraic properties.

A Shamir polynomial stores its secret at the constant term. A participant assigned $x_i=0$ would receive that term directly, so nonzero-point validation is a confidentiality condition. `zero_eval_point_leaks_secret_term` makes this failure explicit.

The shared key representation is 32 bytes per party independently of the CNF family size. This is a statement about key-share size, not about total per-party memory. Bitsliced state, preprocessing pools, authenticated multiplication, and transcripts add costs. Keccak's Boolean operations embed into tower-field operations, but a malicious participant must still be prevented from substituting a non-Boolean field element.

== Algebraic permutations and preprocessing
The alternative algebraic route uses width-12 Poseidon2 over Goldilocks,
$ p=2^64-2^32+1. $
A permutation uses $4 dot 12+22 dot 1+4 dot 12=118$ power-7 S-boxes. Linear packing places secret bytes in 56-bit limbs without an input arithmetic-to-Boolean conversion. The theorem `poseidon2Perm12_bijective` concerns the permutation, and `bytesToLimbs56_injective` addresses packing rather than hash collision resistance.

With preprocessed authenticated powers of a random mask $r$, opening $y=x+r$ permits local evaluation of
$ [x^7] = sum_(k=0)^7 binom(7,k)(-1)^k y^(7-k)[r^k]. $
`power7BinomialEval_eq_sbox7` is the algebraic identity supporting this online step. One online opening round for an S-box assumes valid preprocessing and authenticated masking; it does not absorb preprocessing or all surrounding conversions into that round. Canonical output conversion remains significant: the documented dual-adder conversion consumes 760 Beaver triples per unrevealed 256-bit chain step.

Base OT uses the Ring-LWE ring
$ R_q = ZZ_(12,289)[X] slash (X^1024+1). $
With CBD noise parameter $eta=1$, the documented rounding bound is
$ norm(e_1 r_c-e_2 s_R+e_3)_infinity <= 2,049 < 3,072 = floor(q/4). $
`rlwe1024_ot_decrypt_exact` checks the corresponding exact-decryption statement. A Fujisaki–Okamoto [18] re-encryption check binds the seed and auxiliary randomness; `fo_cut_and_choose_selective_failure_bound` addresses selective failure in the modeled protocol. A seeded 2-universal leftover-hash combiner [19] maps 384 input bits to 128 output bits. Given 384 bits of min-entropy, the usual leftover-hash bound gives distance at most $2^(-128)$ from uniform; input length alone is insufficient. `lhl_combiner_384_to_128_stat_dist` proves a collision-count and collision-excess bound, not that full statistical-distance conclusion.

The KOS extension protocol [9] is interactive: column commitments precede an independent challenge and then a consistency proof. `kos_interactive_check_sound` models the residual with the bitwise-AND correlation used in Rust: for a nonzero challenge, acceptance holds exactly when the masked bit error vanishes. `kos_single_bit_does_not_pin_key` records the limit of that statement: a one-bit corruption leaves the remaining key bits unconstrained.

Experimental PCG preprocessing [14] uses GGM punctured-PRF expansion and quasi-cyclic LPN compression to model pseudorandom correlations without transmitting every expanded triple. `ggm_punctured_tree_hiding` and `pcg_lpn_ole_expansion_sound` describe the corresponding modeled properties. Sacrifice then checks the relation among the proposed authenticated values: `spdz_triple_sacrifice_sound` and `pow7_sacrifice_sound` are relevant witnesses. Dealerless preprocessing does not mean assumption-free preprocessing. Ring-LWE, the pseudorandom generators, correlation checks, and the specification-to-code connection all remain in the argument.

The current preprocessing model is incomplete as an implementation refinement. The RLWE proof models scalar rounding rather than the full negacyclic NTT, and the KOS statement covers a single-column residual rather than the batched protocol. The exact local statements remain useful, but they do not close those gaps.

== Booleanity, release ordering, and abort
In characteristic 2, a field element is Boolean exactly when
$ b^2+b=0. $
`towerFrobenius_eq_zero_iff_bit` characterizes this property. An unauthenticated check is insufficient: `frobenius_unauthenticated_offset_break` demonstrates how a malicious offset can cancel the residual. Authenticated Beaver multiplication must establish the residual relation before a zero test is accepted. The constructive `dkg_frobenius_booleanity_soundness` belongs to that modeled argument.

Cut opening follows the order *commit → MAC-verify → open*. The adversarial result `open_before_mac_leaks_faulted_cut` explains why an eventual abort is too late if a faulted secret-dependent value has already been exposed. A correct signature at the end of a successful run does not constrain information revealed during a failing run. Release ordering is therefore a privacy condition as well as an integrity condition.

The BDOZ path uses paired Tower128 MACs, while the algebraic path uses `GoldilocksExt2` MACs. The documented model bounds are $2^(-256)$ and $p^(-2)<2^(-127)$, respectively, under their authenticated-sharing assumptions. `spdz_batch_mac_soundness` and `bdoz_2lane_mac_soundness` address those checks. An adversarial party can still deny service; dishonest-majority security is expressed with abort, not guaranteed output delivery.

Identifiable abort requires sound attribution. `extractBdozCheaterOrValid` constructs a check result; `honest_party_never_slashed` shows an honestly formed opening passes the pairwise MAC check. `protocol_realizes_idealTsig_id_abort` assumes culprit identification as a hypothesis. Neither theorem proves attribution soundness.



== Resharing and epochs
Sub-polynomial resharing changes $(t,n)$ to $(t',n')$ without reconstructing the full secret. `reshare_preserves_public_key_and_refreshes_degree` expresses preservation of the public key with a refreshed polynomial degree. Old-share erasure is part of the operational transition: retaining both historical and current material changes the compromise model.

For stateful Jorts, the Rust `MonotonicEpochLatch` binds an epoch to a message and its retry state. `stateful_jorts_crash_retry_idempotent` permits an identical retry, while `stateful_jorts_equivocation_rejected` refuses a different message at the consumed epoch. `epochLatch_trace_no_equivocation` extends the property over a trace; `jorts_quorum_never_double_signs` uses a quorum-intersection premise. No particular network quorum formula is asserted here.



= Succinct $K$-to-$1$ aggregation
== Trace and digest representation
`qsag-agg` encodes parallel verifications of `JortsPoseidon2` or `CorduroyPoseidon2` into a 256-column multilinear trace over Goldilocks. The evaluated Jorts configuration has a 4,328-byte raw signature and a height-6 XMSS tree. The stateless aggregation configuration has 76,896-byte raw signatures, $k=32$, $a=8$, $d=16$, and $h'=4$, with $Q_"max"=2^20$. It must not be confused with the custom custody geometry in @params.

Challenges lie in `GoldilocksExt2`, modeled as $FF_p[u] slash (u^2-7)$. `nonResidue_not_square` supports the extension construction, and `goldilocksExt2_card_gt_two_pow_126` supplies the documented cardinality bound.

`Digest5` addresses that separate problem by packing a 256-bit digest as four 56-bit limbs and one 32-bit limb, all canonical below $p$. `digest5FromBitVec256_injective` rules out collisions caused by reducing a wider digest directly modulo the field.

== Commitments, challenges, and terminal checks
The prover commits to the trace and folded codewords through an interleaved BaseFold Reed–Solomon/Merkle construction. Constraint residuals are checked by Sumcheck, coupled to polynomial commitments. The crucial ordering is to absorb each codeword commitment before squeezing the challenge that folds it. `prechallenge_fold_forgery_attack` records an explicit failure when a prover can choose the committed object after seeing the relevant challenge.

`basefold_committed_quartet_roots_le_one` is a local root-count statement under commitment-before-challenge. `sumcheck_cubic_round_roots_le_three` bounds a cubic round in the abstract model. `terminal_check_omission_unsound` shows that a sequence of apparently well-formed intermediate rounds is insufficient without checking the terminal relation. Each theorem addresses a component obligation, not a full deployed-verifier soundness theorem.

The configured rate and query count give the idealised query-phase calculation:
$ rho=1/16, quad Q=64, quad
  sqrt(rho)^Q=(1/4)^64=2^(-128). $
A provable proximity bound includes a gap term, $(sqrt(rho)+epsilon)^Q$, and a commit-phase error. The 16-bit proof of work increases grinding cost, not soundness. Extension-field Sumcheck and folding terms cap overall soundness below 128 bits; we do not state a composite figure. Generic quantum search over Fiat–Shamir challenges roughly halves the idealised exponent, so these parameters do not target 128-bit quantum soundness.

The Rust arithmetization uses degree 8, whereas `Aggregation.lean` uses a degree-3 round bound and abstracts away message, committee, and trace-commitment binding in `verifyAggregatedSignature`. Consequently, the machine-checked aggregation results concern the abstract Sumcheck/fold/bitmap layer. The constructive `qsag_aggregate_unforgeability_reduction` remains a reduction skeleton without a separate adequate soundness theorem.

== Disjoint merging and measured compression
`SignerBitmap` prevents a merge from counting the same signer twice. `overlapping_merge_rejected` records rejection of overlap; `merge_aggregates_disjoint_sound` describes a valid disjoint fold.

`merge_aggregates` implements a 2-to-1 recursive tree fold. `MAX_MERGE_TREE_DEPTH = 16` bounds recursion, supporting up to 65,536 shards under the documented tree accounting.

#figure(tbl((1.6fr, 0.4fr, 1fr, 1fr, 0.6fr, 1fr, 0.7fr, 1fr, 0.7fr),
  table.cell(colspan: 5)[Batch and encoding], table.cell(colspan: 2)[Intel (ms)], table.cell(colspan: 2)[AMD (ms)],
  [Profile], [$K$], [Raw B], [Proof B], [Ratio], [prove], [verify], [prove], [verify], table.hline(),
  [JortsPoseidon2], [16], [69,248], [132,533], [0.52×], [2,467.08], [1.74], [3,642.64], [3.68],
  [JortsPoseidon2], [64], [276,992], [156,954], [1.76×], [9,410.49], [2.72], [11,257.38], [8.92],
  [JortsPoseidon2], [256], [1,107,968], [190,976], [5.80×], [41,689.88], [6.20], [43,749.85], [8.01],
  [JortsPoseidon2], [512], [2,215,936], [201,723], [10.99×], [86,218.08], [10.75], [92,283.88], [13.44],
  [CorduroyPoseidon2], [16], [1,230,336], [188,697], [6.52×], [44,141.90], [2.67], [44,108.83], [7.09],
  [CorduroyPoseidon2], [32], [2,460,672], [201,704], [12.20×], [89,253.73], [3.01], [88,474.99], [8.92],
), placement: top, scope: "parent", caption: [Aggregation measurements; all times in ms. Intel is Core i9-12900; AMD is EPYC-Milan. Ratio is raw bytes divided by proof bytes. A disjoint $64+64$ merge takes 4.91 ms on Intel and 12.80 ms on AMD. AMD verification is non-monotone across some batch sizes, consistent with measurement noise.]) <aggbench>

@aggbench shows that aggregation is not a bandwidth win for every batch. At $K=16$, the Jorts proof is larger than the raw signatures. The measured crossover is between that point and $K=64$, where compression is 1.76×; it is reasonable to describe compression as winning from approximately $K=64$ among the measured configurations, not as a precise universal break-even threshold. At $K=512$, the recorded ratio reaches 10.99×.

Stateless CorduroyPoseidon2 starts with much larger raw signatures and already reaches 6.52× compression at $K=16$. This difference follows from both the base-signature size and the aggregation relation. It does not imply that the stateless signer itself is faster.

= Custody and credentials
*`qsag-hd`.* `PiHdCommitInventory` provisions a Merkle-committed watch-only table of independently generated child public keys, with child secrets retained in party vaults. Experimental `PiHdLinearModule` instead supports local public/share derivation under $bold(t)=bold(A)bold(s)_1+bold(s)_2 mod 8,380,417$, using deterministic public CBD2 shifts and 7-lane SPDZ authentication. It requires no online derivation messages and caps depth at 1,024. The latter is bounded related-key homomorphic derivation, not a standard-model rerandomized Module-LWE reduction. Norm growth prevents an unqualified substitution into tight FIPS 204 rejection bounds. Independent inventory secrets provide the alternative when child isolation is required.

*`qsag-addr`.* The address layer uses a strict 67-character Bech32m [24] codec with `qsp1...` addresses and checksum constant `0x2bc830a3`. Versioned cSHAKE256 [2] and Poseidon2 commitments bind script/public-key identity. `SingleOrThreshold` avoids encoding whether the underlying key is held by a single signer or committee. `HybridPinnedEnvelope` pins the post-quantum key rather than accepting a replacement carried by an adversarial envelope. `bech32m_rejects_bech32_and_detects_single_subst` checks codec behavior; `selfCarried_pq_key_substitution_refuted` addresses the substitution failure mode. Address checks do not establish that an external system selected the intended trust anchor.

*`qsag-policy`.* A 4-round pairwise 2-lane BDOZ guard checks chain and suite identifiers, recipient allowlists, single-transaction and rolling velocity limits, timestamp windows, self-approval restrictions, and amount-dependent quorum or hardware-guardian rules. Only after the committed MAC barrier may it release an `AuthorizedSignReleaseToken`. A MAC or phase fault wipes the 64 guard slots. The guard's authorization result depends on its configured policy and authenticated inputs; it does not prove the correctness of an external clock, transaction interpretation, or administrative policy choice. The construction separates authorization from the mathematical ability to produce a signature.

*`qsag-migrate`.* Migration binds knowledge of a legacy spending key to a target `QsagAddress` and campaign nullifier, covering HASH160, Taproot x-only, Ethereum Keccak20, and SLIP-0010 Ed25519 relations. It uses 219-repetition ZKBoo [15] with dual `GoldilocksExt2` Sumcheck; the repetition accounting is $(2/3)^219<2^(-128)$ in the classical analysis. These parameters target 128-bit classical soundness; generic quantum challenge search roughly halves the exponent. Proofs are transparent and non-succinct; we do not report an unmeasured size. Every proof requires fresh, never-repeated 256-bit OS entropy; tape reuse across distinct challenges can reveal all three views. Verifiers must persist `(domain, migration_nullifier)`. The experimental distributed `co_zk_mpc` helper fails its intended passive 1-of-3 privacy and must not be used (§8); single-prover proofs are unaffected by that issue.

*`qsag-cred`.* Experimental `ThresholdMlDsa` produces signatures accepted by an ordinary FIPS 204 [3] verifier, with subset/Shamir committees satisfying $2<=t<=n<=5$. The intended setup requires the interactive 3-round DKG ceremony and pluggable `MlDsaHighBitsOt` preprocessing; single-caller test helpers are not the production ceremony. Linear nonce typestate and durable burning protect masking nonce use, with `threshold_mldsa_nonce_reuse_extracts_sk_and_typestate_prevents` exposing the modeled failure. The crate also contains experimental `PiVoprf`, a 2-round verifiable OPRF over the Mersenne field with modulus $2^127-1$, and experimental `PiBlindVc`, combining threshold issuance, an issuer accumulator, and fresh unlinkable selective disclosure. The intended assumption is Module-LWE over a degree-128 ring of rank 3 (dimension 384), not discrete-log hardness in the base field. Its “DLEQ” is a Chaum–Pedersen-shaped same-key proof with bounded errors and smudging. The audit found insufficient parameters and missing checks; both stacks are insecure prototypes (§8).

#figure(tbl((1.4fr, 1fr, 1fr),
  [FIPS 204 profile], [Public key B], [Signature B], table.hline(),
  [ML-DSA-44], [1,312], [2,420],
  [ML-DSA-65], [1,952], [3,309],
  [ML-DSA-87], [2,592], [4,627],
), caption: [Standard-verifier ML-DSA sizes. Threshold participation does not change these external formats.])

*`qsag-accel`.* `AcceleratorBackend` defines batch interfaces for Keccak, Poseidon2, Goldilocks NTT, extension-field coset expansion, Merkle layers, and Tower128 BDOZ dot products. `VerifiedKernelDigestRegistry` pins loader-measured binary digests, and authenticated `ExecutionReceipt`s bind them into transcripts. Such receipts establish integrity/provenance binding rather than a succinct proof that an untrusted GPU performed the arithmetic correctly. Off-CPU results need `spot_check_merkle_layer` or final signature/proof verification. `accelerator_backend_simulation_sound` is a specification-level simulation statement under its premises; it does not certify arbitrary accelerator firmware or drivers.

= Four-tier verification
The development reports 37,530 Lean lines and 1,162 theorem declarations, with no Mathlib dependency, 0 `sorry`, 0 custom axioms, and 0 `native_decide`. Axioms used are a subset of {`propext`, `Quot.sound`, `Classical.choice`}. The audit found about 71 of 1,623 `Qsag` declarations transitively use `Classical.choice` through standard-library or `omega` lemmas; `QsagVerified/Proofs.lean` also has transitive uses. Constructive elimination of the remaining choice dependencies is in progress.

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 6pt,
    panel([#smallcaps[Tier 1 · specifications]\
      `Fips205.lean` · `ThresholdMpc.lean`\
      `Aggregation.lean`\ Algebra, signing, state, and protocol relations]),
    align(center)[↓ Differential / KAT links; scoped refinement ↓],
    grid(columns: (1fr, 1fr), gutter: 7pt,
      panel([#smallcaps[Tier 2 · MIR core]\
        `QsagMirProofs.lean`\ Safe-Rust arithmetic and local state refinement]),
      stack(dir: ttb, spacing: 5pt,
        panel([#smallcaps[Tier 3 · ISA models]\
          `ConstantTimeIsa.lean`\ Kernel algebra and leakage; dudect tests]),
        align(center)[↓ Pinned decoding],
        panel([#smallcaps[Tier 4 · archive NI]\
          `ElfBinaryVerify.lean`\ `CompiledRlibFixtures.lean`\ PC / memory / latency-operand analysis]),
      ),
    ),
  )
}, caption: [Complementary evidence, not a completed refinement chain. The MIR core and assembly kernels cover separate code; there is no formal Tier 2 → Tier 3 link.])


== Tier 1: specification spine
The specification tier comprises 17 modules with 905 theorems, of which 592 are public, alongside constructive Type-valued extractors. `Goldilocks.lean` and `BinaryTower.lean` establish field and embedding properties. `Keccak.lean` and `Poseidon2.lean` formalize permutation, framing, and packing behavior. Representative claims include `goldilocksPrime_isPrime`, `Goldilocks.mul_inv_cancel`, `mulExec_refines`, `encodeMultiFrame_injective`, and `poseidon2PadBytes_injective`.

These algebraic results support the signing specifications in `Fips205.lean` and `HashSigs.lean`. `fips205_wots_incomparable_no_chain_forgery` and `tsw_incomparable_no_chain_forgery` address chain-order reasoning. `verifyPqHashSig_evalSingleSign` expresses modeled completeness. `HypertreeEufCma.lean` supplies epoch and retry statements, while `ThresholdMpc.lean` connects shared evaluation to single-signer evaluation.

`Preprocessing.lean`, `MaliciousSecurity.lean`, and `IdealTsig.lean` formalize preprocessing checks, authenticated release, and ideal threshold approval. For universal composition [20], `UcGames.lean` includes `multi_session_uc_realizes` and `uc_composition_theorem`. Those names describe formal statements in their models; they do not establish that every implementation detail satisfies the premises. In particular, an ideal functionality with insufficient membership conditions can admit behavior that the intended functionality should reject.

The extractor distinction is central. `extractFips205WotsForgery`, `extractPqHashForgery`, `extractFullHypertreeForgery`, and `qsag_aggregate_unforgeability_reduction` are constructive definitions. A Type-valued output alone does not establish the intended security conclusion. Under-constrained witness fields and missing soundness theorems mean that the current full-hypertree and aggregate definitions should be described as reduction skeletons.

*Not covered:* Tier 1 does not prove an end-to-end deployed EUF-CMA reduction, a tight QROM Fiat–Shamir reduction, or a complete implementation refinement. Its aggregation and custom-profile abstractions must be read with the known gaps in §8.

== Tier 2: Safe-Rust MIR refinement
Charon and Aeneas [22] translate the dedicated Safe-Rust verification core into pure Lean functions. `QsagMirProofs.lean` re-exports 92 specifications/theorems, including 8 `tooth_*` refusal witnesses. This is the interface count; it is not presented as a separate theorem-only total.

Arithmetic specifications include `goldilocks_canon_spec`, `goldilocks_reduce128_spec`, `goldilocks_mul_spec`, `goldilocks_pow7_spec`, and `goldilocks_ext2_mul_spec`. For tower fields and authenticated Boolean operations, the interface includes `tower_gf256_field_laws`, `tower_gf256_boolean_iff_frobenius`, `dkg_beaver_frobenius_eval_spec`, and `verify_mac_2lane_burn_irreversible`.

The scope also includes `rss_keccak_chi_lane_spec`, `shamir_eval_poly_gf256_spec`, `shamir_lagrange_at_zero_gf256_3of3_spec`, full 24-round `keccak_f1600_total`, and `ct_eq_bytes32_spec`. FIPS address and checksum results are `fips205_adrs_roundtrip_spec` and `fips205_wots_checksum_spec`. `tsw_check_target_sum_spec` and `epoch_latch_multiturn_safety` cover local validation and multi-turn epoch behavior.

Negative witnesses test the meaning of refusal: `tooth_goldilocks_noncanonical_rejected`, `tooth_gf256_nonboolean_rejected`, `tooth_shamir_duplicate_points_rejected`, and `tooth_epoch_equivocation_rejected` address malformed arithmetic or state inputs.

Differential parity tests in `parity_qsag_core.rs` connect the dedicated extraction core to the operational `qsag-core` code. That bridge is testing evidence, not a proof that all duplicated code remains equivalent after arbitrary edits.

*Not covered:* Tier 2 does not translate or refine all network/session state machines across the 11 workspace crates. Its scope is the extracted core and stated specifications, with differential tests linking that core to broader implementation use.

== Tier 3: ISA semantics and timing evidence
`ConstantTimeIsa.lean` models selected x86-64 and AArch64 instructions and their leakage events. The trace records program counter, branch behavior, memory addresses, variable-latency operands, and dirty upper-vector state on return. `x86_ct_checker_sound` and `arm_ct_checker_sound` establish relational properties of the modeled taint checkers.

Functional statements are separate from leakage statements. The GFNI path uses a Wiedemann-to-AES-polynomial isomorphism; `gfni_phi_left_inv`, `gfni_phi_right_inv`, and `gfni_isomorphism_homomorphic` connect the field representations. `gf256ShamirMulGfni_32lane_correct` and `gf256ShamirMulGfni_exec_1block_correct` address the modeled multiplication kernel; `gf256ShamirMulGfni_constant_time` addresses its leakage behavior. Likewise, `keccakChiMpc_3party_rss_sound` and `keccakChiMpcAvx2_exec_lane0_correct` concern the RSS relation and modeled execution, while `keccakChiMpcAvx2_constant_time` and `keccakSha3Neon_constant_time` concern traces.

For canonical Goldilocks inputs, `goldilocksMulCtX86_canonical_correct` and `goldilocksMulCt_x86_eq_arm` establish equivalence of the modeled x86-64 and AArch64 instruction sequences. `goldilocksMulCtX86_constant_time` and `goldilocksMulCtArm_constant_time` are distinct leakage results. The equality kernels similarly have `ctEq32X86_functional_correct` and `ctEq32Arm_functional_correct`.

Negative tests include `tooth_secret_jcc_leaks_and_rejected`, `tooth_secret_mem_index_leaks_and_rejected`, `tooth_secret_div64_leaks_even_under_doit`, and `tooth_arm_csel_requires_msr_dit1`. They make the modeled leakage policy inspectable. The accompanying dudect [21] measurements ask whether tested hardware executions exhibit class-dependent timing under the measurement setup; lack of a detected timing signal is empirical evidence rather than a universal timing theorem.

*Not covered:* Tier 3 does not cover unmodeled speculation, silicon errata, power or electromagnetic leakage, or the compiled control flow of every Safe-Rust crate. Correctness and noninterference are relative to the stated ISA and leakage models.

== Tier 4: pinned compiled archives
`CompiledRlibFixtures.lean` embeds SHA-256-pinned `libqsag_asm.rlib` fixtures. `ElfBinaryVerify.lean` parses GNU archives and ELF64 sections, extracts symbol bodies, decodes instructions, and runs an abstract-interpretation taint analysis. `parseArMember_subslice` and `extractElfFuncBytes_in_text_section` support the connection between archive bytes and extracted code.

The pinned fixtures contain 16 x86-64 symbols and 7 AArch64 symbols. `x86_rlib_all_16_decode_954_instrs` and `aarch64_rlib_all_7_decode_191_instrs` account for 954 and 191 symbol-body instructions, respectively. Those are fixture-specific counts. The recorded current source-head audit instead disassembles to 999 and 299 instructions; fixtures must be regenerated for each release.

`checkElfFuncThreeWayNI_sound` connects accepted checks to the formal three-way noninterference property: program-counter control flow, memory-address observations, and avoidance of secret variable-latency operands. The all-symbol results are `rlib_x86_all_16_three_way_ni` and `rlib_aarch64_all_7_three_way_ni`, with soundness statements `rlib_x86_every_symbol_three_way_ni_sound` and `rlib_aarch64_every_symbol_three_way_ni_sound`. The model also checks callee-saved conventions and epilogue vector hygiene, including `vzeroupper` and NEON clearing.

`x86_contract_init_inhabited` and `aarch64_contract_init_inhabited` provide non-vacuity witnesses for initial contracts. Mutation witnesses such as `mutant_secret_branch_rejected`, `mutant_secret_lut_rejected`, `mutant_udiv_rejected`, and `mutant_missing_vzeroupper_rejected` show rejection of selected corrupted fixtures. They test sensitivity to known bad changes, not completeness of the decoder or leakage model.

*Not covered:* Tier 4 does not prove functional correctness of every lifted binary, binary noninterference for the high-level Rust workspace, or correctness of arbitrary future builds. Known carry-less-multiply, decoding, and register-model defects limit the interpretation of its current NI theorems.

= Evaluation
== Hardware and measurement scope
The recorded testbeds are Intel Core i9-12900 (Alder Lake) and AMD EPYC-Milan (Zen 3, virtualized), both running Linux x86-64. The Intel path uses AVX2, GFNI, and VPCLMULQDQ, while the AMD path uses AVX2 and PCLMULQDQ. Kernel comparisons exercise different instruction paths on those processors; they are not controlled evidence that a single instruction explains every speedup.

AArch64 targets are covered by static and Lean binary analysis. There are no AArch64 timing numbers in this evaluation. Guest scheduling and virtualization can affect AMD cycle counts and timing statistics.

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
), placement: top, scope: "parent", caption: [Kernel measurements in cycles per indicated unit, and dudect Welch statistics over 1,000,192 traces. Goldilocks cycle counts are per multiplication; dot2 and pow7 timing tests are separate rows. RSS uses AVX2; tag equality is straight-line; the negative control leaks intentionally. Speedups reproduce recorded values, which need not equal ratios of rounded cycle entries.]) <simdbench>

== Kernel throughput and dudect
The dispatched `qsag-asm` kernels in @simdbench are standalone: none of the ten sibling crates currently depends on them. They are not yet called by protocol crates; the protocol timings use portable constant-time paths.

@simdbench separates cycle measurements from timing-class tests. GF256 arithmetic benefits substantially from the specialized field representation and vector paths. The GFNI multiplication result on Intel is 0.039 cycles per byte versus 19.890 in the portable measurement. The corresponding AMD path uses a different implementation and reports 0.551 cycles per byte. These are batched kernel numbers, not the cost of a complete threshold signing session.

The nine timing tests (splitting Goldilocks dot2 and pow7) satisfy the reported $abs(t)<4.5$ criterion over 1,000,192 traces on both processors. A separate post-hardening harness covers 10 operations with 100,096 samples and maxima 2.62 on Intel and 2.23 on AMD. The deliberately leaking early-exit comparison is rejected with very large statistics on both machines. This negative control demonstrates sensitivity to that chosen leak under the harness; it does not characterize sensitivity to all smaller or differently structured leaks.



== Protocol micro-benchmarks
@microbench reports the complete protocol digest: release build, single thread, `CpuReferenceBackend`, medians unless marked single run. All multi-party entries are in-process simulations without network latency and use portable constant-time code. Experimental components retain the issues in §8; timing is not a security validation.

#figure(tbl((2.2fr, 1.6fr, 1.25fr, 1.25fr),
  [Operation / profile], [Order of measurements], [Intel (ms)], [AMD (ms)], table.hline(),
  [Jorts-Poseidon2, $h=8$], [sign / verify], [1,196.80 / 2.053], [1,581.94 / 2.623],
  [Frontier Compact514], [keygen / sign / verify], [166.50 / 0.564 / 0.263], [221.26 / 0.816 / 0.355],
  [Frontier Compact770], [keygen / sign / verify], [323.27 / 1.883 / 0.380], [441.04 / 2.933 / 0.513],
  [Frontier Full256Bit], [keygen / sign / verify], [4.36 / 0.735 / 0.374], [3.49 / 0.568 / 0.372],
  [Frontier Compact1314], [keygen / sign / verify], [376.74 / 3.001 / 0.927], [440.56 / 2.166 / 0.951],
  [Parallel FTS, 3 parties], [threshold sign / verify], [327.05 / 13.045], [662.84 / 26.830],
  [ML-DSA-44, 2-of-3], [test setup / sign / verify], [6.36 / 1,172.94 / 0.073], [8.18 / 1,915.03 / 0.096],
  [ML-DSA-65, 2-of-3], [test setup / sign / verify], [5.26 / 2,248.95 / 0.116], [7.27 / 3,631.76 / 0.156],
  [ML-DSA-87, 2-of-3], [test setup / sign / verify], [7.27 / 2,486.71 / 0.198], [10.42 / 4,037.30 / 0.256],
  [PiVoprf, 2-of-3], [DKG / 2-round eval + DLEQ], [33.68 / 26.40], [46.68 / 38.81],
  [PiBlindVc, blind request], [prove / verify], [52.65 / 19.79], [88.50 / 26.09],
  [PiBlindVc, disclosure], [prove / verify], [1,266.97 / 500.78], [1,566.74 / 623.23],
  [HD inventory, 64 children], [provision / proof verify], [2.17 / 0.04537], [1.72 / 0.03737],
  [HD linear module], [xpub / per-party share], [3.13981 / 3.23087], [4.03894 / 4.06379],
  [Policy, 3 signers, 64 entries], [4-round BDOZ barrier], [0.05014], [0.16928],
  [Migration, HASH160], [prove / verify (single run)], [5,560.84 / 1,448.33], [7,431.82 / 2,287.30],
), placement: top, scope: "parent", caption: [Protocol micro-benchmarks. All entries are in ms, including converted µs measurements. ML-DSA setup is the single-caller test key-generation helper, not the interactive 3-round DKG ceremony. Parallel FTS uses trusted-dealer test setup.]) <microbench>

The cached Jorts bench profile (`LEAN_SIG_BENCH_CACHED`) has $h=8$ and a 4,405 B wire signature, distinct from the height-6 aggregation inputs. Parallel FTS uses `CUSTODY_H10_W5`, depth 292, and approximately 2,544 B signatures in its 3-party trusted-dealer simulation.

Full RSS 2-of-3 SLH-DSA-SHAKE-128f keygen plus signing did not finish within a 100 s cap, nor an earlier 600 s cap, on either host. Full-hypertree FIPS 205 fast/small-set MPC signing remains minutes-scale and unmeasured to completion; correctness evidence comes from tests and Lean equivalence. The (3,4) SPDZ DKG benchmark aborted in `run_dealerless_dkg_seed32_gf256` with `PcgDepthOutOfRange { depth: 10 }`, outside the supported 14–16 range. No dishonest-majority DKG or signing timing is reported. Migration proof size is not reported because the harness estimate is unreliable.

== Interpreting the costs


Dishonest-majority Keccak is especially demanding. An unbatched permutation consumes 38,400 authenticated Boolean Beaver triples, corresponding to the nonlinear work across 24 rounds. A shallow cut can still invoke many such permutations. Batching 64 lanes or selecting the algebraic Poseidon2 route changes the practical cost structure; neither removes the need for secure preprocessing or authenticated openings.

Kernel speedups, aggregation compression, and height-independent scheduling address distinct costs; these measurements do not establish distributed-network throughput or production availability.

= Limitations and threat-model boundaries
== Trusted base and implementation scope
The 11 workspace crates and dedicated MIR crate use no external crates.io dependencies, relying on `core`, `alloc`, and `std`. This reduces dependency exposure but does not eliminate a trusted computing base. Outside the pinned assembly symbols analyzed by Tier 4, compiler and LLVM code generation remain trusted. OS entropy and hardware entropy interfaces remain trusted for key, nonce, and proof randomness. Filesystem durability and exclusive locking remain trusted for monotonic state.

The system is not a proof that Safe Rust alone guarantees cryptographic correctness or constant time. Memory safety, arithmetic correctness, transcript security, and leakage are separate properties. The isolated assembly and volatile zeroization paths require their own reasoning. Tier 2 covers a dedicated core, not whole-crate network/session translation; parity and KAT tests are the link for broader code paths.

Fiat–Shamir protocols in aggregation, migration, and credentials are analyzed in classical interactive-proof/ROM models, including `KeyedLazyRO`-style modeling. The selected hash and lattice primitives do not automatically upgrade these reductions to QROM. Tight compressed-oracle or online-extraction results for multilinear BaseFold and 219-repetition ZKBoo are not claimed. Their query/repetition settings target classical soundness; generic quantum Fiat–Shamir challenge search roughly halves the exponent.

== Leakage models and release artifacts
Architectural PC-NI, Mem-NI, and DOIT-NI do not model all microarchitectural leakage. Power/EM attacks, silicon errata, and speculation beyond the formal architectural observations are outside scope. The high-level Rust crates have no general binary-level NI theorem. A kernel's functional theorem and leakage theorem also remain separate obligations.

On x86-64, enabling the DOITM control requires privileged kernel support; a ring-3 application cannot simply assume that setting has been enabled. On AArch64, `msr dit, #1` can be used in EL0 where the relevant DIT feature is present.

Tier 4 covers SHA-256-pinned archive fixtures, not all artifacts bearing the same crate name. The fixture counts 954 / 191 and source-head audit counts 999 / 299 refer to different recorded builds. Release procedures must regenerate fixtures and rerun the corresponding analysis. The present model defects listed below remain limitations even when the bytes are correctly pinned.

== Persistence, primitives, and availability
Stateful Jorts, both few-time signature variants, and threshold ML-DSA nonce burning require durable write-ahead logging with `fsync` and exclusive lock fencing. `FsWalEpochLatch`, `FsWalEpochSink`, and `NonceBurnPersistence` embody this requirement. `InMemoryBurnLog`, VM snapshot rollback, or cloning state across signing sessions defeats monotonicity. The frontier cap is two uses; the parallel FTS implementation’s two-use budget conflicts with its intended leaf discipline (§8.5).

Compact FTS node widths limit generic preimage strength as stated in §2. The parallel-seeded SPN is a custom symmetric compression design. Its bijective S-box and formal degree growth are useful algebraic facts, but do not rule out all differential, structural, or implementation attacks. Davies–Meyer feedforward is used as one-way compression rather than as an invertible permutation.

Dishonest-majority security permits abort and does not promise liveness. Identifiable abort needs a correct accountability relation, authenticated participant identities, and the missing side conditions identified by the audit. Resource exhaustion and expensive full-hypertree evaluation remain operational concerns independent of whether the mathematical cut is correct.



== Known specification gaps
This paper describes the repository state of November 2026; the development is under active remediation, so individual items below may already be closed in later revisions. An internal audit identified the following gaps. The machine-checked statements must be interpreted with these qualifications.

- *Extractor meaning.* `WotsBackwardInversionWitness`, `Fips205ChainPreimageBreak`, `SumcheckSchwartzZippelHit`, and `MacKeyRecoveryWitness` have under-constrained return types. Merely obtaining such a value need not constitute the intended break. `extractFullHypertreeForgery` and `qsag_aggregate_unforgeability_reduction` are constructive definitions without separate soundness theorems. They are reduction skeletons, not proved full EUF-CMA reductions.
- *Aggregation statement.* `verifyAggregatedSignature` in `Aggregation.lean` abstracts away message, committee, and trace commitment, and uses a degree-3 round bound while Rust uses degree 8. Current results cover the abstract Sumcheck/fold/bitmap layer rather than the deployed verifier end-to-end.
- *Custom hash-signature correspondence.* `HashSigs.lean` and `tsw_baggy.rs` differ in wire magic, stateless leaf-index derivation, tag names, bit-window ordering, and FORS address layout. The bit-exact Lean/Rust correspondence is checked by KAT and differential tests for FIPS 205, not yet for the custom Corduroy and Baggy profiles.
- *Preprocessing correspondence.* RLWE OT is modeled at scalar rounding level without the negacyclic NTT, and the KOS check is modeled for a single column rather than the batched extension.
- *Binary semantics.* `ElfBinaryVerify.lean` has known carry-less multiplication helper defects, prefix/condition-code decoding simplifications, and SP/XZR conflation. Its NI theorems are relative to that current model.
- *Approval and release conditions.* `mac_before_open_blocks_faulted_cut_leakage` and `validThresholdApproval` have weaker-than-intended statements, missing membership or `Nodup` side conditions. The intended release and approval properties need strengthened premises and statements.

These gaps identify concrete obligations for strengthening the assurance story. They do not invalidate every local algebraic equality, but they prevent composing the existing results into an unqualified whole-system security claim. The FIPS threshold/single-signer equivalence and canonical Goldilocks equivalence between ISA models remain the clearest narrowly scoped bit-exact claims.

== Open implementation issues
An internal audit identified these seven issues; fixes are in progress.

- *Co-ZK migration:* head/share assignment lets one passive custodian reconstruct the legacy key with high probability; `co_zk_mpc` must not be used (single-prover proofs unaffected).
- *PCG preprocessing:* missing dense dual-LPN shares leave correlations far from uniform; dealerless DKG aborts at depth 10; not production-ready.
- *ParallelSeededFts:* SPN shares are broadcast before pending MAC checks, exposing faults; the epoch budget permits two signatures on one leaf against the intended design.
- *ThresholdMlDsa:* uncommitted public-key reveals risk rogue keys; responses precede aggregate rejection, leaking across attempts; subset consistency lacks a public proof.
- *PiVoprf / PiBlindVc:* no blinded-input well-formedness proof or server nonce latch, and dimension-384 lattice parameters are insufficient; insecure prototypes.
- *HD linear module:* cloned child shares reuse MAC keys and poison state, enabling MAC forgery after a fault; experimental.
- *Ring-LWE OT:* per-repetition challenge hashing permits cheap grinding; secret-indexed access may leak the receiver’s choice through cache timing.

The standalone SIMD kernels are not integrated into the protocol crates. Their measured speedups and scoped leakage results do not transfer to the portable protocol paths.

= Conclusion
QSAG's central architectural choice is to keep secret evaluation behind a small authenticated oracle boundary and perform public tree work outside MPC. This unifies several hash-signing profiles while leaving their work, state, and encoding costs visible. Aggregation addresses a separate bandwidth problem, and the custody suite supplies authorization, persistence, and migration interfaces around signing. The four verification tiers provide machine-checked statements at distinct abstraction levels, supported by differential tests and recorded measurements. Completing the extractor, arithmetization, preprocessing, and ISA-model connections is necessary before claiming end-to-end implementation security.

#heading(numbering: none)[References]
#block[
#set text(size: 7.6pt)
#set par(justify: false, leading: 0.4em)
#set enum(numbering: "[1]", spacing: 3pt)
+ NIST FIPS 202 (2015), SHA-3 Standard.
+ NIST SP 800-185 (2016), SHA-3 Derived Functions.
+ NIST FIPS 204 (2024), Module-Lattice-Based Digital Signature Standard.
+ NIST FIPS 205 (2024), Stateless Hash-Based Digital Signature Standard.
+ D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, "The SPHINCS+ Signature Framework", ACM CCS 2019.
+ J. Buchmann, E. Dahmen, A. Hülsing, "XMSS – A Practical Forward Secure Signature Scheme Based on Minimal Security Assumptions", PQCrypto 2011.
+ H. Zeilberger, B. Chen, B. Fisch, "BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes", CRYPTO 2024.
+ C. Lund, L. Fortnow, H. Karloff, N. Nisan, "Algebraic Methods for Interactive Proof Systems", J. ACM 1992.
#colbreak()
#set enum(start: 9)
+ M. Keller, E. Orsini, P. Scholl, "Actively Secure OT Extension with Optimal Overhead", CRYPTO 2015.
+ I. Damgård, V. Pastro, N. Smart, S. Zakarias, "Multiparty Computation from Somewhat Homomorphic Encryption", CRYPTO 2012.
+ R. Bendlin, I. Damgård, C. Orlandi, S. Zakarias, "Semi-Homomorphic Encryption and Multiparty Computation", EUROCRYPT 2011.
+ J. Furukawa, Y. Lindell, A. Nof, O. Weinstein, "High-Throughput Secure Three-Party Computation for Malicious Adversaries and an Honest Majority", EUROCRYPT 2017.
+ D. Boneh, E. Boyle, H. Corrigan-Gibbs, N. Gilboa, Y. Ishai, "Zero-Knowledge Proofs on Secret-Shared Data via Fully Linear PCPs", CRYPTO 2019.
+ E. Boyle, G. Couteau, N. Gilboa, Y. Ishai, L. Kohl, P. Rindal, P. Scholl, "Efficient Two-Round OT Extension and Silent Non-Interactive Secure Computation", ACM CCS 2019.
+ I. Giacomelli, J. Madsen, C. Orlandi, "ZKBoo: Faster Zero-Knowledge for Boolean Circuits", USENIX Security 2016.
+ L. Grassi, D. Khovratovich, M. Schofnegger, "Poseidon2: A Faster Version of the Poseidon Hash Function", AFRICACRYPT 2023.
+ D. Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly 26(4), 1988.
+ E. Fujisaki, T. Okamoto, "Secure Integration of Asymmetric and Symmetric Encryption Schemes", CRYPTO 1999.
+ R. Impagliazzo, L. Levin, M. Luby, "Pseudo-random Generation from One-Way Functions", STOC 1989.
+ R. Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols", FOCS 2001.
+ O. Reparaz, J. Balasch, I. Verbauwhede, "Dude, is my code constant time?", DATE 2017.
+ S. Ho, J. Protzenko, "Aeneas: Rust Verification by Functional Translation", ICFP 2022.
+ L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021.
+ P. Wuille, BIP-350 "Bech32m format for v1+ witness addresses", 2020.
+ Y. Ishai, E. Kushilevitz, R. Ostrovsky, A. Sahai, "Zero-Knowledge from Secure Multiparty Computation", STOC 2007.
]
