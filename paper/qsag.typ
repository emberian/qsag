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
    #text(size: 17pt, weight: "bold")[QSAG: Quorum-Switching Threshold Hash Signatures, Succinct Post-Quantum Aggregation, and a Four-Pillar Machine-Checked Custody Stack]
    #v(8pt)
    #text(size: 11pt)[The QSAG Authors]
  ]
  #v(10pt)
  #block(inset: (x: 18pt))[
    #set align(left)
    *Abstract.* QSAG (Quorum-Switching AGgregation / Quantum Succinct AGgregation) is a research preview; its mechanized results are statements about named specifications and artifacts, and §8 lists what they do not cover. The system combines threshold hash signing, signature aggregation, and custody protocols. A public/secret cut restricts secret evaluation to message randomization, chain starts and selected chain values, and FORS leaves; tree compression and target-sum grinding execute publicly. On this cut we build the _Pants_ suite: stateless Baggy with the Waistband cache of static upper-layer signatures, stateful Jorts guarded by a durable one-time-leaf latch (BeltLatch), two generalized $(t,n)$ quorum-switching modes, and the algebraic Corduroy hypertree. The aggregation layer, Hem, proves batch verification of algebraic hash signatures with a degree-8 Sumcheck [8] and a rate-escalating WHIR [7] opening over a quartic extension of Goldilocks, under five explicit query-accounting regimes. Custody components cover derivation, addresses, policy, migration, threshold ML-DSA [3], credentials, and accelerator provenance. Four assurance pillars distinguish Lean protocol specifications, extracted Safe-Rust MIR, ISA and compiled-ELF leakage analysis, and executable differential gates. We report measurements, name the regimes that rest on conjectured proximity bounds, and identify the open refinement, linkage, and reduction obligations. The development does not establish end-to-end implementation security or a total quantum-random-oracle reduction for its Fiat–Shamir protocols.
  ]
]

= Introduction
QSAG is a research preview. A proved model, a passing benchmark, and an integrated deployment guarantee are different results, and this paper keeps them apart (§8).

Threshold custody must preserve a signing key across failures, membership changes, and malicious participants while remaining compatible with external verification. Hash-based signatures are attractive because the public verifier can remain unchanged when secret evaluation moves into a committee. Their large trees, however, make a literal secure-circuit translation expensive. Tree height, signature size, nonlinear circuit depth, and online communication are different costs; reducing one does not eliminate the others.

QSAG organizes the problem around the point where a secret-derived value is already permitted to become public. Secret shares need not follow that value through every subsequent compression or authentication-path computation. This observation gives a reusable cut interface for stateless and stateful hash signatures. It also exposes the obligations that a malicious-secure implementation must satisfy before opening a value: preprocessing validity, authenticated evaluation, transcript binding, and irreversible state transitions.

Stateful signing adds a second problem. A one-time leaf must never open two codewords, yet a threshold system lets the adversary choose which signer set answers each request. The first reading of the name, _quorum switching_, refers to this: QSAG's stateful modes are designed so that changing the signer set cannot spend a leaf twice, either because each leaf belongs to exactly one committee or because every opening requires a latch certificate whose quorums intersect in an honest custodian.

A third problem is verification scale. Collecting many threshold signatures leaves a substantial bandwidth burden. The second reading of the name, _quantum succinct aggregation_, refers to Hem, an algebraic layer placed after signing. It proves a batch-verification relation and preserves signer-set accounting across disjoint merges. It is a distinct protocol with distinct assumptions, not an additional property of the threshold signature itself.

The last problem is the meaning of verification evidence. A theorem about a protocol specification, refinement of an extracted arithmetic routine, a leakage check over compiled bytes, and a differential test answer different questions. We use a four-pillar presentation to make those boundaries explicit. In particular, a constructive function returning an alleged break witness is not automatically a security reduction: the witness must express the intended break, and the function needs an adequate soundness statement.

*Contributions.*
- A post-quantum threshold hash-signing architecture with a four-oracle public/secret cut, a 256-lane replicated honest-majority engine, and authenticated dishonest-majority field computation.
- The Pants suite: Baggy and Waistband, Jorts and BeltLatch, the quorum-switching modes QS-A and QS-B, and Corduroy (§2).
- Hem, a $K$-to-$1$ aggregation implementation using 256-column multilinear traces, Sumcheck, WHIR over `GoldilocksExt4`, Steiner-deduplicated Merkle multi-proofs, and disjoint signer bitmaps, with a mandatory 128-bit Grover floor on query accounting (§4).
- A custody suite connecting derivation, address binding, policy authorization, migration, threshold ML-DSA, credentials, and accelerator provenance to explicit state and entropy obligations (§5).
- A four-pillar Lean 4.35 [23] development with no `sorry`, no custom axioms, and a `{propext, Quot.sound}` axiom allowlist, over a 13-crate Rust project with no external crates (§6). “Verified” denotes the stated specification, MIR, or leakage-model property within its scope; it does not denote whole-system security.

== Mechanisms and threat models
*Related work.* CNF replicated sharing trades local simplicity for combinatorial storage. Paillier/MtA threshold ECDSA distributes an arithmetic signing relation; generic MPC evaluation of hash signatures instead hides the full hash circuit. Our cut exposes only authorized outputs and leaves tree work public. Hash-signature designs build on stateless hypertrees [5] and stateful Merkle trees [6]; the checksum-free target-sum Winternitz encoding follows WOTS+C [28]. SNARK-based signature aggregation proves batch verification through a separate proof system; Hem uses Sumcheck [8] with a WHIR [7] Reed–Solomon proximity argument. MPC-in-the-head [25] supplies the distinct migration and credential proof mechanism. The honest-majority engines check multiplications with distributed zero-knowledge proofs over fully linear PCPs [13, 27].

*Sharing models.* The specialized 2-of-3 replicated path serves the honest-majority case with abort. The general SPDZ [10]/BDOZ [11] path addresses dishonest-majority computation with abort; identifiable-abort claims additionally require attribution evidence and adequate membership conditions. Subfield-embedded Shamir sharing makes the per-party key share independent of the CNF family size, at the cost of authenticated multiplication and preprocessing.

*Fiat–Shamir.* The aggregation, migration, credential, and preprocessing proofs are made non-interactive by hashing. Several parameters are now sized against generic quantum search over challenges (a square-root loss), and `ConcreteSecurityBudget.lean` mechanizes hybrid-argument query bounds in the style of [29, 30]. Sizing a challenge space is not a reduction: no multi-round QROM extraction theorem is claimed for any of these protocols.

*State.* Stateful signing, few-time signatures, nonce burning, and policy counters require that a process crash never turns a consumed epoch or nonce into a reusable one. The design rule throughout is bind durably before any share is opened; a crash may lose a leaf but must not reuse one.

= Cut-the-Hash and the Pants suite
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
    align(center)[↓\ #smallcaps[Durable bind · verify barrier · open]\ ↓],
    panel([#smallcaps[Public reconstruction]\
      $T_ell$ compression · FORS roots · Merkle $H$\
      $H_"msg"$ and target-sum grinding on authorized outputs]),
  )
}, caption: [The cut releases permitted outputs after authentication; secret seeds remain shared.])

== Depth, work, and chain tabulation
The tabulation bound is
$ N_"chain" <= 1+w $
secret hash evaluations per tabulated chain: one PRF and at most $w$ chain steps. `buildMpcChainTable` includes one further step whose output is discarded; the retained positions need only $w$ evaluations. The selected opening has sequential hash-call depth $1+s<=w$: 4 for the custom $w=4$ setting, and 16 for FIPS 205 [4]. A hash call can itself contain many nonlinear permutation rounds.

The benefit is independence from the height of the public tree above the cut. It does not assert that the number of leaf chains is independent of height, that a sponge evaluation is a single multiplication, or that preprocessing is free. Batching many independent secret operations can reduce their sequential dependency without reducing their total number.

Every WOTS public-key compression $T_ell$, FORS root compression, and binary Merkle internal hash executes in plaintext after the cut. So do $H_"msg"$ and counter grinding. These operations depend only on public inputs and already opened cut digests.

The custom profiles use WOTS+C [28] with $w=4$: a 256-bit digest is read most-significant-first as 128 base-4 digits, and a digest is valid when
$ sum_(j=1)^(ell_1) d_j = S,
quad S = floor((ell_1(w-1))/2) = 192, $
for $ell_1=128$. No checksum chains are needed: with a fixed sum, no valid digest dominates another digit by digit (`wotsC256_strict_incomparability`). The signer grinds a public counter until the sum holds; the preset `WotsCParams::V128` forces no digit to zero, so a forgery on a signed leaf needs a second preimage of the full 256-bit digest. `tooth_wotsc_without_target_sum_forges` shows that dropping the sum check admits a forgery with one public hash evaluation.

== Parameters and encoding boundaries
@params gives the FIPS 205 SHAKE geometries and the custom profiles. The FIPS sizes are standard signature encodings. A dash for a custom wire size means no common byte count is asserted here. Poseidon2 [16] is the algebraic hash used by the aggregation profiles. The two Hem rows are the geometries that `qsag-agg` arithmetizes; they differ from the custody profiles of the same family and are not interchangeable with them.

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
    [Jorts], [32], [16], [1], [16], [—], [—], [4], [$2^16$], [—], table.hline(),
    [Hem / Jorts], [32], [6], [1], [6], [—], [—], [4], [$2^6$], [—],
    [Hem / Corduroy], [32], [64], [16], [4], [8], [32], [4], [$2^20$], [—],
    table.hline(stroke: 0.6pt),
  )),
  caption: [Signature geometries; $n$ is node bytes. Custom rows are `CORDUROY_CUSTODY_128`, `BAGGY_TSW_128F`, and `JORTS_POSEIDON2`, with $ell_1=128$ and $S=192$; Baggy's FORS+C opens $k-1$ trees. The Hem rows are the `JortsPoseidon2` and `CorduroyPoseidon2` aggregation profiles. Encodings differ from FIPS 205.],
) <params>

== Baggy and Waistband
Baggy (`BaggySha3`, `BaggyPoseidon2`) is the stateless member of the suite: a hypertree of $d$ layers of height-$h'$ subtrees over WOTS+C leaves, whose bottom leaf signs a FORS+C public key. FORS+C grinds a public counter until the index of the $k$-th tree is zero and omits that tree. The pure-hash path runs on the 256-lane replicated Keccak engine of §3.

Signing (`baggy_sign_mpc`) has three phases. The randomizer $R$ is derived under MPC from the shared PRF key and the message alone, so a signer that aborts after seeing $R$ obtains the same $R$, leaf, and FORS indices on every retry. Because $R$ fixes every address, the FORS leaves and the chains of every subtree on the path are then evaluated together, level by level: one PRF level and three $F$ levels in total, independent of the number of layers. A single barrier verifies every gate of that sweep before chain endpoints and leaf hashes are opened; subtree roots and the digits they imply are computed in public, and the selected chain nodes are opened in a second round.

Upper-layer leaves always sign the same child root, so they always reveal the same digits. Waistband (`WaistbandCache`) exploits this: for the top $L$ layers it stores the public leaves of subtrees and the deterministic WOTS+C signatures of their leaves on child roots, with authentication paths. A cached signature removes that layer from the sweep. Everything in the cache is public, and it is _static_: it never holds a message-binding leaf, so it cannot pre-commit a one-time key to a future message.

A cached value decides which message an uncached layer above it signs, so a wrong entry could make a static key open a second codeword. Three checks therefore precede every chain-node opening: the cache is bound to one `BaggyKeyBinding` (seed, root, and a digest of every parameter); every cached entry on the path is re-verified against its stored roots up to $"PK.root"$; and a first-signed ledger (`FirstSignedLedger`) records the child root each static key first signed. `tooth_corrupted_intermediate_waistband_opens_second_ancestor_codeword` exhibits the attack these checks exclude.

“Stateless” here means no signing-leaf exhaustion counter. It does not make the system state-free: concrete security still depends on a finite signature budget, and MPC preprocessing, the first-signed ledger, and custody resources keep their own persistence requirements.

== Jorts and BeltLatch
Jorts is the stateful member: one Merkle tree of height $h$ over $2^h$ one-time WOTS+C leaves, each signature spending one leaf (an _epoch_). `JortsSha3` runs on the replicated Keccak engine; `JortsPoseidon2` uses the authenticated-share Poseidon2 engine. All three signers take part in every signature; the threshold is on the secret sharing, not on attendance.

Every opening is gated by BeltLatch (`belt_latch.rs`). Before any chain share is opened, each signer (i) writes $("epoch", "digest", "salt", "digits")$ through a durable write-ahead log and only then updates memory, (ii) on retry replays the persisted record and refuses a different digest or a different salt, and (iii) exchanges an authenticated echo of the binding with both peers. Opening routines consume the resulting `OpenPermit`s. Echoes carry a cSHAKE256 [2] MAC under a key held by exactly one pair of signers, so the third cannot forge an echo between the other two. The retry salt is a joint coin drawn after the message is fixed. A fresh bind is accepted only within `MAX_EPOCH_JUMP` $=64$ of the high-water mark, which bounds how many leaves a malicious proposer can burn per request. A signer holding a record its peers lack cannot prove the salt was a coin flip; the remedy is to burn the epoch, never to adopt a claimed salt.

Two modes share the latch. Mode 3A evaluates the 128 chains of the epoch's leaf online. Mode 3B evaluates and verifies the chains of the next leaves ahead of time and keeps them shared, so online signing is the salt coin, the latch echo, and one opening round. The staged window lives in memory only: after a crash the epoch is re-signed with Mode 3A under the same latched salt, which opens the same nodes. Key generation evaluates every leaf under MPC ($2^h dot 128 dot 4$ lane-permutations), a long offline ceremony at production heights.

The filesystem latch is a two-slot authenticated snapshot under a permanent genesis lock (`durable_ledger.rs`), and multi-resource releases are sequenced by `FsCeremonyJournal`. `PosixCrashWal.lean` models this storage path against kernel-volatile state, a drive write-back cache, and torn sector writes, with `flock(2)` ownership keyed by open file description rather than process; its main result is `reserve_before_sign_multi_crash_epoch_uniqueness`.

== Quorum switching: QS-A and QS-B
`qsag-quorum` generalizes Jorts to $(t,n)$. A signer set never evaluates a hash on secret data online: staging stores, for every chain of every leaf, a sharing of each of the three secret chain states, and signing opens the share of the state selected by the digit. Whoever combines the openings hashes each node forward to the public chain end, so a wrong share is detected without authenticated sharing. The remaining risk is the one in the name: corrupted custodians joining different signer sets to spend one leaf twice.

*QS-A (`CommitteePartitionedJorts`).* The leaves are split into $binom(n,t)$ disjoint ranges, one per $t$-subset of the custodians, and a committee's chain states are shared additively $t$-of-$t$ among its members only. Any $t$ online custodians form exactly one committee and sign from its range. With at most $t-1$ corruptions every committee contains an honest member whose durable latch binds each leaf to one digit vector, and no other set holds shares of that leaf; no assumption on $n$ is needed. The cost is twofold. Leaf capacity is divided by $binom(n,t)$, and the leaf index identifies the committee: QS-A is _committee-revealing partitioned custody_ (`qs_a_leaf_index_identifies_committee`). Safety is with abort; a corrupt online member can withhold its share.

*QS-B (`BftShamirJorts`).* One global tree; every chain state is $(t,n)$-Shamir shared bytewise over $FF_(2^8)$ with an independent polynomial per chain step, so a custodian stores 12,288 bytes per leaf for every $(t,n)$. A custodian opens its shares of a leaf only against a `LatchCertificate`: acknowledgements of one binding from $q$ custodians with
$ 2q > n+f. $
Two certificates for one leaf then share at least $f+1$ acknowledgers, hence an honest one, and an honest custodian acknowledges one binding per leaf (`beltLatch_quorum_intersection_global_uniqueness`). Liveness of the latch needs $n >= 3f+1$ (`beltLatch_safe_and_live_iff_n_ge_3f_plus_1`); for example $n=7$, $f=2$, $q=5$. The signing threshold $t$ and the latch quorum $q$ are separate requirements. The pre-stepped shares are self-verifying and carry no MACs; the certificate does, one per verifying custodian under pairwise keys. `tooth_under_threshold_latch_quorum_switches_double_sign` shows that a smaller quorum admits a double signature.

Two qualifications apply to both modes. Staging (`stage_committee_partitioned`, `stage_bft_shamir`) is a dealer that derives every chain from one seed; in a deployment that role is a multi-party computation which this crate does not provide. And the single-process drivers exist for tests and measurements; `party_node` runs one custodian per thread over a framed transport whose MAC supplies authenticity but no confidentiality.

== Corduroy
Corduroy is the stateless target-sum hypertree instantiated with the Poseidon2 tweakable hash and the `CORDUROY_CUSTODY_128` geometry, signed by the authenticated-share Poseidon2 engine. It adds no new cryptography to the suite; it is the algebraic counterpart that Hem can arithmetize. The aggregation profile `CorduroyPoseidon2` uses the larger geometry of @params ($k=32$, $a=8$ FORS over a $d=16$, $h'=4$ hypertree).

== Bit identity and static upper layers
The strongest bit-exact result concerns FIPS 205. The declarations `thresholdSlhSign_eq_slhSignInternal` and `rss_thresholdSlhSign_eq_slhSignInternal` identify threshold evaluation with the single-signer specification, assuming the oracles compute the four cut functions (`MatchesKey`); the RSS instantiation discharges this premise in the specification. Together with differential and known-answer tests linking `Fips205.lean` and `fips205.rs`, this supports the stated threshold/single-signer equivalence for all six SHAKE sets. Pure and prehashed message framing are separated by `pure_vs_preHash_disjoint` and `preHash_downgrade_rejected`.

The equality is a _matched-input_ claim: for the same key, parameters, leaf and message, and hedging seed or randomizer, successfully evaluated threshold bytes equal the single-signer bytes. The same form of claim is made for Baggy, 2-of-3 Jorts, and QS-B. It does not assert that separate entropy policies induce the same output law, that outputs conditioned on a malicious abort are distributed like unfiltered standalone outputs, or that timing hides participation. QS-A has only a same-committee-schedule reference (`qs_a_single_signer_equiv_given_same_leaf_schedule`) and cannot hide the committee.

At the custom-specification level, `evalCutBatchSignMpc_eq_evalSingleSign`, `rss_thresholdPqHashSign_eq_evalSingleSign`, and `shamir_poseidon2_thresholdSign_eq_evalSingleSign` express corresponding cut-evaluation equalities. Static upper-layer hashing omits external $R$ and $mu$ from `th_hash_internal_node`, so upper layers grind deterministically for fixed internal inputs; `stateless_leaf_reuse_identical_wots_chains` expresses the consequence that at most one codeword is revealed for a fixed internal keypair. This property does not authorize reuse of a stateful leaf for a different external message; the latch is responsible for that boundary.

== Few-time signatures
`FrontierSumFts` maps a randomized public message digest into a decorated prefix-free binary-tree frontier. A frontier of length $L$ and height bound $h$ is paired with chain offsets whose sum is $S$. The exact ranking construction factors its counting problem as
$ M(h,w,L,S) = N(h,L) dot D(L,S). $
`frontierAntichain_paths_prefixFree` checks the frontier property, and `frontierSumFts_rank_unrank_bijection` checks the ranking correspondence. `U384` arithmetic supports exact ranking. Rank and unrank operate on public digests; secret expansion is straight-line and guarded by a monotonic use latch with a durable burn journal.

#figure(tbl((1.5fr, auto, auto, auto, auto, auto, auto, auto),
  [Profile], [B], [$n$], [$h$], [$w$], [$L$], [$S$], [Uses], table.hline(),
  [Compact514], [514], [16], [14], [5], [31], [62], [1],
  [Compact770], [770], [16], [15], [5], [47], [118], [2],
  [Compact1314], [1,314], [16], [15], [5], [81], [162], [2],
  [Full256Bit], [2,338], [32], [8], [5], [72], [144], [1],
), caption: [`FrontierSumFts` wire profiles; $n$ is node bytes and Uses is the enforced `max_safe_uses`.])

The compact profiles use 16-byte nodes and therefore cap generic node-preimage strength at 128 classical bits or 64 Grover bits. The 32-byte-node `Full256Bit` profile has a 256-bit rank and permits one use. These are node-width and rank-width bounds, not a substitute for a complete few-time signature security analysis; `ConcreteSecurityBudget.lean` records the corresponding fiber-size statements, including a negative witness for a 122-bit rank.

Experimental `ParallelSeededFts` derives independent leaf-chain work from a shared root seed, opens authenticated endpoints, and constructs a height-$h$ Merkle tree publicly. Its compression primitive is a 48-round $x^7$ SPN over $FF_(2^128)^2$ with Davies–Meyer feedforward. The S-box is bijective because $gcd(7,2^128-1)=1$; the feedforward compression is not thereby a bijection, and algebraic degree growth alone is not a cryptanalytic security argument. The reference schedule reports
$ D_"parallel" = 48(1+w)+8 = 296 $
for `CUSTODY_H10_W5` ($h=10$, $w=5$, $L=68$, $S=136$, 1,024 epochs), the added term accounting for intermediate and output MAC barriers. `parallelSeededFts_mpc_depth_independent_of_height` proves the structural height invariance. The current implementation includes every masked power opening in the committed MAC check before any share is released, caps each leaf at one signature, and counts uses through the mandatory durable journal (`FtsEpochGuard` in the extracted core).

= Sharing, preprocessing, and release ordering
== Replicated sharing and the binary tower
In CNF replication accounting, a general threshold construction carries $binom(n,t-1)$ shares, with $binom(n-1,t-1)$ active terms per party. At $n=15$, $t=8$, these are 6,435 and 3,432. Such replication is useful for small committees but does not scale like a single field share.

The honest-majority path is `Rss256Engine`, a 256-lane bitsliced 2-of-3 replicated Keccak-f[1600] engine [12]: at most one corrupted party, security with abort. One _wave_ evaluates up to 256 independent permutations; bit $i$ of every lane's state lives in one 256-bit plane, so each of the 1,600 $chi$ ANDs per round is one plane operation. Nothing may be opened until a verification barrier has accepted every gate evaluated so far. The barrier fixes a hash of all gate messages, runs a commit-then-open coin flip bound to that transcript, and then checks the products with a distributed zero-knowledge proof [27] over $FF_(2^128)$ under two independent challenges, using carry-less multiplication kernels (`PCLMULQDQ`, `VPCLMULQDQ`, `PMULL`). Any failure poisons the engine permanently. `BaggyAndRss256Security.lean` proves exact one-corruption view privacy (`rss256_one_corrupt_perfect_view_privacy`), two-challenge soundness with error at most $(2 deg)^2 slash 2^256$ (`rss256_post_wave_two_challenge_bgin19_soundness`), and absorption of the poisoned state (`rss256_sticky_poison_terminal_absorption`), each paired with a negative witness: a mis-assigned mask key that leaks an AND wire, a challenge revealed before the wave, and a non-sticky error path.

The arbitrary-threshold path uses Shamir sharing embedded in a Wiedemann tower [17]:
$ cal(T)_0 = FF_2, quad
  cal(T)_1 = cal(T)_0[x_0] slash (x_0^2+x_0+1), $
$ cal(T)_k = cal(T)_(k-1)[x_(k-1)] slash
  (x_(k-1)^2+x_(k-2)x_(k-1)+1). $
The construction reaches $cal(T)_3=FF_(2^8)$ and $cal(T)_7=FF_(2^128)$. The former supports up to 255 distinct nonzero evaluation points. `embedTowerChain_injective` and `towerMul_inv` state the relevant algebraic properties. A participant assigned $x_i=0$ would receive the secret directly, so nonzero-point validation is a confidentiality condition (`zero_eval_point_leaks_secret_term`).

The shared key representation is 32 bytes per party independently of the CNF family size. This is a statement about key-share size, not about total per-party memory: bitsliced state, preprocessing pools, authenticated multiplication, and transcripts add costs.

== Algebraic permutations and preprocessing
The algebraic route uses width-12 Poseidon2 over Goldilocks,
$ p=2^64-2^32+1. $
A permutation uses $4 dot 12+22 dot 1+4 dot 12=118$ power-7 S-boxes. With preprocessed authenticated powers of a random mask $r$, opening $y=x+r$ permits local evaluation of
$ [x^7] = sum_(k=0)^7 binom(7,k)(-1)^k y^(7-k)[r^k], $
supported by `power7BinomialEval_eq_sbox7`. One online opening round per S-box assumes valid preprocessing and authenticated masking. Canonical output conversion remains significant: the documented dual-adder conversion consumes 760 Beaver triples per unrevealed 256-bit chain step.

*Base OT.* Base OT uses the Ring-LWE ring
$ R_q = ZZ_(12,289)[X] slash (X^1024+1) $
with CBD noise $eta=1$; the rounding bound is
$ norm(e_1 r_c-e_2 s_R+e_3)_infinity <= 2,049 < 3,072 = floor(q/4), $
and `rlwe1024_ot_decrypt_exact` checks exact decryption. A Fujisaki–Okamoto [18] re-encryption check binds the seed and auxiliary randomness. The receiver's proof of well-formedness is an OR-Sigma protocol whose challenge is a signed-monomial ring element $plus.minus X^(p_0) plus.minus X^(512+p_1)$ carrying 20 bits; 13 repetitions are hashed _jointly_ from one transcript, giving
$ 13 times 20 = 260 $
challenge bits, sized so that generic quantum search over the joint challenge costs about $2^130$. Earlier per-repetition hashing, which permitted cheap grinding, is removed, and receiver-choice selection is constant-time at source level. `LatticePreprocessingFull.lean` models the ring, the challenge map (injective, nonzero, $ell_1$-norm 2), and the joint verifier `verifyJointOrSigma`. Widening the challenge addresses generic search only; it is not an extraction theorem for the signed-monomial relation (§8).

*Extension and correlations.* The KOS extension [9] is interactive: column commitments precede an independent challenge and then a consistency proof (`kos_interactive_check_sound`; `kos_single_bit_does_not_pin_key` records the limit of that statement). A seeded 2-universal leftover-hash combiner [19] maps 384 input bits to 128. The PCG [14] is a dense dual-LPN construction (`pcg_dense.rs`, wire version 3): 64 regular-noise GGM trees of depth 14 or 15 with 256-bit nodes, a dense expand-accumulate parity-check matrix so that individual shares and reconstructed masks are computationally uniform, and an active single-point COT consistency check run twice with independent weights, which a fixed discrepancy passes with probability about $2^(-226)$ per directed pair at depth 15. Seeds are single-use (`SeedBurnTracker`). For $n >= 3$ parties, products use authenticated KOS/MASCOT [32] multiplication with batch sacrifice; `spdz_triple_sacrifice_sound` and `pow7_sacrifice_sound` are the corresponding specification statements. Dealerless preprocessing does not mean assumption-free preprocessing: Ring-LWE, the pseudorandom generators, the correlation checks, and the specification-to-code connection all remain in the argument.

== Booleanity, release ordering, and abort
In characteristic 2, a field element is Boolean exactly when
$ b^2+b=0. $
`towerFrobenius_eq_zero_iff_bit` characterizes this property. An unauthenticated check is insufficient: `frobenius_unauthenticated_offset_break` demonstrates how a malicious offset can cancel the residual. The constructive `dkg_frobenius_booleanity_soundness` belongs to the authenticated argument.

Cut opening follows the order *commit → MAC-verify → open*. The adversarial result `open_before_mac_leaks_faulted_cut` explains why an eventual abort is too late if a faulted secret-dependent value has already been exposed. Release ordering is therefore a privacy condition as well as an integrity condition, and the same rule recurs as the barrier of §3.1, the latch of §2.5, and the pre-open zero test of §5.

The BDOZ path uses paired Tower128 MACs, while the algebraic path uses `GoldilocksExt2` MACs. The documented model bounds are $2^(-256)$ and $p^(-2)<2^(-127)$, respectively (`spdz_batch_mac_soundness`, `bdoz_2lane_mac_soundness`). An adversarial party can still deny service; dishonest-majority security is expressed with abort, not guaranteed output delivery. `extractBdozCheaterOrValid` constructs a check result and `honest_party_never_slashed` shows an honestly formed opening passes; `protocol_realizes_idealTsig_id_abort` assumes culprit identification as a hypothesis. Neither theorem proves attribution soundness.

== Key lifecycle
`dkg.rs` implements a two-round commit-then-open DKG, refresh, and resharing from $(t,n)$ to $(t',n')$ without reconstructing the secret; `reshare_preserves_public_key_and_refreshes_degree` expresses preservation of the public key with a refreshed polynomial. Old-share erasure is part of the transition: retaining historical and current material changes the compromise model. For the 2-of-3 stateful path, `stateful_jorts_crash_retry_idempotent` permits an identical retry, `stateful_jorts_equivocation_rejected` refuses a different message at a consumed epoch, and `epochLatch_trace_no_equivocation` extends the property over a trace.

= Hem: succinct $K$-to-$1$ aggregation
== Trace and field
`qsag-agg` encodes parallel verifications of `JortsPoseidon2` or `CorduroyPoseidon2` signatures into a 256-column multilinear trace over Goldilocks: 512 rows per Jorts signer and 8,192 per Corduroy signer, so a shard holds at most 128 or 8 signers under the 24-variable commitment bound. The columns carry one Poseidon2 permutation per row (input, 118 S-box outputs), a 44-limb machine state before and after the step, and auxiliary cells; a fixed per-signer program of step opcodes drives digest decomposition, chain walks, endpoint compression, and Merkle paths.

All challenges lie in `GoldilocksExt4`,
$ E = FF_p [v] slash (v^4-7), quad abs(E) = p^4 > 2^(255.99), $
built as a quadratic extension of `GoldilocksExt2`. The Lean model proves it a commutative ring without zero divisors with inverses (`mul_inv_cancel`) and contrasts its error denominators with those of the quadratic extension it replaced (`ext4_error_denominator_bound`, `ext2_error_denominator_cliff`). `Digest5` packs a 256-bit digest as four 56-bit limbs and one 32-bit limb, all canonical below $p$; `digest5FromBitVec256_injective` rules out collisions from reducing a wider digest modulo the field.

== Argument
Zero-residual satisfaction of the row constraints is proved by a degree-8 Sumcheck (a degree-1 equality kernel times degree-7 gates) with a random-$tau$ equality point and $gamma$-batched constraint columns, plus an ungated inter-row shift claim linking each row's next state to its successor's previous state. The resulting column evaluations are opened with WHIR [7]: after an exact hypercube-to-monomial transform, each stage folds up to six variables and re-encodes the folded witness at an escalating Reed–Solomon blowup $B = 4, 16, 64, 256$, which keeps intermediate domains bounded. Every committed oracle is pinned at a fresh out-of-domain point of $E$ before its Sumcheck challenges are squeezed, and stage queries fold into shift claims batched into the next stage. `prechallenge_fold_forgery_attack` and `terminal_check_omission_unsound` record, in the abstract model, why commitment must precede challenge and why the terminal relation must be checked.

Commitments are Merkle trees over a precomputed cSHAKE256 midstate with 4-way batched Keccak; openings are `CanopyMultiProof`s, canonical bottom-up multi-proofs in which shared ancestors appear once. The Lean verifier `verifyCanopyMultiproof` has an exact sibling count determined by the index set (`verifyCanopyMultiproof_exact_sibling_count`), and two distinct accepted openings of one index set yield an explicit hash collision (`verifyCanopyMultiproof_binding`). Each stage carries a 16-bit transcript proof of work, which raises grinding cost and is not counted as soundness beyond the stated per-round budget.

== The five-regime ladder
Query counts are not chosen ad hoc; `WhirSecurityRegime` fixes them per stage as a function of $log_2 B$ (@regimes). Two families appear. The `Habr24*` regimes take the per-query agreement to be $rho$, a _conjectured_ proximity bound. The `BciksJohnson*` regimes use the proven Johnson bound $sqrt(rho)+eta$ [26], at roughly twice the queries. Within each family, the QROM regimes double the classical bit target so that generic quantum search over a round's challenges retains 128 bits.

#figure(tbl((2.3fr, 1.9fr, 1.6fr, 0.8fr),
  [Regime], [Queries per stage], [$q$ at $B=4,16,64,256$], [Round bits], table.hline(),
  [`Habr24Classical128`], [$ceil(112 slash log_2 B)$], [56, 28, 19, 14], [128 / 64],
  [`Habr24Interactive128`], [$ceil(128 slash log_2 B)$], [64, 32, 22, 16], [144 / 72],
  [`BciksJohnsonClassical128`], [$ceil(256 slash log_2 B)+1$], [129, 65, 44, 33], [144 / 72],
  [`Habr24Qrom128` (default)], [$ceil(256 slash log_2 B)$], [128, 64, 43, 32], [272 / 136],
  [`BciksJohnsonQrom128`], [$ceil(512 slash log_2 B)+1$], [257, 129, 87, 65], [272 / 136],
), placement: top, scope: "parent", caption: [Hem query-accounting regimes. Round bits are the classical query-plus-proof-of-work budget and its Grover half, as returned by `classical_fs_round_bits` and `qrom_grover_round_bits`. The fourth stage ($B=256$) exists only for 23 or 24 variables.]) <regimes>

The aggregate verifier `verify_aggregate` accepts only regimes satisfying `meets_qrom_128_floor`, that is, the last two rows; the weaker regimes are reachable only through `verify_aggregate_with_regime` with an explicit expectation. The regime is bound into the wire format and a merge requires both children to share it.

These numbers are _query accounting_, and the distinction matters. The 272-bit budget leaves eight Grover bits of slack for a union over rounds; it does not include extension-field, folding, and out-of-domain errors, list sizes, commitment binding, or the loss of a multi-round Fiat–Shamir reduction. “Unconditional” in the Johnson regimes describes the coding-theoretic proximity bound and nothing else. The Lean model checks the schedule and its denominators (`whir_regime_query_counts`, `whirStageSchedule_deployed`) and takes the per-query agreement bound as an input: it proves no proximity-gap or list-decoding statement.

== Merging
`SignerBitmap` prevents a merge from counting the same signer twice (`overlapping_merge_rejected`, `merge_aggregates_disjoint_sound`). Inside a shard batch the opening is accumulated: one prover commits every shard under one tree and settles all evaluation claims with one WHIR opening. Across batches nothing is compressed. `merge_aggregates` takes two finished proofs; the merging party holds no witness and the crate has no recursive verifier circuit, so a branch node is concatenation. It enforces statement structure only: disjoint signer sets, a common regime, a canonical child order, and depth at most `MAX_MERGE_TREE_DEPTH` $=16$. Verification checks every leaf. Merge trees are therefore an accounting mechanism, not recursive proof composition, and proof size grows linearly in the number of shard batches.

== Mechanized coverage
`SuccinctAggregationIop.lean` (11,677 lines) formalizes four layers of the implementation. For the packed four-limb signature engine it proves completeness (`aggNativeSig_completeness`) and a Type-valued extraction of a hash break from a forgery (`aggNativeSig_wots_merkle_soundness`), with the FORS and 1-based XMSS node addressing of the Rust verifier (`forsNodeAddr_injective`, `tooth_fors_cross_tree_transplant_rejected`). For the 256-column step table it transcribes the column layout, the fixed program, and the constraint classes, and proves the permutation group exact (`stepOp256_groupA_exact`), the shift constraints (`stepOp256_shift_iff`), and root-count bounds for the random-$tau$ and $gamma$-batched claims (`stepOp256_ext4_random_tau_sound`, `stepOp256_gamma_roots_le`). For a separate row-committed layout, constraint vanishing is equivalent to signature validity (`trace_satisfies_constraints_iff_all_k_sigs_valid`).

The two layouts are not yet connected, and the gap is specific. The module proves completeness of the step table for inactive slots only (`stepOp256_inactive_table_complete`). It does not prove that an honest signature yields a satisfying table for an active slot, nor that a satisfying table yields an accepted signature: the Rust trace filler `populate_active_signer_rows` has no proved Lean counterpart, and the simulation between the 44-limb step machine and the verifier is open. Instantiating the batching bound with the deployed opcode offsets, the transcript binding of the opening, and the merge tree are likewise open. The older `Aggregation.lean` remains an abstract Sumcheck/fold/bitmap layer, and its `qsag_aggregate_unforgeability_reduction` remains a reduction skeleton.

= Custody and credentials
*`qsag-hd`.* Roots, child rekeys, MAC keys, opening masks, and inventory child seeds are produced by the custodians themselves from a one-time subset-seed ceremony, in an honest-majority model ($n >= 2t-1$, at most $t-1$ static corruptions, security with abort). `PiHdCommitInventory` provisions a Merkle-committed watch-only table of independently generated child public keys. Experimental `PiHdLinearModule` supports local derivation under $bold(t)=bold(A)bold(s)_1+bold(s)_2 mod 8,380,417$ with public CBD2 shifts; chain codes are derived from secret seeds, each child receives fresh MAC keys, and a persistent poison journal quarantines a family after a fault. This is bounded related-key derivation, not a rerandomized Module-LWE reduction, and depth bounds do not establish ML-DSA compatibility. Watch-only batch enrollment can reconstruct selected child seeds, though not parent or subset seeds.

*`qsag-addr`.* The address layer uses a strict 67-character Bech32m [24] codec with a three-character prefix and checksum constant `0x2bc830a3`. Versioned cSHAKE256 and Poseidon2 commitments bind script and public-key identity. `SingleOrThreshold` avoids encoding whether the key is held by one signer or a committee, and `HybridPinnedEnvelope` pins the post-quantum key rather than accepting one carried by an adversarial envelope (`bech32m_rejects_bech32_and_detects_single_subst`). Address parsing is not an ownership proof, and address checks do not establish that an external system selected the intended trust anchor.

*`qsag-policy`.* A pairwise 2-lane BDOZ guard checks chain and suite identifiers, recipient allowlists, per-transaction and rolling velocity limits, timestamp windows, self-approval restrictions, and amount-dependent quorum rules inside a committed MAC barrier, and only then releases an `AuthorizedSignReleaseToken`. Initiator authentication is on by default, and replay protection uses monotonic nonce and session watermarks carried in an authenticated ledger snapshot. That snapshot is not a storage transaction: a MAC cannot detect rollback of both the checkpoint and its external generation fence, so callers must persist it atomically and fence its generation in trusted monotonic storage. Real-time caps additionally require an authoritative clock or agreed logical epochs.

*`qsag-migrate`.* Migration binds knowledge of a legacy spending key to a target `QsagAddress` and campaign nullifier, covering HASH160, Taproot x-only, Ethereum Keccak20, and SLIP-0010 Ed25519 relations, with 438-repetition mixed-domain ZKBoo [15]:
$ (2 slash 3)^438 < 2^(-256), $
that is, 256 classical bits and 128 bits against generic quantum search over the challenge; no QROM extraction theorem is claimed. Proofs are transparent and non-succinct, and each requires fresh 256-bit entropy. The distributed prover `co_zk_mpc` is now an actively checked three-custodian protocol over confidential authenticated pairwise channels: every Boolean AND and prime-field multiplication is batch-verified under coin-flipped challenges, using inner-product instances with a randomized base-case sacrifice in the style of [13], before any wire opening, conversion difference, view commitment, public output, or challenged view is reconstructed; circuit outputs are zero-tested before opening (`all_outputs_zero`), and a faulted tape aborts with `Error::InvalidTape`. It tolerates one corrupted custodian with non-identifiable abort; two colluding custodians reconstruct the witness. `ActiveMigrationZeroTest.lean` (3,018 lines) formalizes the curve-order semantics, the replicated 64-lane sharing, and the zero-test and tape barriers, with negative witnesses including `tooth_premature_residual_open_recovers_spending_key`: opening the residual before the zero test lets 256 aborted single-bit-fault queries recover the key. Privacy on the abort path is conditional on that ordering.

*`qsag-cred`.* Threshold ML-DSA is enabled for ML-DSA-44 only and produces signatures accepted by an ordinary FIPS 204 verifier, with $n <= 5$, privacy threshold $t >= 2$, and $n >= 2t-1$. No party or dealer ever holds $bold(s)_1$ or $bold(s)_2$; coefficients are sampled on replicated shares exactly as FIPS 204 rejection sampling prescribes, and $bold(t)$ is computed on shares before it is opened, so there are no per-party key contributions to choose adaptively. A corrupt custodian can abort after seeing the public key; it cannot move a coefficient outside $[-2, 2]$. Signing needs a quorum of $2t-1$, since the rejection test is a multiparty computation that is sound only with an honest majority: the response $bold(z)$ is opened only after a single shared accept bit, behind verified multiplications, so a rejected attempt reveals $bold(w)_1$ and the reject bit and nothing else. That this pair is harmless is the usual Fiat–Shamir-with-aborts heuristic, not a theorem. Nonces are burned in a durable log (`threshold_mldsa_nonce_reuse_extracts_sk_and_typestate_prevents`).

`PiVoprf` is now a 2-of-5 threshold OPRF over a keyed width-12 Poseidon2 sponge with replicated additive sharing and majority decoding, correct against one malicious server; counters are reserved durably before any evaluation message. `PiBlindVc` has the issuer authorize disclosed issuance attributes together with a proof of their blinded commitment, enrolls that commitment in an issuer accumulator through an authenticated OPRF evaluation, and uses six-limb Poseidon2 digests with a 438-repetition `Quantum128` membership proof. Both replace earlier lattice-based prototypes. A token is not a publicly verifiable signature, the issuer sees issuance attributes, and `Quantum128` is a challenge-size profile under classical Fiat–Shamir assumptions.

#figure(tbl((1.4fr, 1fr, 1fr),
  [FIPS 204 profile], [Public key B], [Signature B], table.hline(),
  [ML-DSA-44], [1,312], [2,420],
), caption: [Standard-verifier ML-DSA-44 sizes. Threshold participation does not change the external format.])

*`qsag-accel`.* `AcceleratorBackend` defines batch interfaces for Keccak, Poseidon2, Goldilocks NTT, coset expansion, Merkle layers, and Tower128 dot products. `VerifiedKernelDigestRegistry` pins loader-measured digests, and keyed cSHAKE256 `ExecutionReceipt`s bind them into transcripts. A keyed receipt authenticates a computation report; it is not hardware remote attestation and not a proof that an untrusted accelerator computed correctly. `accelerator_backend_simulation_sound` is a specification-level simulation statement under its premises.

= Four assurance pillars
The Lean library `Qsag` comprises 39 modules, 115,146 lines, and 3,599 theorem declarations, with no Mathlib dependency. The policy is no `sorry`, no custom axioms, no `native_decide`, and no `Classical.choice`: permitted axioms are `{propext, Quot.sound}`. The earlier revision's transitive choice dependencies have been eliminated. Two build-time gates enforce the policy by scanning every declaration in scope and failing on any other axiom, each with a negative control. The recorded run of `AuditAxioms` covers 23,496 `Qsag` declarations and that of `AuditMirAxioms` covers 4,110 extracted-core declarations, with none rejected.

One qualification is needed. `AuditAxioms` scans the import closure of the library root, and at this revision five modules are built by the library glob but not imported by that root: `ActiveMigrationZeroTest`, `BaggyAndRss256Security`, `ConcreteSecurityBudget`, `JortsBeltLatchAndQuorumSwitching`, and `PosixCrashWal`. The first two carry in-file audits (`#verify_constructive`, and an explicit axiom check over a named declaration list); the other three state the policy in their headers and build under it, but are outside the crawling gate until the root imports them.

#figure(kind: image, supplement: [Figure], {
  set text(size: 8pt)
  set par(justify: false)
  stack(dir: ttb, spacing: 6pt,
    panel([#smallcaps[Pillar 1 · protocol, storage, and query-bound spine]\
      `Fips205.lean` · `ThresholdMpc.lean` · `SuccinctAggregationIop.lean`\
      `PosixCrashWal.lean` · `ConcreteSecurityBudget.lean`]),
    align(center)[↓ `MirSpecBridge.lean`; differential / KAT links ↓],
    grid(columns: (1fr, 1fr), gutter: 7pt,
      panel([#smallcaps[Pillar 2 · extracted MIR]\
        `QsagMirProofs.lean`\ Arithmetic, sponges, and affine release guards]),
      panel([#smallcaps[Pillar 3 · ISA and ELF64]\
        `ConstantTimeIsa.lean`\ `ElfBinaryVerify.lean`\ PC / memory / latency-operand analysis]),
    ),
    align(center)[↑ exercised by ↑],
    panel([#smallcaps[Pillar 4 · executable gates]\
      `spec-oracle` · `isa-cosim` · dudect · kernel replay]),
  )
}, caption: [Complementary evidence, not a completed refinement chain. The extracted core is a separate workspace, and the assembly kernels and the MIR core cover separate code.])

== Pillar 1: specification spine
`Goldilocks.lean` and `BinaryTower.lean` establish field and embedding properties; `Keccak.lean` and `Poseidon2.lean` formalize permutation, framing, and packing behavior (`goldilocksPrime_isPrime`, `Goldilocks.mul_inv_cancel`, `encodeMultiFrame_injective`, `poseidon2Perm12_bijective`, `bytesToLimbs56_injective`). These support the signing specifications in `Fips205.lean` and `HashSigs.lean` (`fips205_wots_incomparable_no_chain_forgery`, `tsw_incomparable_no_chain_forgery`, `verifyPqHashSig_evalSingleSign`), `HypertreeEufCma.lean`, and `ThresholdMpc.lean`. `Preprocessing.lean`, `MaliciousSecurity.lean`, and `IdealTsig.lean` formalize preprocessing checks, authenticated release, and ideal threshold approval; for universal composition [20], `UcGames.lean` includes `multi_session_uc_realizes` and `uc_composition_theorem`. Those names describe formal statements in their models; they do not establish that every implementation detail satisfies the premises.

Six modules are new since the earlier draft.

`JortsBeltLatchAndQuorumSwitching.lean` models the latch as a multi-turn state machine over lists of turns, with byte-exact domain tags and framing matching `belt_latch.rs` and `quorum_jorts.rs`, and proves the sufficiency, necessity, and availability trilogy cited in §2.6 together with `committee_partitioned_jorts_safe_and_live_for_2f_plus_1`.

`BaggyAndRss256Security.lean` covers 256-bit WOTS+C (a Type-valued one-use reduction, `wotsC256_one_use_euf_cma_sound`, returning an explicit second preimage, compression collision, chain collision, or chain preimage), the replicated engine, and Waistband.

`PosixCrashWal.lean` gives a three-tier storage model: kernel-volatile descriptor, lock, and page-cache state; a drive write-back cache that survives a kernel panic but not power loss; and non-volatile media subject to sector-granular torn writes. Locks are held by `OpenDescriptionId`, so duplicated and inherited descriptors share a lock while independent opens contend, and an I/O error during synchronization poisons the handle. Over this model a genesis-sealed, MAC-authenticated record with parent-directory synchronization yields epoch uniqueness across arbitrary crash sequences.

`ConcreteSecurityBudget.lean` develops exact rational bit-margin arithmetic and a unitary query model over Gaussian-integer amplitudes. It proves a square-root-free form of the hybrid argument [29] and a one-way-to-hiding disturbance bound [30] (`qrom_o2h_telescoping_disturbance_le`, `born_prob_diff_sq_le_four_state_dist_sq`), and couples them to protocol encodings: adversary success is bounded by $8(q+1)^2 abs("Fiber") slash 2^n$ for quantum queries and $(q+1) abs("Fiber") slash 2^n$ classically (`qrom_fiber_search_bound`, `classical_lazy_ro_fiber_search_bound`), where the fiber cardinality comes from a proved injectivity statement rather than a numeric literal. These are search bounds for stated encodings; they are not Fiat–Shamir extraction theorems, and the measure-and-reprogram accounting [31] enters as budget arithmetic.

`MirSpecBridge.lean` packages the nine machine-code refinement theorems (`compiled_rlib_nine_kernels_verified`) and relates fixed-width guards of the extracted core to protocol-level statements. `Tactic/AssuranceKit.lean` supplies the audit commands `#verify_constructive` and `#tooth_pair`, which checks that a security theorem is paired with a structurally related refusal theorem and that neither is vacuous, and the tactic `bv_xor_cancel`.

The extractor distinction remains central. `extractFips205WotsForgery`, `extractPqHashForgery`, `extractFullHypertreeForgery`, and `qsag_aggregate_unforgeability_reduction` are constructive definitions; a Type-valued output alone does not establish the intended security conclusion.

*Not covered:* Pillar 1 does not prove an end-to-end deployed EUF-CMA reduction, a total QROM Fiat–Shamir reduction, concurrent ceremony composition, or implementation refinement of the concrete runtime profiles.

== Pillar 2: Safe-Rust MIR refinement
Charon and Aeneas [22] translate the dedicated crate `aeneas/qsag-verified` into pure Lean functions with no external-function module. `QsagMirProofs.lean` exports 261 names, including 33 `tooth_*` refusal witnesses.

Arithmetic specifications include `goldilocks_canon_spec`, `goldilocks_reduce128_spec`, `goldilocks_mul_spec`, `goldilocks_pow7_spec`, and `goldilocks_ext2_mul_spec`; for tower fields and authenticated Boolean operations, `tower_gf256_field_laws`, `tower_gf256_boolean_iff_frobenius`, `dkg_beaver_frobenius_eval_spec`, and `verify_mac_2lane_burn_irreversible`. The scope also includes `rss_keccak_chi_lane_spec`, `shamir_eval_poly_gf256_spec`, full 24-round `keccak_f1600_total`, `ct_eq_bytes32_spec`, `fips205_adrs_roundtrip_spec`, `fips205_wots_checksum_spec`, `tsw_check_target_sum_spec`, and `epoch_latch_multiturn_safety`. Tower128 has a pure specification written independently of the extracted code.

The crate now also contains affine release guards: `VerifiedBeltQuorumGuard`, `VerifiedWotsC256Guard`, `VerifiedRssPoisonLatch`, `VerifiedWaistbandRootGuard`, `FtsEpochGuard`, `MlDsaReleaseGate`, `StatefulVelocityGuard`, and `RssCutGateSession`. Guard state is held in private fields, and `compile_fail` doctests pin that external code cannot reset an authorization flag; the hardening record counts 13 such structs. `VerifiedBeltQuorumGuard` authenticates each custodian acknowledgement with a per-custodian MAC, deduplicates acknowledgers by bitmap within the bound epoch and message, and requires a receipt MAC from the WAL authority; it performs no I/O.

Negative witnesses test the meaning of refusal: `tooth_goldilocks_noncanonical_rejected`, `tooth_gf256_nonboolean_rejected`, `tooth_shamir_duplicate_points_rejected`, and `tooth_epoch_equivocation_rejected`. Differential parity tests in `parity_qsag_core.rs` connect the extraction core to operational `qsag-core` code; that bridge is testing evidence.

*Not covered:* the extracted crate is a separate workspace that the root workspace does not link (§8.1). A correct guard does not constrain callers that own raw shares or construct outputs independently. Proofs over BDOZ openings of arbitrary slice length and multi-block SHAKE absorption are established for totality and the single-opening and bounded cases, not by a general induction over the extracted loops.

== Pillar 3: ISA semantics and compiled ELF64
`ConstantTimeIsa.lean` models selected x86-64 and AArch64 instructions and their leakage events: program counter, branch behavior, memory addresses, variable-latency operands, and dirty upper-vector state on return. `x86_ct_checker_sound` and `arm_ct_checker_sound` establish relational properties of the modeled taint checkers. Functional statements are separate from leakage statements: `gfni_phi_left_inv`, `gfni_phi_right_inv`, and `gfni_isomorphism_homomorphic` connect field representations; `gf256ShamirMulGfni_32lane_correct` and `keccakChiMpc_3party_rss_sound` address modeled kernels; `goldilocksMulCtX86_canonical_correct` and `goldilocksMulCt_x86_eq_arm` establish equivalence of the modeled instruction sequences on canonical inputs; the `*_constant_time` theorems are distinct leakage results.

`ElfBinaryVerify.lean` works from compiled bytes. `CompiledRlibFixtures.lean` embeds SHA-256-pinned archive fixtures; the parser extracts symbol bodies (`parseArMember_subslice`, `extractElfFuncBytes_in_text_section`), decodes them, and runs an abstract-interpretation taint analysis with one kernel-checked certificate per symbol. The pinned fixtures contain 16 x86-64 and 7 AArch64 symbols, 999 and 299 instructions (`x86_rlib_all_16_decode_999_instrs`, `aarch64_rlib_all_7_decode_299_instrs`). `checkElfFuncThreeWayNI_sound` connects accepted checks to three-way noninterference (control flow, memory addresses, secret variable-latency operands), with all-symbol results `rlib_x86_every_symbol_three_way_ni_sound` and `rlib_aarch64_every_symbol_three_way_ni_sound`, plus callee-saved conventions and epilogue vector hygiene.

Decoder repairs since the earlier draft are pinned by witnesses: `VZEROALL` (`c5 fc 77`) is distinguished from `VZEROUPPER` by the VEX length bit; base-less SIB addressing decodes to an absolute displacement (`tooth_sib_absolute_decode`); and the AArch64 bitfield move follows the reference extraction and insertion semantics (`tooth_ubfm_extract`, `tooth_ubfm_insert`, `tooth_ubfm_illegal_n`). The address and bitfield semantics are anchored to two public Lean ISA developments by citation in the source; neither is imported or proved equivalent. Mutation witnesses (`mutant_secret_branch_rejected`, `mutant_secret_lut_rejected`, `mutant_udiv_rejected`, `mutant_missing_vzeroupper_rejected`) show rejection of selected corrupted fixtures; they test sensitivity to known bad changes, not completeness of the decoder.

Beyond the archive fixtures, the project records extending the symbol inventory to 37 archive symbols and 28 symbols of a ThinLTO-linked executable. The repository's own binary-verification notes still list linked `ET_EXEC`/`ET_DYN` coverage as integration work, and we report it as such.

*Not covered:* unmodeled speculation, silicon errata, power or electromagnetic leakage, the compiled control flow of every Safe-Rust crate, and functional correctness of every lifted binary. Noninterference is relative to the stated ISA and leakage models, and to x86-64 DOIT and AArch64 `PSTATE.DIT` assumptions that capability enumeration alone does not establish.

== Pillar 4: executable ground-truth gates
Proofs establish properties of specifications; these gates ask whether the specifications say what the code and the hardware do.

`lake exe spec-oracle` exposes the live Lean specifications over a streaming protocol, and a differential driver compares them with the Rust implementations across hash, signature, tower, aggregation, and WAL surfaces, with metamorphic cases and a _clause-drop_ search: a guarded harness and five mutants, each dropping one guard (custodian uniqueness, quorum intersection, epoch monotonicity, target sum, limb canonicity), run identical random action traces, and an observer of emitted effects must find a trace that separates each mutant. The mutants are harness mutants; production code is never rewritten. The recorded strict run reports 2,800 Rust-to-Lean comparisons with no mismatch, against a 500-schedule mutation baseline. WAL schedules execute the Lean model; equivalence with the Rust POSIX behavior under real crashes is not asserted.

`lake exe isa-cosim` runs the Lean byte decoder and operational semantics against physical x86-64 execution: a `ptrace` single-step harness installs and captures all general registers, all 256-bit vector registers, flags, and shared memory outside the tested instruction stream. The default run is 2,314 checks: 2,304 scheduled instruction cases over vector shifts, carry-less multiplication, shuffles, extraction, `VZEROUPPER`/`VZEROALL`, and SIB addressing, plus two rounds over five kernel bodies. Its limits are stated in §8.2.

dudect [21] measurements ask whether tested executions exhibit class-dependent timing; absence of a detected signal is empirical evidence. Finally, a configured challenge replays exported theorem statements through six independent proof checkers.

*Not covered:* these gates are sampled. They can refute a specification; they do not prove one. Executables and configured challenges are not evidence of a fresh run against a given release binary.

= Evaluation
== Hardware and measurement scope
The kernel testbeds are Intel Core i9-12900 (Alder Lake) and AMD EPYC-Milan (Zen 3, virtualized), both running Linux x86-64. The Intel path uses AVX2, GFNI, and VPCLMULQDQ, while the AMD path uses AVX2 and PCLMULQDQ. Kernel comparisons exercise different instruction paths on those processors. AArch64 targets are covered by static and Lean binary analysis; there are no AArch64 timing numbers. Guest scheduling and virtualization can affect AMD cycle counts.

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
), placement: top, scope: "parent", caption: [Kernel measurements in cycles per indicated unit, and dudect Welch statistics over 1,000,192 traces. Goldilocks cycle counts are per multiplication; dot2 and pow7 timing tests are separate rows. RSS uses AVX2; tag equality is straight-line; the negative control leaks intentionally. Speedups reproduce recorded values, which need not equal ratios of rounded cycle entries. These kernel figures were recorded at an earlier revision and have not been re-measured.]) <simdbench>

== Kernel throughput and dudect
@simdbench separates cycle measurements from timing-class tests. GF256 arithmetic benefits substantially from the specialized field representation and vector paths: the GFNI multiplication on Intel is 0.039 cycles per byte versus 19.890 portable, while the AMD path uses a different implementation at 0.551. These are batched kernel numbers, not the cost of a signing session. The nine timing tests satisfy the reported $abs(t)<4.5$ criterion over 1,000,192 traces on both processors, and the deliberately leaking early-exit comparison is rejected with very large statistics. That negative control demonstrates sensitivity to the chosen leak; it does not characterize sensitivity to all smaller leaks.

In the earlier revision these kernels were standalone. They are now dispatched from the protocol crates: `qsag-core`, `qsag-quorum`, `qsag-agg`, `qsag-cred`, `qsag-migrate`, `qsag-hd`, `qsag-policy`, and `qsag-accel` depend on `qsag-asm`, and the replicated engine, the PCG expansion, and the Merkle commitment call its batched Keccak and carry-less paths through runtime backend selection. Kernel-scoped leakage results still do not transfer to the Rust code that calls them.

== Protocol measurements
@protobench collects the protocol-level figures the project currently reports. All are computation or loopback measurements on a single host; none measures a durable, authenticated, geographically separated deployment.

#figure(tbl((2.4fr, 1.9fr, 1.5fr),
  [Operation], [Setting], [Reported], table.hline(),
  [Hem, `Habr24Qrom128`], [proof size], [≈ 137.8 kB],
  [], [prove / verify], [≈ 680.9 ms / 7.93 ms],
  [Hem, `BciksJohnsonQrom128`], [proof size], [≈ 251.2 kB],
  [], [prove], [≈ 1.01 s],
  [Jorts 2-of-3, Mode 3B], [local compute], [≈ 1.0 ms],
  [], [simulated WAN], [≈ 81 ms],
  [QS-A, 3-of-5], [loopback TCP, two offline], [≈ 0.56 ms],
), caption: [Reported protocol measurements. Hem figures are for the reference `JortsPoseidon2` batch; the in-tree regression gate independently bounds the $K=8$ default-regime proof at 170 kB. Jorts and QS-A figures exclude key generation, staging, and durable synchronization.]) <protobench>

Three readings of @protobench should be resisted. First, the Hem proof is tens of kilobytes larger under the Johnson regime; that is the price of replacing a conjectured agreement bound with a proven one, and the default remains the conjectural regime. Second, aggregation is not a bandwidth win at every batch size, since proof size is dominated by query openings and grows slowly with the trace, while the raw signatures it replaces grow linearly; and merged proofs grow linearly in shard batches (§4.4). Third, sub-millisecond online signing in Mode 3B and QS-A reflects work moved offline, into the staged window and the dealer-staged chain tables respectively. The online path is one opening round; the offline path evaluates every chain.

The earlier draft's aggregation table (a BaseFold instantiation over a quadratic extension, with multi-second to minute-scale proving) and its protocol micro-benchmark table are withdrawn: the measured constructions for aggregation, migration, threshold ML-DSA, the OPRF and credential stack, and HD derivation have been replaced, and we do not carry numbers forward for superseded protocols.

Negative results remain part of the evaluation. In the bounded documentation check (12 GiB memory cap, 600 s per command), the full threshold example completed replicated signing and stock verification and then timed out during Shamir DKG and SPDZ preprocessing; 12 of 13 commands passed. Full-hypertree FIPS 205 MPC signing remains minutes-scale. No dishonest-majority DKG or signing time is reported, and reducing Ring-LWE base-OT latency in that path is ongoing work.

== Interpreting the costs
Dishonest-majority Keccak is especially demanding: an unbatched permutation consumes 38,400 authenticated Boolean Beaver triples. A shallow cut can still invoke many such permutations. Batching lanes or selecting the algebraic Poseidon2 route changes the practical cost structure; neither removes the need for secure preprocessing or authenticated openings. Kernel speedups, aggregation size, and height-independent scheduling address distinct costs; these measurements do not establish distributed-network throughput or production availability.

= Limitations and threat-model boundaries
== Trusted base and linkage
The project comprises 13 crates with no external crates.io dependencies: 12 packages in the root workspace and `aeneas/qsag-verified`, which has its own workspace. The root workspace does not depend on the extracted crate. Theorems of Pillar 2 therefore attach to the generated functions, and their relation to production code rests on parity tests and on similarly structured source, not on direct execution linkage. Closing this requires the production paths to call the extracted guards, fresh extraction with generated-body comparison at each change, and ownership of secrets inside the guarded boundary.

Outside the pinned assembly symbols, compiler and LLVM code generation remain trusted. So do Charon, Aeneas and the hand-written prelude, OS and hardware entropy, the durable storage semantics the host promises, transport provisioning, and policy time authority. Independent proof-checker replay reduces dependence on one kernel; it does not validate a wrong theorem statement or a stale extraction. Human review of theorem statements is part of the trusted base.

== Open specification and proof obligations
The machine-checked statements must be read with the following qualifications. This paper describes the repository in November 2026; the development is under active change.

- *Aggregation completeness and soundness.* As detailed in §4.5, active-slot completeness and soundness of the 256-column step table against the signature verifier are unproved; `populate_active_signer_rows` is unmodeled. Transcript binding of the opening and the merge tree are open, and no proximity-gap statement is mechanized.
- *Total security of Hem.* Regime selection is query accounting. A total bound needs one profile consumed by both the concrete verifier and a proof, with list, field, hash, and union terms, and an applicable multi-round QROM reduction. The default regime additionally rests on a conjectured agreement bound.
- *Ring-LWE extraction.* The deployed challenge is a signed-monomial ring element. An extractor for Boolean challenges does not establish extraction for a polynomial difference; invertibility and exceptional cases, witness norms, and Fiat–Shamir losses must be proved for the real relation.
- *MIR induction.* BDOZ verification over arbitrary-length opening slices and multi-block SHAKE absorption lack general inductive proofs over the extracted loops.
- *ISA cosimulation.* `isa-cosim` models only the carry, overflow, and zero flags. Default coverage is vector and memory instructions, whose flags are unchanged; the opt-in scalar probes (multiply, shifts, rotate) expose the unmodeled arithmetic flags as failing cases, eight in the recorded run, and are not masked. Kernel-body comparisons stop before `RET` under restricted initial flags, so stack-pointer behavior at the return and caller spill slots are outside the comparison. There is no AArch64 cosimulation.
- *Axiom-audit closure.* Five modules are outside the root import closure scanned by `AuditAxioms` (§6).
- *Extractor meaning.* `extractFullHypertreeForgery` and `qsag_aggregate_unforgeability_reduction` are constructive definitions without adequate separate soundness theorems; they are reduction skeletons.
- *Attribution.* Identifiable abort is assumed as a hypothesis where it appears.
- *Fiat–Shamir.* The 438-repetition and 260-bit parameters size challenge spaces against generic quantum search. No online-extraction or compressed-oracle theorem is claimed for the migration, credential, preprocessing, or aggregation proofs.

Several issues listed as open in the earlier draft are closed in the implementation and are no longer limitations in that form: the distributed migration prover is actively checked; the PCG shares are dense and receiver-checked; `ParallelSeededFts` verifies before opening and caps one signature per leaf; threshold ML-DSA samples and opens its key on shares and rejects before opening a response; the OPRF and credential prototypes were replaced; HD children receive fresh MAC keys with persistent poison; the Ring-LWE challenge is jointly hashed; and the SIMD kernels are dispatched from protocol paths. In each case what closed is an implementation defect. The corresponding proof obligations above, and the linkage of §8.1, are not thereby discharged.

== Leakage models and release artifacts
Architectural control-flow, memory-address, and operand-latency noninterference do not model all microarchitectural leakage. On x86-64, enabling the DOITM control requires privileged kernel support; a ring-3 application cannot assume it. On AArch64, `msr dit, #1` can be used in EL0 where the feature is present. Scratch zero-on-exit covers named registers and frame locations; preserved caller registers, compiler copies, old allocations, OS context saves, speculation, and physical faults require separate treatment. `VZEROUPPER` is not full vector erasure, and a call is not a scrub operation.

Pillar 3 covers SHA-256-pinned fixtures, not all artifacts bearing the same crate name. Release procedures must regenerate fixtures after any change to compiler, flags, target features, dispatch, or assembly, and rerun the analysis.

== Persistence, transport, and composition
Stateful Jorts, both quorum modes, few-time signatures, nonce burning, policy counters, and OPRF counters require durable logging with synchronization and exclusive locking. An in-memory latch is not custody. Filesystem logs cannot detect a whole-disk or VM snapshot rollback without an external monotone anchor.

Correct atomic replacement of one record does not prove atomicity across policy spend, leaf reservation, preprocessing cursors, nonce burns, and poison state. Every useful partial output needs prior durable reservations in the same bound ceremony context, under every crash prefix and interleaving; `FsCeremonyJournal` sequences these, but the per-file crash model of `PosixCrashWal.lean` is not a ceremony-level proof, and sequential session proofs are not yet instantiated for the concurrent scheduler.

Deployment needs authenticated _confidential_ channels with session, peer, and round binding, replay protection across reconnects, and consistent broadcast where used. A MAC-sealed frame is not encrypted. A local cluster holding all shares is a demonstration, not separated custody, and staging in both quorum modes is currently a dealer.

== Primitives and availability
Compact few-time profiles limit generic preimage strength as stated in §2. The parallel-seeded SPN is a custom symmetric design; its bijective S-box and degree growth are algebraic facts that do not rule out differential, structural, or implementation attacks. Custom Pants signature formats are not NIST formats. Dishonest-majority security permits abort and does not promise liveness; QS-A trades committee anonymity and leaf capacity for $t$-of-$t$ online signing; QS-B needs $n >= 3f+1$ to stay live. Resource exhaustion and expensive full-hypertree evaluation remain operational concerns independent of whether the mathematical cut is correct.

= Conclusion
QSAG's central architectural choice is to keep secret evaluation behind a small authenticated oracle boundary and perform public tree work outside MPC. The Pants suite instantiates that boundary for stateless, stateful, and quorum-switching signing, with a durable latch as the single place where a one-time leaf is committed. Hem addresses the separate bandwidth problem, under query-accounting regimes whose assumptions are named, and the custody suite supplies authorization, persistence, and migration interfaces around signing. The four pillars provide machine-checked statements and executable checks at distinct abstraction levels. Since the earlier draft, most known implementation defects have been repaired and the constructive axiom policy is enforced by a crawling gate. What remains is narrower and harder: connecting the deployed arithmetization to the verifier it claims to encode, linking the extracted guards into the code that runs, proving extraction for the relations actually deployed, and composing per-resource crash safety into ceremony safety. Until those are done, the development supports scoped claims and not end-to-end implementation security.

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
+ G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT 2025.
+ C. Lund, L. Fortnow, H. Karloff, N. Nisan, "Algebraic Methods for Interactive Proof Systems", J. ACM 1992.
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
+ E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed–Solomon Codes", FOCS 2020.
+ E. Boyle, N. Gilboa, Y. Ishai, A. Nof, "Practical Fully Secure Three-Party Computation via Sublinear Distributed Zero-Knowledge Proofs", ACM CCS 2019.
+ A. Hülsing, M. Kudinov, E. Ronen, E. Yogev, "SPHINCS+C: Compressing SPHINCS+ With (Almost) No Cost", IEEE S&P 2023.
+ C. Bennett, E. Bernstein, G. Brassard, U. Vazirani, "Strengths and Weaknesses of Quantum Computing", SIAM J. Comput. 26(5), 1997.
+ A. Ambainis, M. Hamburg, D. Unruh, "Quantum Security Proofs Using Semi-classical Oracles", CRYPTO 2019.
+ J. Don, S. Fehr, C. Majenz, "The Measure-and-Reprogram Technique 2.0: Multi-Round Fiat–Shamir and More", CRYPTO 2020.
+ M. Keller, E. Orsini, P. Scholl, "MASCOT: Faster Malicious Arithmetic Secure Computation with Oblivious Transfer", ACM CCS 2016.
]
