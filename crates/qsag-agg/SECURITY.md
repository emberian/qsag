# Aggregation security

This document states what is proven about committed-mask zk-Hem
(`src/zk_hem/protocol.rs`) and the Hem WHIR commitment (`src/pcs.rs`), under which
hypotheses, and with which numbers. The numbers are computed by
`src/zk_hem/bounds.rs` (`security_report`, `pcs_report`) and pinned by its tests.
Every statement carries one of four labels:

- **[cited]** a theorem of a paper, with its hypotheses checked against the code;
- **[ours]** an argument made in this document, not peer reviewed;
- **[model]** an idealisation the statement depends on;
- **[open]** not established.

Papers are named by their file in `/Users/ember/paperbin` on first use.

## 0. Verdicts

**FAILED as shipped, fixed: one seed used under two regimes leaked
linear functionals of the witness.** `prove` derived its coins from the seed, the
relation, the statement and the witness, but not from the regime. The regime's schedule
is bound into the transcript, so the two proofs have different challenges and the same
masks. The twelve masking variables then cover `(Az, Bz, Cz)` at two different row
points: twenty-four base-field equations in twelve unknowns, which reveal at least
twelve base-field linear functionals of the witness, enough to confirm a guessed
witness. The sumcheck masks and the companions repeat as well. The attack needs the
caller to reuse a seed, which the documentation forbade only across "different proofs"
while promising that a repeated seed was harmless. `prove` now absorbs the schedule into
the coin derivation; `zk_hem::bounds::tests::coins_do_not_repeat_across_regimes` fails
on the previous code (equal `row_mask_sum` in both proofs).

**NOT MET: no regime provides the 128-bit QROM level its name carries.** The proven QROM
knowledge-soundness level is **81 bits for every regime**, set by the 256-bit Merkle and
transcript digests (`6380 t^3 / 2^256`). With longer digests the next limits are the
blend of the hiding protocol (86 to 95 bits) and then the quartic field itself: a proven
128-bit QROM level needs a per-round error below `2^-264.4`, and no challenge set here
has more than `2^256` elements. The best this field can give under the cited theorem is
about 116 bits. The nominal figures of `WhirSecurityRegime::qrom_grover_round_bits`
(136, 108, 107) count queries and grinding in one round and are not security levels.

**NOT MET: tag 2 (`BciksJohnsonClassical128`) reaches 124.5 bits per query round, not
128**, before grinding (141.4 with it, against the 144 of `classical_fs_round_bits`).
It is rejected by the aggregate policy and used in raw PCS tests only.

What holds:

1. **Knowledge soundness.** Classical ROM: **127 bits** for every accepted regime at
   every project size (collision-bound; the round-by-round margin is 57 bits or more).
   QROM: 81 bits, as above. Sections 2 and 5. [cited] + [ours] + [model]
2. **Batching proximity loss.** The scalar blend of the five tables has mutual
   correlated agreement up to the Johnson radius with error
   `(m + 1/2)^7 * 4 n^2 / (3 rho^(3/2) |F|)`, between `2^-199` and `2^-184` at project
   sizes, and it forces the Stage-0 analysis to an agreement fraction of
   `(1 + 1/(2m)) sqrt(rho)`. This is the weakest round of the hiding protocol. Section 3.
   [cited]
3. **Zero knowledge.** The interactive oracle proof is **perfect** honest-verifier zero
   knowledge: `blind_cells` equals the number of opened assignment symbols, later-stage
   queries, out-of-domain values and folded words are functions of a uniform word, and
   fresh masks make repeated proofs of one witness independent. Section 4. [ours]
4. **Unopened-leaf hiding.** Only Stage-0 leaves need it; they carry a 128-bit salt in
   every regime. The proven distance is `t P / 2^128` classically and
   `2 t sqrt(P / 2^128)` against quantum queries (`P` proofs, `t` hash queries). The
   quantum figure is weak (`2^-23` at `t = 2^40`); 256-bit salts make it `2^-87`.
   Section 4.4. [ours], using [cited] one-way to hiding.

## 1. The protocol as analysed

`p = 2^64 - 2^32 + 1`, `E = F_{p^4}`. A relation has `2^n` rows (`log_rows = n`) and a
variable subcube of `2^k` cells (`var_bits = k`). The prover commits five base-field
tables of `N = 2^l` cells (`Layout::new` in protocol.rs): the
assignment table `Z` (variables, twelve masking variables, the sumcheck masks `g1`,
`g2`, and `blind_cells` uniform cells at the top) and four uniform companions `C_0..C_3`. Their Reed-Solomon
codewords on a coset `D_0` of size `4N` share one Merkle tree whose leaf `g` holds fiber
`g` (`2^{s_0}` points) of all five codewords and a 16-byte salt.

Verifier rounds, in the order `verify` (protocol.rs) and
`whir_verify_core_claims` (pcs.rs) replay them. Every challenge is drawn after the
listed prover messages were absorbed.

| # | Prover message | Challenge | Grinding |
| --- | --- | --- | --- |
| 0 | Stage-0 root; statement, relation digest, layout, schedule, public inputs | `tau` in `E^n` | no |
| 1 | `G1 = sum g1` | `rho1 != 0` | no |
| 2..n+1 | row round polynomial, degree 9 | `rx_i` | no |
| n+2 | `(Az, Bz, Cz)(rx)` | three weights | no |
| n+3 | `G2 = sum g2` | `rho2 != 0` | no |
| .. | column round polynomial, degree 2 (`k` rounds) | `ry_i` | no |
| .. | none | `lambda` | no |
| .. | `sigma_j = <C_j, K>` | `beta` outside `F_{p^2}` | no |
| .. | none | two out-of-domain points | no |
| .. | two evaluations of `U` | two weights | no |
| per fold | `sigma_even, tau_01, tau_10` | `phi` | no |
| per fold | `c_F, c_G`, nonce | `theta, alpha, beta` | regime |
| per stage but the last | next root | two out-of-domain points | no |
| per stage but the last | two evaluations, nonce | `q_i` distinct fibers, then two weights and `gamma` | regime |
| last | terminal coefficients, nonce | `q` distinct fibers | regime |

`U = Z + beta C_0 + beta^2 C_1 + beta^3 C_2 + beta^4 C_3`, and `K` is the linear
functional of step 4 of the module comment. There are `6 + n + k + 2 f + 2 M + 1`
rounds for `f` folded variables and `M` stages: 71 to 91 at project sizes.

## 2. Knowledge soundness

### 2.1 Round-by-round errors

**Theorem 1 [ours, from cited lemmas].** Fix a regime, a size, a proximity parameter
`m >= 3` and, per stage `i`, an agreement threshold `A_i` (in fibers) for which every
fold level of the stage has an interpolation witness. Let `l_i` be the Johnson list
bound of the stage's word at `A_i`, and `L_i = l + 2 l_0 + 1` the list numerator of
[CWYZ26] (5.5) maximised over the stage's fold levels. The interactive oracle proof has
round-by-round knowledge soundness with these errors:

| Round | Error | Source |
| --- | --- | --- |
| `tau`; `rho1`, `rho2`; row and column rounds; weights; `lambda` | `d l_0 / |E|`, `d = max(n, 9, 4 + num_public)` | Schwartz-Zippel per list member |
| `beta` | `eps_mca(m) + 4 l_0 / |E \ F_{p^2}|` | [BCGM25] Lemma 9.3; section 3 |
| out-of-domain points of stage `i` | `(l_i^2 / 2) ((2^{r_i} + 2) / |E|)^2` | [ACFY24b] Lemma 4.25, two samples |
| Stage-0 out-of-domain weights | `2 l_0 / |E|` | linear identity per list member |
| `phi` | `L_i / |E|` | linear identity per list member |
| `theta, alpha, beta` | `L_i / |E|` | [CWYZ26] Theorem 5.1, bound (5.5), finite form Theorem 4.10 |
| queries of stage `i`, with the batching weights | `C(A_i + s_i, q_i) / C(n_i, q_i) + (q_i + 2) l_{i+1} / |E|` | sampling without replacement; linear identity |

Here `n_i` is the number of fibers, `s_i` the folds of the stage and `r_i` the variables
before them. Grinding of `b` bits in front of a round multiplies its error by `2^-b`
in the classical bound (section 2.2).

*Sources.* [CWYZ26] is `2026-affine-combiners-reed-solomon-proximity-gaps-2611.15128`
(arXiv, 11 November 2026, not yet peer reviewed). [BCGM25] is
`bordage-chiesa-guan-manzur-all-polynomial-generators-MCA-2025-2051`, extending
`habock-mutual-correlated-agreement-RS-2025-2110`. [ACFY24b] is `whir` (2024/1586),
whose Theorem 5.2 fixes the shape of the fold, out-of-domain, shift and final errors.

*Hypotheses checked against the code.*

- [CWYZ26] Theorem 5.1 needs `theta, alpha, beta` uniform in the field of the words,
  drawn after the two cross claims `c_F, c_G` (`bridge_verify_finish`,
  pcs/affine.rs), and the claims `sigma_even, tau_01, tau_10` fixed before `phi`
  (`bridge_prefix`, pcs/affine.rs). Both orders hold. It needs `B^2 > n (d + 1)` and the
  interpolation inequality (4.5); `bounds::affine_fold_numerator` searches a witness
  `(m, D)` per fold level and `bounds::tests::finite_witnesses_of_the_schedule_are_reproduced`
  checks that the stored witnesses of `pcs/affine_schedule.rs` satisfy the same
  inequality. The second term of (4.13) is below `1 / |E|` for every witness used.
- The theorem costs one coordinate of agreement per fold. A fold maps a word on `2n`
  points to one on `n` points, so the lost coordinate removes at most one fiber per
  fold: a stage with `s_i` folds is analysed at `A_i + s_i` fibers. [ours]
- Queries are distinct (`sample_stage_queries`, pcs.rs), so the query error is the
  hypergeometric product, computed with every division rounded up.
- The Stage-0 words are base-field words. A polynomial over `E` that agrees with a
  base-field word on more points than its degree has base-field coefficients, so the
  extracted assignment lies in `F_p`. [ours]
- The extractor decodes the Stage-0 word within the Johnson radius (Guruswami-Sudan)
  and returns the list member consistent with the transcript; the knowledge errors
  equal the soundness errors, as in [ACFY24b] section 7.2.1. [ours]

*State function.* After the Stage-0 root the list of five-tuples of codewords within
`A_0` of the committed words is fixed, of size at most `l_0`. A transcript is doomed when
no list member is consistent with every claim made so far; each row of the table bounds
the probability that one challenge turns a doomed transcript into a live one. This is
the state function of [ACFY24b] Theorem 5.2 with the sumcheck of zk-Hem in front. [ours]

*What the affine fold does not use.* No capacity conjecture. Tags 0, 1 and 3 relied on
mutual correlated agreement up to capacity, which is false
(`fri-proximity-gaps-conjectures-DISPROVED-2025-2046`;
`failure-proximity-gaps-capacity-2026-782`;
`sok-hash-based-pcs-fri-basefold-stir-whir-2026-1367` section 5.4). Every bound above
is at or inside the Johnson radius and proven.

### 2.2 Classical random-oracle model

**Theorem 2 [cited + ours].** Against a prover making `t` random-oracle queries the
knowledge-soundness error is at most

```
t * eps_rbr + 3 (t^2 + 1) / 2^256 + t^2 / 2^257        <= t * eps_rbr + 4 t^2 / 2^256
```

where `eps_rbr` is the largest entry of Theorem 1 with grinding credited. Sources:
`2016-bcs-interactive-oracle-proofs-2016-116` Theorem 7.1 (state-restoration error plus
`3 (m^2 + 1) 2^-lambda`; its construction chains the transcript as this one does);
state restoration from round-by-round soundness, `eps_sr(t) <= t eps_rbr`
(attributed to `2019-cms-succinct-arguments-qrom-2019-834` and stated in the BCS
discussion of `fiat-shamir-security-of-fri-block-etal-2023-1071`); grinding,
`2026-aborting-random-oracles-grinding-fiat-shamir-2026-016` Corollary 3
(`sum_i q_i 2^-tau_i eps_i`). The last term is collisions in the 256-bit chain.

[ours] Corollary 3 is stated for Fiat-Shamir of interactive proofs; applying it to the
rounds of a BCS-compiled oracle proof is immediate from its proof but is not its
statement.

### 2.3 Quantum random-oracle model

**Theorem 3 [cited + model].** Against a prover making `t >= 2^24` quantum queries the
knowledge-soundness error is at most

```
320 (t + k + 1)(t + k) * eps_rbr'  +  6380 t^3 / 2^256  +  lower-order terms
```

where `eps_rbr'` is the largest entry of Theorem 1 **without** any credit for grinding.
Source: `2025-cdhz-pq-snrdx-bcs-2025-2166` ("CDHZ25": Chiesa, Di, Hu, Zheng) Theorem 11.3
(`4 kappa_sr + 4 kappa_extract + 8 kappa_offline + 4 kappa_online + 2 q_V^2 kappa_com`),
Theorem 6.10 (`kappa_sr <= 80 (t + k + 1)(w + k) kappa_rbr + (t + k + 1) k / 2^r_min`)
and Theorem 8.3 (`kappa_offline <= 160 w t^2 / 2^sigma + ..`,
`kappa_online <= 240 w t^2 / 2^sigma`). With `w <= t`: `8 * 160 * (2t + 1)^2 t + 4 * 240 t^3`
gives `6080 t^3`; 300 more for the chain (below). The paper states that both the
quadratic loss and the cubic Merkle term are tight.

Where this protocol departs from the theorem's construction:

- **D1 [model].** Construction 11.7 derives round `i`'s randomness from a separate
  oracle applied to the instance and all commitments so far, and commits every prover
  message. This code chains one 256-bit state through labelled absorptions
  (`FiatShamirTranscript::absorb`, sponge.rs) and absorbs short messages (round
  polynomials, claims, out-of-domain values) in full instead of committing them, which
  is the identity commitment with every position read. Without a collision in the chain
  the challenge is a function of the whole prefix; the bound adds `300 t^3 / 2^256` for
  a collision (`2020-cfhl-compressed-oracle-technique-pq-proofs-sequential-work-2010.11658`
  Theorem 5.29). That a collision-free chain can stand for the per-round full-prefix
  oracles inside the quantum reduction is assumed, not proven here.
- **D2 [open].** No theorem on disk covers grinding against quantum queries. The proven
  bound gives it no credit. `SecurityReport::qrom_work_bits_crediting_grinding` reports
  the heuristic figure and is labelled as such.
- **D3 [model].** cSHAKE256, TurboSHAKE256 and the width-12 Poseidon2 sponge are treated
  as random oracles with independent domains. For Poseidon2 this is a stronger
  assumption than for the Keccak modes: its 256-bit capacity is four Goldilocks limbs
  and its permutation has received less cryptanalysis.

*Security level.* The bound is vacuous at `t = min(2^{(-log2 eps_rbr' - 8.35)/2},
2^{(256 - 12.66)/3})`. The same value is the largest `kappa` with error at most
`t / 2^kappa` for all `t <= 2^kappa`. The second term is `2^81.1` whatever the regime.

*What each digest must resist* [ours].

| Use | Property needed | Why nothing weaker |
| --- | --- | --- |
| Merkle leaves and nodes, every stage | collision resistance | the prover builds the tree, so a second preimage of an honest node is not what it needs; two openings of one position under one root are a collision |
| transcript chain | collision resistance | the prover chooses the absorbed messages; two prefixes with one chain value share every later challenge |
| grinding | preimage of a `b`-bit pattern | `2^b` classical, `2^{b/2}` quantum evaluations |
| Stage-0 salts, coin derivation | pseudorandomness under a secret 256-bit seed | hiding only; no binding role |

A quantum collision costs about `2^85` queries at 256 bits (the review's figure). One
collision lets the prover open one leaf two ways, which does not by itself forge a
proof, so `2^85` is a lower bound on an attack through the digests. The theorem
certifies `2^81`: it charges the first collision in full, because extraction from the
Merkle commitment fails there, and [CDHZ25] shows that bound on the commitment property
is tight. Leaf-index and node-index binding do not help against collisions in a tree the
adversary builds itself.

## 3. Batching proximity loss

The hiding protocol opens one word `U = sum_j beta^j W_j` over five committed words.
What soundness needs is mutual correlated agreement: outside a small set of `beta`,
every codeword within the analysis radius of `U` is `sum_j beta^j P_j` for codewords
`P_j` that agree with the `W_j` on the same set.

**[cited]** [BCGM25] Lemma 9.3: the generator `(1, x, .., x^d)` has mutual correlated
agreement for `RS[F, D, k]`, `rho = k / n`, at every distance
`gamma <= 1 - (1 + 1/(2m)) sqrt(rho)`, `m >= 3`, with error

```
eps_mca = (m + 1/2)^7 * d * n^2 / (3 rho^(3/2) |F|).
```

Hypotheses against the code: `d = 4` (`COMPANIONS`), `n = 4N` points, `rho = 1/4`,
words over `F_p` inside `E`, `beta` uniform in `E \ F_{p^2}` (`PrimitiveChallenge`), so
the bad set has probability at most `eps_mca |E| / |E \ F_{p^2}|`. The claim
`<U, K> = V + sum_j beta^{j+1} sigma_j` is a polynomial of degree four in `beta` for
each list member: `4 l_0` more roots.

**The loss.** Two things, both computed by `bounds::scalar_blend`:

1. the error itself, `2^-199` at `N = 2^18` and `2^-189` at `N = 2^23` for `m = 3`
   (it grows as `n^2`);
2. the Stage-0 queries must be analysed at agreement `(1 + 1/(2m)) sqrt(rho)` instead of
   the `sqrt(rho) (1 + o(1))` the affine folds allow. For tag 4 this turns the
   Stage-0 query error from `2^-256` into `2^-201`.

`m` is a parameter of the analysis, not of the code; the calculator picks the `m` that
maximises the weakest round. The doc comment on `prove` said the loss "is the standard
one for random linear combinations"; the schedule was in fact accounted for the affine
cascade only, and under the scalar blend no regime reaches its nominal per-round figure
(`bounds::tests::no_regime_reaches_its_nominal_level_as_implemented`).

**Cannot be improved by parameters.** [CWYZ26] Proposition 6.1 shows scalar combiners
have worst-case error `Omega(n / q)` at this threshold, and the proven upper bound is
`n^2 / q`. An affine blend removes the factor (section 6, R4).

## 4. Zero knowledge

### 4.1 What the verifier sees

1. The Stage-0 root.
2. `G1`, the row rounds, `(Az, Bz, Cz)(rx)`, `G2`, the column rounds, `sigma_0..sigma_3`.
3. From WHIR on `U`: two out-of-domain values per stage, five scalars per fold, the
   roots of the later stages, their opened fibers and authentication paths, the terminal
   coefficients, the grinding nonces (the smallest valid ones, a function of the
   transcript).
4. At the `q_0` queried Stage-0 fibers: every symbol of `Z` and of the `C_j`, the leaf
   salt, and the authentication siblings, which are hashes of unopened salted leaves or
   of nodes above them.

### 4.2 The blinding lemma

**Lemma 4.1 [ours].** Let `b = blind_cells`. For any set `Q` of at most `b` distinct
nonzero points and any values of the other cells of `Z`, the symbols of the codeword of
`Z` at `Q` are uniform in `F_p^{|Q|}` when the top `b` cells are uniform.

*Proof.* The codeword symbol at `x` is `sum_i c_i x^i`, where `c` is the Moebius
transform of the table: `c_S = sum_{T subset S} (-1)^{|S \ T|} Z_T`. `T subset S`
bitwise implies `T <= S` as integers, so the transform is unitriangular for the integer
order. A table supported on the top `b` cells therefore has coefficients supported on
the top `b` indices, and the map between them is a bijection. Its codeword is
`x^{N - b} R(x)` with `R` uniform of degree below `b`. Evaluation of `R` at `|Q| <= b`
distinct points is surjective (Vandermonde), and `x^{N-b}` is a nonzero scalar at each
point. Adding the contribution of the other cells shifts a uniform vector. QED

This closes a gap in the existing argument: the Lean lemma
`opened_symbols_perfectly_simulated` is about `b` low *monomial* coefficients, while the
code blinds the top *hypercube* cells. The two are equivalent by the triangularity
above. `Layout::new` sets `b = q_0 2^{s_0}`, exactly the number of opened points
(`ZkBound::view_perfectly_simulated`; equality is asserted for every regime and size).

### 4.3 The simulator

**Theorem 4 [ours]. The interactive oracle proof is perfect honest-verifier zero
knowledge**, conditioned on the public event that `mask_rows_full_rank(rx)` holds (the
prover aborts otherwise; the event depends on verifier coins only).

*Simulator.* Given the verifier's coins:

1. Sample `G1` uniformly and each row round uniformly among degree-9 polynomials with
   `s(0) + s(1)` equal to the running claim. Sample `(Az, Bz, Cz)(rx)` uniformly in
   `E^3`. Sample `G2` and the column rounds the same way.
2. Compute the value `V` the verifier assigns to the functional `K`.
3. Pick any base-field table `Z'` with `<Z', K> = V` and uniform top `b` cells. Sample
   `C_0..C_3` uniformly, set `sigma_j = <C_j, K>` and `U' = Z' + sum_j beta^{j+1} C_j`.
4. Run the honest WHIR prover on `U'`, and open the Stage-0 fibers of `(Z', C_j)`.

*Why it is exact.*

- *Row sumcheck.* `g1(x) = sum_i sum_k a_{i,k} x_i^k` with all `a_{i,k}` uniform in `E`
  (`Mask::sample`). The coefficient of `X^k`, `k = 1..9`, of round `i` is the honest one
  plus `rho1 2^{n-i} a_{i,k}`, and `G1` contains `2^n sum_i a_{i,0}`. Since `rho1 != 0`
  (`NonzeroChallenge`) and `2` is invertible, `(G1, s_1, .., s_n)` is uniform over
  consistent tuples whatever the summand. The column sumcheck is the same with
  degree 2. Nothing else about `g1`, `g2` is sent: `g1(rx)` and `g2(ry)` enter `K` only.
- *Row values.* The twelve masking variables add `(k_0 R_0 + k_2 R_2, k_1 R_1,
  k_0 R_0 + k_1 R_1 + 2 k_2 R_2)` to `(Az, Bz, Cz)(rx)`, with `R_g` uniform in `E` when
  the four corner weights are an `F_p`-basis (`CornerPadBasis`) and determinant
  `k_0 k_1 k_2 != 0` (`mask_rows_full_rank`). No other row uses these variables.
- *The blend.* `beta` has degree four over `F_p`, so `beta, .., beta^4` is a basis of
  `E` and `(C_j) -> sum_j beta^{j+1} C_j` is a bijection onto `E^N`: `U` is uniform and
  independent of `Z`. Given `U`, `beta` and `V`, the claims are determined:
  `sigma_j = <pi_j(U), K> - e_j V`, where `pi_j` are the coordinates in that basis and
  `1 = sum_j e_j beta^{j+1}`. So `(sigma, U)` depends on `Z` through `V` alone.
- *`Z'` exists.* The `F_p`-span of the entries of `K` is `E`: changing the constant
  coefficient of `g1` by `delta` changes `<Z, K>` by `delta (2^n + lambda^2)`, changing
  its linear coefficient in the first variable changes it by
  `delta (2^{n-1} + lambda^2 rx_0)`, the quadratic one by
  `delta (2^{n-1} + lambda^2 rx_0^2)`, and these cannot all vanish.
- *Opened symbols.* `K` reads no blinding cell, so by Lemma 4.1 the opened symbols of
  `Z` are uniform and independent of everything above. The opened symbols of the `C_j`
  are the coordinates of `U(x) - Z(x)`.
- *Everything else* WHIR sends (later-stage oracles in full, out-of-domain values,
  folds, terminal coefficients) is a function of `U` and the coins. No later-stage
  query needs a blinder, and the count of blinders is compared with Stage-0 symbols
  only. QED

**The full codeword of `Z` determines the witness**, as the parallel experiment found:
`b` blinders cover exactly `b` symbols. This is not a defect of the statement above,
which is about a verifier who sees the `q_0` queried fibers; it means there is no slack.
One more opened fiber of `Z` than the layout provides would leak.

**Repeated proofs.** With fresh seeds two proofs of one witness have independent masks,
companions, blinders and salts, and the simulator runs once per proof. With the same
seed, relation, statement, witness and regime the proof is the same string. The case
"same seed, different regime" is the failure in section 0.

**Non-interactive statement [ours, after `2016-bcs-..-2016-116` section 7.4].** In the
explicitly programmable random-oracle model the simulator programs the transcript oracle
along its simulated transcript and commits to `(Z', C_j)` honestly. Real and simulated
proofs differ only in the unopened Stage-0 leaves, which are hidden as in section 4.4,
and in programming collisions, at most `(t + P) P / 2^255` classically. [open] The
quantum version of the programming step needs an adaptive-reprogramming lemma that this
document does not supply; the quantum figure below covers the hiding term only.
[BCS16] Theorem 7.1 itself does not apply: it needs `2 lambda`-bit salts for statistical
hiding against unbounded queries.

**Seed.** Coins are `cSHAKE256(seed, relation digest, schedule, H(statement),
H(witness))`. Their pseudorandomness is the random-oracle assumption on cSHAKE256 with
a uniform 256-bit seed: `t / 2^256`.

### 4.4 Hiding of unopened leaves

What the leaves are, per regime:

| Regimes | Stage-0 leaf | Later-stage leaf |
| --- | --- | --- |
| 4, 5, 6 (cSHAKE256) and 9, 10 (TurboSHAKE256) | 256-bit hash of tag, arity, table count, leaf index, **16-byte salt**, `5 * 2^{s_0}` field elements (`hash_round0_leaf_mode`, pcs.rs) | 256-bit hash of tag, stage, leaf index, `2^{s_i}` elements of `E`; no salt |
| 7, 8 (Poseidon2) | four limbs; capacity `[leaf index, arity, table count, 0]`, rate: the same **16-byte salt** in three limbs, then the symbols (`poseidon2_round0_leaf`, pcs.rs) | four limbs; no salt |

Salts are `H(tag, salt_seed, leaf index)` truncated to 128 bits, with a 256-bit
`salt_seed` from the coin stream.

**Later stages need no hiding.** Their leaves are functions of `U`, which the simulator
reproduces exactly; an adversary who inverted every such hash would learn nothing about
the witness. The absence of salts there is correct.

**Stage 0 [ours].** An unopened leaf influences the view only through hashes. The
adversary learns something only if it queries the oracle at a leaf's exact preimage,
which contains that leaf's salt. A query names one leaf index, so it can match at most
one leaf per proof:

- classical: `Pr <= t P / 2^128`;
- quantum: distinguishing advantage at most `2 t sqrt(P / 2^128)`, by
  `2018-ahu-semi-classical-oracles-o2h-2018-904` Theorem 3 with the set of leaf
  preimages as the reprogrammed set.

The quantum figure is the proven one and it is poor: `2^-23` at `t = 2^40`, vacuous at
`t = 2^63`. It ignores that each Stage-0 leaf also contains `4 * 2^{s_0}` companion
symbols the adversary does not know. [open] Turning those into a bound requires showing
that the evaluations of `U` on an unopened fiber are independent of the few thousand
linear functionals of `U` the proof reveals; the count leaves ample room (`N >= 2^18`
unknowns) but no lemma here proves it. **No confirmation attack on a guessed witness is
known**: a guess of the witness does not determine a leaf without `U` on that fiber and
the salt.

## 5. Numbers

Command (prints every row below and more):

```sh
cargo test --release -p qsag-agg --lib -- \
  zk_hem::bounds::tests::print_security_tables --ignored --nocapture
```

Bits are `-log2` of an error; "level" is the query count at which a bound is vacuous.
`rbr` is the weakest round of Theorem 1 with grinding credited (classical) and without
(QROM). Relations with `2^r` rows and `2^r` variables commit `2^{r+1}` cells.

### 5.1 Committed-mask zk-Hem as implemented

| Tags | Rows | rbr, classical (round) | rbr, no grinding (round) | Classical level | QROM level: digest / round term | QROM error at `t = 2^40`, `2^64` | Proof bytes (bound) |
| --- | ---: | --- | --- | ---: | --- | --- | ---: |
| 4, 9 | 2^17 | 198.9 (blend) | 198.9 (blend) | 127.0 | **81.1** / 95.3 | 2^-109.6, 2^-50.3 | 528,380 |
| 4, 9 | 2^20 | 192.9 (blend) | 192.9 (blend) | 127.0 | **81.1** / 92.3 | 2^-103.6, 2^-50.3 | 896,644 |
| 4, 9 | 2^22 | 188.9 (blend) | 188.9 (blend) | 127.0 | **81.1** / 90.3 | 2^-99.6, 2^-50.3 | 966,957 |
| 5, 7, 10 | 2^17 | 192.7 (blend) | 187.5 (Stage-0 queries) | 127.0 | **81.1** / 89.6 | 2^-98.2, 2^-50.2 | 426,876 |
| 5, 7, 10 | 2^20 | 188.4 (blend) | 183.5 (Stage-0 queries) | 127.0 | **81.1** / 87.6 | 2^-94.2, 2^-46.2 | 716,932 |
| 5, 7, 10 | 2^22 | 184.4 (blend) | 180.9 (Stage-0 queries) | 127.0 | **81.1** / 86.3 | 2^-91.6, 2^-43.6 | 773,101 |
| 6, 8 | 2^17 | 191.2 (blend) | 191.2 (blend) | 127.0 | **81.1** / 91.4 | 2^-101.9, 2^-50.3 | 455,004 |
| 6, 8 | 2^20 | 186.7 (blend) | 186.7 (blend) | 127.0 | **81.1** / 89.2 | 2^-97.3, 2^-49.3 | 764,580 |
| 6, 8 | 2^22 | 184.4 (blend) | 184.4 (blend) | 127.0 | **81.1** / 88.0 | 2^-95.0, 2^-47.0 | 825,197 |

The full-shard parent of section 9.2 (tag 8, `2^21` rows, `2^22` cells): rbr 185.4
(Stage-0 queries), classical level 127.0, QROM level 81.1, size bound 799,980 bytes
against 780,083 measured (the bound counts shared authentication siblings twice).

Zero knowledge, every regime and size: perfect for the oracle proof; hiding
`t P / 2^128` classical, `2 t sqrt(P) / 2^64` quantum.

### 5.2 The public opening alone (non-hiding Hem, hologram, recursion)

| Tags | Cells | rbr, classical (round) | rbr, no grinding (round) | Classical level | QROM level: digest / round term |
| --- | ---: | --- | --- | ---: | --- |
| 4, 9 | 2^21 | 247.5 (kernel fold) | 240.1 (shift batching) | 127.0 | **81.1** / 115.9 |
| 5, 7, 10 | 2^21 | 215.9 (Stage-0 queries) | 199.9 (Stage-0 queries) | 127.0 | **81.1** / 95.8 |
| 6, 8 | 2^21 | 213.8 (Stage-0 queries) | 213.8 (Stage-0 queries) | 127.0 | **81.1** / 102.7 |
| 2 | 2^21 | 143.2 (Stage-0 queries) | 127.2 | 127.0 | 59.4 (round term) |
| 2 | 2^18 | 141.4 (stage 2 queries) | 125.4 | 127.0 | 58.5 (round term) |

The public paths reveal the assignment and claim no zero knowledge (section 9.1).

### 5.3 Against the constants the code asserts

- `pure_query_target_bits` (256, 214, 200): met by every stage of every QROM regime at
  `2^17..2^24` cells, with the fold loss included
  (`stage_bounds_against_the_constants_asserted_by_the_regimes`). Tag 2: 124.5, not 128.
- Stage affine-combiner error below `2000 / p^4` (`AFFINE_PROTOCOL.md`): met, 247 bits or
  more.
- `classical_fs_round_bits` (272, 216, 214): this is queries plus grinding in one round.
  The rounds without grinding sit at a list size over the field, 240 to 248 bits, so 272
  is not a per-round error of the protocol; for the hiding protocol the blend lowers
  every regime to 184..199.
- `qrom_grover_round_bits` (136, 108, 107): not security levels. See section 0.
- The bounded-query profiles (tags 5, 7, 10 at `Q <= 2^38`; 6, 8 at `Q + 1 <= 2^40`):
  with grinding credited as a factor `2^-16` inside the [CDHZ25] bound, the query term
  of the *public* opening is `320 * 2^76 * 2^-216 < 2^-128`; that is the origin of the
  name. Under Theorem 3 (no credit) the public opening gives `2^-114.5` (tags 5, 7, 10)
  and `2^-122.3` (tags 6, 8, digest-bound) at those caps, and the hiding protocol
  `2^-95` to `2^-106`.

`is_accepted_aggregate_profile()` therefore accepts profiles that are equivalent today:
127 bits classical, 81 bits QROM. Acceptance does not need to change. Its documentation
does (R5).

## 6. Required parameter changes

Costs are for tag 4 at `2^20` rows (896,644 bytes, 4,199 digests, 258 Stage-0 queries,
425,984 tree hashes, `2^20` grinding hashes), from
`bounds::tests::required_changes_are_costed`.

**R1. Coins bind the schedule. Done** (protocol.rs, one line in
`prove_with_claimed_publics`). Cost: none. Proofs for a given seed change; no test
pinned them.

**R2. Stage-0 salts: 16 to 32 bytes.** `derive_round0_salt*` output length,
`HemWhirOpeningProof::round0_salts: Vec<[u8; 32]>`, the leaf framings
(`hash_round0_leaf_mode`: salt at bytes 7..39; `hash_salted_base_group_mode`: 6..38;
`poseidon2_round0_leaf`: five limbs of at most 7 bytes instead of three), the wire
reader, and the recursive verifier's leaf gadget. Buys: quantum hiding
`2 t sqrt(P) / 2^128` (`2^-87` at `t = 2^40`), classical `t P / 2^256`. Cost: 16 bytes
per opened Stage-0 leaf, **+4,128 bytes (0.46 %)**; 16 more bytes hashed per leaf (at
most one more Keccak block; two more Poseidon2 rate limbs). New wire version.

**R3. Digests: 32 to 48 bytes (or 50).** `CanopyCommitment::root`,
`CanopyMultiProof::auth_siblings`, `MerkleCanopyTree::nodes`, the transcript
`chain_digest`, every `*_32` canopy call. An internal node becomes
`1 + 4 + 2 * 48 = 101` bytes, still one cSHAKE256 or TurboSHAKE256 block, so the hash
count and time do not change. Buys: QROM digest term 81.1 to **123.8** bits (48 bytes)
or **129.1** (50 bytes); classical collision level 127 to 191. Cost: 16 bytes per
digest, **+67,184 bytes (7.5 %)**; 50 bytes: +75,582 (8.4 %). For the Poseidon2 regimes
(7, 8) this is not a parameter change: a 384-bit digest is six limbs, which needs a
sponge with capacity six (rate six instead of eight) and a re-derivation of the
recursive verifier's hash gadgets and row budget.
After R3 the hiding protocol is limited by its blend at 86 to 95 bits and the public
opening at 96 to 116.

**R4. Affine blend for the hiding protocol (design change, not mechanical).** Replace
`U = sum_j beta^j W_j` by the cascade `sum_i (a_i + b_i X) W_i` that `whir_open_batch`
already uses (`pcs::affine::cascade_weights`). Error: four applications of [CWYZ26]
Theorem 5.1 instead of [BCGM25], and the Stage-0 threshold returns to the fold
threshold. With R3: round term 92.3 to **115.9** bits, the ceiling of the field. Cost:
no bytes; one more degree, inside the two overflow slots. **It is not zero knowledge as
it stands**: the image of `(C_j) -> sum_j (a_j + b_j X) C_j` has codimension four over
`F_p` in the space of words of degree `N`, so `U` reveals one `E`-valued linear
functional of `Z`. Four more blinding cells and a rank lemma in the style of Lemma 4.1
(jointly for the opened symbols and that functional) are required first. Until then the
scalar blend stays, and its loss is the number in section 5.1.

**R5. Documentation of the regimes. Done** (doc comments of pcs.rs only). The enum, tag 2, tag 4, tag 9,
`meets_unconditional_grover_128_floor` and `whir_stage_schedule` now state the levels of
this document instead of "unconditional Johnson-radius QROM budget". Not done, because
they change public names or wire-visible behaviour and are the owner's call:

- renaming the `*Qrom128` variants and `meets_unconditional_grover_128_floor`;
- tag 2: `ceil(256 / log2 B) + 1` gives 124.5 bits per query round at worst;
  `ceil(256 / log2 B) + 3` restores 128 at every stage for `2^17..2^24` cells
  (`bounds::min_queries`), if the tag is ever used outside tests.

**Not a parameter: 128-bit QROM.** Under Theorem 3 it needs `eps_rbr' <= 2^-264.4` and
digests of 400 bits. Options, none taken here: a quintic or sextic extension of
Goldilocks for the challenges (every round polynomial, fold scalar and terminal
coefficient grows by a quarter or a half); a theorem that credits grinding against
quantum queries (D2); or stating the claim as a bounded-query one, which is what the
numbers in section 5 support (`2^-99` or better up to `2^40` queries for tag 4).
Grinding the rounds that have none (`algebraic_pow_bits = 24`, about `2^30` hash
evaluations per proof instead of `2^20`) lifts the classical round term to 216 and the
heuristic QROM figure, and changes no proven QROM number.

## 7. Newer constructions

What was read, and what each would buy here.

- **Proximity gaps at the Johnson radius.** `bchks-proximity-gaps-..-2025-2055` proves
  correlated agreement up to the Johnson radius with `O(n)` exceptional scalars instead
  of the `O(n^2)` of `bciks-proximity-gaps-reed-solomon-2020-654`, and shows `n^1.99`
  is needed at or beyond it. That is correlated agreement for a line; the *mutual*
  version this protocol needs is [Hab25]/[BCGM25] with `n^2`. If the `O(n)` bound is
  extended to mutual agreement of the powers generator, the blend of section 3 gains
  about 20 bits with no code change. [CWYZ26] already gives `O(1/q)` for affine
  combiners and is what the folds use.
- **Above the Johnson radius.** `fri-soundness-above-johnson-2026-858` claims an
  unconditional bound for FRI, STIR and WHIR above Johnson by doubling queries. Its
  proof was not checked here and nothing depends on it. The capacity conjectures stay
  refuted; fewer queries than the Johnson schedule are not available on proven ground.
- **WHIR-based stacks.** `grey-openvm-swirl-whitepaper` (SWIRL over WHIR) states "We do
  not claim zero knowledge"; `sok-hash-based-pcs-fri-basefold-stir-whir-2026-1367`
  surveys FRI, Basefold, STIR and WHIR and does not treat hiding variants. No hash-based
  multilinear commitment with native zero knowledge was found on disk or by search that
  would replace the masking here; one search hit, "Sum-Checking SmallWood" (eprint
  2026/2880), could not be fetched and was not read.
- **Zero-knowledge codes.** `code-based-scalable-collaborative-snarks-lagrange-2026-729`
  section 2.1 uses `l`-zero-knowledge codes: any `l` codeword symbols reveal nothing.
  Lemma 4.1 says the encoding of `Z` already is one with `l = blind_cells`. What that
  paper adds is the collaborative setting, where each party encodes its own share with
  its own randomness. A split commitment of that shape must satisfy Lemma 4.1 for the
  *sum* table (the sum of uniform blinders is uniform, so one honest party suffices);
  this crate has none.
- **Sumcheck masking.** zk-Hem uses the Libra mask (`libra-2019`, a separable
  polynomial committed with the witness): 64 cells per row round and 16 per column
  round. `2024-frigo-shelat-anonymous-credentials-from-ecdsa-ligero-sumcheck-2024-2010`
  instead appends a one-time pad for the sumcheck transcript to the committed witness
  and proves the decrypted transcript. Both commit about one field element per
  transcript element, and neither shortens the proof at these sizes, because the
  opening dominates (the front messages are under 10 KB of 430 to 970 KB).
- **Grinding.** `2026-aborting-random-oracles-grinding-fiat-shamir-2026-016` proves
  the classical accounting used in Theorem 2. Nothing comparable exists for quantum
  queries (D2).
- **Existing calculators.** `grey-ethereum-soundcalc-*` (ethereum/soundcalc) computes
  per-round classical error bits for FRI and WHIR in the unique-decoding and Johnson
  regimes, with grinding, and a proof-size estimate (rows `whir_fold_rbr`,
  `whir_ood_rbr`, `whir_query`, `whir_shift_rbr`). It has no quantum composition, no
  Merkle term and no zero-knowledge accounting, and it assumes scalar folding.
  `bounds.rs` follows its row structure for the parts they share.

## 8. Tests and commands

```sh
cargo test --release -p qsag-agg --lib -- zk_hem::bounds
```

runs `logarithms_bracket_the_true_value`,
`query_error_matches_the_hypergeometric_product`,
`finite_witnesses_of_the_schedule_are_reproduced`,
`stage_bounds_against_the_constants_asserted_by_the_regimes`,
`reports_are_pinned_at_the_project_sizes`,
`no_regime_reaches_its_nominal_level_as_implemented`, `required_changes_are_costed`,
`proof_size_model_brackets_the_measured_full_shard_proof`,
`layout_matches_the_protocol` and `coins_do_not_repeat_across_regimes`.

## 9. Inventory of the earlier audit

The audit, the measurements and the red/green runs of this section were made on the
`dregg-sig` fork of this crate (taken at qsag `cf41f1c`; its `crates/agg` is this crate
with `dregg_sig_*` identifiers) and ported here unchanged. Package names in the
commands are this repository's.

### 9.1 Full-shard witness leak and repair

The original parent used `prove_public_hologram`. Its serialized `eval_z` is an
unmasked multilinear evaluation of the parent assignment. Given two complete
candidate child-proof sets with the same committee, message and signer count, an
observer can construct both assignments, replay Fiat–Shamir to recover `ry`, and
compare the two evaluations with `eval_z`. This distinguishes the candidates; it
is not an algorithm for recovering arbitrary signer sets without auxiliary input.

`zk_hem::full_shard::tests::full_shard_candidate_witness_distinguisher` reproduces
this with one child, two committee keys and one signer. Two slots and one child
are the smallest supported full-shard geometry. The pre-fix test required neither
candidate to match and failed with `[false, true]`. The final test retains the
public hologram attack as a positive control and applies the terminal-evaluation
comparison to the committed-mask parent. It reconstructs candidate-consistent
row-mask cells from the public row values first, so random row masks alone cannot
make the comparison appear protected. It then compares the candidate's unmasked
column claim with the transmitted masked terminal claim.

This is regression evidence for that distinguisher on this deterministic fixture.
The zero-knowledge statement for the committed-mask parent is Theorem 4. The final test also
roundtrips both full-shard carriers and rejects their old wire versions.

The relation is compatible with the existing committed-mask path without changing
its constraint semantics:

1. `ConstraintSystem::finish`, including its hologram-aligned layout, appends
   twelve fresh variables and twelve rows of the forms `r * 1 = r`, `1 * r = r`,
   and `r * 2 = 2r`. The other constraints do not reference these variables.
2. `protocol::prove` overwrites these cells. Its rank check certifies the local
   map from these pads to the three disclosed row evaluations at the sampled
   point. The row sumcheck itself also receives a committed separable mask.
3. The column sumcheck receives its own committed mask. Its final claim is
   `M(rx, ry) Z(ry) + rho2 g2(ry)`; neither `Z(ry)` nor `g2(ry)` is sent.
4. The mask checks, public inputs and terminal claim are batched into a linear
   functional. Four companion tables, opening blinders and salted leaves use the
   existing `protocol::prove` machinery, analysed in sections 2 to 5.

The public hologram's verifier expects an unmasked terminal claim and standalone
`eval_z` opening. Merely randomizing its assignment or hiding the `eval_z` field
would not implement the masked checks. The selected repair uses the existing
full-shape masked verifier instead: verification scans the relation matrices,
and no hologram is compiled or retained during full-shard setup. A sublinear
masked hologram verifier would require an additional protocol design.

Compatibility changes: the parent payload is now `ZkHemProof`; inner wire magic
is `QSAGFSM2`, outer wire magic is `QSAGFSA2`, and the parent statement label is
`QSAG.FULL.SHARD.MERGE/v2`. Old non-hiding carriers are rejected. The full-shard
relation's obsolete `hologram()` and `verifier_key()` accessors were removed;
`shape()` supplies the verifier relation. Other hologram APIs remain available
and explicitly non-hiding. A rank-deficient mask challenge is reported as
`FullShardError::MaskRankDeficient`, allowing retry with a fresh secret seed.

### 9.2 Smallest-fixture measurement and validation

One real child, two committee slots, one signer, JortsPoseidon2 height 6, using
`Poseidon2Cdhz25ZeroPowQrom128` (107 nominal Grover bits, `Q + 1 <= 2^40`). The
relation has 1,719,058 variables and 2,097,152 padded rows. Measurements are single
runs on hbox under `SWARM_MEM_MAX=16G swarm-build`, release Rust 1.99.1; they are
not general performance bounds. Both rows below come from the same final test run.
Proof sizes include the eight-byte parent framing. Proving timings include
serialization, exclude relation/hologram setup, and the masked wrapper also
reconstructs its assignment.

| Parent path | Serialized bytes | Prove seconds | Verify seconds |
| --- | ---: | ---: | ---: |
| Public hologram control | 1,368,818 | 47.210 | 0.020 |
| Committed-mask full-shard parent | 780,091 | 6.864 | 0.127 |

Full-shard setup without compiling a hologram took 1.843 seconds. The original
pre-fix run, including hologram setup, took 16.126 seconds to set up and produced
1,367,922 bytes in 51.982 seconds. Its evaluation test failed with `[false, true]`;
the final test passes, including the public positive control and both versioned
wire roundtrips. The public control in the final run uses the new statement label,
so its Fiat–Shamir points and Merkle proof size differ slightly from the pre-fix run.

The exact red/green command was:

```sh
SWARM_MEM_MAX=16G swarm-build cargo test --release -p qsag-agg --lib \
  zk_hem::full_shard::tests::full_shard_candidate_witness_distinguisher -- --exact --nocapture
```

Logs: `/var/tmp/dregg-sig-astra-aggclaims-red.log` and
`/var/tmp/dregg-sig-astra-aggclaims-green.log` on hbox. The test was written and
executed against the original non-hiding prover before changing its production
path. Its observer adapter was then updated for the masked wire transcript, with
the original observer retained as a positive control. No other new unit test was
introduced in this change.

### 9.3 Claims corrected in the earlier audit

| Location | Correction |
| --- | --- |
| Root `README.md`, aggregation row and credential row’s aggregation reference | Removed unqualified zero-knowledge claim and the implication that all recursion uses masking; described witnessed policies rather than guaranteed policy privacy. |
| `src/lib.rs`, committed-mask relations section | Qualified privacy/security status and corrected the list of backend users. |
| `src/zk_hem.rs`, module documentation | Distinguished Lean masking ingredients from the unproved composition. |
| `src/zk_hem/protocol.rs`, module and `ZkHemProof` documentation | Qualified zero-knowledge wording and scoped uniformity claims to ideal ingredient sampling. |
| `src/zk_hem/protocol.rs`, `prove_public_hologram` | Explicitly documented the unmasked row values and `eval_z` disclosure. |
| `src/zk_hem/full_shard.rs`, module, relation, proof and prover documentation | Described committed masks, full-relation verification, secret-seed requirement and remaining bounds. |
| `src/recursive.rs`, `SuccinctFullShardAggregate` and its prover | Replaced unconditional signer hiding with the actual masking/security scope and seed requirement. |
| `src/zk_hem/recursive_whir.rs`, `FixedPathWhirProof` and `commit_for_recursion` | Distinguished omitted witness serialization from hiding; public merge remains non-hiding. |
| `src/zk_hem/blind_vc.rs`, module documentation | Bounded selective-disclosure expectations by backend limitations. |
| `src/zk_hem/multisig.rs`, module documentation | Described witnessed policy/active bits rather than guaranteed secrecy. |
| `src/zk_hem/capability.rs`, module, presentation-tag function and proof documentation | Removed unconditional hiding, zero-knowledge and unlinkability claims; specified deterministic per-context tags. |
| `src/zk_hem/capability/offline.rs`, delegated relation documentation | Qualified the presentation's masking/security scope. |
| `src/pcs.rs`, regime, bounded variants and policy predicates | Gave 108/107-bit estimates and query caps; renamed policy membership predicates. |
| `src/lib.rs`, `src/arithmetize.rs`, `AFFINE_PROTOCOL.md`, profile-policy descriptions | Replaced generic QROM-128-floor language with the actual acceptance policy. |
| `src/sponge.rs`, `keccak_p1600_12` | Removed unsupported implication of composed WHIR QROM security from the permutation description. |


### 9.4 Validation commands of the earlier audit

The following existing tests also passed on hbox using the same release binary.
Each was run separately with
`SWARM_MEM_MAX=16G swarm-build cargo test --release -p qsag-agg --lib <name> -- --exact --nocapture`:

- `zk_hem::full_shard::tests::full_shard_merge_end_to_end_and_tamper_rejection`
- `recursive::tests::succinct_full_shard_aggregate_needs_no_child_and_binds_its_statement`
- `zk_hem::full_shard::tests::variable_height_jorts_recursive_shard_and_masked_merge`
- `pcs::pcs_unit_tests::exact_regime_ladder` (also passed on pre-fix source,
  establishing the old predicate's accepted 107/108-bit profiles)

Local checks passed:

```sh
cargo check -p qsag-agg --all-features
cargo check -p qsag-agg --no-default-features
cargo check -p qsag-agg --tests --all-features
cargo check --manifest-path fuzz/Cargo.toml --bin fuzz_hologram_and_subtree_decode --bin fuzz_whir_agg_verify
cargo doc -p qsag-agg --no-deps
```

Rustdoc completed with existing unresolved/private intra-doc-link warnings. No
fuzz campaign was run; the fuzz targets were adapted and compile-checked.
No CLI or quorum callers required changes. Source edits stay within `crates/qsag-agg`,
the two affected fuzz targets, and root README aggregation-related text.

### 9.5 WHIR profile policy

`WhirSecurityRegime::is_accepted_aggregate_profile()` reports verifier policy
membership. It is not a security floor. The nominal single-round figures it is built
from (136 for tags 4 and 9; 108 for tags 5, 7, 10 with `Q <= 2^38`; 107 for tags 6, 8
with `Q + 1 <= 2^40`) are asserted by `pcs::pcs_unit_tests::exact_regime_ladder`; what
they do and do not establish is section 5.3.

