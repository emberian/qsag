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

## V2. zk-Hem v2

Status: design, proofs and calculator. The implementation state is in V2.9. Sections 0 to 9
below describe v1, which v2 does not change; v2 lives in `src/zk_hem/v2/` behind its own
wire magic and profile tags. Labels in this section: **[lean]** a checked theorem in
`lean/Qsag` (theorem named), **[proof]** an argument in this section, **[cited]**, **[model]**,
**[open]** as above. A source file alone is not evidence of a successful Lean build.
"[ours]" in sections 0 to 9 is the same thing as [proof] here.
V2.6 lists formalization targets and their precise scope; validation status is in V2.9.

### V2.0 What changes and why

| | v1 | v2 | Reason |
| --- | --- | --- | --- |
| Challenge field `E` | `F_{p^4}` | `F_{p^5} = F_p[X]/(X^5 - 3)` | a 128-bit QROM level needs round errors below `2^-264.4` (Theorem 3); `|F_{p^4}| = 2^256` cannot give them |
| Committed in Stage 0 | five base-field tables of `N` cells | one base-field table `Z` of `N` cells and one `E`-valued word `R` on the folded domain (`N / 2^s + 2` coefficients) | four of the five base-field Reed-Solomon encodings are companions; at the v1 tag-4 `2^21`-cell fixture their opened symbols occupy `258 * 64 * 4 * 8 = 528,384` bytes of the 896,644-byte model (58.9 %) |
| Table size | `N >= 2 * 2^k` | smallest `N >= 2^16` holding variables, masks and blinders in one cube | the layout doubled every table |
| Batching of committed words | `Z + sum beta^j C_j` on `4N` points, `[BCGM25]` with `d = 4` | `fold^s(Z) + beta R` on `4N / 2^s` points, `[BCGM25]` with `d = 1` | error falls by `4 * 2^(2s)`; this was the weakest round |
| Stage-0 out-of-domain points | 2 | 5 | they are the masks of the fold scalars (Lemma V2.3) |
| Digests, chain value | 256 bits | 400 bits | `6380 t^3 / 2^sigma` at `t = 2^128` |
| Stage-0 salt | 128 bits | 256 bits | hiding term (R2 of section 6) |
| Grinding | 0 or 16 bits | none | no proven quantum credit (D2); the classical level is collision-bound either way |
| Masking variables of a relation | 12 (three groups of four) | 15 (three groups of five) | an `E`-value has five base-field coordinates |
| Profile names | `*Qrom128` | `CshakeJohnson400`, `TurboShakeJohnson400` (tags 16, 17) | name the mechanism; levels are computed (V2.7) |

**Departures from the recommendation this implements** (`zkhem-frontier.md`, section 5.2):

1. *The mask is blended by a scalar line, not by the affine combiner.* With
   `g = P + (a + bY) R` the prover must send two claims on `R` (`<R, v>` and `<YR, v>`) for
   one equation, so the transcript reveals `P(-a/b)` and `<(P - P(-a/b)) / (a + bY), v>`, a
   functional of the witness whose restriction to the blinders depends on the kernel `K` of
   the statement. No closed-form rank lemma covers it. The scalar line reveals nothing
   (Lemma V2.4) and its `[BCGM25]` error stays below `2^-264.6` up to `N = 2^24` (at the `m`
   of V2.7) because it lives on the folded domain. The price is Stage-0 queries: 266 would do at the fold
   threshold; the line needs the counts of V2.7. A two-mask affine cascade that is zero
   knowledge under a checkable rank condition is sketched in V2.8 and not adopted.
2. *"About 160 more blinder cells" is `25 * 2^s` (1,600 at `s = 6`).* The fold scalars are
   not covered by counting them. They are covered by five out-of-domain evaluations, each of
   which costs five base-field blinders per residue class (Lemma V2.2).
3. *266 Stage-0 queries* is replaced by the table of V2.7 (item 1).
4. *Tables above `2^24` cells* do not reach `2^-264.4` with this mask line at rate 1/4 and
   `s = 6`; v2 profiles reject them.
5. *Poseidon2 profiles* do not exist in v2: a 400-bit digest is seven Goldilocks limbs, two
   children of seven limbs do not fit one width-12 permutation, and the sponge rate would
   fall from eight to five (V2.10).

Precedent, and what it does not provide. ProveKit's zkWHIR overlays a sparse mask on the
witness and uses out-of-domain openings for hiding
(`2026-worldfnd-provekit-v2-whitepaper-wip-zo0k`, sections 5.3 and 5.4); its zero-knowledge
appendix D.1 is unwritten ("tbc") and the code states "Assumed: the shared-tree variant
preserves the ZK bound". The proven zero-knowledge WHIR,
`2026-chiesa-fenzi-weissenberg-zk-iopps-constrained-interleaved-codes-rev-2026-11-16-2026-391`
(Corollary 2), uses a zero-knowledge encoding, which raises the degree and is a different
commitment. `2026-feneuil-provin-rivain-sum-checking-smallwood-hash-based-zk-arguments-2026-2880`
Lemma 1 proves the count used in Lemma V2.2 from the other side: a base-field mask with fewer
than `[E : F_p]` coordinates cannot hide an `E`-valued evaluation. The proofs below are this
project's.

### V2.1 The protocol

`p = 2^64 - 2^32 + 1`, `E = F_p[X]/(X^5 - 3)`, `sigma` the Frobenius map of `E` (it fixes
exactly `F_p`; `E` has no other proper subfield because 5 is prime). A v2 relation has `2^n`
rows, `num_vars` variables (variable 0 is the constant 1, then the public inputs, the
witness, and fifteen masking variables in three groups of five) and three corners of eight
rows at the top of the row cube, five rows used in each: `p * 1 = p`, `1 * p = p`,
`p * 2 = 2p`. `k = ceil(log2 num_vars)`. Valid dimensions have `n >= 5`,
`n < usize::BITS`, `num_vars >= 16`, and `num_public <= num_vars - 16`; the latter keeps
the constant and the fifteen secret pads outside the public-input slice. `Layout` rejects
dimensions outside these conditions before doing size arithmetic.

**Table.** `Z` in `F_p^N`, `N = 2^l` (`params::Layout`):

```text
[ variables | 0 | row masks | column masks | 0 | blinders ]
  0   num_vars  var_cells                        N - b    N
```

`var_cells` is `num_vars` rounded up to a multiple of `2^max(4, k - 8)`. The row mask holds
`n` rounds of five limbs of sixteen cells, the column mask `k` rounds of five limbs of four
cells, as in v1 with five limbs. The top `b = 2^s (q_0 + 25)` cells are uniform, where `s`
and `q_0` are the folds and queries of Stage 0. `l` is the smallest value in `16..=24` for
which everything fits. `b` and `N - b` are multiples of `2^s`.

**Commitment.** `c` in `F_p^N` is the vector of monomial coefficients of the multilinear
polynomial with hypercube values `Z`; `Z^(x) = sum_i c_i x^i` is its codeword on a coset
`D_0` of `4N` points. `R` in `E[Y]` is uniform of degree at most `N / 2^s + 1`, with codeword
on `D' = {x^(2^s) : x in D_0}` (`4N / 2^s` points). Leaf `g` of the one Stage-0 tree holds a
32-byte salt, the `2^s` symbols of `Z^` on fiber `g` (the points over `y_g` in `D'`) and the
symbol `R^(y_g)`.

**Kernels.** A linear claim on a polynomial with coefficient vector `c` is `<c, kappa> = v`.
Two kinds of term occur: *tensor terms* (`kappa_i = w prod_j r_j^{bit_j(i)}`, zero on
overflow coefficients) and *point terms* (`kappa_i = w x^i` for every coefficient index,
overflow included). The fold of `pcs/affine.rs` maps `kappa` to
`v = kappa_even + phi kappa_odd`; a point term at `x` with weight `w` becomes the point term
at `x^2` with weight `w (1 + phi x)`, exactly, because its geometric continuation is kept on
the overflow coefficients. (v1 truncates every term at the overflow slot. Soundness holds for
any fixed kernel; Lemma V2.3 needs point terms to be evaluations.)

**Rounds.** Each challenge is drawn after the listed prover message is absorbed.

| # | Prover | Verifier |
| --- | --- | --- |
| 0 | Stage-0 root; bound: magic, profile, relation digest, layout, schedule, statement, public inputs | `tau` in `E^n` |
| 1 | `G1 = sum g1` | `rho1 != 0` |
| 2 | `n` row rounds, degree 9 | `rx_i` |
| 3 | `(Az, Bz, Cz)(rx)` | three weights |
| 4 | `G2 = sum g2` | `rho2 != 0` |
| 5 | `k` column rounds, degree 2, of `M(rx, y) Z_var(y)` | `ry_i` |
| 6 | none | `lambda` |
| 7 | none | `omega_1..omega_5` in `E` |
| 8 | `a_j = Z^(omega_j)`, `j = 1..5` | weights `w_1..w_5` |
| 9, per fold `i < s` | `sigma_even, tau_01, tau_10` | `phi_i` |
| | `c_F, c_G` | `theta_i, alpha_i, beta_i` |
| 10 | `mu = <R, v_s>` | `beta_R != 0` |
| 11 | root of the Stage-1 oracle, the codeword of `g = P_s + beta_R R` | two out-of-domain points |
| 12 | two evaluations of `g` | `q_0` distinct Stage-0 fibers; two weights and `gamma` |
| 13.. | the WHIR of v1 on `g` (stages 1.., over `E`, no grinding, no salts), except that the point terms of every stage (out-of-domain and query claims) keep their exact continuation on overflow coefficients, as in Stage 0 | |

`Z_var` is `Z` on the cells below `var_cells` and zero above. `K` is the functional of v1
step 4 with one change: the terminal term is `M(rx, ry) Z_var~(ry)`, written as at most
`k - var_align + 1` tensor terms (the dyadic decomposition of `[0, min(var_cells, 2^k))`), so that `K`
reads no cell at or above `var_cells` other than the two sumcheck masks. `V` is its value.
The Stage-0 claim is `<c, K + sum_j w_j e_{omega_j}> = V + sum_j w_j a_j`, with `e_x` the
point kernel at `x`. `P_i` is the polynomial after `i` folds
(`P_{i+1} = G + (alpha_i + beta_i Y)(F + theta_i G)` for the even and odd parts `F, G` of
`P_i`), `v_i` its kernel and `sigma_i` its claimed value
(`sigma_{i+1} = gamma_G + alpha (gamma_F + theta gamma_G) + beta (c_F + theta c_G)` as in
`AFFINE_PROTOCOL.md`). The claim on `g` is `<g, v_s> = sigma_s + beta_R mu`. At a queried
fiber over `y` the verifier folds the `2^s` opened symbols of `Z^` with the challenges of
round 9 to `P_s(y)` and uses `P_s(y) + beta_R R^(y)` as the value of `g` at `y`.

The prover aborts (`MaskRankDeficient`, retry with a new seed) unless the public event
**Good** holds; it depends on verifier coins only:

- (G1) the five weights `eq((rx_0, rx_1, rx_2), c)`, `c = 0..4`, are an `F_p`-basis of `E`,
  and the three corner factors are nonzero (v1's condition with five limbs);
- (G2) `z_j = omega_j^(2^s)` is outside `F_p` for each `j`, and no `z_j` is a Frobenius
  conjugate of another;
- (G3) `w_j != 0`, and for every fold `i < s`: `phi_i != 0` and
  `1 + phi_i omega_j^(2^i) != 0` for each `j`.

`Pr[not Good] <= 15 / p + (5 * 2^s * p + 50 * 2^s + 5 + 6 s + 3 n) / |E| < 2^-59`
[proof]: (G1) fails when a determinant of degree at most 15 in the base-field coordinates
of `rx_0..rx_2` vanishes (Schwartz-Zippel over `F_p`; the polynomial is not zero: at
`(rx_0, rx_1, rx_2) = (X, X^2, X^4)` the determinant is 16) or a corner factor, a
product of `n - 3` linear forms, does; `x^(2^s) in F_p` has at most `2^s (p - 1) + 1`
solutions; `x^(2^s) = sigma^i(y^(2^s))` has at most `2^s` for each of ten pairs and five
`i`; the remaining conditions are single field elements. The failure probability affects
completeness only (see Theorem V2.Z).

### V2.2 Zero knowledge

**Lemma V2.1 [proof; the triangularity is Lemma 4.1].** A table supported on the top `b`
cells has monomial coefficients supported on the top `b` indices, bijectively. So
`Z^(x) = W(x) + x^(N-b) B(x)` where `W` is determined by the cells below `N - b` and `B` is
uniform in `F_p[x]` of degree below `b`, independent of `W`.

**Lemma V2.2 (blinding count) [proof; formalization scope in V2.6].**
Let `Q` be a set of distinct nonzero points of `F_p` and
`z_1..z_t` in `E \ F_p`, pairwise non-conjugate. If `b >= |Q| + 5 t 2^s` then

```
B  |->  ( (B(q))_{q in Q},  (x^(N-b) B mod (x^(2^s) - z_j))_{j = 1..t} )
        in  F_p^|Q|  x  prod_j E[x] / (x^(2^s) - z_j)
```

is a surjective `F_p`-linear map, so its value is uniform for uniform `B`.

*Proof.* `m_j(x) = prod_{i<5} (x^(2^s) - sigma^i(z_j))` has coefficients fixed by `sigma`,
so `m_j` is in `F_p[x]`, of degree `5 * 2^s`. Reduction `F_p[x] / m_j -> E[x] / (x^(2^s) - z_j)`
is injective: an `f` over `F_p` divisible by `x^(2^s) - z_j` is divisible by each conjugate
factor, and those are pairwise coprime because the `sigma^i(z_j)` are distinct (`z_j` is
outside `F_p` and 5 is prime), hence by `m_j`. Both sides have `F_p`-dimension `5 * 2^s`, so
it is a bijection. The moduli `x - q` (`q in Q`) and `m_j` are pairwise coprime: the roots
of `m_j` have `2^s`-th powers `sigma^i(z_j)`, which are distinct across `(i, j)` and are not
in `F_p`, while `q^(2^s)` is. All are coprime to `x` (`q != 0`, `z_j != 0`). By the Chinese
remainder theorem every tuple of residues is attained by a polynomial of degree below the
sum of the degrees, `|Q| + 5 t 2^s <= b`; multiplication by the unit `x^(N-b)` permutes each
residue ring. QED

**Lemma V2.3 (fold scalars).** Fix `j` and write `A = E[x] / (x^(2^s) - z_j)`,
`T = Z^ mod (x^(2^s) - z_j)`, `x_i = omega_j^(2^i)`.

(a) [proof] The value `a_j` and, for each fold `i < s`, the contribution of the point term
`j` to the five scalars are `E`-linear functions of `T`. In detail, with `u_i = P_i(x_i)`
(so `u_0 = a_j`), `F_i, G_i` the even and odd parts of `P_i` evaluated at `x_i^2`, and
`w_{j,i}` the weight of the term (`w_{j,0} = w_j`, `w_{j,i+1} = w_{j,i}(1 + phi_i x_i)`):

```
u_i = F_i + x_i G_i,     u_{i+1} = G_i + (alpha_i + beta_i x_i^2)(F_i + theta_i G_i),
(sigma_even, tau_01, tau_10, c_F, c_G)_j
    = w_{j,i} ( F_i,  x_i F_i,  G_i,  (1 + phi_i x_i) x_i^2 F_i,  (1 + phi_i x_i) x_i^2 G_i ).
```

*Proof.* `P_i mod (X^(2^(s-i)) - z_j)` is a function of `T` (each fold is a ring operation on
even and odd parts, compatible with reduction), and evaluation at `x_i` factors through that
residue because `x_i^(2^(s-i)) = z_j`. The scalars are the inner products of `F, G, YF, YG`
with point kernels, i.e. evaluations. QED

(b) [proof] The `s + 1` functionals `u_0, F_0, .., F_{s-1}` on `A` (an `E`-space of dimension
`2^s`) are linearly independent, with no condition beyond `omega_j != 0`.

*Proof.* Induction from the last fold, on the statement: `u_i, F_i, F_{i+1}, .., F_{s-1}` are
independent functionals on `A_i = E[X] / (X^(2^(s-i)) - z_j)`. For `i = s` the list is `u_s`
alone on a one-dimensional space, and `u_s` is the identity. Step: write an element of `A_i`
as its parts `(F, G)` in `A_{i+1}^2` and let `Phi(F, G) = G + (alpha + beta Y)(F + theta G)`.
`Phi` is onto `A_{i+1}` (take `F = -theta G`), so the pull-backs of `u_{i+1}, F_{i+1}, ..`
are independent and all vanish on `ker Phi`. `u_i` and `F_i` span the same plane as the
evaluations `F(x_i^2)` and `G(x_i^2)`, which are independent (`x_i != 0`), and that plane
contains the pull-back of `u_{i+1}`. The plane is not inside the annihilator of `ker Phi`:
`(F, G) = (1 + theta (alpha + beta Y), -(alpha + beta Y))` is in `ker Phi` and its two
evaluations are `1 + theta e` and `-e` with `e = alpha + beta x_i^2`, not both zero. So the
plane meets the pull-backs in the line of `u_{i+1}`, and replacing `u_{i+1}` by a basis
`u_i, F_i` of the plane keeps the list independent. QED

(c) [proof; formalization target `v2_fold_scalar_matrix_bijective`, V2.6]
Under (G2), (G3), for each fold `i` the map from `(F_i)_{j = 1..5}` in `E^5` to the sum over
`j` of the five-scalar contributions, at fixed `u_i`, is an affine bijection of `E^5`.

*Proof.* Substituting `G_i = (u_i - F_i) / x_i`, column `j` of the linear part is
`w_{j,i} (1, x, -1/x, (1 + phi x) x^2, -(1 + phi x) x)` at `x = x_{j,i}`. Row operations
with `phi_i != 0` turn the rows into `x^(-1), 1, x, x^2, x^3`, a Vandermonde matrix times
`diag(w_{j,i} / x_j)`. The `x_{j,i}` are distinct and nonzero by (G2) and the weights are
nonzero by (G3). QED

**Lemma V2.4 (mask line) [proof; formalization in V2.6].** For `beta_R != 0` and
any `P` of degree at most `N / 2^s + 1`, `R |-> g = P + beta_R R` is a bijection of
`E^(N / 2^s + 2)`, with inverse `R = (g - P) / beta_R`. Given `g`, `beta_R`,
the true claim `sigma_s = <P_s, v_s>` and the opened symbols of `Z^`, the claim
`mu = (<g, v_s> - sigma_s) / beta_R` and
the opened symbols `R^(y) = (g(y) - P_s(y)) / beta_R` are determined.

**Theorem V2.Z [proof]. The interactive oracle proof of V2.1 is perfect honest-verifier zero
knowledge**, for a satisfying assignment and independent uniform prover coins; the view on
coins outside Good is the transcript up to the prover's abort. An oracle commitment is an
opaque handle, not a Merkle root. Seed expansion and hashed commitments are treated in V2.4
and V2.5, and Fiat-Shamir below.
The abort is a predicate of verifier coins, and each condition is tested before the first
message that needs it: (G1) before the row values, (G2) and `w_j != 0` before and after the
`a_j` (which are uniform under (G2) alone), the conditions on `phi_i` after the first three
scalars of fold `i` (rows `1, x, 1/x` of Lemma V2.3 (c) have rank three on five distinct
points whatever `phi_i` is) and before `c_F, c_G`. The simulator below, stopped at the same
point, reproduces every such prefix.

*Simulator.* Given the verifier's coins (stated for coins in Good):

1. Front (rounds 1 to 6): sample uniform `G1`; each degree-9 row polynomial uniformly
   subject to its endpoint sum being the running claim; uniform `(Az, Bz, Cz)(rx)` in
   `E^3`; uniform `G2`; each degree-2 column polynomial subject to its endpoint sum.
   Compute `V` from these messages and the coins. In particular, round polynomials are
   uniform in an affine hyperplane, not unconstrained coefficient vectors.
2. Pick lower cells `W'` with `<c(W', 0), K> = V`, where `c` is the Moebius transform;
   existence is proved below. Sample
   the blinders, `R` and the salts uniformly. Run the honest prover from round 7 on
   `Z' = (W', blinders)` and `R`.

*Front and existence of the surrogate.* For a fixed satisfying assignment, including its
pads, a mask `g1(x) = sum_{i,h} a_{i,h} x_i^h` contributes
`rho1 * 2^(n-i-1) a_{i,h}` to coefficient `h >= 1` of row `i` (zero-based). These
coefficients are independent uniform elements; `G1` fixes only one linear combination of
the constant coefficients, with nonzero coefficient `2^n`. Sequentially this proves the
stated distribution of `G1` and the consistent row rounds, independently of the pads.
On G1, each five-pad group maps bijectively to `R_j in E`. The row-value offset is
`(k0 R0 + k2 R2, k1 R1, k0 R0 + k1 R1 + 2 k2 R2)`; its determinant is `k0 k1 k2 != 0`.
Thus the three values remain uniform conditional on the previous row messages. The
independent column mask gives the same argument with degree 2, conditional on that entire
front prefix. This also proves the prefix before a G1 abort, without needing the pad rank.

For every simulated front, the restriction of `K` to cells below `N-b` surjects onto `E`.
Vary a constant, linear, or quadratic coefficient of the first row-mask polynomial; its
five limb cells realize any `delta in E`. Their multipliers in `K` are respectively
`2^n + lambda^2`, `2^(n-1) + lambda^2 rx_0`, and `2^(n-1) + lambda^2 rx_0^2`.
If the first two vanish, `lambda^2 = -2^n` and `rx_0 = 1/2`, so the third is
`2^(n-2) != 0`. Solving in one such coefficient constructs `W'` over `F_p`. It need not
satisfy the relation or reproduce each mask separately: subsequent messages use the
front only through `K,V`, and their conditional distribution below is independent of all
lower cells. This is the required front/Stage-0 correlation argument.

*Why it is exact.* The real view is a function of the coins and of
`(front, a, S_0..S_{s-1}, g, O, salts)`, where `a` are the five out-of-domain values, `S_i`
the five scalars of fold `i` and `O` the opened symbols of `Z^`: `mu` and the opened symbols
of `R^` are functions of these by Lemma V2.4, every later message is a function of `g`, and
the oracles are ideal: the theorem is about the interactive oracle proof, in which the
verifier sees oracle answers at the queried positions and nothing of the unqueried ones. The
compiled proof also contains the Stage-0 root and authentication paths, whose preimages hold
unopened symbols; those are covered by the hiding bound of V2.4, not by this theorem, and so
are the roots sent before an abort. It suffices that, conditioned on the coins and on every
cell below `N - b`, the tuple `(a, S_0.., g, O)` is uniform on `E^5 x E^(5s) x E^(N/2^s+2) x
F_p^|O|` in both worlds; the front is simulated as in Theorem 4 (its masks and pads are cells
below `N - b`, the row values use (G1), and `K` reads no blinder).

- `K` vanishes on the support of the blinder part of every `P_i`, and on its shifts by `Y`:
  the blinder part of `c` is supported on indices at or above `N - b`, a multiple of `2^s`.
  The inverse Moebius transform also preserves this support, so a functional reading only
  lower hypercube cells has zero coefficient-kernel entries at all indices `>= N-b`;
  one fold maps support `[L, ..)` with `L` even to `[L/2, ..)`, and maps a kernel vanishing
  on `[L, ..)` to one vanishing on `[L/2, ..)`; tensor terms are zero on overflow
  coefficients. More precisely, at fold `i`, `L_i = (N-b)/2^i` is even. Both even and odd
  blinder parts start at `L_i/2`; multiplication by `Y` only raises this index, while the
  folded statement kernel is zero at every index `>= L_i/2`, including overflow. This
  proves the claim for all five scalars and the next fold, not just for `P_i` itself.
  So the blinders enter `a` and the `S_i` through the five point terms only.
- By Lemma V2.1 and Lemma V2.2 with `Q` the opened points and `t = 5` (`b = |Q| + 25 * 2^s`
  exactly, (G2)), `O` and the five residues `T_j` are jointly uniform and independent of the
  cells below `N - b`.
- By Lemma V2.3 (a), (b), `(u_0, F_0, .., F_{s-1})_j` is uniform in `E^(5(s+1))`. `a` is
  `(u_0)_j`, and `S_i` is an offset depending on the cells below `N - b` and on earlier
  values, plus the map of Lemma V2.3 (c) applied to `(F_i)_j`. The map from
  `(u_0, F_0, .., F_{s-1})` to `(a, S_0, .., S_{s-1})` is therefore triangular with bijective
  diagonal blocks: `(a, S)` is uniform, independent of `O` (which is independent of the
  `T_j`).
- `g` is uniform and independent of all of the above by Lemma V2.4, `R` being independent of
  `Z`. QED

**Fiat-Shamir scope.** In the classical explicitly programmable ROM, use the same
simulator and program the transcript challenges. Under the fresh 400-bit chaining-state
model, the programming loss is at most `M(t + M) / 2^399`, where `M` counts all programmed
oracle inputs across all simulated proofs (including challenge-expansion inputs), not
merely the number of proofs. Each pre-existing query or pair of programmed inputs can
hit a fresh state with probability at most `2^-400`; the factor two is conservative.
Add the hiding and seed-expansion losses of V2.4--V2.5. **[open]** The quantum
adaptive-reprogramming step is not supplied. Malicious-verifier zero knowledge is not
claimed for the interactive protocol.

**How tight `b` is.** Lemma V2.2 makes all `2^s` residues at each point uniform, while the
transcript reveals only `s + 1` functionals of them: `b = |Q| + 25 * 2^s` is sufficient and
not necessary (`|Q| + 25 (s + 1)` base-field coordinates are revealed). The 1,600 cells at
`s = 6` are not worth a finer lemma. Outside the hypotheses the proof does not apply; that
is not by itself a demonstrated leak. With four point terms the
five scalars of a fold are five affine functions of four uniform values, so one
`E`-combination of them per fold is a function of the cells below `N - b` (the toy
computation of V2.9: rank 68 of 78, two folds). This is a rank obstruction to the uniformity
proof, not a witness-leakage proof: such a residual could already be fixed by the public
claim. Neither one extra fiber nor four points is asserted here to leak a witness.

### V2.3 Knowledge soundness

**Theorem V2.1 [proof, from cited lemmas, at the rigour of Theorem 1].** Fix `m >= 3` and
agreement thresholds `A_i` (in fibers) as in Theorem 1, with
`A_0 >= (1 + 1/(2m)) sqrt((N/2^s + 2) |D'|)`. The protocol of V2.1 has round-by-round
knowledge soundness with these errors (`l_0`: Johnson list of `Z^` at `A_0`; `L_i`, `l_i` as
in Theorem 1; `rho' = (N/2^s + 2) / |D'|`):

| Round | Error | Source |
| --- | --- | --- |
| `tau`, `rho1`, `rho2`, row and column rounds, weights, `lambda` | `d l_0 / (|E| - 1)`, `d = max(n, 15, 4 + num_public)` | Schwartz-Zippel per list member; denominator covers the nonzero `rho` challenges |
| `omega_1..omega_5` | `(l_0^2 / 2) ((N + 2) / |E|)^5` | [ACFY24b] Lemma 4.25 with five samples |
| `w_1..w_5` | `5 l_0 / |E|` | linear identity per list member |
| `phi_i`; `(theta, alpha, beta)_i` | `L_i / |E|` each | [CWYZ26] Theorem 5.1, (5.5) |
| `beta_R` | `(m + 1/2)^7 |D'|^2 / (3 rho'^(3/2) (|E| - 1)) + l' / (|E| - 1)` | [BCGM25] Lemma 9.3, `d = 1`; `l'` pairs, one root each |
| two out-of-domain points of stage `i >= 1` | `(l_i^2 / 2) ((2^{r_i} + 2) / |E|)^2` | [ACFY24b] Lemma 4.25 |
| queries of stage `i`, and weights batching them with the next OOD claims | `C(A_i + s_i, q_i) / C(n_i, q_i) + (q_i + 2) l_{i+1} / |E|` | distinct uniform fibers; polynomial identity in the batching challenge |
| last-stage queries after the terminal polynomial | `C(A_i + s_i, q_i) / C(n_i, q_i)` | terminal coefficients fixed before the queries; no next-stage batching |

*What is new relative to Theorem 1.* (o) `d` has 15 where Theorem 1 has 9: a committed
row-mask block of sixteen cells is a univariate of degree up to 15 in `rx_i`, and the
verifier does not check that the honest prover's zero coefficients are zero, so the identity
that ends the row sumcheck has that degree. Theorem 1 and `bounds.rs` undercount this for v1
(by `log2(15/9)` bits on a round that is not its weakest). (i) The two words of the line, `fold^s(Z^)` and `R^`,
are fixed before `beta_R`: the first is a function of the Stage-0 commitment and the
challenges of round 9, the second is committed. [BCGM25] Lemma 9.3 is stated for a challenge
uniform in the field of the code; `beta_R` is uniform among nonzero elements, hence
`|E| - 1`. Outside its exceptional set, every codeword `g*` agreeing with the line on a set
`S` of at least `A_0` points is `c_0 + beta_R c_1` for codewords agreeing with the two words
on `S`. The pairs `(c_0, c_1)` with joint agreement at least `A_0` number at most the
Johnson bound `l'` (two distinct pairs agree jointly on at most `N / 2^s + 1` points), and
for each pair the residual `(<c_0, v_s> - sigma_s) + beta_R (<c_1, v_s> - mu)` of the claim
on `g` is a nonzero affine function of `beta_R` unless both claims hold. (ii) From `c_0` the
`s` folds are undone by Theorem 5.1 of [CWYZ26] exactly as in Theorem 1, losing one fiber
each, which is why the Stage-0 queries are analysed at `A_0 + s`. (iii) The extracted
assignment has base-field coefficients as in section 2.1. (iv) Five out-of-domain samples
replace two. Nothing else in the state function changes; the kernel convention for point
terms is covered because (5.5) holds for every fixed kernel. The loose degree envelope
allows two overflow coefficients when unfolding; the statement kernel is zero there, so
extraction uses the first `N` coefficients and their inverse Moebius transform. The initial
agreement exceeds even this loose degree, so these coefficients are in `F_p`.

For (iv), a fixed nonzero difference of two list polynomials has at most `N+2` roots.
The five independent samples therefore give the fifth power, with at most `l_0(l_0-1)/2`
pairs; independently uniform weights then test one nonzero linear identity per member
(the displayed factor 5 is conservative). Good is an honest-prover abort predicate;
soundness is analysed with the original uniform challenges, not conditioned on Good.
Rejecting additional transcripts cannot increase acceptance. Column-mask blocks can have
degree 3, also covered by 15. The finite affine witnesses bound `C < 2^255.998` in the
term `C/|E|^2` of (4.13); hence `C/|E|^2 < 1/|E|` over the larger field as well.

Theorems 2 and 3 apply with `sigma = 400` and `|E| = p^5`. No grinding is used, so the
classical and quantum round errors coincide. Models D1 and D3 are unchanged (D3 now asks
cSHAKE256 and TurboSHAKE256, capacity 512, to behave as random oracles with 400-bit output).
D2 does not arise.

### V2.4 Hiding of unopened leaves

In the random-oracle model with independent uniform salts, the joint compiled interactive
view differs from the ideal-oracle simulation by at most `t P / 2^256 + delta_salt`
classically, `2 t sqrt(P / 2^256) + delta_salt` against quantum queries, where
`delta_salt = H * binom(P,2) / 2^256` and `H` bounds the Stage-0 leaves per proof.
For one proof `delta_salt = 0`: the quantum bounds are `2^-87` at `t = 2^40` and
`2^-63` at `t = 2^64`. [proof, using [cited] one-way to hiding as in section 4.4.]

Couple the algebraic transcript by V2.Z, including the opened `Z,R` symbols and salts.
Assign shared independent random digest labels to every unopened Stage-0 leaf in the two
worlds; hash the internal nodes and root identically from those labels. First exclude
equal salts at the same index in different proofs, costing at most `delta_salt`; indices
already separate leaves within one proof. All programmed leaf preimages are then distinct
across proofs, so assigning the shared labels respects random-oracle consistency. This couples the
root and all authentication siblings jointly, not merely their marginals. Program each
unopened leaf's own preimage to its assigned label. The two oracles differ only on those
preimages, each containing an independent hidden 256-bit salt; domain framing binds a
query to one leaf index, hence at most one candidate leaf per proof. Union over the `P`
proofs gives hit probability at most `P/2^256`.
The classical fundamental lemma and the quantum one-way-to-hiding lemma give the bounds
above. Hash-output collisions need not be excluded for this hiding coupling. For an abort
prefix, apply the same construction with no leaf answers if queries have not occurred;
the root is still coupled. Later-stage leaves and all their hashes are functions of `g`.
This is bounded-query hiding, not perfect simulation of hashed commitments. Actual seed
expansion adds the hybrid of V2.5; quantum Fiat-Shamir simulation remains open.

### V2.5 Coins

Two steps, as in v1: a 32-byte key
`cSHAKE256("QSAG.ZKHEM2.COINS.SEED/v1", seed, profile tag, relation digest, layout and
schedule, H(statement), H(witness))`, then the stream `SeedStream("QSAG.ZKHEM2.COINS/v1",
key)` (`v2/protocol.rs`), so distinct profiles, layouts, and v1/v2 protocols have distinct derivation
inputs. Independent outputs are a random-oracle/PRG claim, not a guarantee that random
strings can never coincide. `v2::protocol::tests::coins_do_not_repeat_across_profiles` is
a regression test present in source; its execution is outside the bounds checks of V2.9.
V2.Z uses uniform coins. Replacing a fresh secret uniform 256-bit seed stream (including
the derived salt seed) by independent coins costs an additional seed-guessing hybrid:
at most `t P / 2^256` classically, or `2 t sqrt(P / 2^256)` quantum, plus
`binom(P,2)/2^256` for accidental seed collisions, per hidden derivation layer in the
ideal-oracle model. These are separate from leaf hiding and Fiat-Shamir
programming. Reusing a seed with identical inputs reproduces the proof, not fresh coins.

### V2.6 Lean

| Statement | Theorem | Module |
| --- | --- | --- |
| `F_{p^5}` is a field; `sigma` fixes exactly `F_p` | see V2.9 | `Qsag.Math.QuinticExt5` |
| Lemma V2.4, bijection and composed claim/opening view | `v2_mask_line_perfectly_simulated`, `v2_mask_line_view_perfectly_simulated` | `Qsag.Protocol.Aggregation.ZkHemV2` |
| Lemma V2.2, in the interpolation form: `|Q| + 5 |Y|` base-field coefficients against `|Q|` base points and a Frobenius-closed set of `5 |Y|` points of `E` | `v2_blinding_count` | same |
| Lemma V2.3 (c) | `v2_fold_scalar_matrix_bijective` | same |

Both modules compiled on bb2 against the warm library (`ZkHemV2`: 374 declarations,
`Tests/ZkHemV2Teeth`: 21, axioms within `[propext, Quot.sound]`, policy gate passing; the
whole-library build and `AuditAxioms` target were not run). The simulation statements use
`ZkHemV2.CoinBijectionSimulated`, a definition with the same body as
`ZkHem.PerfectlySimulated`, which is sealed to importing modules. Teeth: a zero mask
challenge reveals the word; `phi = 0`, a repeated point, or four points break the
bijection of Lemma V2.3 (c); a base-field point, two conjugate points, or one coefficient
too many break the blinding count. `v2_blinding_count` is about point evaluations, not
directly the quotient rings of Lemma V2.2. For the protocol's `z_j = omega_j^(2^s)`,
the bridge must use the `2^s` distinct roots
of each `x^(2^s)-z_j` and their disjoint Frobenius orbits (all roots lie in `E`, since
`omega_j` does and `2^s` divides `p-1`), followed by the evaluation/residue isomorphism.
Lemma V2.3 (b), Theorem V2.Z as a composition and Theorem V2.1 are not formalized.

### V2.7 Numbers

Command:

```sh
cargo test --release -p qsag-agg --lib -- zk_hem::v2::bounds::tests::print_v2_tables \
  --ignored --nocapture
```

Both profiles have the same numbers. Bits are `-log2`; a reported level is a downward
bound in millibits on `log2` of the query count where the summed error reaches one.
Assumptions behind every row: [CWYZ26] Theorem 5.1 (arXiv preprint, its
closing note says the proofs were produced with AI assistance; unrefereed), [BCGM25]
Lemma 9.3, [ACFY24b] Lemma 4.25, [CDHZ25] Theorems 6.10, 8.3, 11.3, [BCS16] Theorem 7.1,
models D1 and D3, and the state-function argument of Theorems 1 and V2.1 ([proof] at the
rigour of this document, not machine checked). This is conditional knowledge soundness,
not a claim of 128-bit quantum zero knowledge. Uniform challenges, exact distinct-fiber
sampling and the prescribed round order are required; neither coin rejection nor Good
is credited as grinding.

The QROM envelope also uses `t >= 2^24`, fewer than `2^9` challenge rounds, and
`q_V + rounds <= 2^15` verifier hash/challenge queries, counting a framed hash call as one
oracle query (D1). Proof queries are at most `2^15` and tree depth at most 28. These are
the resource hypotheses for the reduction, including its challenge-sampling abstraction;
they are not a wall-clock work estimate. The calculator uses `2^0.023` slack on both
leading terms. It covers the offsets in
`1280 t (2t+1)^2 + 960 t (t+1+q_V+rounds)^2 + 300 t^3`, the commutativity remainder
`480 q_V^2 (t+rounds+q_V+2)`, and the offline remainder `128 q_Pi * 28`, all divided by
`2^400`. The state-restoration remainder `4(t+rounds+1) rounds / 2^319` is absorbed in
the round slack (the canonical worst-round bound is no stronger than 266 bits).
At the smallest `t`, the digest offsets consume less than 0.004 of its leading term;
`2^0.023 - 1 > 0.016`, leaving room for both remainders. These ratios decrease with `t`.
Thus no unnamed lower-order term is discarded from the reported envelope. The classical
simplification `t eps_rbr + 4t^2/2^400` is used only for `t >= 3`.

| Rows, variables | Cells | Queries per stage | `m` | Weakest round | Classical level | QROM level (round term, digest term alone) | QROM error at `t = 2^64` | Proof bytes (upper bound) | v1 tag 4, same rows |
| --- | ---: | --- | ---: | --- | ---: | --- | ---: | ---: | ---: |
| 2^17, 82,000 | 2^17 | 281, 136, 92 | 11 | 264.827 (Stage-0 queries) | 198.999 | **128.123** (128.241, 129.112) | 2^-128.481 | 356,040 | 528,380 |
| 2^17, 2^17 | 2^18 | 287, 136, 92 | 9 | 264.838 (mask line) | 198.999 | **128.129** (128.246, 129.112) | 2^-128.492 | 386,838 | 528,380 |
| 2^20, 2^20 | 2^21 | 300, 136, 92 | 6 | 264.667 (mask line) | 198.999 | **128.062** (128.161, 129.112) | 2^-128.321 | 534,692 | 896,644 |
| 2^21, 1,088,721 | 2^21 | 300, 136, 92 | 6 | 264.667 (mask line) | 198.999 | **128.062** (128.161, 129.112) | 2^-128.321 | 535,212 | 966,957 (2^22 cells) |
| 2^22, 2^22 | 2^23 | 342, 136, 92, 70 | 3 | 265.042 (Stage-0 queries) | 198.999 | **128.209** (128.348, 129.112) | 2^-128.696 | 692,954 | 966,957 |
| 2^23, 2^23 | 2^24 | 342, 136, 92, 70 | 3 | 264.918 (mask line) | 198.999 | **128.158** (128.286, 129.112) | 2^-128.572 | 730,594 | - |

A relation whose variables fill its cube exactly (the rows with `2^r` variables) moves to the
next table size because the masks and blinders need room; the 82,000- and 1,088,721-variable
rows are the statements of `zkhem-frontier.md`.

`Report::qrom_work_bits` searches for the last millibit certified by the rounded upper
bound on the **sum** of the quadratic round term and cubic digest term, including the
slack above. Directed logarithm rounding makes this a lower bound on the exact crossover;
it is not the minimum of the two single-term figures. The classical method likewise
solves the sum. Stage-0 queries by table size (`params::STAGE0_QUERIES`, the minimum for a level of
128 bits; `bounds::tests::stage0_queries_are_minimal`): 281, 281, 287, 295, 300, 300, 320,
342, 342 for `2^16..2^24` cells. At `2^25` cells no count suffices.

The byte column bounds the current `ZkHemV2Proof::to_bytes` encoding: magic (8), profile
(1), log cells (1), Stage-0 root (50), then all prover field elements in round order.
Each later root is 50 bytes; field elements are 40 bytes, base symbols 8, Stage-0 salts 32.
Only authentication-sibling vectors carry a count (one little-endian `u32` per stage).
All other lengths follow from the public shape and schedule; relation digest, statement,
public inputs, full layout and schedule are transcript inputs, not repeated proof fields.
There are five scalars per fold, five initial OOD values, two per later stage, one mask
claim, and `2^early_stop_vars + 2` terminal coefficients. The sibling bound is
`q (log2 leaves - floor(log2 q))` (zero when every leaf is read). With
`u = ceil(log2 q)` and height `h`, the upper `u` levels contribute at most `2^u-q`
siblings, and the remaining levels at most `q(h-u)`; their sum is no larger than the
displayed bound. The serializer-field
test checks this byte accounting at all nine sizes and both tags; actual multiproofs may
use fewer siblings. This records the existing encoding, without changing its fields.

Zero knowledge at every size: perfect for the oracle proof (`blind_cells` equals
`opened symbols + 25 * 2^s`, asserted); leaf hiding `t P / 2^256 + delta_salt` classical,
`2 t sqrt(P) / 2^128 + delta_salt` quantum (V2.4; seed expansion is separate).
Completeness error (abort) below `2^-59` per attempt.

Where the bytes go at `2^21` cells (535 KB): 4,663 digests of 50 bytes, 233 KB; 300 Stage-0
leaves of 584 bytes, 175 KB; later-stage leaves, 102 KB; everything else, 25 KB. The digests
are now the largest part; v1's 4,199 digests were 134 KB of 897 KB.

Tests (`cargo test --release -p qsag-agg --lib -- zk_hem::v2::bounds`):
`stage0_queries_are_minimal`, `every_accepted_size_reaches_128_bits_classical_and_qrom`,
`one_query_fewer_or_a_shorter_digest_misses_the_target`,
`mask_line_matches_the_lemma_by_hand`, `layout_puts_everything_in_one_cube`,
`directed_rounding_and_summed_crossovers`, `byte_bound_matches_serializer_fields`,
`documented_table_matches_calculator`, `calculator_rejects_malformed_geometry`,
`hiding_counts_cross_proof_salt_collisions`.

### V2.8 Not adopted: affine mask cascade

`g = P_s + (a_1 + b_1 Y) R_1 + (a_2 + b_2 Y) R_2` with two masks of degree one less than
`P_s` and four claims. **[open] Design sketch, not an analysed alternative.** Distinct
linear factors can make the map from the two masks onto `g` surjective; hiding the four
claims additionally requires rank three on the kernel of that map. Independence of `v_s`,
its shift and its double shift is a proposed sufficient condition, still requiring a
degree-correct proof and an abort-prefix analysis. The claimed failure bound `3/|E|` is
not established here. Soundness would require two applications of the affine theorem
with checked degree bounds, finite witnesses, agreement losses and claim timing; its
`n^2/|E|^2` term does not disappear. About 266 queries is an estimate, not a certified
schedule or an assertion of no size limit. One additional `E`-symbol per Stage-0 leaf
would be sent. None of these proposals changes V2.1 or the calculator.

### V2.9 Implementation state

As of 2026-11-17:

- The bounds repair pass checks `v2/params.rs`, `v2/bounds.rs`, and their integration with
  the current serializer using only the filtered bounds suite listed in V2.7. Presence of
  other test functions in source is not a record of their execution by this pass.
- Checked numerically on a toy field (`p = 15361`, `N = 256`, `s = 2`, two opened fibers):
  the `F_p`-linear map from the blinders to (opened symbols, five out-of-domain values, ten
  fold scalars) has rank 83 of 83 with an arbitrary kernel `K` present, and rank 68 of 78
  with four points instead of five. This checks Lemmas V2.2 and V2.3 and the kernel
  convention together; it is evidence, not proof.
- Implementation source is present for `v2/field5.rs`, `v2/hash.rs`, `v2/pcs.rs`,
  `v2/protocol.rs`, the v2 relation closing, and the Lean modules of V2.6. These are under
  concurrent development. This pass does not certify the full protocol tests or a Lean
  build. The named Lean source statements exist; a checked build and the connection from
  point interpolation to the residue-ring lemma remain separate validation obligations.

### V2.10 Hardware, GPU, Poseidon2

Not changed by this revision. v1 fixtures, KATs, SPIR-V pins and RTL stay valid because no
v1 source is edited. What v2 would need: the extension multiplier (tower Karatsuba with
`* 7` to quintic schoolbook with `* 3`) in all three verifier tops
(`hardware/asic/rtl/qsag_asic_ext4_p2_shared.sv`, `hardware/fpga/rtl/qsag_ext4_mac*.sv`,
`hardware/gf180mcu/rtl/qsag_field_engine.sv`), 400-bit digest ports and the 105-byte node
framing in the Keccak canopy engines, the Stage-0 leaf layout, and new kernel slots with new
pins in `crates/qsag-accel` (`whir_fold_sumcheck.comp`, `whir_lde_merkle.comp`,
`air_row_group_{a,b}.comp`; the 128-byte push-constant block does not hold three 40-byte
challenges). A Poseidon2 profile needs a node function for two seven-limb children (two
permutations, or a wider permutation) and a rate-5 sponge, in software, in the recursion
gadgets and in every Poseidon2 canopy unit; none of that is designed here.

### V2.11 Lookups and virtual product rows (constraint-system features; not implemented)

**Lookups.** The argument to port is `dregg-sig`'s (`crates/agg/src/zk_hem/protocol.rs`,
module section "Lookups", steps L1 to L4: logUp with committed helpers,
`logup-2022-1530` Lemma 5). **[open] Porting assessment, not a v2 lookup theorem:**

- *Second commitment.* The helper table `H` is committed after `gamma, alpha`, so it is a
  second Stage-0 commitment `(H, R_H)` with its own blinders, five mask points and mask line,
  opened by a second run of rounds 7 to 13. Fresh independent blinders and masks allow
  V2.2--V2.4 to simulate each opening conditional on its claimed functional and values.
  They do not prove that the joint lookup front end is simulated: `H` depends on the first
  witness and the lookup challenges. That conditional front-end proof, pole handling and
  an explicit helper kernel avoiding its blinders are required before applying V2.Z.
- *Limbs and masking entries.* `h` has five limb tables, not four (5 cells per fraction; v1
  paid 20 with companions). The values `(n, v, h)(rl)` revealed in L3 are three elements of
  `E`, so five masking entries are needed where the v1-field design has four, with the
  basis condition on the lookup point. A count alone is not a rank proof for the three
  correlated values; the masking rows and their joint map must be specified.
- *Soundness candidates.* Substitution of `|E| = p^5` into the proposed accounting gives
  `(w - 1) L T l_0 / |E|` (`gamma`), `(L + 2T + 1) l_0 / |E|` (`alpha`),
  `max(d, 5) l_0 l_0' / |E|` (lookup sumcheck), and Theorem V2.1 once more for the helper
  opening at its own size. These formulas require checking the port's polynomial identities
  and lists. `L,T <= 2^24` alone does not imply 264.4 bits: the first numerator also depends
  on tuple width `w` and list size `l_0`. All such parameters, helper layout and extra rounds
  must enter a new calculator before a security level is assigned.
- *Cost estimate.* One more root, proposed `5 d + 8` field elements, and a second opening.
  Its size depends on the helper layout; the previous 330 KB estimate is not a bound.
  This is a cost of this proposed construction, not a lower bound for every hash-based
  lookup scheme. Batching fractions may reduce the helper table and its opening geometry.

**Virtual product rows.** The proposal (`zkhem-frontier.md` 5.3): commit only the bits of
the SHA-2 state words; `Sigma`, `Ch`, `Maj` outputs are products that are never committed,
and each 32-bit addition becomes one equation over a weighted sum of bit products. As a
constraint-system feature it is a third product matrix `D` and a grouped row check:

```
for every group g:   sum_{i < 2^e} 2^i (A z)(g, i) (B z)(g, i) (D z)(g, i)  =  (C z)(g).
```

*Algebraic soundness of the proposed check [proof; conditional on binding the row values].*
The check is the vanishing, on the group cube, of
`q(g) = sum_i 2^i (ABD)(g, i) - C(g)`. For `tau` uniform, `sum_g eq(tau, g) q(g) = 0` holds
with probability at most `n_g / |E|` unless `q = 0` (`n_g` group variables). The left side
is `sum_{g,i} eq(tau, g) pow(i) (A B D)(g, i) - sum_g eq(tau, g) C(g)` with
`pow(i) = prod_j (1 + (2^(2^j) - 1) i_j)` multilinear, so it is one sumcheck of individual
degree 4 over the row cube and one of degree 2 over the group cube, ending in the claims
`(Az, Bz, Dz)(rx)` and `(Cz)(rg)`, which join the column sumcheck with four weights. Every
step is Schwartz-Zippel per fixed list member. Before the sumcheck challenges the prover must fix
the two claimed sums `U,V` with `U=V`; the two sumchecks bind them to their respective
summands. Without those claims and the equality check, two independent sumchecks do not
test the displayed identity. Their individual degrees are 4 and 2: `eq` and `pow` use
disjoint variable groups. The terminal four linear evaluations can be batched with fresh
independent weights after they are sent, then checked by a column sumcheck. This proves
the local algebraic reduction, not the soundness of an unspecified full extension.
Although these degrees fit below 9, extra masks and claims may raise the degree of the
final `lambda` batching polynomial and the round count; Theorem V2.1's `d` cannot simply
be reused. The carries and Boolean inputs require ordinary range/Boolean constraints,
and integer addition additionally requires bounds excluding modular wraparound in `F_p`.

*Zero knowledge [open].* There are four revealed values total: three at `rx` and one at
`rg`; counting `C(rg)` again as a fifth value was incorrect. An explicit padding pattern
must mask them jointly at these two points while preserving the grouped constraints.
Both new sumchecks and their initially equal sums also need masks. Four groups of five
are only a dimension count, not a sufficient construction or a proof. The opening lemmas
remain available once the new kernel's support and the conditional front simulation are
proved; this assessment does not extend Theorem V2.Z to virtual rows.

*Why it is not in this revision.* It changes `Shape`, the relation digest of every
statement, every SHA-2 and RIPEMD-160 gadget and the witness generator. The saving (2.8
times fewer committed cells for SHA-512 in the frontier measurement) is on top of v2 and
does not itself require a different challenge field or digest, but its masks, layout and
opening composition must be designed and analysed before assigning the v2 guarantees.

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

