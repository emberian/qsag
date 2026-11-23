# Aggregation security

This document states what is proven about committed-mask Quintic `Fp5` zk-Hem v2
(`src/zk_hem/v2/`), public Quintic `Fp5` `HemQuintic128` (`src/hem_quintic.rs`), and
`[DKT26]` binary recursive IVC (`src/zk_hem/recursive_ivc.rs`), under which hypotheses,
and with which numbers. The numbers are computed by `src/zk_hem/v2/bounds.rs` (`report`)
and `src/zk_hem/bounds.rs` and pinned by their tests.
Every statement carries one of four labels:

- **[cited]** a theorem of a paper, with its hypotheses checked against the code;
- **[ours]** an argument made in this document, not peer reviewed;
- **[model]** an idealisation the statement depends on;
- **[open]** not established.

Papers are named by their file in `/Users/ember/paperbin` on first use.

## V2. zk-Hem v2

Status: design, proofs and calculator. The implementation state is in V2.9. v2 lives in
`src/zk_hem/v2/` behind its own wire magic (`QSAGZKH2` / `QSAGZKS2`) and profile tags
(`16`, `17`). Labels in this section: **[lean]** a checked theorem in `lean/Qsag`
(theorem named), **[proof]** an argument in this section, **[cited]**, **[model]**,
**[open]** as above. A source file alone is not evidence of a successful Lean build.
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

Both modules elaborate under the workspace Lean 4.35 kernel and paranoid comparator (`ZkHemV2`: 374 declarations,
`Tests/ZkHemV2Teeth`: 21, axioms within `[propext, Quot.sound]`, policy gate and `AuditAxioms` passing). The simulation statements use
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

### V2.11 Single-prover LogUp and virtual product rows

**Checked fractions and poles.** In `v2/protocol.rs`, `gamma` compresses the
tuple (including its table tag), and `alpha` selects the pole. For a checked
entry let `v_i = sum_j gamma^j D_j[i] z` and `n_i = N[i] z`. The helper
is `h_i = n_i / (alpha - v_i)`. The prover checks the product of *all*
checked denominators in the extension field before its one batch inversion.
A zero product returns `LookupPoleHit` before the helper commitment. In a
satisfying witness, every queried tuple occurs in the public table. All table
rows are checked, including rows of multiplicity zero. Thus the pole set is
exactly the set of compressed public table rows, augmented by zero if there
are checked padding rows. The simulator can reproduce this abort given only
the relation and challenges. Its probability is at most `(T+1)/|E|`.

**Joint lookup evaluations.** The last eight entries lie outside the checked
prefix. The first five have independent uniform base cells `a_j` in the
numerator and `b_j` in denominator column zero. All higher tuple columns
on these rows vanish. The helper samples an independent extension cell on
each of the eight entries. Write `u_j = eq(rl[0..3],j)` and let `k` denote
the product of the remaining corner coordinates. The implementation checks
that the five limb columns of the `u_j` have nonzero determinant over the
base field. Hence `A = sum_j u_j a_j` and `B = sum_j u_j b_j` are independent
uniform elements of `E`. Hold seven helper pads fixed and vary the first,
`C`. Conditional on these pads and the checked rows, the three disclosures
are a translation of `diag(k,k,k*u_0) (A,B,C)`. Both prover and replay
check its extension-field determinant before accepting the disclosures.
This supplies rank 15 over the base field even though the checked helper is
a nonlinear function of the witness. The extra rank abort probability is
bounded by `15/p + (d-3)/|E|` using the basis determinant witness of V2.1;
basis independence already implies `u_0 != 0`.

**Front simulator.** Fix a satisfying witness and verifier coins, treating
commitments as opaque oracle handles. For a non-pole `alpha`, the rational
identity gives zero initial unmasked claim. Conditional on every entry of
`n,v,h`, sample the lookup mask sum uniformly in `E`. Each degree-four
lookup round is uniform subject to the endpoint sum specified by the
running claim. Indeed the four nonconstant coefficients in round `i`
receive independent fresh offsets scaled by the nonzero
`rho * 2^(d-i-1)`. Conditioning on the initial sum fixes one combination
of constant coefficients with coefficient `2^d`. The endpoint condition
then fixes that round's constant term. This also describes every prefix
before a rank abort. Thus observing all the masked rounds gives no
information about the corner pads. On the good event sample the final
triple uniformly, and compute the terminal mask value from the public gate
and the running claim. The row pads in V2.Z occupy disjoint assignment
cells. Its row and column mask argument applies conditionally, with the
two extra matrix terms for the lookup numerator and compressed tuple in
the column claim.

**Both openings.** The helper claim batches the mask sum, terminal mask
evaluation and `h(rl)` with weights `1, eta, eta²`. Its cell weights read
only the five limb columns and the lookup-mask blocks ending at
`5*2^d + 8*5*d`. The layout places that end at or below `N_H-b_H`.
The transpose subset transform sums only over supersets, so its monomial
kernel also vanishes on every helper blinder. The functional on lower cells
surjects onto `E`. For `eta != 0`, vary the five limbs of any helper entry
with nonzero equality weight (their weights sum to one). At `eta = 0`,
vary a constant mask coefficient, scaled by `2^d`. The main functional
retains the row-mask surjection in V2.Z. A simulator can therefore choose
lower tables satisfying the two public scalar claims independently. After
fixing **both** lower tables and the complete front, each commitment still
has independent top blinders and an independent mask polynomial. Apply
V2.2–V2.4 first to the assignment opening and then conditional on it to the
helper opening. This couples all opened symbols, fold messages and subsequent
oracles jointly on good coins. Each abort prefix has the same law by the
same argument stopped at the first failed public check.

For hashed commitments use the unopened-leaf coupling of V2.4 with the
tree nonce of V2.12. A batch of `P` single-prover lookup proofs has `2P`
Stage-0 trees. Use that count in the leaf-guessing and nonce-collision
bounds, and add the secret-seed and Fiat–Shamir hybrids of V2.2 and V2.5.
Exact equality is in the interactive ideal-oracle model. The compiled
classical result uses a programmable random oracle; the quantum
Fiat–Shamir simulation remains open. The calculator checks each tree's
blinder budget separately. The constructive regression
`coupled_lookup_front_for_distinct_witnesses` translates the two sets of
pads and sumcheck coefficients to identical disclosures, solves the
observed Stage-0 blinding systems on a small PCS schedule, and exercises
the mask-line and unopened-label couplings for both trees.

**Round-by-round soundness.** Let `L,T,w,d` be the query count, public table
row count, tuple width including tag, and lookup cube dimension. Write
`l_0,l_0'` for the two Stage-0 word list sizes. For each inconsistent first
list word choose a tuple with nonzero net residue. For its residue to
disappear on compression it must collide with another distinct tuple, among
at most `L+T-1 <= L*T` alternatives when both counts are positive. Each
difference polynomial has degree at most `w-1`. Multiplying the nonzero
compressed rational sum by its distinct linear factors gives a nonzero
numerator of degree at most `L+T-1`. At a query pole the local equation
with numerator one fails. Table poles and the possible padding pole add at
most `T+1` exceptional challenges. These counts give the conservative
numerators below. The rational identity uses the characteristic bound
`L < p` for lookup membership. [LogUp, Lemma 5](https://eprint.iacr.org/2022/1530)

| Round | Error upper bound |
| --- | --- |
| Tuple compression | `(w-1) L T l_0 / |E|` |
| Pole and rational identity | `(L+2T+1) l_0 / |E|` |
| Lookup algebraic rounds | `max(d,5) l_0 l_0' / |E|` |

For an unused registered table (`L=0`), the calculator keeps `T-1` in place
of `L*T` to cover inconsistent auxiliary multiplicities. For a fixed pair of
list words, a false local identity on the Boolean cube has a multilinear
equality-weight test of total degree at most `d`. The subsequent scalar
batch has degree one, each sumcheck variable has degree at most four in
`sel * (h + lambda * eq * (h*(alpha-v)-n))`, and the final three-claim
batch has degree two. The degree-five envelope covers these individual
rounds. Verifier mask evaluation also has degree four for arbitrary helper
cells: the lower four subset-sum cells define degrees zero through three,
and cell four minus cell zero is the quartic coefficient. Unused higher
subset-sum cells have zero weight in both the sum and point functionals.
Both sparse and dense helper kernels use these weights. The lookup layout
transcript includes this kernel revision; earlier lookup proof bytes require
the earlier verifier. `report_with_lookup` additionally accounts for the
helper PCS, its queries and digests, and the extra protocol rounds.

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

### V2.12 DKT26 Upgrades: DKT26 (`2026/2056`) Soundness, Per-Tree Nonce, LogUp Lookups, Split-Share Opening, and `v1` Hiding Retirement

Implemented in `src/zk_hem/v2/{bounds,hash,params,pcs,protocol}.rs` and `src/zk_hem/protocol.rs`:

1. **DKT26 (`eprint 2026/2056`) Proximity-Gap Upgrade (`v2/bounds.rs`, `v2/params.rs`):**
   - Replaces the quadratic-in-block-length `[BCGM25]` Lemma 9.3 error on the `beta_R` mask line
     with **Dao–Kominers–Thaler (`2026/2056`) Theorem 5.12** (two-element line generator inside
     the Johnson radius: linear in `|D'| = 4N / 2^s` rather than `|D'|^2`).
   - Lifts the `zk-Hem v2` cell-table ceiling from `N <= 2^24` to **`N <= 2^28`** (`MAX_LOG_CELLS = 28`)
     while reducing Stage-0 queries across `2^16..=2^28` cells from `281..342` to **`267`** (`2^16..=2^23`)
     and **`266`** (`2^24..=2^28`, `STAGE0_QUERIES`), exceeding the 128-bit QROM target at every supported
     domain size.
   - Also exposes the **DKT26 beyond-Johnson** calculator (`dkt26_beyond_johnson_first_order`,
     Proposition 5.10 + Lemma 5.6 + Corollary 7.8, first-order list-2 regime giving `209..220` Stage-0
     queries while keeping `MCA > 265` bits), verified by exact integer/rational cross-checks in
     `v2::bounds::tests`.
2. **Per-Tree 256-bit `tree_nonce` Eliminating `delta_salt` (`v2/hash.rs`, `v2/pcs.rs`):**
   - Every Stage-0 commitment samples an independent 32-byte `tree_nonce` absorbed into every
     Stage-0 leaf hash (`hash_stage0_leaf` / `hash_stage0_leaf_with_nonce`) and serialized in
     `Opening` / `SplitOpening` (`32 + 50 = 82` bytes per Stage-0 commitment).
   - Because two proofs (or two custodian share trees in a `ZkHemV2SplitProof`) collide in domain
     prefix only if their 256-bit `tree_nonce`s collide, the cross-proof multi-leaf birthday term drops
     from `H * binom(P, 2) / 2^256` (which scaled with `H = |D'| = 2^(l - s + 2)`) to
     **`binom(P, 2) / 2^256`**, independent of table size (`hiding_bound` in `v2/bounds.rs`).
3. **LogUp `LookupV2Proof` & Split-Share `ZkHemV2SplitProof` (`QSAGZKS2`) (`v2/protocol.rs`, `v2/pcs.rs`):**
   - Implements the committed-helper LogUp argument over `F_{p^5}` (`5` helper limbs, `5` masking
     entries in an `8`-entry corner, degree-4 lookup sumcheck, and a second Stage-0 `(H, R_H)`
     commitment + opening, accounted in `report_with_lookup` and `max_proof_bytes`).
   - Implements `ZkHemV2SplitProof` (`QSAGZKS2`) and `pcs::open_from_reduced_split` / `verify_split`
     over `c in 1..=255` additive Stage-0 share trees (`Z = sum_p Z^(p)`, `R = sum_p R^(p)`), where
     even one honest custodian's uniform blinders, `R^(p)`, `tree_nonce`, and 256-bit leaf salts
     statistically mask the reconstructed joint view.
4. **Complete Removal of Quartic `v1` & Non-Succinct Proof Formats:**
   - All hiding proof paths (`blind_vc`, `multisig`, `capability`, and `qsag-migrate` single-party +
     threshold `collab` + Zcash relations) run exclusively on `zk-Hem v2` (`QSAGZKH2` / `QSAGZKS2`).
   - All public committee signature aggregation runs exclusively on Quintic `Fp5` `HemQuintic128`
     (`QSAGHQM2`, `TurboShake400` 400-bit or `Poseidon2Gl24` 448-bit digests, `< 2^{-128}` QROM) and
     regional `HierarchicalHemAggregate` (`QSAGHEM\x04`).
   - All binary recursive IVC runs exclusively on `[DKT26]` `< 2^{-128}` QROM `SuccinctIvcProof`
     (`QSAGIVC1`, constant `639,673` bytes, strict profile tag `0x00`).
   - All legacy quartic `F_{p^4}` PCS/WHIR modules, 256-bit Merkle regimes, child-concatenated merge
     trees, summary-hash chains, and diagnostic wire polymorphism have been permanently deleted.
