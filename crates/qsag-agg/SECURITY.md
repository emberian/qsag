# Aggregation Security Specification

This document states what is proven about committed-mask Quintic `Fp5` **zk-Hem v2**
(`src/zk_hem/v2/`, wire formats `QSAGZKH2` and `QSAGZKS2`), public Quintic `Fp5`
**`HemQuintic128`** (`src/hem_quintic.rs`, wire format `QSAGHQM2`), regional composition
**`HierarchicalHemAggregate`** (`src/recursive.rs`, wire format `QSAGHEM\x04`),
overlapping-bitfield binary recursive IVC **`SuccinctIvcProof`**
(`src/zk_hem/recursive_ivc.rs`, wire format `QSAGIVC1`), and high-arity commit-and-open
committee aggregation **`HighArityProof`**
(`src/zk_hem/recursive_ivc/high_arity_ivc.rs`, wire format `QSAGIVC2`), under which hypotheses,
and with which concrete bounds. The schedule calculator tables are computed by `src/zk_hem/v2/bounds.rs` and
`src/zk_hem/bounds.rs` using conservative directed integer-millibit rounding and pinned by
automated regression tests.

The labels below identify the evidence for a claim.

- **[lean]** a machine-checked constructive theorem in `lean/Qsag` or `aeneas/lean-whir`
  (`0 sorry`, `0 Classical.choice`, axioms confined to `{propext, Quot.sound}`);
- **[proof]** a mathematical argument proved in full in this document;
- **[cited]** a theorem imported from the cryptographic literature under the stated hypotheses;
- **[model]** an idealization (such as the ROM/QROM) on which the bound depends;
- **[open]** not yet established.

---

## 1. Shared Algebraic Substrate (`Fp5`) and QROM Envelope

All proof families operate over the Goldilocks prime field $\mathbb{F}_p$
($p = 2^{64} - 2^{32} + 1$) and draw sumcheck and WHIR challenges from its pure quintic
extension (`src/zk_hem/v2/field5.rs`, `Qsag.Math.QuinticExt5`):
$$E = \mathbb{F}_{p^5} = \mathbb{F}_p[X] / (X^5 - 3), \qquad |E| = p^5 > 2^{319.998}.$$

- **Algebraic structure [lean: `Qsag.Math.QuinticExt5`, `aeneas/lean-whir/Arithmetic.lean`].**
  Since $p \equiv 1 \pmod 5$ and $\zeta_5 = 3^{(p-1)/5} \bmod p = 1{,}041{,}288{,}259{,}238{,}279{,}555 \ne 1$,
  $X^5 - 3$ is irreducible over $\mathbb{F}_p$. Because $[E : \mathbb{F}_p] = 5$ is prime,
  $E$ admits zero intermediate proper subfields, and the Frobenius automorphism
  $\sigma(\sum_{i=0}^4 c_i X^i) = \sum_{i=0}^4 c_i \zeta_5^i X^i$ fixes $\mathbb{F}_p$
  pointwise. Every element $z \in E \setminus \mathbb{F}_p$ has five distinct conjugates
  $\{\sigma^i(z)\}_{i=0}^4$. Canonical wire encoding uses five little-endian `u64` limbs
  strictly below $p$ (`40` bytes; `FIELD_MILLIBITS = 319_998`).
- **Zero grinding.** No proof-of-work grinding is performed in any Quintic Hem protocol
  (`0` PoW bits). The round-by-round (RBR) budget takes no grinding credit.
- **QROM compilation envelope [cited: `[CDHZ25]` Theorems 6.10, 8.3, 11.3; `[BCS16]` Theorem 7.1; model].**
  Modelling framed hash calls to 400-bit `cSHAKE256` `[SP800-185]`, 400-bit `TurboSHAKE256`
  `[RFC9861]`, or 7-limb `Poseidon2-GL-w24` `[GKS23]` as ideal random oracles with
  $k < 2^9$ challenge rounds, $q_V + k \le 2^{15}$ verifier queries, $q_\Pi \le 2^{15}$
  proof openings, tree depth $\le 28$, and adversary query budget $t \ge 2^{24}$, the
  knowledge-extraction error satisfies
  $$\varepsilon_{\mathrm{QROM}}(t) \le 2^{0.023}\!\left(320\,(t + k + 1)(t + k)\,\varepsilon_{\mathrm{RBR}} + \frac{6380\,t^3}{2^{400}}\right).$$
  The certified $2^{0.023}$ slack (`QROM_ROUND_SLACK = 23` millibits) absorbs all lower-order
  commutativity, offline-path, and state-restoration remainders (`4(t+k+1)k / 2^{319}`)
  without discarding unnamed terms. Reaching $\varepsilon_{\mathrm{QROM}}(2^{64}) < 2^{-128}$
  requires $-\log_2 \varepsilon_{\mathrm{RBR}} \ge 264.5$ bits, which quartic $\mathbb{F}_{p^4}$
  ($|\mathbb{F}_{p^4}| < 2^{256}$) cannot provide without grinding and which $\mathbb{F}_{p^5}$
  accommodates in the transcribed budgets across all 13 schedules $\log_2 N \in [16, 28]$.

---

## 2. Committed-Mask Zero-Knowledge WHIR (`zk-Hem v2`)

`zk-Hem v2` lives in `src/zk_hem/v2/` behind wire magics `QSAGZKH2` (single-prover
`ZkHemV2Proof`) and `QSAGZKS2` (collaborative split-share `ZkHemV2SplitProof`). Both
decoders accept four 400-bit (`50`-byte) digest profiles (`v2/params.rs`):
- Tag `16`: `Profile::CshakeJohnson400` (`cSHAKE256`, capacity 512 `[SP800-185]`),
- Tag `17`: `Profile::TurboShakeJohnson400` (`TurboSHAKE256`, capacity 512 `[RFC9861]`).
- Tags `18` and `19` select `CshakeRateHalf400` and `TurboShakeRateHalf400`, respectively.
  They bind the rate-half schedule from §2.3.1 to the transcript. Tag 17 is the default.

Quartic `zk-Hem v1` and non-succinct hiding formats have been retired; all hiding relations
(`blind_vc`, `multisig`, `capability`, and `qsag-migrate` single-party and collaborative
proving) execute exclusively on `zk-Hem v2`. Unlike constrained interleaved-code ZK-IOPPs
`[CFW26]`, `zk-Hem v2` preserves the standard Reed–Solomon WHIR commitment family via a
single packed base-field cube paired with a folded-domain mask codeword. (Poseidon2 profiles
are deliberately excluded from `zk-Hem v2` because two 7-limb children exceed a single
width-12 permutation.)

### 2.1 Protocol, Packed Cube Layout, and `Good` Event

A v2 relation has $2^n$ rows ($n \ge 5$, $n < \text{usize::BITS}$), `num_vars >= 16`
variables (variable `0` is the constant `1`, followed by `num_public <= num_vars - 16`
public inputs, private witness variables, and 15 secret masking pads in three 5-limb
groups), and 24 reserved top rows in three 8-row corners enforcing `p * 1 = p`, `1 * p = p`,
and `p * 2 = 2p` on five rows each. Let $k = \lceil \log_2 \text{num\_vars} \rceil$.

**Packed Stage-0 table (`params::Layout`).** A single base-field cube $Z \in \mathbb{F}_p^N$
with $N = 2^\ell$, $\ell \in [16, 28]$ (`MIN_LOG_CELLS = 16`, `MAX_LOG_CELLS = 28`):

```text
[ variables | 0 | row masks | column masks | 0 | blinders ]
  0   num_vars  var_cells                        N - b    N
```

`var_cells` rounds `num_vars` up to a multiple of $2^{\max(4, k - 8)}$. Row masks occupy
$5 n \cdot 16$ cells; column masks occupy $5 k \cdot 4$ cells. The top
$b = 2^s (q_0 + 25)$ cells are sampled uniformly in $\mathbb{F}_p$, where $s$ and $q_0$ are
the Stage-0 fold count and fiber query count; $\ell$ is the smallest integer in `16..=28`
fitting `var_cells + masks + b <= 2^ell`. Both $b$ and $N - b$ are multiples of $2^s$.

**Commitment and kernels.** Let $c \in \mathbb{F}_p^N$ be the multilinear monomial
coefficient vector of $Z$ (`hypercube_to_monomial_coeffs`), with Reed–Solomon codeword
$\hat{Z}(x) = \sum_{i < N} c_i x^i$ on coset $D_0$ ($|D_0| = b_0 N$, with $b_0=4$ for tags 16–17 and $b_0=2$ for tags 18–19). Simultaneously, the
prover samples a uniform mask polynomial $R \in E[Y]$ of degree at most $N / 2^s + 1$,
evaluated on the folded domain $D' = \{x^{2^s} : x \in D_0\}$ ($b_0 N / 2^s$ fibers), and a
fresh 32-byte per-tree `tree_nonce`. Stage-0 leaf $g$ hashes `(tree_nonce, g, salt_g,
Z_hat|_fiber(g), R_hat(y_g))`, where `salt_g` is a fresh 32-byte per-leaf salt.

Linear claims $\langle c, \kappa \rangle = v$ combine *tensor terms*
($\kappa_i = w \prod_j r_j^{\text{bit}_j(i)}$, zero on overflow indices) and *point terms*
($\kappa_i = w x^i$ across all coefficient indices, retaining exact geometric continuation
on overflow slots so $\kappa_{\text{even}} + \phi \kappa_{\text{odd}}$ maps a point term at
$x$ with weight $w$ to $x^2$ with exact weight $w(1 + \phi x)$).

**Interactive rounds.** Each challenge is squeezed after absorbing the preceding prover
message:

| # | Prover message | Verifier challenge |
| --- | --- | --- |
| 0 | `tree_nonce` (32 B) + Stage-0 root (50 B), bound to magic, profile, relation digest, layout, schedule, statement, public inputs | $\tau \in E^n$ |
| 1 | Row mask sum $G_1 = \sum g_1$ | $\rho_1 \in E^\times$ |
| 2 | $n$ degree-9 row sumcheck polynomials | $r_{x,i} \in E$ |
| 3 | $(Az, Bz, Cz)(r_x) \in E^3$ | three batch weights in $E$ |
| 4 | Column mask sum $G_2 = \sum g_2$ | $\rho_2 \in E^\times$ |
| 5 | $k$ degree-2 column sumcheck polynomials of $M(r_x, y) Z_{\mathrm{var}}(y)$ | $r_{y,i} \in E$ |
| 6 | — | $\lambda \in E$ |
| 7 | — | $\omega_1, \dots, \omega_5 \in E$ |
| 8 | Five OOD evaluations $a_j = Z^\wedge(\omega_j)$ ($j = 1..5$) | $w_1, \dots, w_5 \in E$ |
| 9 | Per fold $i < s$: $(\sigma_{\mathrm{even}}, \tau_{01}, \tau_{10})$ then $(c_F, c_G)$ | $\phi_i \in E$, then $(\theta_i, \alpha_i, \beta_i) \in E^3$ |
| 10 | Mask claim $\mu = \langle R, v_s \rangle \in E$ | $\beta_R \in E^\times$ |
| 11 | Stage-1 root of scalar mask line $g = P_s + \beta_R R$ | two Stage-1 OOD points in $E$ |
| 12 | Two evaluations of $g$ | $q_0$ distinct Stage-0 fibers; batch weights |
| 13+ | Unsalted `Fp5` WHIR stages $1\dots$ on $g$, ending in $2^{\text{early\_stop\_vars}} + 2$ terminal coefficients and final fiber checks | stage challenges & queries |

Here $Z_{\mathrm{var}}$ restricts $Z$ below `var_cells` via at most $k - \text{var\_align} + 1$
dyadic tensor terms so the statement kernel $K$ reads zero cells $\ge \text{var\_cells}$
outside the two sumcheck masks. At each queried Stage-0 fiber over $y \in D'$, the verifier
folds the $2^s$ opened base symbols of $Z^\wedge$ using the round-9 challenges to $P_s(y)$
and verifies $g(y) = P_s(y) + \beta_R R^\wedge(y)$.

**Public coin guard (`Good`).** The honest prover tests `Good` on verifier coins before
each dependent message (aborting with `MaskRankDeficient` to retry with a fresh seed if
false):
- **(G1)** The five weights $\mathrm{eq}((r_{x,0}, r_{x,1}, r_{x,2}), c)$ ($c = 0..4$) form
  an $\mathbb{F}_p$-basis of $E$, and the three $(n - 3)$-factor corner products are nonzero.
- **(G2)** Each $z_j = \omega_j^{2^s}$ lies in $E \setminus \mathbb{F}_p$, and no $z_j$ is a
  Frobenius conjugate $\sigma^i(z_{j'})$ of another ($j \ne j'$).
- **(G3)** $w_j \ne 0$, and for each fold $i < s$: $\phi_i \ne 0$ and
  $1 + \phi_i \omega_j^{2^i} \ne 0$ for all $j \in \{1..5\}$.

**[proof]** $\Pr[\neg\mathsf{Good}] \le 15/p + (5 \cdot 2^s p + 50 \cdot 2^s + 5 + 6s + 3n)/|E| < 2^{-59}$
(evaluated at $(r_{x,0}, r_{x,1}, r_{x,2}) = (X, X^2, X^4)$, the basis determinant is
$16 \ne 0$, bounding (G1) via Schwartz–Zippel over $\mathbb{F}_p$). `Good` affects
completeness only; soundness is analyzed unconditionally over uniform verifier coins.

### 2.2 Zero Knowledge (`Lemmas V2.1–V2.4` & `Theorem V2.Z`)

**Lemma V2.1 (Top-cell monomial triangularity) [proof].** A table supported on the top $b$
hypercube indices $[N - b, N)$ has multilinear monomial coefficients supported bijectively
on $[N - b, N)$. Consequently $Z^\wedge(x) = W(x) + x^{N - b} B(x)$, where $W$ is fixed by
cells below $N - b$ and $B \in \mathbb{F}_p[x]$ is uniform of degree $< b$, independent of $W$.

**Lemma V2.2 (Frobenius CRT blinding count) [proof; point-interpolation form `[lean: v2_blinding_count]`; matching lower bound `[cited: [FPR26] Lemma 1]`].**
Let $Q \subset \mathbb{F}_p^\times$ be distinct nonzero base points and
$z_1, \dots, z_t \in E \setminus \mathbb{F}_p$ be pairwise Frobenius non-conjugate. If
$b \ge |Q| + 5 t \cdot 2^s$, then
$$B \longmapsto \Big((B(q))_{q \in Q},\; \big(x^{N - b} B \bmod (x^{2^s} - z_j)\big)_{j = 1..t}\Big) \in \mathbb{F}_p^{|Q|} \times \prod_{j=1}^t E[x]/(x^{2^s} - z_j)$$
is a surjective $\mathbb{F}_p$-linear map, hence uniform for uniform $B$ of degree $< b$.

*Proof.* Set $m_j(x) = \prod_{i < 5} (x^{2^s} - \sigma^i(z_j))$. Its coefficients are
$\sigma$-invariant, so $m_j \in \mathbb{F}_p[x]$ of degree $5 \cdot 2^s$. Because
$z_j \notin \mathbb{F}_p$ and $5$ is prime, the five $\sigma^i(z_j)$ are distinct, so any
$f \in \mathbb{F}_p[x]$ divisible by $x^{2^s} - z_j$ is divisible by all five coprime
conjugate factors and hence by $m_j$; equal $\mathbb{F}_p$-dimension $5 \cdot 2^s$ makes
$\mathbb{F}_p[x]/m_j \to E[x]/(x^{2^s} - z_j)$ an isomorphism. Across $q \in Q$ and $j$,
$x - q$ and $m_j$ are pairwise coprime ($q^{2^s} \in \mathbb{F}_p$ whereas
$\sigma^i(z_j) \notin \mathbb{F}_p$ are distinct) and coprime to $x$ ($q \ne 0, z_j \ne 0$),
so Chinese Remainder Theorem surjectivity and invertibility of $x^{N - b}$ complete the
proof. $\square$

**Lemma V2.3 (Fold-scalar Vandermonde bijection).** Fix $j \in \{1..5\}$ and write
$A = E[x]/(x^{2^s} - z_j)$, $T_j = Z^\wedge \bmod (x^{2^s} - z_j)$, and
$x_{j,i} = \omega_j^{2^i}$.
1. **[proof]** With $u_i = P_i(x_{j,i})$ ($u_0 = a_j$), $F_i, G_i$ the even/odd parts of
   $P_i$ at $x_{j,i}^2$, and $w_{j,0} = w_j$, $w_{j,i+1} = w_{j,i}(1 + \phi_i x_{j,i})$, we
   have $u_i = F_i + x_{j,i} G_i$, $u_{i+1} = G_i + (\alpha_i + \beta_i x_{j,i}^2)(F_i + \theta_i G_i)$,
   and point $j$'s contribution to the five fold-$i$ scalars is $E$-linear in $T_j$:
   $$(\sigma_{\mathrm{even}}, \tau_{01}, \tau_{10}, c_F, c_G)_j = w_{j,i}\big(F_i,\; x_{j,i} F_i,\; G_i,\; (1 + \phi_i x_{j,i}) x_{j,i}^2 F_i,\; (1 + \phi_i x_{j,i}) x_{j,i}^2 G_i\big).$$
2. **[proof]** Whenever $\omega_j \ne 0$, the $s + 1$ functionals $u_0, F_0, \dots, F_{s-1}$
   on $A$ ($\dim_E A = 2^s$) are $E$-linearly independent (by backward induction from $i = s$:
   $\Phi(F, G) = G + (\alpha_i + \beta_i Y)(F + \theta_i G)$ surjects onto $A_{i+1}$, and
   $(1 + \theta_i(\alpha_i + \beta_i Y), -(\alpha_i + \beta_i Y)) \in \ker \Phi$ witnesses
   that $\mathrm{span}(u_i, F_i)$ meets $(\ker \Phi)^\perp$ only along $u_{i+1} \circ \Phi$).
3. **[proof; `[lean: v2_fold_scalar_matrix_bijective]`]** Under (G2) and (G3), for each fold
   $i < s$ and fixed $(u_i)_{j=1..5}$, mapping $(F_i)_{j=1..5} \in E^5$ to the summed
   5-scalar contribution is an affine bijection of $E^5$: substituting
   $G_i = (u_i - F_i)/x_{j,i}$ and row-reducing at $\phi_i \ne 0$ yields the rows
   $(x^{-1}, 1, x, x^2, x^3)$, i.e., a $5 \times 5$ Vandermonde matrix on distinct nonzero
   $x_{1,i}, \dots, x_{5,i}$ times $\mathrm{diag}(w_{j,i}/x_{j,i})$.

**Lemma V2.4 (Scalar mask line) [proof; `[lean: v2_mask_line_perfectly_simulated, v2_mask_line_view_perfectly_simulated]`].**
For $\beta_R \in E^\times$ and any $P_s$ of degree $\le N/2^s + 1$,
$R \mapsto g = P_s + \beta_R R$ is a bijection on $E^{N/2^s + 2}$ with inverse
$R = (g - P_s)/\beta_R$, uniquely fixing $\mu = (\langle g, v_s \rangle - \sigma_s)/\beta_R$
and opened symbols $R^\wedge(y) = (g(y) - P_s(y))/\beta_R$.

**Theorem 3.1 of the paper (V2.Z, perfect HVZK of the IOP) [paper proof].**
Lean mechanizes the algebraic mask-bijection and rank results of Lemmas 3.2–3.4
(V2.2–V2.4 above), including the point-interpolation form of V2.2. The composition
of these results into a simulator for the complete interactive view is a paper proof.
For every satisfying assignment and
independent uniform prover coins, the IOP of §2.1 is perfect honest-verifier zero-knowledge
(matching exact abort prefixes outside `Good`). The view contains the specified fold projections and queried symbols. Disclosing complete remainders can expose coefficients.
- *Front & surrogate $W'$:* Nonconstant mask coefficients make `G1`, row polynomials on the
  affine space fixed by the endpoint sum, `(Az, Bz, Cz)(rx)` (via invertible corner determinant
  $k_0 k_1 k_2 \ne 0$ on (G1)), `G2`, and column polynomials conditionally uniform. Varying
  the constant, linear, or quadratic 5-limb block of row-mask round 0 scales $\langle c, K \rangle$
  by $2^n + \lambda^2$, $2^{n-1} + \lambda^2 r_{x,0}$, or $2^{n-1} + \lambda^2 r_{x,0}^2$
  (never simultaneously zero: $\lambda^2 = -2^n, r_{x,0} = 1/2 \implies 2^{n-2} \ne 0$), so a
  lower surrogate $W' \in \mathbb{F}_p^{N-b}$ with $\langle c(W', 0), K \rangle = V$ always
  exists.
- *Stage-0 decoupling:* Because $2^s \mid (N - b)$, the blinder start $L_i = (N - b)/2^i$ is
  even across all $i < s$, so folded tensor kernels vanish on all blinder indices and their
  $Y$-shifts (including overflow). Blinders enter $(a, S_0, \dots, S_{s-1})$ solely via the
  five OOD point kernels, where Lemmas V2.1–V2.4 establish joint uniformity of
  $(a, S_0..S_{s-1}, g, O)$.

**Fiat–Shamir, leaf hiding, and coin derivation scope.**
- *Unopened leaf hiding [proof, from `[cited: [AHU19]]` O2H]:* Because every Stage-0 leaf
  absorbs `(tree_nonce, leaf_idx, salt)`, leaf domain prefixes across $P$ proofs collide iff
  two proofs draw the same 256-bit `tree_nonce` ($\binom{P}{2}/2^{256}$, independent of
  $|D'|$). Coupling unopened leaf digests identically across real and simulated worlds bounds
  distinguishing advantage by $t P / 2^{256} + \binom{P}{2}/2^{256}$ classically and
  $2 t \sqrt{P / 2^{256}} + \binom{P}{2}/2^{256}$ against $t$ quantum queries (`2^-63` for
  $P = 1, t = 2^{64}$).
- *Seed expansion [model]:* Deriving prover coins via `cSHAKE256("QSAG.ZKHEM2.COINS.SEED/v1", ...)`
  and `SeedStream("QSAG.ZKHEM2.COINS/v1", key)` adds a standard PRG/ROM seed-guessing hybrid
  ($t P / 2^{256}$ classical, $2 t \sqrt{P / 2^{256}}$ quantum).
- *Fiat–Shamir zero knowledge:* Classical programmable-ROM simulation incurs programming loss
  $\le M(t + M)/2^{399}$ across $M$ programmed oracle inputs. **[open]** Quantum adaptive
  Fiat–Shamir reprogramming and malicious-verifier interactive ZK are not claimed.

### 2.3 Knowledge Soundness (`[DKT26]` Theorem 5.12 & Schedule Table)

**Theorem V2.1 (Round-by-round knowledge soundness) [proof, from `[cited: [DKT26] Theorem 5.12, [CWYZ26] Theorem 5.1, [ACFY25] Lemma 4.25]`; rational packed-fiber error budgets `[lean: ZkHemV2PackedFiberCerts.lean]`].**
Fix proximity parameter $m \in [3, 512]$ and Stage-0 fiber agreement threshold
$A_0 \ge (1 + \frac{1}{2m})\sqrt{(N/2^s + 2)|D'|}$ ($D = N/2^s + 1$, Johnson list bounds
$l_0, l', l_i$, `[CWYZ26]` fold numerator $L_i = l + 2l_0 + 1 < 16{,}384$):

| Round | RBR error upper bound | Citation / justification |
| --- | --- | --- |
| Front sumchecks & batching ($\tau, \rho_1, r_x, \rho_2, r_y, \lambda$) | $d l_0 / (|E| - 1)$, $d = \max(n, 15, 4 + \text{num\_public})$ | Schwartz–Zippel per list word (unconstrained 16-cell row-mask block has degree $\le 15$) |
| Stage-0 OOD points $\omega_1..\omega_5$ & weights $w_1..w_5$ | $\min\!\big(\frac{l_0^2}{2}(\frac{N+2}{|E|})^5,\; \frac{5 l_0}{|E|}\big)$ + $\frac{5 l_0}{|E|}$ | `[ACFY25]` Lemma 4.25 (5 samples) + linear batching |
| Kernel fold $\phi_i$ & affine fold $(\theta, \alpha, \beta)_i$ | $L_i / |E|$ each | `[CWYZ26]` Theorem 5.1, eq. (5.5) |
| Scalar mask line $\beta_R \in E^\times$ | $\big(\lceil \frac{(2m+1)^3 |D'|^2}{3 D} \rceil + l'\big) / (|E| - 1)$ | `[DKT26]` Theorem 5.12 ($d = 1$) + $l'$ joint-agreement pairs |
| Stage $i \ge 1$ OOD points (2 samples) | $\frac{l_i^2}{2}(\frac{2^{r_i} + 2}{|E|})^2$ | `[ACFY25]` Lemma 4.25 |
| Stage $i$ distinct fiber queries & next-stage batching | $\binom{A_i + s_i}{q_i} / \binom{|D'_i|}{q_i} + \frac{(q_i + 2) l_{i+1}}{|E|}$ | Hypergeometric distinct-fiber sampling (`s_i` fold losses) |
| Final-stage queries after terminal polynomial | $\binom{A_{\text{last}} + s_{\text{last}}}{q_{\text{last}}} / \binom{|D'_{\text{last}}|}{q_{\text{last}}}$ | Terminal coefficients absorbed prior to query squeeze |

Replacing `[BCGM25]` Lemma 9.3 ($(m + 1/2)^7 |D'|^2 / \rho'^{3/2}$) with `[DKT26]`
Theorem 5.12 reduces the $(2m+1)$ exponent from $7$ to $3$ and makes $B_{\mathrm{cf}}$ scale
linearly in $|D'|$ at fixed rate, unlocking all 13 table sizes $2^{16}\dots 2^{28}$ with
minimal Stage-0 queries `STAGE0_QUERIES = [267, 267, 267, 267, 267, 267, 267, 267, 266, 266, 266, 266, 266]`
(`ZkHemV2PackedFiberCerts.lean`: `zkHemV2_packed_all13_budget_lt_128`). Beyond the
Johnson radius, `dkt26_beyond_johnson_first_order` (`[DKT26]` Prop. 5.10 + Lemma 5.6 +
Cor. 7.8, list size $L \le 2$) is an exploratory Rust calculation of $209\dots 220$-query first-order schedules. Tags 16–17 use the schedules above.

Reproduce the full calculator table:

```sh
cargo test --release -p qsag-agg --lib -- zk_hem::v2::bounds::tests::print_v2_tables --ignored --nocapture
```

| Rows, variables | Cells | Queries per stage | $m$ | Weakest round (RBR bits) | Classical level | QROM level (RBR, digest) | QROM error at $t = 2^{64}$ | Max proof bytes |
| --- | ---: | --- | ---: | --- | ---: | --- | ---: | ---: |
| `2^16`, 40,000 | `2^16` | `267, 136, 92` | 54 | `265.230` (Stage-0 query) | `198.999` | **128.276** (`128.442`, `129.112`) | `2^-128.884` | 288,624 |
| `2^17`, 82,000 | `2^17` | `267, 136, 92` | 54 | `265.183` (Stage-0 query) | `198.999` | **128.253** (`128.419`, `129.112`) | `2^-128.837` | 347,280 |
| `2^17`, `2^17` | `2^18` | `267, 136, 92` | 75 | `264.811` (Stage-0 query) | `198.999` | **128.121** (`128.233`, `129.112`) | `2^-128.465` | 373,310 |
| `2^20`, `2^20` | `2^21` | `267, 136, 92` | 145 | `265.009` (Stage-0 query) | `198.999` | **128.192** (`128.332`, `129.112`) | `2^-128.663` | 500,602 |
| `2^21`, 1,088,721 | `2^21` | `267, 136, 92` | 145 | `265.009` (Stage-0 query) | `198.999` | **128.192** (`128.332`, `129.112`) | `2^-128.663` | 501,122 |
| `2^22`, `2^22` | `2^23` | `267, 136, 92, 70` | 271 | `265.374` (Stage-0 query) | `198.999` | **128.317** (`128.514`, `129.112`) | `2^-129.028` | 607,936 |
| `2^23`, `2^23` | `2^24` | `266, 136, 92, 70` | 364 | `264.514` (Stage-0 query) | `198.999` | **128.001** (`128.084`, `129.112`) | `2^-128.168` | 640,642 |
| `2^24`, `2^24` | `2^25` | `266, 136, 92, 70` | 480 | `264.620` (Stage-0 query) | `198.999` | **128.047** (`128.137`, `129.112`) | `2^-128.274` | 690,902 |
| `2^25`, `2^25` | `2^26` | `266, 136, 92, 70` | 511 | `264.634` (Stage-0 query) | `198.999` | **128.048** (`128.144`, `129.112`) | `2^-128.288` | 791,962 |
| `2^26`, `2^26` | `2^27` | `266, 136, 92, 70` | 512 | `264.629` (Stage-0 query) | `198.999` | **128.051** (`128.142`, `129.112`) | `2^-128.283` | 839,782 |
| `2^27`, `2^27` | `2^28` | `266, 136, 92, 70` | 512 | `264.627` (Stage-0 query) | `198.999` | **128.050** (`128.141`, `129.112`) | `2^-128.281` | 1,027,882 |

#### 2.3.1 Rate-half packed commitments (`tags 18–19`) and query-factor reality

Tags 18–19 use $2N$ base evaluations and 644 distinct Stage-0 fibers, 2.41–2.42 times the legacy query count. Both the assignment and optional lookup helper use the selected profile. Each cube is sized with its own blinding requirement $2^s(644+25)$. Comparisons at fixed $N$ assume the relation fits both layouts. Later stages retain their original rates and query counts.

**Exact query factor vs. unique decoding.** With folded fiber count $n=2N/2^s$, code dimension $k=n/2+2$ (rate $\rho=k/n=1/2+2/n$), inner error count $e=n/4-2<(n-k)/2$, and inner agreement $A=n-e=3n/4+2$, both `v2/bounds.rs` (`rate_half_stage_bound`) and `Qsag.Coding.AboveJohnsonWhir` (`rateHalfWitness`) prove and charge the without-replacement falling-factorial query bound $(A+1)_{644}/(n)_{644}$, whose per-query survival ratio $(A+1)/n=3/4+3/n\to 3/4=(1+\rho)/2$ coincides with ordinary unique decoding at rate $\rho=1/2$. Two-witness RVW13 halving (`aboveJohnson_rvw`; Chai–Fan, ePrint `2026/858` Theorem 5, unrefereed preprint) maps an outer proximity premise $\delta_{\mathrm{outer}}=2e/n<1-\rho$ on the first fold into the unique-decoding ball $\delta_{\mathrm{inner}}=e/n<(1-\rho)/2$, so its per-query factor $1-\delta_{\mathrm{outer}}/2>(1+\rho)/2$ approaches $1-(1-\rho)/2=(1+\rho)/2=3/4$ near capacity (and by AM–GM exceeds the Johnson factor $\sqrt{\rho}$ at every rate), saving **zero queries** over unique decoding. Moreover, knowledge extraction of R1CS, lookup, and evaluation claims (`word_list = 1`) already operates directly inside the inner unique-decoding ball $2^s A$ via CWYZ Theorem 5.1 and `aboveJohnson_lift_chain`, yielding the identical $(A+1)_{644}/(n)_{644}$ query bound; RVW13 only extends pure proximity rejection for unclaim-bound words from distance $1/4-2/n$ out to $1/2-4/n$. Tags 18–19 are therefore a **Stage-0 prover-memory and encoding-speed profile, not a proof-size optimization**: halving $|D_0|$ buys **$2.19\times$ faster Stage-0 CPU LDE** at $2^{20}$ (`211.395 ms` vs. `462.372 ms`) and **$-5{,}312\text{ MiB}$ (`-5.19 GiB`) Stage-0 Canopy device buffer footprint** at $2^{28}$, at the cost of **`+38.6%` to `+63.1%` larger proof bytes** vs. Rate-1/4 Johnson (`tags 16–17`: `+38.6%–38.7%` on `pin` at $2^{16}$, `+39.5%–63.1%` across the $2^{16}\dots 2^{28}$ max-byte envelope).

**Which result transfers.** In Chai–Fan Theorem 5, two scalar challenges with codeword agreements on all but $h$ positions each yield a joint explanation on all but $2h$ positions. Subtracting the two equations on the intersection recovers the slope and then the intercept. This proves the bound of one exceptional scalar for any linear code, including the linear kernels of Corollary 48. A nonzero OOD evaluation defines an affine coset. Subtracting two explanations for it produces an element of the homogeneous kernel. For v2 the five OOD values are batched into the coefficient functional before the first fold. Its point terms extend to the overflow coefficients. The candidate-list OOD and claim-binding terms in §2.3 remain necessary. [Chai–Fan, Theorems 5, 14, 18 and Corollary 48](https://eprint.iacr.org/2026/858)

**The first binary fold.** Put $n=2N/2^s$, $k=n/2+2$, $e=n/4-2$, and $A=n-e$. The premise distance $2e/n$ is strictly between $1-\sqrt{k/n}$ and $1-k/n$, and $k+2e<n$. The first virtual output domain has $n_1=2^{s-1}n$ positions. Write $F,G$ for the even and odd words and $H=F+\theta G$. Pairing both antipodes lifts each joint agreement to two input agreements. For the degree-$N+1$ analysis envelope the even and odd polynomials each have degree at most $N/2$. Hence an input farther than $2e/n$ from this ambient code has joint distance above $2e/n$. Except for at most one $\theta$, $H$ has at most $2^{s-1}A-1$ agreements with every polynomial of degree at most $N/2$. The honest packed polynomial has degree below $N$. Extraction for the relation uses its first $N$ coefficients, with zero statement weights on the two overflow indices. More than $N+1$ agreements with base symbols at distinct base points force its coefficients into the base field by interpolation. Proximity to the larger analysis code alone does not certify that an arbitrary oracle has degree below $N$.

The actual output at $y=x^2$ is $G(y)+(\alpha+\beta y)H(y)$. Conditional on $\theta$, the affine decomposition theorem gives a witness for $H$ of degree at most $N/2$ on all but one of a candidate's agreements. Thus, outside the affine exceptional set, the first output agreement cap is $2^{s-1}A$. Each remaining binary step with cap $M$ has cap $\lfloor M/2\rfloor+1$ on good challenges because a candidate with $u$ agreements lifts to at least $2(u-1)$ parent agreements. These bounds apply on virtual domains determined by the committed word and preceding challenges. There is no intermediate oracle commitment inside the fiber. Starting at $2^{s-1}A$ gives $A+1$ after the remaining folds for $s>1$, and $A$ for $s=1$. Equivalently, $A+2$ exit agreements lift to at least $2^s A+2$ at entry. This is the finite-coordinate cost of affine decomposition. Repeated threshold halving would give a different query budget. [CWYZ, §§4–5](https://arxiv.org/abs/2611.15128)

**Claims and the mask.** Ambient distance covers only one case. For a false coefficient claim with a nearby ambient word, v2 applies CWYZ Theorem 5.1 at the inner agreement $2^j A$ on **every** virtual domain $2^j n$, including the first. A passing candidate lifts to a pair explaining the same agreement set up to one position. At the scaled thresholds the overlap of two such pairs at agreement $2^j A-1$ exceeds the component degree, including overflow. Thus the component witnesses are fixed before the kernel challenge. For their four inner products $u,v,x,y$ against the even and odd kernel halves, the two claimed evaluations at $\phi$ must equal $u+\phi v$ and $x+\phi y$. Equality as polynomials in $\phi$ forces the incoming claim to equal $u+y$. An incorrect claim therefore escapes at at most one $\phi$. The two shift claims are sent after $\phi$ and before $(\theta,\alpha,\beta)$, as permitted by the preannounced shift-claim variant in §5. The calculator charges the finite CWYZ numerator plus five field challenges for the initial scalar line and bridge terms. The Lean certificate checks interpolation at every intermediate size with multiplicity 3 and total degree 14. All lists used by the front end are evaluated at the inner agreement. The argument requires no list bound at the outer distance.

After those folds the independently committed mask still needs a common explanation on exactly the coordinates opened by the verifier. On the $n$-point folded domain the maximum degree is $D=k-1$. At $m=16$ the calculator checks $32^2 A^2\ge 33^2 n k$. DKT Theorem 5.12 then gives equality of the entire agreement sets for the two witnesses to $P_s+\beta_R R$ and a count below $33^3 n^2/(3D)$ of exceptional scalars. The separate list term accounts for cancellation of a false mask claim. The denominator is $|E|-1$ because the mask challenge is nonzero. The resulting pure query bound is $(A+1)_q/(n)_q$ for $q=644$, where $(a)_q$ is a falling factorial. The claim-aware argument also gives this bound for inputs farther than $2(e-1)/n$. Their distance already rules out an entry witness at the stronger inner agreement, and $(A+1)/n=1-(e-1)/n$. [DKT, Theorem 5.12](https://eprint.iacr.org/2026/2056)

**Composition.** Theorem 52 of Chai–Fan assumes at least as many shift queries as final queries. The v2 verifier batches independently sampled shifts into the next stage and finishes by testing the terminal polynomial. Its proof imports WHIR's OOD and sumcheck results for that protocol. Theorem 18's multi-deviation argument also treats distance from a code as a lower bound on distance from an arbitrary next oracle. A next oracle can differ in just one coordinate while both words are far from the code. Appendix D's Theorem 72 defines its state using the current oracle's distance, which omits earlier consistency obligations. Theorem 73 gives a classical random-oracle bound. For v2 the state carries the coefficient claim, the nearby witnesses, and the authenticated shift queries. Each query round uses its own without-replacement bound plus batching, followed by the §1 CDHZ25 compilation for a fixed relation in the ideal-oracle model. The new profiles reserve 512 calls for the round offset and debit the maximum Merkle verification work before allocating the transcript's remaining calls, including retries. A tree with $q$ opened leaves and $S$ authentication siblings uses $2q+S$ hashes including the framed root. Lookup helper trees and split-share trees each count. The verifier rejects split layouts exceeding this envelope and checks each lookup relation’s tuple-compression, pole and sumcheck errors against the target. [Chai–Fan, Theorem 52 and Appendix D](https://eprint.iacr.org/2026/858) · [CDHZ25](https://eprint.iacr.org/2025/2166)

**Space, time and wire size.** For $L=b_0N$, one base transform and five mask-limb transforms take exactly $[L\log_2 L+5(L/2^s)\log_2(L/2^s)]/2$ radix-2 butterflies. Halving $L$ also removes one Merkle level. At $\log_2 N=28$ this reduces 17,112,760,320 butterflies to 8,266,973,184, an exact work ratio of $1360/657$. In a paired CPU measurement at $\log_2 N=20$ the two Stage-0 encoders together took **462.372 ms and 211.395 ms** (2.19×). These are single-worker release medians from three alternating runs after warmup on an i9-12900. The timing includes coset scaling and output allocation.

At $\log_2 N=28$, the base codeword drops from 8 GiB to 4 GiB, the mask codeword from 640 MiB to 320 MiB, and the Vulkan Canopy heap (two slots per leaf at 56 bytes each) from 1,792 MiB to 896 MiB. The three device payloads of the Canopy dispatch thus shrink by **5,312 MiB** in total, counting the mask in its metadata buffer once. These are exact buffer lengths. Allocator headroom, staging and retained buffers affect device residency. The RX 6750 XT reports a maximum storage-buffer range of 4,294,967,295 bytes, one byte short of the smaller base buffer. A peak VRAM measurement for this size requires a chunked backend.

The table compares single-prover shapes with $\log_2 N$ row variables, $N/2$ assignment variables and no lookup. Byte columns give the exact maximum over query placements in the wire format. For depth $d$ and $q$ openings the maximum sibling count is $2^h-q+q(d-h)$, $h=\lceil\log_2 q\rceil$. Spread leaves attain it at every depth. For a specific transcript the exact length uses its actual sibling count at each tree. In the fixed-seed `pin` fixture ($2^{16}$ cells), cSHAKE proofs grew from 264,204 to 366,154 bytes and TurboSHAKE proofs from 264,254 to 366,554 bytes.

| $\log_2 N$ | Stage-0 leaves at rate ½ | RBR bits | QROM work bits | $-\log_2\varepsilon(2^{64})$ | Max bytes at ¼ | Max bytes at ½ | Extra bytes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 8,192 | 268.787 | 128.992 | 132.441 | 283,804 | 395,804 | 112,000 |
| 17 | 8,192 | 268.787 | 128.992 | 132.441 | 342,460 | 502,716 | 160,256 |
| 18 | 16,384 | 268.599 | 128.980 | 132.253 | 369,010 | 548,116 | 179,106 |
| 19 | 32,768 | 268.867 | 129.001 | 132.521 | 396,840 | 594,796 | 197,956 |
| 20 | 65,536 | 267.757 | 128.849 | 131.411 | 427,230 | 644,036 | 216,806 |
| 21 | 65,536 | 267.757 | 128.849 | 131.411 | 496,302 | 809,620 | 313,318 |
| 22 | 131,072 | 267.017 | 128.779 | 130.671 | 553,892 | 886,060 | 332,168 |
| 23 | 262,144 | 266.649 | 128.652 | 130.303 | 603,036 | 954,054 | 351,018 |
| 24 | 524,288 | 266.466 | 128.591 | 130.120 | 635,842 | 1,006,794 | 370,952 |
| 25 | 1,048,576 | 266.374 | 128.558 | 130.028 | 686,102 | 1,075,954 | 389,852 |
| 26 | 2,097,152 | 266.328 | 128.561 | 129.982 | 787,162 | 1,195,914 | 408,752 |
| 27 | 4,194,304 | 266.306 | 128.550 | 129.960 | 834,982 | 1,262,634 | 427,652 |
| 28 | 8,388,608 | 266.294 | 128.544 | 129.948 | 1,023,082 | 1,469,634 | 446,552 |

Reproduce the size and security table with `cargo test --release -p qsag-agg --lib above_johnson_rate_half -- --nocapture` and the paired timing with `cargo test --release -p qsag-agg --lib rate_half_lde_timing -- --ignored --nocapture`. The constructive [Lean module](../../lean/Qsag/Coding/AboveJohnsonWhir.lean) proves the scalar-line lemma, RS uniqueness, the packed agreement recurrence and the without-replacement count, with kernel-checked witnesses for all 13 sizes.

### 2.4 Jointly Masked LogUp (`LookupV2Proof`) and Split-Share Opening (`QSAGZKS2`)

- **Jointly masked LogUp (`v2/protocol.rs`, `[cited: [Hab22] Lemma 5]`, `[lean: ZkHemV2ComposedZkAndCerts.lean]`).**
  For $L$ lookups and $T$ public table rows ($L < p$) of width $w$ in a lookup cube of
  dimension $d = \max(3, \lceil \log_2(L + T + 8) \rceil)$, $\gamma$ compresses tuples and
  $\alpha$ selects the pole. Before batch inversion, the prover verifies that the product of
  *all* checked denominators $\alpha - v_i$ (including zero-multiplicity table rows) is
  nonzero in $E$, returning `LookupPoleHit` on the public pole set ($\le (T + 1)/|E|$)
  without witness-dependent timing. The helper cube $H$ packs the five limbs of
  $h_i = n_i / (\alpha - v_i)$, degree-4 lookup sumcheck masks, an 8-entry corner supplying
  rank-15 base-field masking across joint disclosures, and `blind_cells_for` top blinders
  with an independent `tree_nonce` and mask polynomial $R_H$. `lookup_terms` charges RBR
  errors $((w - 1) L T l_0,\; (L + 2T + 1) l_0,\; \max(d, 5) l_0 l'_0) / |E|$ (replacing
  $L T$ by $T - 1$ when $L = 0$).
- **Split-share collaborative opening (`QSAGZKS2`, `v2/pcs.rs`).**
  `ZkHemV2SplitProof` commits $c \in [1, 255]$ additive Stage-0 share trees
  ($Z = \sum_{p=1}^c Z^{(p)}$, $R = \sum_{p=1}^c R^{(p)}$), each with an independent
  32-byte `tree_nonce` and 32-byte per-leaf salts (`max_split_proof_bytes`). Whenever at
  least one custodian is honest, its uniform top blinders, $R^{(p)}$, `tree_nonce`, and leaf
  salts statistically mask the reconstructed joint opening view.

---

## 3. Public Committee Aggregation (`HemQuintic128` / `QSAGHQM2` & `QSAGHEM\x04`)

`prove_hem_quintic_128` and `verify_hem_quintic_128` (`src/hem_quintic.rs`) aggregate active
`JortsPoseidon2` (`512` rows/signer, heights $6\dots 20$) or `CorduroyPoseidon2` (`8,192`
rows/signer) signatures into a deterministic unmasked proof (`QSAGHQM2`):
- **Canopy profiles:** `HemQuinticProfile::TurboShake400` (`tag = 1`, 50-byte
  `TurboSHAKE256` digests: `360,391` B on the 3-of-4 sparse Jorts vector) and
  `HemQuinticProfile::Poseidon2Gl24` (`tag = 2`, 56-byte 7-limb `Poseidon2-GL-w24` Jive
  digests: `381,661` B on the same vector). Transcript calls are capped at
  `FS_CALL_LIMIT = 4096`.
- **Inactive-slot constraints [paper argument, Rust regression].** In
  `hem_quintic/rows.rs`, on inactive padding slots (`INACTIVE = 1 - active`), the degree-8
  row sumcheck pins all **138 non-S-box columns** (`COL_ST_IN[0..12]` and
  `COL_PREV_STATE..256`) to canonical zero via random $\gamma$-powers; the width-12
  Poseidon2 permutation equations then uniquely pin all 118 `COL_SBOX_OUT` columns,
  fixing the unique inactive row in the unbatched relation. A fixed nonzero residual can vanish under batching only at a root of the challenge polynomial.
- **Concrete error budget [lean arithmetic, cited bounds, ideal-oracle model].**
  For either Canopy, all 13 sizes and $Q \le 2^{64}$,
  `publicHemQuintic_budget_lt_128` in `PublicHemQuintic128.lean` proves
  `RatBound.lt (publicHemError profile logCells Q) …` with right-hand side $2^{-128}$.
  The corresponding packed-fiber result in §2.3 also compares rationals. Both have the
  form `*_budget_lt_128`. They check the arithmetic of transcribed CDHZ25/DKT26
  error terms under the cited reduction and proximity hypotheses.
- **Protocol reductions [lean, conditional].** In `Top/ClosedProtocolReductions.lean`,
  `whir_exec_closed_qrom_soundness` bounds failure in a modeled verifier experiment.
  The deployed succinct specialization requires a `WhirScheduleCert` for that
  environment, a root-consistency premise and a bound on the Merkle collision event.
  Checking numerical parameters does not construct these premises for the Rust verifier.
- **Extraction boundary [lean, Rust].** The 86 extracted definitions of
  `qsag-whir-verified` cover `Fp5` arithmetic and Frobenius, canonical decoding,
  Steiner multiproof sibling counting, and row-round and CWYZ fold payload checks.
  `compute_steiner_multiproof_siblings` agrees with `Qsag.steinerSiblingCount`.
  The public verifier calls `verify_qsaghqm2_row_rounds_at`,
  `verify_qsaghqm2_cwyz_folds_at` and `verify_qsaghqm2_multiproof_and_rounds`
  on bounded payloads. The enclosing Rust verifier owns transcript and challenge
  derivation, query sampling, Merkle hashing and authentication, and the final
  control flow. The count in `Funs.lean` includes constants and generated loop bodies.
  Compiler correctness and the complete verifier require separate arguments.
- **Acceptance policy [Rust].** Direct callers must bind their expected profile and
  participation rule when accepting a proof. The CLI enforces `--min-signers K` or
  explicit `--allow-any-subset`, with the expected profile selected outside the proof.

---

## 4. Overlapping-Bitfield Binary Recursive IVC (`QSAGIVC1`)

`prove_ivc_tree` and `verify_ivc_tree` (`src/zk_hem/recursive_ivc/`) aggregate contiguous
runs of Jorts committees into a fixed-size **639,673-byte** root (`QSAGIVC1\x00`,
`IvcStepConfig::dkt26(23)`, `ivcRootProof_byteSize_independent_of_depth`):

- **Participation and interval width (Rust).** `IvcSubtreeStatement::total_signers`
  counts signing member positions. `completed_shards()` returns the width of the
  authenticated half-open interval. A partial single-committee statement still has
  width one. The default leaf verifies up to 64 signatures at 256 possible bitmap
  positions. Within one committee the circuit takes the Boolean union of the two
  bitmaps and counts each set bit once. Joining adjacent intervals requires each
  single committee to meet its threshold (32-bit range check on the surplus).
  The parent then clears the bitmap and threshold and adds the signer totals with
  checked 64-bit arithmetic. Root verification also checks completion.
- **Multi-depth QROM extraction scope [lean: `MultiDepthRecursiveQromExtractor.lean`, `RecursiveIvcPublicRowQrom.lean`].**
  1. *Margin schedule (`2^20` cells, `304 / 148 / 100` queries):* Straight-line extraction
     in the recorded-query model charges a whole-tree budget below $2^{-128}$ for
     $d \le 16$ and $Q \le 2^{64}$ (`multidepth_recursive_qrom_lt_2_neg_128`).
  2. *Production `dkt26(23)` whole-tree budget (`267 / 136 / 92 / 70` queries, 95 public sumcheck rounds/node):*
     Prefix-encoded public-round QROM failure mass across all $2^{d+1}-1$ nodes is
     $< 2^{-160}$ for $d \le 20, Q \le 2^{64}$ (`tree_public_sumchecks_qrom`). Combined
     whole-tree WHIR + collision error clears $< 2^{-128}$ for **$d \le 7$ at $Q \le 2^{64}$**
     or **$d \le 20$ at $Q \le 2^{57}$** (`treeBudget_lt_128`; at $d = 20, Q = 2^{64}$ the
     union sum lies in $(2^{-116}, 2^{-115})$, `depth20_budget_interval`).
  3. *Single-spine overclaim in the Lean participation model:* A target committee or
     modeled quorum-count overclaim selects a single authenticated root-to-leaf spine of $d + 1$ nodes whose
     combined public-round, `dkt26(23)` WHIR, and collision budget is **$< 2^{-130} < 2^{-128}$
     for all $d \le 64$ and $Q \le 2^{64}$** (`spineBudget_lt_130`), locating a bad extraction event or, for an authenticated roster matching enrolled keys,
     a Jorts signature for a nonparticipant (`overclaimed_spine_euf_cma_forgery`).
  4. *Explicit assumptions **[model / open]**:* Internal PCD steps use unmasked sumchecks
     (zero knowledge requires an outer `zk-Hem v2` wrapper); instantiating the `FixedPathWhirW24`
     transcript with width-24 Poseidon2 models that sponge as a random oracle; and connecting
     Rust WHIR codeword openings at adaptively chosen spine nodes to the recorded
     node-commitment query (`successful_spine_requires_node_query`) remains an explicit
     bridge obligation. Applying the model to `total_signers` also requires a refinement relating its sum of bitmap weights to the Rust count, including merges of overlapping bitmaps.

### 4.1 High-arity committee aggregation (`QSAGIVC2`)

`prove_high_arity_tree` and `verify_high_arity_tree` prove a batch of completed Jorts committees against the caller's registry root, message digest, interval and signer count. Each distinct (shard, member position) has one private leaf assignment. The proof publishes one 42-byte record per shard (u64 ID, u16 threshold, 256-bit signer union). Adjacent groups for a shard share a union. The verifier derives the single-bit leaf statements from the set positions, checks the population against the threshold and applies `IvcSubtreeStatement::merge` to contiguous, complete shards. The native checks use checked endpoints and totals. The leaf relation authenticates each position, signature and threshold against the directory at that ID. Only the Johnson profiles (wire tags 16 and 17) are accepted. The rate-half tags 18 and 19 of §2 have no projection analysis, schedule or oracle-call account in this layout: the prover returns `HighArityError::UnsupportedProfile`, and the decoder and verifier reject them.

**Constraint census.** The binary step counter gives the following disjoint costs for both children together. One width-24 permutation uses 236 native seventh-power rows. The other rows enforce ordinary rank-one constraints, including equalities and Boolean assertions. The allocation column excludes the supplied public inputs.

| Binary step operation | Seventh-power rows | Other rows | Allocated variables |
| --- | ---: | ---: | ---: |
| Public limb checks, bitmap union, threshold surplus and interval addition | 0 | 3,856 | 3,508 |
| Child relation selectors | 0 | 2 | 2 |
| Four-claim matrix reduction and output digest | 42,244 | 5,034 | 47,761 |
| Two child row/column arguments and their public bindings, excluding openings | 99,592 | 10,140 | 112,814 |
| Distinct-index sampling, permutation of memory events and bit decomposition | 17,464 | 331,086 | 307,914 |
| Fiber leaf hashes | 1,244,664 | 0 | 1,244,664 |
| Frontier authentication, sibling ordering, routing and root comparisons | 2,974,544 | 1,622,084 | 4,675,816 |
| Remaining WHIR transcript, fiber and kernel folds, mask and terminal checks | 265,736 | 1,038,690 | 1,386,720 |
| **Total** | **4,644,244** | **3,010,892** | **7,779,199** |

The binary circuit uses 19,679 permutations and 7,655,136 rows before closing. The constant, 38 public inputs and 12 closing variables bring its variable count to 7,779,250. Rows and columns fit the fixed $2^{23}$ geometry. In V2 the aggregation verifier adds **zero R1CS rows and zero witness variables**. Its transcript, commitment hashes, WHIR queries, Merkle paths, roster union and interval checks all run natively. Each application leaf uses **79,432 rows** (73,632 seventh-power and 5,800 ordinary rows) and **80,406 variables** including its constant, 31 public inputs and 12 closing variables. Its padded row and column dimensions are both $2^{17}$. The leaf still executes the Jorts hash chains, the member path and the 64-level policy directory path. Jorts signature security and binding of the existing Poseidon2 policy directory remain application assumptions.

**Commitment and folding relation [proof under the PCS hypotheses of §2.3].** Let $Z(i,j)$ be the Boolean table of assignments, with column bits low and instance bits high. The prover pads missing instances with zero. It commits the complete table before the first challenge. Both supported profiles use their 400-bit Keccak transcript and tree hash. The transcript binds the protocol, profile, fixed shape digest, external root statement, ordered roster, nonce and witness commitment. For each short algebraic message the verifier recomputes the domain-separated commitment from its canonical opening, absorbs the commitment and derives the next challenge. This specializes the commit-and-open idea to disclosed short messages. Construction 6.1 itself uses a CP-SNARK for message consistency and a SNARK for the output relation. Here the verifier checks message consistency directly. Public evaluations and signer positions are disclosed. [Chen, Symphony, Construction 6.1](https://eprint.iacr.org/2025/1905)

1. At random instance and row points $t,\tau$, the row sumcheck starts at zero for the equality-weighted residual. At row point $x$ write $a_i,b_i,c_i$ for the multilinear row evaluations of the three matrices applied to assignment $i$. The gate is $s a_i^7+(1-s)a_ib_i-c_i$, where $s$ is the public prefix selector for seventh-power rows evaluated at $x$. The row polynomial has individual degree at most nine. A zero terminal row equality factor aborts.
2. On the instance cube write $D_j(i)=a_i^j$ at Boolean indices and extend each table multilinearly. A degree-three sumcheck reduces the equality-weighted gate using $D_4D_3$ and $ab$. At its terminal point $r$ the prover opens five scalars. A fresh $\lambda$ batches $D_4(r)+\lambda D_3(r)$ into the sum of $\mathrm{eq}(r,i)D_2(i)(D_2(i)+\lambda a(i))$. A third cubic sumcheck checks $D_2(v)=\sum_i\mathrm{eq}(v,i)a(i)^2$. These two identities bind the intermediate powers also at non-Boolean challenges.
3. A fresh power-batch of the resulting five linear claims and a quadratic sumcheck give $a(u),b(u),c(u)$ at one common instance point. Since the matrix is shared, each is a matrix row evaluation against $Z(u,\cdot)$. The column batch uses powers $0,1,2$ of a fresh challenge for the matrices and powers $3$ through $34$ for the constant and **every** public input. The expected prefix is derived from the caller's context and canonical roster at $u$, with zeroes for padding. This independently binds signer position, both interval limbs, threshold and message, including when the aggregate count is unchanged.
4. The degree-two column sumcheck ends at the product of the public matrix evaluation and one private scalar $Z(u,y)$. The verifier evaluates the matrix locally. One v2 WHIR opening authenticates that scalar against the initial commitment. Changing an assignment after seeing the weights would require defeating this opening or one of the preceding polynomial identities.

**Interleaved witnesses.** A scalar codeword accommodates up to 128 assignments at $2^{24}$ coefficients. Above that size, one Merkle leaf commits the identically indexed fiber of *every* codeword, the common folded mask symbol, index, nonce, salt, arity and fiber width. Each high instance coordinate of $u$ combines two halves as $f+r(g-f)$. The verifier performs this same projection on every authenticated fiber and then applies the ordinary WHIR folds. RS encoding, projection and multilinear evaluation commute by linearity. The final WHIR polynomial and OOD evaluations are over $E$. All stripes share the one tree, sampled positions and opening. Wire decoding derives every round length and fiber width from the roster and fixed shape, rejects noncanonical field encodings and consumes the entire input.

**Round-by-round accounting [cited / model].** Condition on a fixed jointly decodable witness candidate. A false Boolean residual survives the initial multilinear test with probability at most $(17+h)/|E|$, where $h$ is the number of instance coordinates. The row, three instance-product, instance-claim reduction and column rounds have respective individual degrees $9,3,3,3,2,2$. The two intermediate batching degrees are 1 and 4. The final prefix batch has degree 34. If only the public prefix is false, track one erroneous prefix coordinate through the reduction to $u$; losing that discrepancy costs at most one additional root per coordinate. Multiply the per-candidate bounds by the initial Johnson list bound $L$.

For the interleaved case set $n=4\cdot2^{24}$, $D=2^{24}-1$ and take the raw symbol agreement threshold $A$ equal to the Stage-0 fiber threshold times its arity. The checked inequality $(2m A)^2\ge(2m+1)^2 D n$ permits DKT26 Theorem 5.12 with $m=364$. At each high coordinate, represent each remaining tuple by a basis in a finite extension of $E$. Apply the theorem to the two words $f,g-f$ there. Its exceptional set has size at most $B=\lceil(2m+1)^3 n^2/(3D)\rceil$ even when the challenge is sampled from the subfield $E$. Outside this set every nearby projected polynomial lifts to component polynomials with the same agreement positions. Expand coefficients in the basis and repeat at the preceding coordinate. At the original commitment, more than $D$ agreeing base-field positions force base-field component coefficients by interpolation. The ordinary Johnson bound applies to the joint word over the larger alphabet. This uses one joint list throughout the reduction. [Dao, Kominers and Thaler, Theorem 5.12](https://eprint.iacr.org/2026/2056)

The algebraic RBR numerator is bounded by $\max(L\max(17+h,34),B+3L)$, with $B=0$ for the scalar layout. The second term includes the simultaneous quadratic check and possible prefix discrepancy. The PCS mask line, OOD, affine folds and distinct-query rounds retain the §2.3 bounds. Apply the §1 CDHZ25 envelope to the **maximum** RBR error. The main transcript rejects on exhaustion of a 4,096-call budget, including sampler retries. Short-message commitment hashes and every queried leaf, internal node and wrapped root are counted separately. `high_arity_qrom_accounting` checks all 17 instance dimensions, the query caps and the degree and agreement inequalities. The figures are lower bounds on $-\log_2$ of the errors, rounded against the claim. [Chiesa, Di, Hu and Zheng, Theorems 6.10, 8.3 and 11.3](https://eprint.iacr.org/2025/2166)

| Signer instances | Code log | Stripes | Challenge rounds | RBR bits | QROM bits at $Q=2^{64}$ |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 21 | 1 | 90 | 265.009 | 128.663 |
| 64 | 23 | 1 | 107 | 265.374 | 129.028 |
| 256 | 24 | 2 | 115 | 264.514 | 128.168 |
| 131,072 | 24 | 1,024 | 151 | 264.514 | 128.168 |

The largest encoded Stage-0 leaf contains 65,536 base symbols, fixed by its u16 width-minus-one. With 64 symbols per source fiber, the exact format maximum is **131,072 distinct (shard, signer) pairs**. That gives 131,072 one-signer shards, or 2,048 shards with 64 signers each. All admitted geometries clear the conditional 128-bit argument budget. The largest case is a parameter calculation. Its unencoded witness cube alone requires 128 GiB. The direct prover materializes this cube, row tables and codewords. The bound assumes the framed hash oracle and WHIR knowledge/list-extraction model of §§1–2.3. The Rust implementation has no machine-checked refinement to the quantum extractor. Registry binding and application signature forgery have separate security budgets.

**Release measurements.** Each input uses a distinct one-member Jorts committee, threshold one, depth-eight policy and a shared application digest. Each trial uses the production API with a warm compiled shape, rustc 1.99.1 and a 16 GiB process-group memory cap. Times exclude signing, registry construction and serialization. Proof sizes are actual serialized lengths. Distinct sampled positions change the number of sibling digests. The binary root always occupies 639,673 B. On a dedicated 32-thread AMD EPYC-Milan host:

| Shards | V2 bytes | V2 prove (s) | V2 verify (s) | V1 prove (s) | V1 verify (s) | Prover speedup | Verifier speedup |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 350,127 | 2.700140 | 0.178875 | 216.111285 | 9.914001 | 80.04× | 55.42× |
| 4 | 376,071 | 3.960543 | 0.178208 | 620.277515 | 9.538311 | 156.61× | 53.52× |
| 16 | 477,147 | 10.933366 | 0.217484 | — | — | — | — |
| 64 | 585,707 | 39.611306 | 0.180572 | — | — | — | — |
| 256 | 761,549 | 150.703961 | 0.193241 | — | — | — | — |

On an Intel Core i9-12900 CPU under shared load, 16, 64 and 256 shards in V2 proved in **6.196961 s**, **32.558938 s** and **115.554995 s** and verified in **0.077684 s**, **0.078170 s** and **0.080647 s**, while 16 shards in V1 took **2,495.234665 s** to prove and **11.121759 s** to verify (**402.65×** and **143.17×**). Even 256 shards in V2 proved faster than two shards in V1 (`124.730 s` on the i9-12900 baseline, `216.111 s` on EPYC-Milan). The timing tests are `high_arity_batch_timings` and `high_arity_binary_timings`. Both require `--ignored --nocapture` with their individual test filter.

---

## 5. Vulkan evidence

On the RX 6750 XT, the planted-fault audit covered ten SPIR-V kernels. Five also have
standalone timings. The other five implement quintic and Canopy operations. The audit set
contains zero legacy Ext2 LDE kernels. RADV reported 32-thread subgroups, zero scratch and
zero register spills. The public and hiding proof timings are three-trial medians. The
recursive timing is one CPU/GPU pair on the earlier relation. A subsequent check with the
integrated seed stream reproduced identical CPU/GPU proof bytes and verified the recursive
root with zero CPU fallbacks. The Lean Poseidon2-12 shader theorem varies the input state
at invocation zero in a fixed environment. The hardware runs exercise a different scope.
[Measurements and reproduction commands](../../docs/PERFORMANCE.md#radeon-rx-6750-xt-proof-and-kernel-timings)

## References

- **`[ACFY25]`** G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, *WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification*, EUROCRYPT 2025 (full version IACR ePrint 2024/1586).
- **`[AHU19]`** A. Ambainis, M. Hamburg, D. Unruh, *Quantum Security Proofs Using Semi-classical Oracles*, CRYPTO 2019.
- **`[BCGM25]`** S. Bordage, A. Chiesa, Z. Guan, I. Manzur, *All Polynomial Generators Preserve Distance with Mutual Correlated Agreement*, IACR ePrint 2025/2051, 2025.
- **`[BCS16]`** E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*, TCC 2016.
- **`[CDHZ25]`** A. Chiesa, Z. Di, Z. Hu, Y. Zheng, *How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions*, [IACR ePrint 2025/2166](https://eprint.iacr.org/2025/2166), 2025.
- **`[CFW26]`** A. Chiesa, G. Fenzi, G. Weissenberg, *Zero-Knowledge IOPPs for Constrained Interleaved Codes*, IACR ePrint 2026/391, 2026.
- **`[CWYZ26]`** A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng, *Affine Combiners for Reed–Solomon Proximity Gaps*, IACR ePrint 2026/2863, 2026.
- **`[DKT26]`** Q. Dao, S. D. Kominers, J. Thaler, *Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs*, [IACR ePrint 2026/2056](https://eprint.iacr.org/2026/2056), 2026.
- **`[FPR26]`** T. Feneuil, K. Provin, M. Rivain, *Sum-Checking SmallWood: Smaller Hash-Based Zero-Knowledge Arguments*, IACR ePrint 2026/2880, 2026.
- **`[GKS23]`** L. Grassi, D. Khovratovich, M. Schofnegger, *Poseidon2: A Faster Version of the Poseidon Hash Function*, AFRICACRYPT 2023.
- **`[Hab22]`** U. Haböck, *Multivariate lookups based on logarithmic derivatives*, IACR ePrint 2022/1530, 2022.
- **`[RFC9861]`** B. Viguier, D. Wong, G. Van Assche, Q. Dang, J. Daemen, *KangarooTwelve and TurboSHAKE*, [IETF RFC 9861](https://www.rfc-editor.org/rfc/rfc9861), 2025.
- **`[SP800-185]`** NIST SP 800-185, *SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash*, 2016.
