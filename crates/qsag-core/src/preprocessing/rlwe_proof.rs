//! Signed-monomial OR-Sigma proofs of short Ring-LWE receiver witnesses.

use super::rlwe_poly::rlwe_barrett_rem_u32;
use super::*;

/// Number of parallel/sequential repetitions in [`RlweReceiverZkPok`] (`24 * 11 = 264` classical challenge bits /
/// `132` quantum Grover bits over pairwise-invertible signed monomials $\pm X^k$).
pub const RLWE_ZKPOK_REPS: usize = 24;
/// Bit-width of one single signed-monomial challenge `c in {0..2048}` (`deg = c & 0x3ff`, `sign = (c >> 10) & 1`),
/// matching `SignedMonomialChal.ofFinIndex` / `signedMonomial_challenge_set_pairwise_invertible` in Lean.
pub const RLWE_ZKPOK_CHAL_BITS: u32 = 11;
const RLWE_ZKPOK_CHAL_MASK: u32 = (1u32 << RLWE_ZKPOK_CHAL_BITS) - 1;
/// Joint Gaussian rejection parameters over the single signed-monomial challenge set
/// $\mathcal{C} = \{\pm X^k : 0 \le k < 1024\}$ (`2048` challenges per repetition, `100%` pairwise
/// invertible over $R_{12289}$ via $(c_1 - c_2) g(X) = 2$). Key generation conditions the two
/// $\mathrm{CBD}_1$ polynomials on total squared norm $\le 1376$ (Chernoff tail $< 2^{-178}$).
/// Because negacyclic multiplication by $\pm X^k$ is an exact $\ell_2$ and $\ell_\infty$ isometry,
/// every coordinate of the shift lies in $[-1, 1]$ and the 24-repetition response shift satisfies
/// $\|v\|_2^2 \le 24 \times 1376 = 33{,}024$.
///
/// Masks follow $\exp(-y^2 / (2 \cdot 700^2))$ on $[-3072, 3071]$. Accept $z = y + v$ only in
/// $[-3070, 3069]$, with probability $\min(1, \exp((\|y\|^2 - \|z\|^2)/980000) / M)$ where
/// $M = \exp(\lceil 980000 \ln(40) \rceil / 980000)$ (`RLWE_GAUSSIAN_LOG_M = 3_615_102`).
/// Every target response has preimages inside $[-3072, 3071]$ since $\|v\|_\infty \le 1$.
/// Exact discrete-Gaussian MGF domination over $\|v\|_2^2 \le 33{,}024, \|v\|_\infty \le 1$ bounds
/// the unclipped tail below $2^{-143}$ ($< 2^{-128}$, and $< 2^{-2592}$ per single repetition at $M = 24$);
/// conditioning on acceptance and the response-box mass ($> 0.99$) leaves statistical HVZK distance
/// and secret-dependent abort indicator bias strictly below $2^{-128}$ (`0` QROM claim).
///
/// Sampling uses uniform proposals and fixed-work, 192-bit Bernoulli rejection,
/// with no mask-indexed table access. Each exponential evaluation has absolute
/// error $< 64 / 2^{192}$. Expected acceptance is $\approx 0.9926 / 40 \approx 1 / 40.3$,
/// and all rejections restart the entire joint real-branch transcript.
///
/// Bimodal rejection (Ducas–Durmus–Lepoint–Lyubashevsky, BLISS: `z = y + b v` with a secret
/// sign `b` and acceptance `1 / (M exp(-|v|^2 / 2 sigma^2) cosh(<z, v> / sigma^2))`) would give
/// `M = exp(33_024 / 980_000) < 1.04` here, but it does not apply to this statement. The sign
/// must cancel in the verification equation, which BLISS obtains from a homogeneous relation
/// `A S = q (mod 2q)`; for `Y = a s + e` that means proving `[2a | 2 | q - 2Y] (s, e, 1) = q
/// (mod 2q)` with a third response `z_3 = y_3 + b c`. Two accepting transcripts then agree only
/// modulo `q`-multiples of the challenge difference: the extractor learns
/// `a ds + de = Y dz_3 (mod q)` for a short `dz_3` with `dz_3 = c - c' (mod 2)` that the prover
/// chooses, not for `c - c'` itself. The exact extraction this proof relies on, where
/// `c - c'` is a difference of signed monomials dividing 2, is lost, and at `q = 12289` (fully
/// split, `|dz_3|_inf` up to `q / 2`) a relaxed witness with an arbitrary short denominator
/// carries no soundness for the receiver's key. `M = 40` is the cost of exact extraction at
/// this modulus across `24` joint repetitions.
pub(super) const RLWE_ZKPOK_Z_BOUND: i16 = 3070;

/// Per-branch squared Euclidean norm cap `‖z_s‖_2^2 + ‖z_e‖_2^2 <= 1_500_000_000`
/// across the `2 * 1024 = 2048` coordinates of one `(z_s[rep], z_e[rep])` pair.
///
/// Under discrete Gaussian masks of parameter `2 * sigma^2 = 980_000` (`E[Z^2] = 489_887.2`,
/// `E[‖z_s‖_2^2 + ‖z_e‖_2^2] = 1_003_288_988`), exact MGF Chernoff concentration gives per-pair
/// tail `< 2^-138.02` (`< 2^-132.44 < 2^-128` union-bounded across all 48 branch pairs in 24
/// repetitions). Forking two accepting transcripts under distinct signed monomials extracts a
/// short Ring-SIS vector `(s_sis, e_sis)` with `‖s_sis‖_2^2 + ‖e_sis‖_2^2 <= 6_060_827_392`
/// (`‖(s_sis, e_sis)‖_2 <= 77_851`, root Hermite factor `delta_0 = 1.003206`), refuting the
/// `s = 1, e = centered(-A)` public-relation bypass (`E[‖centered(-A)‖_2^2] = 12_886_999_040`,
/// tail `< 2^-310`).
pub const RLWE_ZKPOK_PAIR_L2_SQ_BOUND: u64 = 1_500_000_000;

#[inline]
fn rlwe_pair_l2_sq(zs: &[i16; RLWE_N], ze: &[i16; RLWE_N]) -> u64 {
    let mut acc = 0u64;
    for i in 0..RLWE_N {
        let vs = i64::from(zs[i]);
        let ve = i64::from(ze[i]);
        acc += (vs * vs) as u64 + (ve * ve) as u64;
    }
    acc
}

/// Constant-time HVZK OR-Sigma proof of short Ring-LWE witness knowledge for [`RlweOtReceiverMsg`]:
/// proves knowledge of short `(s, e)` on EITHER `Y_0 = pk0` OR `Y_1 = pk0 + t_crs` under `a_crs`
/// over the 11-bit pairwise-invertible signed-monomial challenge set $\pm X^k$ (`24` repetitions, `264` classical / `132` Grover bits).
#[derive(Clone, Debug)]
