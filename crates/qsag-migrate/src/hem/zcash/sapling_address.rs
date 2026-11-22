//! Ownership of a Sapling payment address `d || pk_d`, with the Jubjub gadgets it needs.
//!
//! # The relation
//!
//! Zcash protocol specification v2026.9.0, sections 4.2.2 (Sapling key components),
//! 5.4.1.5 (`CRH^ivk`), 5.4.5.3 (`KA^Sapling`), 5.4.9.3 (Jubjub, `repr_J`) and 5.6.3.1
//! (the raw encoding of a payment address); ZIP 32, "Sapling master key generation" and
//! "Sapling child key derivation" (hardened children only).
//!
//! ```text
//! SpendingKey:  ask = ToScalar(PRF^expand_sk([0x00])),  nsk = ToScalar(PRF^expand_sk([0x01]))
//! Zip32Seed:    I = BLAKE2b-512("ZcashIP32Sapling", seed),  sk_m = I[0..32],  c = I[32..64]
//!               (ask, nsk) as above from sk_m,  ovk = PRF^expand_sk_m([0x02])[0..32],
//!               dk = PRF^expand_sk_m([0x10])[0..32]
//!               for i in (32', coin_type', account'):
//!                 I = PRF^expand_c([0x11] || ask || nsk || ovk || dk || I2LEOSP_32(i))
//!                 ask = ToScalar(PRF^expand_I[0..32]([0x13])) + ask  (mod r_J)
//!                 nsk = ToScalar(PRF^expand_I[0..32]([0x14])) + nsk  (mod r_J)
//!                 ovk = PRF^expand_I[0..32]([0x15] || ovk)[0..32]
//!                 dk  = PRF^expand_I[0..32]([0x16] || dk)[0..32],   c = I[32..64]
//!               with ask != 0 at every level
//! ak = [ask] G^Sapling  (not the zero point)        nk = [nsk] H^Sapling
//! ivk = CRH^ivk(repr_J(ak), repr_J(nk))             (251 bits, not 0)
//! pk_d = [ivk] g_d
//! ```
//!
//! Public inputs, one per bit: the affine coordinates `u`, `v` of
//! `g_d = DiversifyHash^Sapling(d)` (255 bits each, canonical) and `repr_J(pk_d)` (256).
//! The verifier computes `g_d` from `d` natively, so the relation does not check that the
//! public point is on the curve; [`SaplingAddressStatement::public_inputs`] is `None` for
//! an address whose `d` has no diversified base or whose `pk_d` is not a point of the
//! prime-order subgroup other than the zero point (`KA^Sapling.PublicPrimeOrder`). The
//! post-quantum commitment, the migration domain and the epoch are bound through the
//! proof transcript, which absorbs the statement encoding.
//!
//! Only the external (default) incoming viewing key is covered: an address of the ZIP 32
//! internal (change) key is not provable with this statement. Internal Sapling addresses
//! are never given out, so there is nothing to claim under one.
//!
//! Values that enter a hash or an encoding as bytes are canonical there: `ask` and `nsk`
//! of a parent in the child PRF input (`I2LEOSP_256` of the residue below `r_J`), and
//! both coordinates of `ak`, `nk` and `pk_d` for `repr_J`. `ask` and `nsk` of the last
//! level only feed scalar multiplications of points of order `r_J`, where any 255-bit
//! representative of the residue gives the same point. `ak` is not the zero point: its
//! canonical `u` is constrained non-zero, and the only points of the curve with `u = 0`
//! are `(0, 1)` and the point `(0, -1)` of order two, which is not a multiple of
//! `G^Sapling`. `ivk != 0` is a non-zero check on its 251 bits. `nk` may be the zero point
//! (the specification allows `nsk = 0`).
//!
//! One condition of ZIP 32 is not in the relation: an extended key is invalid if its
//! `ivk` is zero, and for the three ancestors `m`, `m/32'`, `m/32'/coin_type'` that would
//! take two fixed-base multiplications and a BLAKE2s compression each (about 480,000 rows
//! in all). The relation checks `ask != 0` for them and `ivk != 0` for the account key
//! only. The native derivation the prover runs refuses such a seed, so no honest proof
//! depends on it, and a seed that makes the difference contains a BLAKE2s preimage of a
//! 251-bit zero string, the same kind of object the soundness below already assumes
//! nobody finds.
//!
//! # What the statement means, and against whom
//!
//! A proof shows knowledge of the spending key (or ZIP 32 seed) behind the address. It
//! proves control of an address and nothing about funds: there is nothing on chain for a
//! verifier to check, and Sapling notes cannot be migrated soundly (see the
//! [module documentation](super)). The registry binds an address once per migration
//! domain ([`SaplingAddressStatement::binding`]).
//!
//! Soundness against an adversary who computes discrete logarithms, given what:
//!
//! * **Only the address.** From `g_d` and `pk_d` the adversary gets `ivk`. A witness then
//!   needs `(ak, nk)` with `CRH^ivk(ak, nk) = ivk`, a preimage of BLAKE2s-256 truncated to
//!   251 bits (the adversary does not know the owner's `(ak, nk)`, and any other pair is
//!   as good), and after that a spending key or seed whose BLAKE2b expansions hit the
//!   discrete logarithms of that pair. Generic cost about `2^125` Grover iterations for
//!   the first step alone.
//! * **The address and the full viewing key `(ak, nk)`.** The discrete logarithms `ask`,
//!   `nsk` follow. The witness is still `sk` with `ToScalar(PRF^expand_sk([0]))= ask` and
//!   `ToScalar(PRF^expand_sk([1])) = nsk`, or a seed whose derivation ends there: a
//!   BLAKE2b preimage problem with a 504-bit target, because the relation takes no `ask`
//!   or `nsk` as a free witness. A wallet that imported bare `(ask, nsk)` without a
//!   spending key cannot use this statement, which is the price of that soundness.
//!
//! These are statements about the relation under the preimage resistance of BLAKE2s and
//! BLAKE2b against quantum adversaries, and they are this crate's, not the
//! specification's; the proof system adds the soundness of zk-Hem under the chosen regime.
//!
//! # Jubjub in the constraint system
//!
//! Jubjub is `-u^2 + v^2 = 1 + d u^2 v^2` over the 255-bit BLS12-381 scalar field, with
//! `d = -10240/10241` a non-square, so the affine addition law
//!
//! ```text
//! u3 (1 + T) = u1 v2 + v1 u2,   v3 (1 - T) = v1 v2 + u1 u2,   T = d u1 u2 v1 v2
//! ```
//!
//! (specification, appendix A.3.3.5, from Bernstein, Birkner, Joye, Lange, Peters,
//! "Twisted Edwards Curves", section 6, with `a = -1`) has no exceptional case for points
//! of the curve: Jubjub is a complete twisted Edwards curve in the sense of section
//! 5.4.9.3 (`a` a square, `d` not), so both denominators are non-zero and `u3`, `v3` are
//! unique residues. That completeness is the cited result; this file relies on it and
//! tests it on equal, opposite, zero and order-two operands. Every gadget here keeps its points on the curve (public tables, the
//! verifier's `g_d`, and sums of such), so there are no distinctness conditions, the zero
//! point `(0, 1)` is an ordinary value, and no witness the specification accepts is
//! excluded.
//!
//! Arithmetic is that of [`super::nonnative`]: a fresh 255-bit element costs 255 rows, a
//! product of two elements 63, and a congruence whose terms are products of two reduced
//! elements about 235. A congruence over wider terms (a product of three elements, or an
//! element times an unreduced product) costs far more, because its carries are wider and
//! its limb groups shorter; the formulas are arranged so that almost every congruence is
//! of the cheap kind:
//!
//! * doubling uses the curve equation, `u3 (v^2 - u^2) = 2 u v` and
//!   `v3 (2 - (v^2 - u^2)) = v^2 + u^2`, with `v^2 - u^2` reduced once: three congruences;
//! * a multiplication by `d` is the congruence `10241 x + 10240 y = 0`;
//! * the fixed-base tables store `d u v` beside `(u, v)`, so `T` for a table point is one
//!   congruence on a product of three elements, in place of two.
//!
//! The variant with fewer reductions was measured and is worse: leaving `v^2 - u^2`
//! unreduced makes a doubling 2,349 rows instead of 1,809, and reducing only
//! `u1 u2 v1 v2` (with `d` a public constant factor) makes an addition 4,055 instead of
//! 2,852.
//!
//! Rows (the tests of this file print them): curve check 1,611; doubling 1,809; addition
//! of two witness points 2,852; fixed-base multiplication of a 255-bit scalar 68,422 (26
//! windows of ten bits, a 96-byte lookup and an addition each); variable-base
//! multiplication of a 251-bit scalar 718,801 (four-bit windows over a table of the 16
//! multiples `0 g .. 15 g`: 255 doublings, 69 additions and 63 selections).
//!
//! # Size
//!
//! The relation has 976,284 rows for a spending key (2^20 padded) and 1,921,425 for a
//! 32-byte seed (2^21; 1,973,855 for a seed above 128 bytes): `[ivk] g_d` 719,000, the
//! two fixed-base multiplications 137,000, the BLAKE2s compression of `CRH^ivk` 21,000,
//! and a BLAKE2b compression of about 50,000 rows for each of the 2 (spending key) or 21
//! (seed of at most 128 bytes; 22 above) blocks of the key derivation. It contains
//! multiplication rows only. Measured on hbox (i9-12900, 22 threads), regime 4
//! (`BciksJohnsonQrom128`), release build:
//!
//! ```text
//! HEM_ZCASH statement="sapling-address SpendingKey" regime=4 rows=976284 padded_rows=2^20 vars=963499 public_inputs=766 cells=2^21 synth_s=3.23 prove_s=5.21 verify_cold_s=2.60 verify_warm_ms=140.8 proof_bytes=882773 proof_kib=862.1 peak_rss_mib=2447
//! HEM_ZCASH statement="sapling-address Zip32Seed { seed_len: 32, coin_type: 133, account: 0 }" regime=4 rows=1921425 padded_rows=2^21 vars=1893808 public_inputs=766 cells=2^22 synth_s=10.04 prove_s=17.96 verify_cold_s=10.45 verify_warm_ms=604.8 proof_bytes=924381 proof_kib=902.7 peak_rss_mib=10127
//! ```

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as protocol, ZkHemV2Proof};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape};

use super::blake2::{blake2b_256, blake2b_512_gadget, blake2s_256_block_gadget};
use super::ecc::{PointTable, monomials, select_limbs};
use super::nonnative::{Elem, Field, LIMBS, Num, enforce_limbs_differ};
use super::orchard::{COIN_TYPE_MAINNET, ZIP32_PURPOSE, ZIP32_SEED_BYTES};
use super::recovery::RecoveryError;
use super::sapling::{
    self, BASE_MODULUS_LE, Fq, JUBJUB_D, Point, SCALAR_MODULUS_LE, SaplingExtendedSpendingKey,
    ZIP32_HARDENED,
};
use crate::hem::hash::{alloc_bits, const_bits, pack_bits};

type F = Goldilocks;

const STATEMENT_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.ZCASH.SADR/1";
const PROOF_MAGIC: &[u8; 8] = b"QSHEMZS2";
const NULLIFIER_PERSONAL: &[u8; 16] = b"QSAG_ZcashSapAdN";

/// Registry tag of a Sapling payment address `d || pk_d`.
pub const LEGACY_TAG_SAPLING_ADDRESS: u8 = 19;

fn wipe(bytes: &mut [u8]) {
    qsag_asm::volatile_fill(bytes, 0);
}

// ============================================================================
// Jubjub gadgets
// ============================================================================

/// The Jubjub base field `q_J` (the BLS12-381 scalar field).
pub fn jubjub_base_field() -> Field {
    Field::new(&BASE_MODULUS_LE)
}

/// The order `r_J` of the prime-order subgroup of Jubjub (252 bits).
pub fn jubjub_scalar_field() -> Field {
    Field::new(&SCALAR_MODULUS_LE)
}

/// The canonical residue of an unreduced integer as a native field element.
fn fq_value(cs: &ConstraintSystem, f: &Field, x: &Num) -> Fq {
    Fq::from_bytes(&f.value(cs, x)).expect("canonical residue")
}

/// `-d = 10240 / 10241`: multiplying a congruence by 10241 turns a factor `d` into the
/// small integer `-10240`.
const D_NUMERATOR: i64 = 10240;
const D_DENOMINATOR: i64 = 10241;

/// An affine point of Jubjub: both coordinates as 32 limbs in `[0, 255]`, representatives
/// of their residues modulo `q_J` (not necessarily the canonical ones). Every gadget
/// assumes its input points are on the curve and returns points on the curve.
#[derive(Clone)]
pub struct Pt {
    u: Vec<Lc>,
    v: Vec<Lc>,
    /// The bits of `(u, v)` when both are bit-decomposed elements.
    bits: Option<(Vec<Lc>, Vec<Lc>)>,
}

impl Pt {
    /// A public point, from its canonical affine coordinates (little-endian).
    pub fn constant(u: &[u8; 32], v: &[u8; 32]) -> Self {
        Self::from_elems(
            &Elem::constant(u, Field::BITS),
            &Elem::constant(v, Field::BITS),
        )
    }

    /// The zero point `(0, 1)`.
    pub fn identity() -> Self {
        let mut one = [0u8; 32];
        one[0] = 1;
        Self::constant(&[0; 32], &one)
    }

    /// A point from two bit-decomposed coordinates. The caller is responsible for the
    /// curve equation ([`enforce_on_curve`], or a point the verifier supplies).
    pub fn from_elems(u: &Elem, v: &Elem) -> Self {
        Self {
            u: u.limbs.clone(),
            v: v.limbs.clone(),
            bits: Some((u.bits.clone(), v.bits.clone())),
        }
    }

    /// A point from limbs that hold exact bytes of points of the curve.
    fn from_limbs(u: Vec<Lc>, v: Vec<Lc>) -> Self {
        assert!(u.len() == LIMBS && v.len() == LIMBS);
        Self { u, v, bits: None }
    }

    fn u_num(&self) -> Num {
        Num::from_limbs(&self.u)
    }

    fn v_num(&self) -> Num {
        Num::from_limbs(&self.v)
    }

    /// The limbs `u || v`.
    fn limbs(&self) -> Vec<Lc> {
        self.u.iter().chain(&self.v).cloned().collect()
    }

    /// Both coordinates as canonical bit-decomposed elements `(u, v)`: the input of
    /// `repr_J`. The point must be the result of an addition or doubling, or come from
    /// [`Pt::from_elems`].
    pub fn canonical_coordinates(&self, cs: &mut ConstraintSystem, f: &Field) -> (Elem, Elem) {
        let (u_bits, v_bits) = self.bits.clone().expect("a bit-decomposed point");
        let u = Elem {
            bits: u_bits,
            limbs: self.u.clone(),
        };
        let v = Elem {
            bits: v_bits,
            limbs: self.v.clone(),
        };
        f.enforce_canonical(cs, &u);
        f.enforce_canonical(cs, &v);
        (u, v)
    }
}

/// `repr_J` of a point with canonical coordinates: the 255 bits of `v`, then the low bit
/// of `u` (specification section 5.4.9.3).
pub fn point_repr(u: &Elem, v: &Elem) -> Vec<Lc> {
    let mut bits = v.bits.clone();
    bits.push(u.bits[0].clone());
    bits
}

/// `-u^2 + v^2 = 1 + d u^2 v^2`, as `10241 (v^2 - u^2 - 1) + 10240 u^2 v^2 = 0` on the
/// reduced squares.
pub fn enforce_on_curve(cs: &mut ConstraintSystem, f: &Field, u: &Elem, v: &Elem) {
    let uu = Num::square(cs, &u.num());
    let uu = f.reduce(cs, &uu).num();
    let vv = Num::square(cs, &v.num());
    let vv = f.reduce(cs, &vv).num();
    let uuvv = Num::mul(cs, &uu, &vv);
    f.enforce_zero(
        cs,
        &vv.sub(&uu)
            .sub(&Num::small(1))
            .scale(D_DENOMINATOR)
            .add(&uuvv.scale(D_NUMERATOR)),
    );
}

/// The result `(u3, v3)` of an addition from `T = d u1 u2 v1 v2` and the two numerators:
/// `u3 (1 + T) = nu` and `v3 (1 - T) = nv`. For points of the curve neither `1 + T` nor
/// `1 - T` is zero, so each congruence has exactly one solution.
fn close_addition(cs: &mut ConstraintSystem, f: &Field, t: &Elem, nu: &Num, nv: &Num) -> Pt {
    let t_num = t.num();
    let t_v = fq_value(cs, f, &t_num);
    let u3_v = fq_value(cs, f, nu).mul(&Fq::ONE.add(&t_v).invert());
    let v3_v = fq_value(cs, f, nv).mul(&Fq::ONE.sub(&t_v).invert());
    let u3 = f.alloc(cs, &u3_v.to_bytes());
    let u3t = Num::mul(cs, &u3.num(), &t_num);
    f.enforce_zero(cs, &u3.num().add(&u3t).sub(nu));
    let v3 = f.alloc(cs, &v3_v.to_bytes());
    let v3t = Num::mul(cs, &v3.num(), &t_num);
    f.enforce_zero(cs, &v3.num().sub(&v3t).sub(nv));
    Pt::from_elems(&u3, &v3)
}

/// The three products every addition shares: `u1 u2`, `v1 v2` and the numerator
/// `u1 v2 + v1 u2 = (u1 + v1)(u2 + v2) - u1 u2 - v1 v2`.
fn addition_products(cs: &mut ConstraintSystem, p: &Pt, q: &Pt) -> (Num, Num, Num) {
    let (pu, pv, qu, qv) = (p.u_num(), p.v_num(), q.u_num(), q.v_num());
    let a = Num::mul(cs, &pu, &qu);
    let b = Num::mul(cs, &pv, &qv);
    let c = Num::mul(cs, &pu.add(&pv), &qu.add(&qv));
    let nu = c.sub(&a).sub(&b);
    (a, b, nu)
}

/// `p + q` by the complete addition law. Four congruences: `x = d u1 u2`, `T = x v1 v2`,
/// `u3` and `v3`.
pub fn add(cs: &mut ConstraintSystem, f: &Field, p: &Pt, q: &Pt) -> Pt {
    let (a, b, nu) = addition_products(cs, p, q);
    let x_v = JUBJUB_D.mul(&fq_value(cs, f, &a));
    let x = f.alloc(cs, &x_v.to_bytes());
    f.enforce_zero(cs, &x.num().scale(D_DENOMINATOR).add(&a.scale(D_NUMERATOR)));
    let xb = Num::mul(cs, &x.num(), &b);
    let t = f.reduce(cs, &xb);
    close_addition(cs, f, &t, &nu, &a.add(&b))
}

/// `2 p`. On the curve `v^2 - u^2 = 1 + d u^2 v^2`, so with `D = v^2 - u^2` the addition
/// law reads `u3 D = 2 u v` and `v3 (2 - D) = v^2 + u^2`; `D` and `2 - D` are the two
/// denominators of the complete law and are not zero. Three congruences.
pub fn double(cs: &mut ConstraintSystem, f: &Field, p: &Pt) -> Pt {
    let (u, v) = (p.u_num(), p.v_num());
    let uu = Num::square(cs, &u);
    let uv = Num::mul(cs, &u, &v);
    let dn = Num::mul(cs, &v.sub(&u), &v.add(&u));
    let d = f.reduce(cs, &dn);
    let d_num = d.num();
    let d_v = fq_value(cs, f, &d_num);
    let two = Fq::ONE.double();
    let u3_v = fq_value(cs, f, &uv).double().mul(&d_v.invert());
    let v3_v = d_v
        .add(&fq_value(cs, f, &uu).double())
        .mul(&two.sub(&d_v).invert());
    let u3 = f.alloc(cs, &u3_v.to_bytes());
    let u3d = Num::mul(cs, &u3.num(), &d_num);
    f.enforce_zero(cs, &u3d.sub(&uv.scale(2)));
    let v3 = f.alloc(cs, &v3_v.to_bytes());
    let v3d = Num::mul(cs, &v3.num(), &Num::small(2).sub(&d_num));
    f.enforce_zero(cs, &v3d.sub(&d_num).sub(&uu.scale(2)));
    Pt::from_elems(&u3, &v3)
}

// ----------------------------------------------------------------------------
// Fixed-base scalar multiplication
// ----------------------------------------------------------------------------

/// Window width of the fixed-base tables.
const WINDOW: usize = 10;
/// Number of windows for a 255-bit scalar.
const WINDOWS: usize = 26;
/// Bytes of a table entry: `u || v || d u v`.
const ENTRY: usize = 3 * LIMBS;

/// The window tables of a public base `B` of the prime-order subgroup: window `j` holds
/// `[w 2^(10 j)] B` for every `w`, the zero point included, as `u || v || d u v`. For a
/// scalar `k = sum_j w_j 2^(10 j)` the sum of the selected entries is `[k] B`.
pub struct FixedBase {
    windows: Vec<PointTable>,
}

impl FixedBase {
    fn new(base: &Point) -> Self {
        let mut windows = Vec::with_capacity(WINDOWS);
        let mut p = *base;
        for j in 0..WINDOWS {
            let nbits = WINDOW.min(Field::BITS - WINDOW * j);
            let mut points = Vec::with_capacity(1 << nbits);
            let mut cur = Point::IDENTITY;
            for _ in 0..1 << nbits {
                points.push(cur);
                cur = cur.add(&p);
            }
            let entries: Vec<[u8; ENTRY]> = Point::batch_to_affine(&points)
                .iter()
                .map(|(u, v)| {
                    let mut e = [0u8; ENTRY];
                    e[..LIMBS].copy_from_slice(&u.to_bytes());
                    e[LIMBS..2 * LIMBS].copy_from_slice(&v.to_bytes());
                    e[2 * LIMBS..].copy_from_slice(&JUBJUB_D.mul(u).mul(v).to_bytes());
                    e
                })
                .collect();
            windows.push(PointTable::from_bytes(&entries, nbits));
            // `cur` is `[2^nbits] p`: the base of the next window.
            p = cur;
        }
        Self { windows }
    }

    /// `[k] B` for 255 Boolean bits of `k`, little-endian. Any representative of the
    /// residue of `k` modulo `r_J` gives the same point, and `k = 0` gives the zero point.
    pub fn mul(&self, cs: &mut ConstraintSystem, f: &Field, scalar_bits: &[Lc]) -> Pt {
        assert_eq!(scalar_bits.len(), Field::BITS);
        let mut acc: Option<Pt> = None;
        for (table, bits) in self.windows.iter().zip(scalar_bits.chunks(WINDOW)) {
            let mut entry = table.lookup_bytes(cs, bits);
            let duv = entry.split_off(2 * LIMBS);
            let v = entry.split_off(LIMBS);
            let t = Pt::from_limbs(entry, v);
            acc = Some(match acc {
                None => t,
                Some(a) => {
                    // T = (u1 v1) (d u2 v2), the second factor from the table.
                    let (pa, pb, nu) = addition_products(cs, &a, &t);
                    let w = Num::mul(cs, &a.u_num(), &a.v_num());
                    let wd = Num::mul(cs, &w, &Num::from_limbs(&duv));
                    let big_t = f.reduce(cs, &wd);
                    close_addition(cs, f, &big_t, &nu, &pa.add(&pb))
                }
            });
        }
        acc.expect("at least one window")
    }
}

/// The fixed bases of the Sapling key components.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Base {
    /// `G^Sapling = FindGroupHash^J("Zcash_G_", "")`: spend authorization.
    SpendAuth,
    /// `H^Sapling = FindGroupHash^J("Zcash_H_", "")`: the proof generation key.
    ProofGeneration,
}

impl Base {
    fn point(self) -> Point {
        match self {
            Self::SpendAuth => sapling::spend_auth_point(),
            Self::ProofGeneration => sapling::proof_generation_point(),
        }
    }

    /// The window tables; kept for the life of the process with `std`.
    pub fn tables(self) -> Arc<FixedBase> {
        #[cfg(feature = "std")]
        {
            use std::sync::OnceLock;
            static TABLES: [OnceLock<Arc<FixedBase>>; 2] = [OnceLock::new(), OnceLock::new()];
            TABLES[self as usize]
                .get_or_init(|| Arc::new(FixedBase::new(&self.point())))
                .clone()
        }
        #[cfg(not(feature = "std"))]
        {
            Arc::new(FixedBase::new(&self.point()))
        }
    }
}

// ----------------------------------------------------------------------------
// Variable-base scalar multiplication
// ----------------------------------------------------------------------------

/// Window width of the variable-base multiplication.
const VAR_WINDOW: usize = 4;

/// `[k] g` for a point `g` of the curve and the Boolean bits of the integer `k`
/// (little-endian, any length): double-and-add from the top over four-bit windows and a
/// table of `0 g, 1 g, .., 15 g`. Windows may be zero and the accumulator may be the zero
/// point; the result is exact for every `k` and every `g`.
pub fn var_base_mul(cs: &mut ConstraintSystem, f: &Field, g: &Pt, k_bits: &[Lc]) -> Pt {
    assert!(!k_bits.is_empty());
    let mut table: Vec<Pt> = Vec::with_capacity(1 << VAR_WINDOW);
    table.push(Pt::identity());
    table.push(g.clone());
    for m in 2..1usize << VAR_WINDOW {
        let p = if m % 2 == 0 {
            double(cs, f, &table[m / 2])
        } else {
            add(cs, f, &table[m - 1], &table[1])
        };
        table.push(p);
    }
    let limbs: Vec<Vec<Lc>> = table.iter().map(Pt::limbs).collect();
    let options: Vec<&[Lc]> = limbs.iter().map(Vec::as_slice).collect();

    let mut acc: Option<Pt> = None;
    for chunk in k_bits.chunks(VAR_WINDOW).rev() {
        let mut bits = chunk.to_vec();
        bits.resize(VAR_WINDOW, Lc::zero());
        let monos = monomials(cs, &bits);
        let mut u = select_limbs(cs, &monos, &options);
        let v = u.split_off(LIMBS);
        let t = Pt::from_limbs(u, v);
        acc = Some(match acc {
            None => t,
            Some(mut a) => {
                for _ in 0..VAR_WINDOW {
                    a = double(cs, f, &a);
                }
                add(cs, f, &a, &t)
            }
        });
    }
    acc.expect("at least one window")
}

// ============================================================================
// Key sources
// ============================================================================

/// Where the Sapling keys of a statement come from. Public: it selects the relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SaplingKeySource {
    /// The witness is the 32-byte Sapling spending key `sk`.
    SpendingKey,
    /// The witness is a ZIP 32 seed of `seed_len` bytes and the keys are those of the
    /// extended spending key `m_Sapling / 32' / coin_type' / account'`.
    Zip32Seed {
        seed_len: u8,
        coin_type: u32,
        account: u32,
    },
}

impl SaplingKeySource {
    /// The account key of Zcash mainnet for a 32-byte seed.
    pub fn mainnet_account(account: u32) -> Self {
        Self::Zip32Seed {
            seed_len: 32,
            coin_type: COIN_TYPE_MAINNET,
            account,
        }
    }

    pub fn tag(&self) -> u8 {
        match self {
            Self::SpendingKey => 1,
            Self::Zip32Seed { .. } => 2,
        }
    }

    pub fn is_well_formed(&self) -> bool {
        match self {
            Self::Zip32Seed {
                seed_len,
                coin_type,
                account,
            } => {
                ZIP32_SEED_BYTES.contains(&usize::from(*seed_len))
                    && *coin_type < ZIP32_HARDENED
                    && *account < ZIP32_HARDENED
            }
            Self::SpendingKey => true,
        }
    }

    fn zip32_path(coin_type: u32, account: u32) -> [u32; 3] {
        [
            ZIP32_PURPOSE | ZIP32_HARDENED,
            coin_type | ZIP32_HARDENED,
            account | ZIP32_HARDENED,
        ]
    }

    /// `tag`, followed for a seed by `seed_len || coin_type(4, BE) || account(4, BE)`.
    fn encode(&self, out: &mut Vec<u8>) {
        out.push(self.tag());
        if let Self::Zip32Seed {
            seed_len,
            coin_type,
            account,
        } = self
        {
            out.push(*seed_len);
            out.extend_from_slice(&coin_type.to_be_bytes());
            out.extend_from_slice(&account.to_be_bytes());
        }
    }

    fn decode(rest: &mut &[u8]) -> Option<Self> {
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, tail) = rest.split_at_checked(n)?;
            *rest = tail;
            Some(head)
        };
        let source = match take(1)?[0] {
            1 => Self::SpendingKey,
            2 => Self::Zip32Seed {
                seed_len: take(1)?[0],
                coin_type: u32::from_be_bytes(take(4)?.try_into().ok()?),
                account: u32::from_be_bytes(take(4)?.try_into().ok()?),
            },
            _ => return None,
        };
        source.is_well_formed().then_some(source)
    }

    fn secret_bytes(&self) -> usize {
        match self {
            Self::Zip32Seed { seed_len, .. } => usize::from(*seed_len),
            Self::SpendingKey => 32,
        }
    }
}

/// The key material behind a [`SaplingKeySource`]. Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub enum SaplingKeyWitness {
    SpendingKey([u8; 32]),
    /// A ZIP 32 seed, 32 to 252 bytes.
    Zip32Seed(Vec<u8>),
}

impl SaplingKeyWitness {
    fn secret(&self) -> &[u8] {
        match self {
            Self::SpendingKey(sk) => sk,
            Self::Zip32Seed(seed) => seed,
        }
    }
}

impl Drop for SaplingKeyWitness {
    fn drop(&mut self) {
        match self {
            Self::SpendingKey(sk) => wipe(sk),
            Self::Zip32Seed(seed) => wipe(seed),
        }
    }
}

fn is_zero(bytes: &[u8; 32]) -> bool {
    bytes.iter().fold(0u8, |acc, b| acc | b) == 0
}

/// The incoming viewing key of a witness: `None` for a witness that does not fit the
/// source or that the specification rejects (`ask = 0` or `ivk = 0`, at any level of a
/// ZIP 32 derivation).
fn resolve_ivk(source: &SaplingKeySource, witness: &SaplingKeyWitness) -> Option<[u8; 32]> {
    let (mut ask, mut nsk) = match (source, witness) {
        (SaplingKeySource::SpendingKey, SaplingKeyWitness::SpendingKey(sk)) => {
            let expanded = sapling::expand_spending_key(sk);
            (expanded.ask, expanded.nsk)
        }
        (
            SaplingKeySource::Zip32Seed {
                seed_len,
                coin_type,
                account,
            },
            SaplingKeyWitness::Zip32Seed(seed),
        ) => {
            if !source.is_well_formed() || seed.len() != usize::from(*seed_len) {
                return None;
            }
            let path = SaplingKeySource::zip32_path(*coin_type, *account);
            let key = SaplingExtendedSpendingKey::derive(seed, &path)?;
            (key.ask, key.nsk)
        }
        _ => return None,
    };
    let valid = !is_zero(&ask);
    let ivk = sapling::crh_ivk(&sapling::derive_ak(&ask), &sapling::derive_nk(&nsk));
    wipe(&mut ask);
    wipe(&mut nsk);
    (valid && !is_zero(&ivk)).then_some(ivk)
}

// ============================================================================
// The relation
// ============================================================================

/// Bits of the public inputs: `u(g_d)`, `v(g_d)`, `repr_J(pk_d)`.
const PUBLIC_BITS: usize = 255 + 255 + 256;
/// Bits of `ivk`.
const IVK_BITS: usize = 251;

/// `got = want` for Boolean bit strings, 60 bits per row.
fn pin(cs: &mut ConstraintSystem, got: &[Lc], want: &[Lc]) {
    assert_eq!(got.len(), want.len());
    for (g, w) in got.chunks(60).zip(want.chunks(60)) {
        cs.enforce_equal(&pack_bits(g), &pack_bits(w));
    }
}

/// The 32-byte little-endian encoding of a canonical element.
fn bytes32(e: &Elem) -> Vec<Lc> {
    let mut bits = e.bits.clone();
    bits.resize(256, Lc::zero());
    bits
}

fn prf_expand(cs: &mut ConstraintSystem, key: &[Lc], t: &[&[Lc]]) -> Vec<Lc> {
    let mut message = key.to_vec();
    for part in t {
        message.extend_from_slice(part);
    }
    blake2b_512_gadget(cs, b"Zcash_ExpandSeed", &message)
}

/// The value is not zero, for limbs in `[0, 255]` (of a canonical element or of bits).
fn enforce_nonzero(cs: &mut ConstraintSystem, limbs: &[Lc]) {
    enforce_limbs_differ(cs, limbs, &vec![Lc::zero(); limbs.len()]);
}

/// `ask` and `nsk` of the key source as 255-bit representatives modulo `r_J`.
fn key_part(
    cs: &mut ConstraintSystem,
    fr: &Field,
    source: &SaplingKeySource,
    secret: &[u8],
) -> (Elem, Elem) {
    let secret = alloc_bits(cs, secret);
    // ToScalar(PRF^expand_key(t)) + addend, canonical where it will be encoded as bytes.
    let scalar =
        |cs: &mut ConstraintSystem, key: &[Lc], t: u8, addend: Option<&Elem>, canonical: bool| {
            let wide = prf_expand(cs, key, &[&const_bits(&[t])]);
            let mut sum = Num::from_bits(&wide);
            if let Some(parent) = addend {
                sum = sum.add(&parent.num());
            }
            let out = fr.reduce(cs, &sum);
            if canonical {
                fr.enforce_canonical(cs, &out);
            }
            out
        };
    let SaplingKeySource::Zip32Seed {
        coin_type, account, ..
    } = source
    else {
        let ask = scalar(cs, &secret, 0x00, None, false);
        let nsk = scalar(cs, &secret, 0x01, None, false);
        return (ask, nsk);
    };

    let i = blake2b_512_gadget(cs, b"ZcashIP32Sapling", &secret);
    let (sk_m, mut chain) = (i[..256].to_vec(), i[256..].to_vec());
    let mut ask = scalar(cs, &sk_m, 0x00, None, true);
    let mut nsk = scalar(cs, &sk_m, 0x01, None, true);
    let mut ovk = prf_expand(cs, &sk_m, &[&const_bits(&[0x02])])[..256].to_vec();
    let mut dk = prf_expand(cs, &sk_m, &[&const_bits(&[0x10])])[..256].to_vec();
    let path = SaplingKeySource::zip32_path(*coin_type, *account);
    for (level, index) in path.into_iter().enumerate() {
        // The parent is a valid extended key only with ask != 0.
        enforce_nonzero(cs, &ask.limbs);
        let i = prf_expand(
            cs,
            &chain,
            &[
                &const_bits(&[0x11]),
                &bytes32(&ask),
                &bytes32(&nsk),
                &ovk,
                &dk,
                &const_bits(&index.to_le_bytes()),
            ],
        );
        let i_l = &i[..256];
        let last = level + 1 == path.len();
        ask = scalar(cs, i_l, 0x13, Some(&ask), !last);
        nsk = scalar(cs, i_l, 0x14, Some(&nsk), !last);
        if !last {
            ovk = prf_expand(cs, i_l, &[&const_bits(&[0x15]), &ovk])[..256].to_vec();
            dk = prf_expand(cs, i_l, &[&const_bits(&[0x16]), &dk])[..256].to_vec();
            chain = i[256..].to_vec();
        }
    }
    (ask, nsk)
}

/// The relation with its assignment, and the number of rows before padding.
fn build(source: &SaplingKeySource, public_bits: &[bool], secret: &[u8]) -> (Shape, Vec<F>, usize) {
    assert_eq!(public_bits.len(), PUBLIC_BITS);
    assert_eq!(secret.len(), source.secret_bytes());
    let mut cs = ConstraintSystem::new();
    let public: Vec<Lc> = public_bits
        .iter()
        .map(|&b| cs.public_input(F::from_u64_reduced(u64::from(b))).into())
        .collect();
    let (fq, fr) = (jubjub_base_field(), jubjub_scalar_field());
    let cs = &mut cs;

    let (ask, nsk) = key_part(cs, &fr, source, secret);

    // ak = [ask] G, not the zero point; nk = [nsk] H.
    let ak = Base::SpendAuth.tables().mul(cs, &fq, &ask.bits);
    let (ak_u, ak_v) = ak.canonical_coordinates(cs, &fq);
    enforce_nonzero(cs, &ak_u.limbs);
    let nk = Base::ProofGeneration.tables().mul(cs, &fq, &nsk.bits);
    let (nk_u, nk_v) = nk.canonical_coordinates(cs, &fq);

    // ivk = CRH^ivk(ak*, nk*): the low 251 bits of the digest, not zero.
    let mut block = point_repr(&ak_u, &ak_v);
    block.extend(point_repr(&nk_u, &nk_v));
    let digest = blake2s_256_block_gadget(cs, b"Zcashivk", &block);
    let ivk = &digest[..IVK_BITS];
    enforce_nonzero(cs, &Elem::from_bits(ivk.to_vec()).limbs);

    // pk_d = [ivk] g_d for the g_d = DiversifyHash(d) the verifier supplies: canonical
    // and on the curve.
    let g_u = Elem::from_bits(public[..255].to_vec());
    let g_v = Elem::from_bits(public[255..510].to_vec());
    let pk_d = var_base_mul(cs, &fq, &Pt::from_elems(&g_u, &g_v), ivk);
    let (pk_u, pk_v) = pk_d.canonical_coordinates(cs, &fq);
    pin(cs, &point_repr(&pk_u, &pk_v), &public[510..]);

    let rows = cs.num_rows();
    let (shape, assignment) = core::mem::take(cs).finish_v2();
    (shape, assignment, rows)
}

fn build_shape(source: &SaplingKeySource) -> Shape {
    let public = vec![false; PUBLIC_BITS];
    let secret = vec![0u8; source.secret_bytes()];
    let (shape, mut assignment, _) = build(source, &public, &secret);
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    shape
}

/// Shapes are a pure function of the key source; with `std` the most recent ones are kept.
#[cfg(feature = "std")]
fn shape_of(source: &SaplingKeySource) -> Arc<Shape> {
    use std::sync::{Mutex, PoisonError};
    const KEEP: usize = 2;
    static CACHE: Mutex<Vec<(SaplingKeySource, Arc<Shape>)>> = Mutex::new(Vec::new());
    let find = |cache: &[(SaplingKeySource, Arc<Shape>)]| {
        cache
            .iter()
            .find(|(s, _)| s == source)
            .map(|(_, shape)| shape.clone())
    };
    if let Some(hit) = find(&CACHE.lock().unwrap_or_else(PoisonError::into_inner)) {
        return hit;
    }
    let shape = Arc::new(build_shape(source));
    let mut cache = CACHE.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(hit) = find(&cache) {
        return hit;
    }
    if cache.len() == KEEP {
        cache.remove(0);
    }
    cache.push((source.clone(), shape.clone()));
    shape
}

#[cfg(not(feature = "std"))]
fn shape_of(source: &SaplingKeySource) -> Arc<Shape> {
    Arc::new(build_shape(source))
}

fn byte_bits(bytes: &[u8], n: usize) -> impl Iterator<Item = bool> + '_ {
    (0..n).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1)
}

// ============================================================================
// The statement
// ============================================================================

/// Public statement of ownership of a Sapling payment address: the prover knows the
/// spending key or ZIP 32 seed behind the external incoming viewing key of `address`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaplingAddressStatement {
    pub key_source: SaplingKeySource,
    /// The raw Sapling payment address `d || pk_d` (specification section 5.6.3.1; the
    /// payload of a `zs` address and the Sapling receiver of a unified address).
    pub address: [u8; 43],
    /// Commitment to the post-quantum destination (`registry::pq_commitment`).
    pub pq_commitment: [u8; 32],
    /// Replay domain of the migration campaign.
    pub migration_domain: [u8; 32],
    pub epoch: u64,
}

/// The affine coordinates of a point, each 32 bytes little-endian.
type AffineBytes = ([u8; 32], [u8; 32]);

/// `g_d = DiversifyHash^Sapling(d)` in affine coordinates and `pk_d`; `None` if `d` has no
/// diversified base or `pk_d` is not in `J^(r)*`.
fn address_points(address: &[u8; 43]) -> Option<(AffineBytes, [u8; 32])> {
    let d: [u8; 11] = address[..11].try_into().ok()?;
    let pk_d: [u8; 32] = address[11..].try_into().ok()?;
    if !sapling::jubjub_is_prime_order(&pk_d) {
        return None;
    }
    let (u, v) = sapling::group_hash_point(b"Zcash_gd", &d)?.to_affine();
    Some(((u.to_bytes(), v.to_bytes()), pk_d))
}

fn address_of(
    source: &SaplingKeySource,
    witness: &SaplingKeyWitness,
    d: &[u8; 11],
) -> Option<[u8; 43]> {
    let mut ivk = resolve_ivk(source, witness)?;
    let address = sapling::payment_address(&ivk, d);
    wipe(&mut ivk);
    address
}

impl SaplingAddressStatement {
    /// The statement for the address of the witness key at diversifier `d`. `None` for a
    /// witness that does not fit the key source, a key the specification rejects, or a
    /// diversifier without a diversified base.
    pub fn derive(
        key_source: &SaplingKeySource,
        witness: &SaplingKeyWitness,
        d: &[u8; 11],
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        Some(Self {
            key_source: key_source.clone(),
            address: address_of(key_source, witness, d)?,
            pq_commitment,
            migration_domain,
            epoch,
        })
    }

    /// Whether the parameters are in range, `d` has a diversified base and `pk_d` is a
    /// point of the prime-order subgroup other than the zero point.
    pub fn is_well_formed(&self) -> bool {
        self.key_source.is_well_formed() && address_points(&self.address).is_some()
    }

    /// The registry nullifier: one value per address and domain,
    /// `BLAKE2b-256("QSAG_ZcashSapAdN", domain || address)`. It is public: an address is
    /// its own identifier.
    pub fn nullifier(&self) -> [u8; 32] {
        blake2b_256(NULLIFIER_PERSONAL, &[&self.migration_domain, &self.address])
    }

    /// `tag(29) || epoch(8, BE) || domain(32) || pq(32) || address(43) || key source`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(160);
        out.extend_from_slice(STATEMENT_TAG);
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.migration_domain);
        out.extend_from_slice(&self.pq_commitment);
        out.extend_from_slice(&self.address);
        self.key_source.encode(&mut out);
        out
    }

    /// Strict inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes.strip_prefix(STATEMENT_TAG.as_slice())?;
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, tail) = rest.split_at_checked(n)?;
            rest = tail;
            Some(head)
        };
        let epoch = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let migration_domain: [u8; 32] = take(32)?.try_into().ok()?;
        let pq_commitment: [u8; 32] = take(32)?.try_into().ok()?;
        let address: [u8; 43] = take(43)?.try_into().ok()?;
        let key_source = SaplingKeySource::decode(&mut rest)?;
        let statement = Self {
            key_source,
            address,
            pq_commitment,
            migration_domain,
            epoch,
        };
        (rest.is_empty() && statement.is_well_formed()).then_some(statement)
    }

    fn public_bits(&self) -> Option<Vec<bool>> {
        let ((gu, gv), pk_d) = address_points(&self.address)?;
        let mut out: Vec<bool> = byte_bits(&gu, 255).collect();
        out.extend(byte_bits(&gv, 255));
        out.extend(byte_bits(&pk_d, 256));
        Some(out)
    }

    /// The relation's public inputs, one per bit: the affine coordinates `u`, `v` of
    /// `DiversifyHash^Sapling(d)` (255 bits each) and `repr_J(pk_d)`. `None` for a
    /// malformed statement.
    pub fn public_inputs(&self) -> Option<Vec<F>> {
        self.key_source
            .is_well_formed()
            .then(|| self.public_bits())
            .flatten()
            .map(|bits| {
                bits.into_iter()
                    .map(|b| F::from_u64_reduced(u64::from(b)))
                    .collect()
            })
    }

    fn transcript(&self, regime: Profile) -> Vec<u8> {
        let mut out = self.to_bytes();
        out.push(regime.wire_tag());
        out
    }

    /// The binding a verified statement asks the registry to record.
    #[cfg(feature = "std")]
    pub fn binding(&self) -> crate::hem::registry::MigrationBinding {
        crate::hem::registry::MigrationBinding {
            nullifier: self.nullifier(),
            migration_domain: self.migration_domain,
            legacy_id: crate::hem::relations::credential_identifier(
                LEGACY_TAG_SAPLING_ADDRESS,
                &self.address,
            ),
            pq_commitment: self.pq_commitment,
            epoch: self.epoch,
            exposure: crate::hem::registry::KeyExposure::Hidden,
        }
    }
}

/// The public relation of a Sapling address statement; it depends on the key source only.
pub fn sapling_address_shape(statement: &SaplingAddressStatement) -> Option<Arc<Shape>> {
    statement
        .is_well_formed()
        .then(|| shape_of(&statement.key_source))
}

/// The relation of `statement` with the assignment for `witness`, after checking natively
/// that the witness owns the address. The assignment is secret. The transcript of a proof
/// over it must be [`sapling_address_transcript`].
pub fn synthesize_sapling_address(
    statement: &SaplingAddressStatement,
    witness: &SaplingKeyWitness,
) -> Result<(Shape, Vec<F>), RecoveryError> {
    let public = statement
        .key_source
        .is_well_formed()
        .then(|| statement.public_bits())
        .flatten()
        .ok_or(RecoveryError::MalformedStatement)?;
    let d: [u8; 11] = statement.address[..11].try_into().expect("11 bytes");
    if address_of(&statement.key_source, witness, &d) != Some(statement.address) {
        return Err(RecoveryError::WitnessMismatch);
    }
    let (shape, assignment, _) = build(&statement.key_source, &public, witness.secret());
    Ok((shape, assignment))
}

/// The statement bytes [`prove_sapling_address`] and [`verify_sapling_address`] hand to
/// zk-Hem.
pub fn sapling_address_transcript(
    statement: &SaplingAddressStatement,
    regime: Profile,
) -> Vec<u8> {
    statement.transcript(regime)
}

/// A Sapling address ownership proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaplingAddressProof {
    key_tag: u8,
    pub regime: Profile,
    pub proof: ZkHemV2Proof,
}

impl SaplingAddressProof {
    /// `magic(8) || key source tag || regime || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = PROOF_MAGIC.to_vec();
        out.push(self.key_tag);
        out.push(self.regime.wire_tag());
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    /// Strict decoding against the statement the proof is for.
    pub fn from_bytes(bytes: &[u8], statement: &SaplingAddressStatement) -> Option<Self> {
        let rest = bytes.strip_prefix(PROOF_MAGIC.as_slice())?;
        let (&key_tag, rest) = rest.split_first()?;
        let (&regime, rest) = rest.split_first()?;
        if key_tag != statement.key_source.tag() {
            return None;
        }
        let regime = Profile::from_wire_tag(regime)?;
        let shape = sapling_address_shape(statement)?;
        let proof = ZkHemV2Proof::from_bytes(rest, &shape)?;
        (proof.profile == regime).then_some(Self {
            key_tag,
            regime,
            proof,
        })
    }
}

/// Prove ownership of a Sapling address. `seed` must be uniform and secret.
pub fn prove_sapling_address(
    statement: &SaplingAddressStatement,
    witness: &SaplingKeyWitness,
    regime: Profile,
    seed: &[u8; 32],
) -> Result<SaplingAddressProof, RecoveryError> {
    let (shape, assignment) = synthesize_sapling_address(statement, witness)?;
    let proof = protocol::prove(
        &shape,
        assignment,
        &statement.transcript(regime),
        regime,
        seed,
    )
    .map_err(RecoveryError::Proof)?;
    Ok(SaplingAddressProof {
        key_tag: statement.key_source.tag(),
        regime,
        proof,
    })
}

/// Verify a Sapling address ownership proof under the regime the verifier requires. On
/// `true`, [`SaplingAddressStatement::binding`] is what the registry should record.
pub fn verify_sapling_address(
    statement: &SaplingAddressStatement,
    regime: Profile,
    proof: &SaplingAddressProof,
) -> bool {
    if proof.regime != regime || proof.key_tag != statement.key_source.tag() {
        return false;
    }
    let (Some(shape), Some(public_inputs)) =
        (sapling_address_shape(statement), statement.public_inputs())
    else {
        return false;
    };
    proof.proof.profile == regime
        && protocol::verify(
            &shape,
            &public_inputs,
            &statement.transcript(regime),
            regime,
            &proof.proof,
        )
}

/// Row count of the relation before padding, for reports: `(rows, variables)`.
pub fn sapling_address_relation_size(key_source: &SaplingKeySource) -> (usize, usize) {
    let public = vec![false; PUBLIC_BITS];
    let secret = vec![0u8; key_source.secret_bytes()];
    let (shape, _, rows) = build(key_source, &public, &secret);
    (rows, shape.num_vars)
}

#[cfg(test)]
mod tests {
    use super::super::recovery::{
        AddressProof, AddressStatement, AddressWitness, KeySource, KeyWitness, RecoveryProof,
        RecoveryStatement, prove_address, verify_address,
    };
    use super::super::sapling::tests::{KEY_COMPONENTS, hex};
    use super::*;
    use qsag_agg::zk_hem::relation::MASK_ROWS;
    use std::println;
    use std::string::String;

    const REGIME: Profile = Profile::TurboShakeJohnson400;
    const PQ: [u8; 32] = [0x51; 32];
    const DOMAIN: [u8; 32] = [0x44; 32];
    const EPOCH: u64 = 7;

    fn sk(i: usize) -> [u8; 32] {
        hex(KEY_COMPONENTS[i][0]).try_into().unwrap()
    }

    fn seed() -> Vec<u8> {
        (0..32).map(|i| (i * 7 + 1) as u8).collect()
    }

    /// `r_J - 1`.
    fn order_minus_one() -> [u8; 32] {
        let mut k = SCALAR_MODULUS_LE;
        k[0] -= 1;
        k
    }

    /// A dense scalar below `2^bits`.
    fn sample_scalar(i: u8, bits: usize) -> [u8; 32] {
        let wide: [u8; 64] = core::array::from_fn(|j| (j as u8).wrapping_mul(i | 1) ^ i ^ 0x5a);
        let mut k = sapling::to_scalar(&wide);
        for (j, byte) in k.iter_mut().enumerate() {
            if 8 * j >= bits {
                *byte = 0;
            } else if 8 * (j + 1) > bits {
                *byte &= 0xff >> (8 * (j + 1) - bits);
            }
        }
        k
    }

    fn g_d(i: u8) -> Point {
        (i..)
            .find_map(|j| sapling::group_hash_point(b"Zcash_gd", &[j; 11]))
            .unwrap()
    }

    fn affine_bytes(p: &Point) -> AffineBytes {
        let (u, v) = p.to_affine();
        (u.to_bytes(), v.to_bytes())
    }

    fn alloc_point(cs: &mut ConstraintSystem, f: &Field, p: &Point) -> Pt {
        let (u, v) = affine_bytes(p);
        let (eu, ev) = (f.alloc(cs, &u), f.alloc(cs, &v));
        Pt::from_elems(&eu, &ev)
    }

    /// The assigned point equals `want`, and its `repr_J` is the native encoding.
    fn assert_point(cs: &mut ConstraintSystem, f: &Field, got: &Pt, want: &Point) {
        let (u, v) = got.canonical_coordinates(cs, f);
        assert_eq!((u.value(cs), v.value(cs)), affine_bytes(want));
        let repr = crate::hem::hash::bits_to_bytes(cs, &point_repr(&u, &v));
        assert_eq!(repr, want.to_bytes());
    }

    /// The assignment satisfies the shape, and changing any one of the sampled variables
    /// from `first` on breaks a row.
    fn assert_bound(cs: ConstraintSystem, first: usize, samples: usize) {
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        assert_eq!(shape.num_sbox, 0);
        let last = z.len() - MASK_ROWS;
        let step = ((last - first) / samples).max(1) | 1;
        for idx in (first..last).step_by(step) {
            let mut bad = z.clone();
            bad[idx] += F::ONE;
            assert!(!shape.is_satisfied(&bad), "variable {idx}");
        }
    }

    /// The index of the next variable.
    fn mark(cs: &mut ConstraintSystem) -> usize {
        cs.alloc(F::ZERO).index() + 1
    }

    #[test]
    fn curve_check_accepts_exactly_the_curve() {
        let f = jubjub_base_field();
        let p = g_d(1);
        let (u, v) = affine_bytes(&p);
        let mut off = v;
        off[0] ^= 1;
        let mut one = [0u8; 32];
        one[0] = 1;
        let mut minus_one = BASE_MODULUS_LE;
        minus_one[0] -= 1;
        for (u, v, ok) in [
            (u, v, true),
            ([0; 32], one, true),
            ([0; 32], minus_one, true),
            (u, off, false),
            (v, u, false),
            ([0; 32], [0; 32], false),
        ] {
            let mut cs = ConstraintSystem::new();
            let (eu, ev) = (f.alloc(&mut cs, &u), f.alloc(&mut cs, &v));
            let rows0 = cs.num_rows();
            enforce_on_curve(&mut cs, &f, &eu, &ev);
            if ok && u != [0; 32] {
                println!("Jubjub curve check: {} rows", cs.num_rows() - rows0);
            }
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    fn addition_and_doubling_match_native() {
        let f = jubjub_base_field();
        let (p, q) = (g_d(1), sapling::spend_auth_point());
        let minus_p = Point::from_bytes(&{
            let mut b = p.to_bytes();
            b[31] ^= 0x80;
            b
        })
        .unwrap();
        let order_two = Point::from_bytes(&{
            let mut b = BASE_MODULUS_LE;
            b[0] -= 1;
            b
        })
        .unwrap();
        // Generic, equal, opposite, zero and order-two operands: one law for all.
        for (i, (a, b)) in [
            (p, q),
            (p, p),
            (p, minus_p),
            (p, Point::IDENTITY),
            (Point::IDENTITY, Point::IDENTITY),
            (order_two, p),
            (order_two, order_two),
        ]
        .into_iter()
        .enumerate()
        {
            let mut cs = ConstraintSystem::new();
            let (pa, pb) = (alloc_point(&mut cs, &f, &a), alloc_point(&mut cs, &f, &b));
            let first = mark(&mut cs);
            let rows0 = cs.num_rows();
            let sum = add(&mut cs, &f, &pa, &pb);
            let rows1 = cs.num_rows();
            let twice = double(&mut cs, &f, &pa);
            if i == 0 {
                println!(
                    "Jubjub addition: {} rows, doubling: {} rows",
                    rows1 - rows0,
                    cs.num_rows() - rows1
                );
            }
            assert_point(&mut cs, &f, &sum, &a.add(&b));
            assert_point(&mut cs, &f, &twice, &a.double());
            assert_bound(cs, first, 40);
        }
        // A wrong sum is rejected: the result of P + Q claimed for P + P.
        let mut cs = ConstraintSystem::new();
        let (pa, pb) = (alloc_point(&mut cs, &f, &p), alloc_point(&mut cs, &f, &q));
        let sum = add(&mut cs, &f, &pa, &pb);
        let (u, v) = sum.canonical_coordinates(&mut cs, &f);
        let (wu, wv) = affine_bytes(&p.double());
        let (cu, cv) = (
            Elem::constant(&wu, Field::BITS),
            Elem::constant(&wv, Field::BITS),
        );
        pin(&mut cs, &u.bits, &cu.bits);
        pin(&mut cs, &v.bits, &cv.bits);
        let (shape, z) = cs.finish();
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn fixed_base_matches_native() {
        let f = jubjub_base_field();
        let mut order = SCALAR_MODULUS_LE;
        let mut wide = [0xffu8; 32];
        wide[31] = 0x7f;
        for (i, (base, k)) in [
            (Base::SpendAuth, sample_scalar(1, 252)),
            (Base::ProofGeneration, sample_scalar(2, 252)),
            (Base::SpendAuth, [0u8; 32]),
            (Base::ProofGeneration, {
                let mut one = [0u8; 32];
                one[0] = 1;
                one
            }),
            (Base::SpendAuth, order_minus_one()),
            // Representatives above r_J: r_J itself, r_J + 5 and 2^255 - 1.
            (Base::ProofGeneration, order),
            (Base::SpendAuth, {
                order[0] += 5;
                order
            }),
            (Base::ProofGeneration, wide),
        ]
        .into_iter()
        .enumerate()
        {
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &k);
            let first = mark(&mut cs);
            let rows0 = cs.num_rows();
            let p = base.tables().mul(&mut cs, &f, &bits[..255]);
            if i == 0 {
                println!(
                    "Jubjub fixed-base multiplication: {} rows",
                    cs.num_rows() - rows0
                );
            }
            let want = base.point().mul(&k);
            assert_point(&mut cs, &f, &p, &want);
            let native = match base {
                Base::SpendAuth => sapling::derive_ak(&k),
                Base::ProofGeneration => sapling::derive_nk(&k),
            };
            assert_eq!(want.to_bytes(), native);
            assert_bound(cs, first, if i < 2 { 25 } else { 3 });
        }
    }

    #[test]
    fn variable_base_matches_native() {
        let f = jubjub_base_field();
        let g = g_d(3);
        let mut one = [0u8; 32];
        one[0] = 1;
        for (i, (k, nbits)) in [
            (sample_scalar(3, IVK_BITS), IVK_BITS),
            ([0u8; 32], IVK_BITS),
            (one, IVK_BITS),
            (order_minus_one(), 252),
            (sample_scalar(4, 13), 13),
        ]
        .into_iter()
        .enumerate()
        {
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &k);
            let base = alloc_point(&mut cs, &f, &g);
            let first = mark(&mut cs);
            let rows0 = cs.num_rows();
            let p = var_base_mul(&mut cs, &f, &base, &bits[..nbits]);
            if i == 0 {
                println!(
                    "Jubjub variable-base multiplication, {nbits} bits: {} rows",
                    cs.num_rows() - rows0
                );
            }
            assert_point(&mut cs, &f, &p, &g.mul(&k));
            assert_bound(cs, first, if i == 0 { 12 } else { 2 });
        }
    }

    fn witness(source: &SaplingKeySource) -> SaplingKeyWitness {
        match source {
            SaplingKeySource::SpendingKey => SaplingKeyWitness::SpendingKey(sk(0)),
            SaplingKeySource::Zip32Seed { seed_len, .. } => SaplingKeyWitness::Zip32Seed(
                seed()
                    .into_iter()
                    .cycle()
                    .take(usize::from(*seed_len))
                    .collect(),
            ),
        }
    }

    /// A valid diversifier at or after `[i; 11]`.
    fn diversifier(i: u8) -> [u8; 11] {
        (i..)
            .map(|j| [j; 11])
            .find(|d| sapling::diversify_hash(d).is_some())
            .unwrap()
    }

    fn statement(source: &SaplingKeySource, d: &[u8; 11]) -> SaplingAddressStatement {
        SaplingAddressStatement::derive(source, &witness(source), d, PQ, DOMAIN, EPOCH).unwrap()
    }

    fn sources() -> [SaplingKeySource; 2] {
        [
            SaplingKeySource::SpendingKey,
            SaplingKeySource::mainnet_account(0),
        ]
    }

    #[test]
    fn statement_matches_the_official_vectors() {
        // sapling_key_components.json: the default address of each spending key.
        for (i, row) in KEY_COMPONENTS.iter().enumerate() {
            let d: [u8; 11] = hex(row[7]).try_into().unwrap();
            let st = SaplingAddressStatement::derive(
                &SaplingKeySource::SpendingKey,
                &SaplingKeyWitness::SpendingKey(sk(i)),
                &d,
                PQ,
                DOMAIN,
                EPOCH,
            )
            .unwrap();
            assert_eq!(st.address[..11], d);
            assert_eq!(st.address[11..], hex(row[8])[..]);
            assert!(st.is_well_formed());
            let public = st.public_inputs().unwrap();
            assert_eq!(public.len(), PUBLIC_BITS);
            // The public point is DiversifyHash(d), and the last 256 inputs are pk_d.
            let g = Point::from_bytes(&sapling::diversify_hash(&d).unwrap()).unwrap();
            let (gu, gv) = affine_bytes(&g);
            let bits = st.public_bits().unwrap();
            assert!(bits[..255].iter().copied().eq(byte_bits(&gu, 255)));
            assert!(bits[255..510].iter().copied().eq(byte_bits(&gv, 255)));
            assert!(bits[510..].iter().copied().eq(byte_bits(&hex(row[8]), 256)));
        }
    }

    #[test]
    fn statement_matches_the_native_derivation() {
        // The seed source is the account key m/32'/133'/0' of ZIP 32.
        let source = SaplingKeySource::mainnet_account(0);
        let path = [32 | ZIP32_HARDENED, 133 | ZIP32_HARDENED, ZIP32_HARDENED];
        let fvk = SaplingExtendedSpendingKey::derive(&seed(), &path)
            .unwrap()
            .to_extended_fvk();
        let (index, d) = fvk.default_diversifier();
        let st = statement(&source, &d);
        assert_eq!(Some(st.address), fvk.address(&index));
        // Another account, coin type or seed is another key.
        for other in [
            SaplingKeySource::mainnet_account(1),
            SaplingKeySource::Zip32Seed {
                seed_len: 32,
                coin_type: 1,
                account: 0,
            },
        ] {
            assert_ne!(statement(&other, &d).address, st.address);
        }
        let longer = SaplingKeySource::Zip32Seed {
            seed_len: 64,
            coin_type: 133,
            account: 0,
        };
        assert_ne!(statement(&longer, &d).address, st.address);

        for source in sources() {
            let w = witness(&source);
            let d = diversifier(3);
            let st = statement(&source, &d);
            // An address of another key, or at another diversifier, is not this witness's.
            let other = SaplingAddressStatement {
                address: SaplingAddressStatement::derive(
                    &SaplingKeySource::SpendingKey,
                    &SaplingKeyWitness::SpendingKey(sk(5)),
                    &d,
                    PQ,
                    DOMAIN,
                    EPOCH,
                )
                .unwrap()
                .address,
                ..st.clone()
            };
            assert_eq!(
                synthesize_sapling_address(&other, &w).err(),
                Some(RecoveryError::WitnessMismatch)
            );
            // A witness of the wrong kind or length has no statement.
            let wrong = match source {
                SaplingKeySource::SpendingKey => SaplingKeyWitness::Zip32Seed(seed()),
                SaplingKeySource::Zip32Seed { .. } => SaplingKeyWitness::SpendingKey(sk(0)),
            };
            assert!(
                SaplingAddressStatement::derive(&source, &wrong, &d, PQ, DOMAIN, EPOCH).is_none()
            );
            assert_eq!(
                synthesize_sapling_address(&st, &wrong).err(),
                Some(RecoveryError::WitnessMismatch)
            );
            assert_ne!(
                st.nullifier(),
                SaplingAddressStatement {
                    migration_domain: [9; 32],
                    ..st.clone()
                }
                .nullifier()
            );
            assert_ne!(
                st.nullifier(),
                statement(&source, &diversifier(40)).nullifier()
            );
        }
        assert!(
            SaplingAddressStatement::derive(
                &SaplingKeySource::mainnet_account(0),
                &SaplingKeyWitness::Zip32Seed(vec![1; 33]),
                &diversifier(3),
                PQ,
                DOMAIN,
                EPOCH
            )
            .is_none()
        );
        // A diversifier without a diversified base has no address.
        assert!(sapling::diversify_hash(&[1; 11]).is_none());
        assert!(
            SaplingAddressStatement::derive(
                &SaplingKeySource::SpendingKey,
                &SaplingKeyWitness::SpendingKey(sk(0)),
                &[1; 11],
                PQ,
                DOMAIN,
                EPOCH
            )
            .is_none()
        );
    }

    #[test]
    fn statement_encoding_is_strict() {
        for source in sources() {
            let st = statement(&source, &diversifier(3));
            let bytes = st.to_bytes();
            assert_eq!(
                SaplingAddressStatement::from_bytes(&bytes),
                Some(st.clone())
            );
            assert!(SaplingAddressStatement::from_bytes(&bytes[..bytes.len() - 1]).is_none());
            assert!(SaplingAddressStatement::from_bytes(&bytes[1..]).is_none());
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(SaplingAddressStatement::from_bytes(&longer).is_none());
            let mut tag = bytes.clone();
            tag[28] ^= 1;
            assert!(SaplingAddressStatement::from_bytes(&tag).is_none());
            // Every field is in the encoding, and so in the proof transcript.
            let mut other_address = st.address;
            other_address[..11].copy_from_slice(&diversifier(40));
            let variants = [
                SaplingAddressStatement {
                    epoch: 8,
                    ..st.clone()
                },
                SaplingAddressStatement {
                    migration_domain: [1; 32],
                    ..st.clone()
                },
                SaplingAddressStatement {
                    pq_commitment: [1; 32],
                    ..st.clone()
                },
                SaplingAddressStatement {
                    address: other_address,
                    ..st.clone()
                },
                SaplingAddressStatement {
                    key_source: SaplingKeySource::mainnet_account(3),
                    ..st.clone()
                },
            ];
            for other in &variants {
                assert!(other.is_well_formed());
                assert_ne!(other.to_bytes(), bytes);
                assert_ne!(
                    sapling_address_transcript(other, REGIME),
                    sapling_address_transcript(&st, REGIME)
                );
                assert_eq!(
                    SaplingAddressStatement::from_bytes(&other.to_bytes()).as_ref(),
                    Some(other)
                );
            }
            assert_ne!(
                sapling_address_transcript(&st, REGIME),
                sapling_address_transcript(&st, Profile::CshakeJohnson400)
            );
        }
        let st = statement(&SaplingKeySource::SpendingKey, &diversifier(3));
        let refused = |st: &SaplingAddressStatement| {
            !st.is_well_formed()
                && SaplingAddressStatement::from_bytes(&st.to_bytes()).is_none()
                && st.public_inputs().is_none()
                && sapling_address_shape(st).is_none()
        };
        // d without a diversified base.
        let mut bad = st.clone();
        bad.address[..11].fill(1);
        assert!(refused(&bad));
        // pk_d: not a field element, not on the curve, the zero point, the point of order
        // two, a point of order 8 r_J (a group hash before the cofactor is cleared), and
        // the non-canonical encoding of the zero point.
        let mut bad = st.clone();
        bad.address[11..].fill(0xff);
        assert!(refused(&bad));
        let off_curve = (2u8..)
            .map(|i| {
                let mut b = [0u8; 32];
                b[0] = i;
                b
            })
            .find(|b| Point::from_bytes(b).is_none())
            .unwrap();
        let mut order_two = BASE_MODULUS_LE;
        order_two[0] -= 1;
        let mut zero_with_sign = sapling::JUBJUB_IDENTITY;
        zero_with_sign[31] |= 0x80;
        let full_order = (0u8..)
            .map(|i| super::super::blake2::blake2s_256(b"Zcash_gd", &[&[i]]))
            .find(|b| Point::from_bytes(b).is_some() && !sapling::jubjub_is_prime_order(b))
            .unwrap();
        for pk_d in [
            off_curve,
            sapling::JUBJUB_IDENTITY,
            order_two,
            zero_with_sign,
            full_order,
        ] {
            let mut bad = st.clone();
            bad.address[11..].copy_from_slice(&pk_d);
            assert!(refused(&bad), "{pk_d:?}");
        }
        // Unknown or out-of-range key sources. Tag 3 is a key source of the Orchard
        // statements only.
        for tag in [0u8, 3, 9] {
            let mut bad = st.to_bytes();
            *bad.last_mut().unwrap() = tag;
            assert!(SaplingAddressStatement::from_bytes(&bad).is_none());
        }
        for key_source in [
            SaplingKeySource::Zip32Seed {
                seed_len: 31,
                coin_type: 133,
                account: 0,
            },
            SaplingKeySource::Zip32Seed {
                seed_len: 253,
                coin_type: 133,
                account: 0,
            },
            SaplingKeySource::Zip32Seed {
                seed_len: 32,
                coin_type: ZIP32_HARDENED,
                account: 0,
            },
            SaplingKeySource::Zip32Seed {
                seed_len: 32,
                coin_type: 133,
                account: ZIP32_HARDENED,
            },
        ] {
            assert!(refused(&SaplingAddressStatement {
                key_source,
                ..st.clone()
            }));
        }
        // An Orchard address statement is not a Sapling one and the reverse.
        let orchard = AddressStatement {
            key_source: KeySource::SpendingKey,
            address: st.address,
            pq_commitment: PQ,
            migration_domain: DOMAIN,
            epoch: EPOCH,
        };
        assert!(SaplingAddressStatement::from_bytes(&orchard.to_bytes()).is_none());
        assert!(AddressStatement::from_bytes(&st.to_bytes()).is_none());
    }

    #[cfg(feature = "std")]
    #[test]
    fn registry_binding_identifies_the_address() {
        use super::super::recovery::LEGACY_TAG_ORCHARD_ADDRESS;
        use crate::hem::relations::credential_identifier as zcash_legacy_identifier;
        use crate::hem::registry::KeyExposure;
        let st = statement(&SaplingKeySource::SpendingKey, &diversifier(3));
        let b = st.binding();
        assert_eq!(b.nullifier, st.nullifier());
        assert_eq!(b.exposure, KeyExposure::Hidden);
        assert_eq!(
            (b.pq_commitment, b.migration_domain, b.epoch),
            (PQ, DOMAIN, EPOCH)
        );
        // One binding per address and domain, whatever the key source and epoch.
        let again = SaplingAddressStatement {
            key_source: SaplingKeySource::mainnet_account(0),
            epoch: 9,
            ..st.clone()
        }
        .binding();
        assert_eq!(
            (again.nullifier, again.legacy_id),
            (b.nullifier, b.legacy_id)
        );
        let elsewhere = SaplingAddressStatement {
            migration_domain: [1; 32],
            ..st.clone()
        }
        .binding();
        assert_ne!(elsewhere.nullifier, b.nullifier);
        assert_eq!(elsewhere.legacy_id, b.legacy_id);
        // The same 43 bytes read as an Orchard address are another credential.
        assert_ne!(
            zcash_legacy_identifier(LEGACY_TAG_ORCHARD_ADDRESS, &st.address),
            b.legacy_id
        );
        let orchard = AddressStatement {
            key_source: KeySource::SpendingKey,
            address: st.address,
            pq_commitment: PQ,
            migration_domain: DOMAIN,
            epoch: EPOCH,
        };
        assert_ne!(orchard.nullifier(), st.nullifier());
    }

    // ------------------------------------------------------------------------
    // The relation itself: up to 2^21 rows per build. These run on a build host:
    // cargo test --release -p qsag-migrate --features std --lib -- \
    //     hem::zcash::sapling_address::tests::relation --ignored --nocapture --test-threads 1
    // ------------------------------------------------------------------------

    fn flip_public(shape: &Shape, z: &[F], at: usize) -> bool {
        let mut bad = z.to_vec();
        bad[1 + at] = F::ONE - bad[1 + at];
        shape.is_satisfied(&bad)
    }

    #[test]
    #[ignore = "builds 2^21-row relations"]
    fn relation_accepts_every_key_source_and_binds_every_public_input() {
        let mut digests = Vec::new();
        for source in sources() {
            let w = witness(&source);
            let d = diversifier(3);
            let st = statement(&source, &d);
            let (shape, z) = synthesize_sapling_address(&st, &w).unwrap();
            let (rows, vars) = sapling_address_relation_size(&source);
            println!(
                "sapling address relation {source:?}: {rows} rows, 2^{} padded, {vars} variables",
                shape.log_rows
            );
            assert!(shape.is_satisfied(&z));
            assert_eq!(
                shape.num_sbox, 0,
                "the collaborative prover needs mul rows only"
            );
            assert_eq!(shape.num_public, PUBLIC_BITS);
            assert_eq!(shape.num_vars, vars);
            // u(g_d), v(g_d) and repr_J(pk_d): a flipped bit anywhere is rejected.
            for at in [0, 100, 254, 255, 400, 509, 510, 511, 700, 764, 765] {
                assert!(!flip_public(&shape, &z, at), "public bit {at}");
            }

            // The shape does not depend on the witness or the address, and it is the one
            // the verifier builds.
            assert_eq!(shape.digest(), sapling_address_shape(&st).unwrap().digest());
            let other_w = match source {
                SaplingKeySource::SpendingKey => SaplingKeyWitness::SpendingKey(sk(4)),
                SaplingKeySource::Zip32Seed { .. } => SaplingKeyWitness::Zip32Seed(vec![0xa7; 32]),
            };
            let other_d = diversifier(90);
            let other_st =
                SaplingAddressStatement::derive(&source, &other_w, &other_d, PQ, DOMAIN, EPOCH)
                    .unwrap();
            let (shape2, z2) = synthesize_sapling_address(&other_st, &other_w).unwrap();
            assert!(shape2.is_satisfied(&z2));
            assert_eq!(shape2.digest(), shape.digest());

            // A foreign key does not satisfy the statement, at this diversifier or its own.
            let public = st.public_bits().unwrap();
            let (s, z_foreign, _) = build(&source, &public, other_w.secret());
            assert!(!s.is_satisfied(&z_foreign), "foreign key");
            let mixed = SaplingAddressStatement {
                address: {
                    let mut a = other_st.address;
                    a[..11].copy_from_slice(&d);
                    a
                },
                ..st.clone()
            };
            let (s, z_mixed, _) = build(&source, &mixed.public_bits().unwrap(), w.secret());
            assert!(!s.is_satisfied(&z_mixed), "foreign pk_d");
            // One changed bit of the secret.
            let mut secret = w.secret().to_vec();
            secret[17] ^= 0x04;
            let (s, z_bit, _) = build(&source, &public, &secret);
            assert!(!s.is_satisfied(&z_bit), "changed secret");
            digests.push(shape.digest());
        }
        assert_ne!(digests[0], digests[1]);
    }

    #[test]
    #[ignore = "builds 2^21-row relations"]
    fn relation_of_a_seed_follows_the_path_and_the_seed_length() {
        let d = diversifier(3);
        let base = SaplingKeySource::mainnet_account(0);
        let st = statement(&base, &d);
        let public = st.public_bits().unwrap();
        // The right seed under another account or coin type does not satisfy the
        // statement, and those relations are other shapes.
        let mut digests = vec![sapling_address_shape(&st).unwrap().digest()];
        for other in [
            SaplingKeySource::mainnet_account(1),
            SaplingKeySource::Zip32Seed {
                seed_len: 32,
                coin_type: 1,
                account: 0,
            },
        ] {
            let (shape, z, _) = build(&other, &public, &seed());
            assert!(!shape.is_satisfied(&z), "{other:?}");
            let own = statement(&other, &d);
            let (shape, z) = synthesize_sapling_address(&own, &witness(&other)).unwrap();
            assert!(shape.is_satisfied(&z), "{other:?}");
            digests.push(shape.digest());
        }
        // Seeds of one and of two BLAKE2b blocks, and the longest.
        for seed_len in [128u8, 129, 252] {
            let source = SaplingKeySource::Zip32Seed {
                seed_len,
                coin_type: 133,
                account: 5,
            };
            let w = witness(&source);
            let st = statement(&source, &d);
            let (shape, z) = synthesize_sapling_address(&st, &w).unwrap();
            let (rows, _) = sapling_address_relation_size(&source);
            println!("sapling address relation, {seed_len}-byte seed: {rows} rows");
            assert!(shape.is_satisfied(&z), "seed of {seed_len} bytes");
            let mut secret = w.secret().to_vec();
            *secret.last_mut().unwrap() ^= 0x80;
            let (s, z, _) = build(&source, &st.public_bits().unwrap(), &secret);
            assert!(!s.is_satisfied(&z), "last seed bit, {seed_len} bytes");
            digests.push(shape.digest());
        }
        for i in 0..digests.len() {
            for j in 0..i {
                assert_ne!(digests[i], digests[j], "{i} {j}");
            }
        }
    }

    #[test]
    #[ignore = "proves 2^21-row relations"]
    fn relation_proofs_roundtrip_and_reject_tampering() {
        let source = SaplingKeySource::SpendingKey;
        let w = witness(&source);
        let d = diversifier(3);
        let st = statement(&source, &d);
        let proof = prove_sapling_address(&st, &w, REGIME, &[3; 32]).unwrap();
        let bytes = proof.to_bytes();
        let decoded = SaplingAddressProof::from_bytes(&bytes, &st).unwrap();
        assert_eq!(decoded, proof);
        assert!(verify_sapling_address(&st, REGIME, &decoded));

        // Every public field is bound, through the relation or the transcript.
        let other_key = SaplingAddressStatement::derive(
            &source,
            &SaplingKeyWitness::SpendingKey(sk(4)),
            &d,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let mut negated = st.address;
        negated[42] ^= 0x80;
        for other in [
            SaplingAddressStatement {
                epoch: 8,
                ..st.clone()
            },
            SaplingAddressStatement {
                migration_domain: [1; 32],
                ..st.clone()
            },
            SaplingAddressStatement {
                pq_commitment: [1; 32],
                ..st.clone()
            },
            SaplingAddressStatement {
                address: other_key.address,
                ..st.clone()
            },
            SaplingAddressStatement {
                address: statement(&source, &diversifier(40)).address,
                ..st.clone()
            },
            SaplingAddressStatement {
                address: negated,
                ..st.clone()
            },
            SaplingAddressStatement {
                key_source: SaplingKeySource::mainnet_account(0),
                ..st.clone()
            },
        ] {
            assert!(other.is_well_formed(), "{other:?}");
            assert!(!verify_sapling_address(&other, REGIME, &proof), "{other:?}");
        }
        // Another regime, tampered proof bytes, truncation and extension.
        assert!(!verify_sapling_address(
            &st,
            Profile::CshakeJohnson400,
            &proof
        ));
        for at in [0, 7, 8, 9, 10, 80, bytes.len() / 2, bytes.len() - 1] {
            let mut tampered = bytes.clone();
            tampered[at] ^= 1;
            assert!(
                SaplingAddressProof::from_bytes(&tampered, &st)
                    .is_none_or(|p| !verify_sapling_address(&st, REGIME, &p)),
                "byte {at}"
            );
        }
        assert!(SaplingAddressProof::from_bytes(&bytes[..bytes.len() - 1], &st).is_none());
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(SaplingAddressProof::from_bytes(&longer, &st).is_none());

        // The prover refuses a witness that does not own the address.
        assert_eq!(
            prove_sapling_address(
                &st,
                &SaplingKeyWitness::SpendingKey(sk(1)),
                REGIME,
                &[3; 32]
            )
            .err(),
            Some(RecoveryError::WitnessMismatch)
        );

        // A proof from a seed, for its own statement only.
        let seed_source = SaplingKeySource::mainnet_account(0);
        let seed_w = witness(&seed_source);
        let seed_st = statement(&seed_source, &d);
        let seed_proof = prove_sapling_address(&seed_st, &seed_w, REGIME, &[4; 32]).unwrap();
        let seed_bytes = seed_proof.to_bytes();
        assert!(verify_sapling_address(
            &seed_st,
            REGIME,
            &SaplingAddressProof::from_bytes(&seed_bytes, &seed_st).unwrap()
        ));
        assert!(!verify_sapling_address(&st, REGIME, &seed_proof));
        assert!(SaplingAddressProof::from_bytes(&seed_bytes, &st).is_none());
        assert!(SaplingAddressProof::from_bytes(&bytes, &seed_st).is_none());
        assert!(!verify_sapling_address(
            &SaplingAddressStatement {
                key_source: SaplingKeySource::mainnet_account(1),
                ..seed_st.clone()
            },
            REGIME,
            &seed_proof
        ));

        // Orchard proofs are not Sapling proofs and the reverse: an Orchard address
        // proof, and the framing of an Ironwood note proof.
        let orchard_w = AddressWitness {
            key: KeyWitness::SpendingKey(sk(0)),
            internal: false,
        };
        let orchard_st = AddressStatement::derive(
            &KeySource::SpendingKey,
            &orchard_w,
            &[0; 11],
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let orchard_proof = prove_address(&orchard_st, &orchard_w, REGIME, &[5; 32]).unwrap();
        let orchard_bytes = orchard_proof.to_bytes();
        assert!(verify_address(
            &orchard_st,
            REGIME,
            &AddressProof::from_bytes(&orchard_bytes, &orchard_st).unwrap()
        ));
        assert!(SaplingAddressProof::from_bytes(&orchard_bytes, &st).is_none());
        assert!(AddressProof::from_bytes(&bytes, &orchard_st).is_none());
        // Even under the other magic the bodies are for other relations.
        let mut relabelled = orchard_bytes.clone();
        relabelled[..8].copy_from_slice(PROOF_MAGIC);
        assert!(
            SaplingAddressProof::from_bytes(&relabelled, &st)
                .is_none_or(|p| !verify_sapling_address(&st, REGIME, &p))
        );
        let mut relabelled = bytes.clone();
        relabelled[..8].copy_from_slice(&orchard_bytes[..8]);
        assert!(
            AddressProof::from_bytes(&relabelled, &orchard_st).is_none_or(|p| !verify_address(
                &orchard_st,
                REGIME,
                &p
            ))
        );
        let note_st = RecoveryStatement {
            key_source: KeySource::SpendingKey,
            anchor: [7; 32],
            nullifier: [1; 32],
            rk: orchard_st.address[11..].try_into().unwrap(),
            value: 5,
            pq_commitment: PQ,
            migration_domain: DOMAIN,
            epoch: EPOCH,
        };
        assert!(note_st.is_well_formed());
        assert!(RecoveryProof::from_bytes(&bytes, &note_st).is_none());
        let mut note_framed = b"QSHEMZN2".to_vec();
        note_framed.extend_from_slice(&bytes[8..10]);
        note_framed.extend_from_slice(&[0x42; 64]);
        note_framed.extend_from_slice(&bytes[10..]);
        assert!(SaplingAddressProof::from_bytes(&note_framed, &st).is_none());
    }

    fn peak_rss_mib() -> Option<u64> {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
        let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
        Some(kib / 1024)
    }

    /// `cargo test --release -p qsag-migrate --features std --lib --
    /// hem::zcash::sapling_address::tests::measure --ignored --nocapture --test-threads 1`
    #[test]
    #[ignore = "measurement"]
    fn measure_sapling_address_proofs() {
        println!(
            "cpus={}",
            std::thread::available_parallelism().map_or(0, |n| n.get())
        );
        let report = |name: &str,
                      shape: &Shape,
                      rows: usize,
                      synth_s: f64,
                      prove_s: f64,
                      verify_cold_s: f64,
                      verify_warm_ms: f64,
                      proof_bytes: usize| {
            let layout = protocol::layout_of(shape).unwrap();
            println!(
                "HEM_ZCASH statement=\"{name}\" regime={} rows={rows} padded_rows=2^{} vars={} \
                 public_inputs={} cells=2^{} synth_s={synth_s:.2} prove_s={prove_s:.2} \
                 verify_cold_s={verify_cold_s:.2} verify_warm_ms={verify_warm_ms:.1} \
                 proof_bytes={proof_bytes} proof_kib={:.1} peak_rss_mib={}",
                REGIME.wire_tag(),
                shape.log_rows,
                shape.num_vars,
                shape.num_public,
                layout.log_cells,
                proof_bytes as f64 / 1024.0,
                peak_rss_mib().map_or_else(|| String::from("n/a"), |m| std::format!("{m}")),
            );
        };
        for source in sources() {
            let name = std::format!("sapling-address {source:?}");
            let w = witness(&source);
            let st = statement(&source, &diversifier(3));
            let t = std::time::Instant::now();
            let (shape, _) = synthesize_sapling_address(&st, &w).unwrap();
            let synth_s = t.elapsed().as_secs_f64();
            let (rows, _) = sapling_address_relation_size(&source);
            let t = std::time::Instant::now();
            let proof = prove_sapling_address(&st, &w, REGIME, &[3; 32]).unwrap();
            let prove_s = t.elapsed().as_secs_f64();
            let bytes = proof.to_bytes();
            let t = std::time::Instant::now();
            assert!(verify_sapling_address(&st, REGIME, &proof));
            let cold = t.elapsed().as_secs_f64();
            let t = std::time::Instant::now();
            let decoded = SaplingAddressProof::from_bytes(&bytes, &st).unwrap();
            assert!(verify_sapling_address(&st, REGIME, &decoded));
            let warm = t.elapsed().as_secs_f64() * 1e3;
            report(
                &name,
                &shape,
                rows,
                synth_s,
                prove_s,
                cold,
                warm,
                bytes.len(),
            );
        }
    }
}
