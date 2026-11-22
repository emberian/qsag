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
