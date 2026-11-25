//! The Orchard-protocol statements: recovery of an Ironwood note (the Recovery Statement
//! of ZIP 2005) and ownership of an Orchard address.
//!
//! See the [module documentation](super) for what these statements are, which notes they
//! cover and what a verifier has to check beside the proof. This file holds the
//! relations, the statement and proof types and their wire encodings.
//!
//! # The relation of a note
//!
//! Public inputs, one per bit: the anchor (256), the nullifier (255), `rk` (256) and the
//! value (64). Witness: the key material of the chosen [`KeySource`], the scope bit, the
//! randomizer `alpha`, `g_d`, `rho`, `rseed`, the position and the authentication path.
//! With the names of ZIP 2005, "Proposed Recovery Statement":
//!
//! ```text
//! SK branch:  ak^P = [H^ask(sk)] G,  nk = H^nk(sk),  rivk_ext = H^rivk_legacy(sk)
//!             (sk is the witness, or sk = ZIP 32 m/32'/coin'/account' of the witness seed)
//! QK branch:  qk = H^qk(qsk),  rivk_ext = H^rivk_ext_qk(ak, nk),  ak^P on the curve
//! ak = Extract(ak^P)                      rk = ak^P + [alpha] G
//! rivk in { rivk_ext, H^rivk_int_rivk_ext(ak, nk) }
//! ivk = Commit^ivk_rivk(ak, nk)           (not 0, not ⊥)
//! pk_d = [ivk] g_d                        psi = H^psi_rseed(rho)
//! rcm = H^rcm_rseed(g_d*, pk_d*, v, rho, psi)
//! cm = NoteCommit_rcm(g_d*, pk_d*, v, rho, psi)   (not ⊥)
//! leaf = leaf(Extract(cm), rho), path opens leaf to the anchor in the rehashed tree
//! nf = DeriveNullifier_nk(rho, psi, cm)
//! ```
//!
//! # The relation of an address
//!
//! Public inputs: the affine coordinates of `g_d = DiversifyHash(d)` (255 + 255) and
//! `repr_P(pk_d)` (256). The relation is the key part above up to `pk_d = [ivk] g_d`.
//!
//! Both relations contain multiplication rows only.

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as protocol, ZkHemV2Error, ZkHemV2Proof};

use super::blake2::{blake2b_256, blake2b_512, blake2b_512_gadget};
use super::blake3;
use super::ecc::{
    Base, Pt, add, enforce_on_curve, point_repr, poseidon_hash2, sinsemilla_commit, var_base_mul,
};
use super::nonnative::{Elem, Field, Num};
use super::orchard::{
    self, COIN_TYPE_MAINNET, FullViewingKey, Note, NoteVersion, ZIP32_HARDENED, ZIP32_PURPOSE,
    ZIP32_SEED_BYTES,
};
use super::pallas::{Fp, Fq, Point};
use super::rehash;
use crate::hem::hash::{alloc_bits, const_bits, pack_bits};
#[cfg(feature = "std")]
use crate::hem::relations::credential_identifier;

type F = Goldilocks;

const NOTE_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.ZCASH.NOTE/1";
const ADDRESS_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.ZCASH.ADDR/1";
const NOTE_PROOF_MAGIC: &[u8; 8] = b"QSHEMZN2";
const ADDRESS_PROOF_MAGIC: &[u8; 8] = b"QSHEMZA2";
const SIGHASH_PERSONAL: &[u8; 16] = b"QSAG_ZcashRcvSig";
const SIGNING_NONCE_PERSONAL: &[u8; 16] = b"QSAG_ZcashRcvRnd";
const ADDRESS_NULLIFIER_PERSONAL: &[u8; 16] = b"QSAG_ZcashAddrNf";

/// Registry tag (`relations::credential_identifier`) of an Ironwood note, identified by
/// its nullifier. The Zcash tags are 16 to 19; `relations::Credential` uses 1 to 6.
pub const LEGACY_TAG_IRONWOOD_NOTE: u8 = 16;
/// Registry tag of an Orchard address `d || pk_d`.
pub const LEGACY_TAG_ORCHARD_ADDRESS: u8 = 17;

fn wipe(bytes: &mut [u8]) {
    qsag_asm::volatile_fill(bytes, 0);
}

// ============================================================================
// Key sources
// ============================================================================

/// Where the Orchard keys of a statement come from. Public: it selects the relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeySource {
    /// The witness is the spending key `sk` (the `SoK^sk` branch).
    SpendingKey,
    /// The witness is a ZIP 32 seed of `seed_len` bytes and `sk` is the account key
    /// `m / 32' / coin_type' / account'` (the `SoK^sk` branch behind the hardened-only
    /// derivation).
    Zip32Seed {
        seed_len: u8,
        coin_type: u32,
        account: u32,
    },
    /// The witness is the quantum spending key `qsk`, with `ak^P` and `nk` (the `SoK^qsk`
    /// branch of ZIP 2005, for FROST and hardware wallet keys).
    QuantumSpendingKey,
}

impl KeySource {
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
            Self::QuantumSpendingKey => 3,
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
            _ => true,
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
            3 => Self::QuantumSpendingKey,
            _ => return None,
        };
        source.is_well_formed().then_some(source)
    }

    fn secret_bytes(&self) -> usize {
        match self {
            Self::Zip32Seed { seed_len, .. } => usize::from(*seed_len),
            _ => 32,
        }
    }
}

/// The key material behind a [`KeySource`]. Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub enum KeyWitness {
    SpendingKey([u8; 32]),
    /// A ZIP 32 seed, 32 to 252 bytes.
    Zip32Seed(Vec<u8>),
    QuantumSpendingKey {
        qsk: [u8; 32],
        /// `repr_P(ak^P)`: the spend validating key as a point, sign bit included.
        ak: [u8; 32],
        nk: [u8; 32],
    },
}

impl Drop for KeyWitness {
    fn drop(&mut self) {
        match self {
            Self::SpendingKey(sk) => wipe(sk),
            Self::Zip32Seed(seed) => wipe(seed),
            Self::QuantumSpendingKey { qsk, nk, .. } => {
                wipe(qsk);
                wipe(nk);
            }
        }
    }
}

/// The keys a witness resolves to.
struct Keys {
    ak_point: Point,
    fvk: FullViewingKey,
    /// `H^ask(sk)` in the `SoK^sk` branch: the discrete logarithm of `ak^P`.
    ask: Option<Fq>,
}

fn resolve_keys(source: &KeySource, witness: &KeyWitness) -> Option<Keys> {
    let from_sk = |sk: &[u8; 32]| {
        let ask = orchard::h_ask(sk);
        let ak_point = orchard::spend_auth_base().mul(&ask);
        (!ask.is_zero()).then(|| Keys {
            fvk: FullViewingKey {
                ak: ak_point.extract(),
                nk: orchard::h_nk(sk),
                rivk: orchard::h_rivk(sk),
            },
            ak_point,
            ask: Some(ask),
        })
    };
    match (source, witness) {
        (KeySource::SpendingKey, KeyWitness::SpendingKey(sk)) => from_sk(sk),
        (
            KeySource::Zip32Seed {
                seed_len,
                coin_type,
                account,
            },
            KeyWitness::Zip32Seed(seed),
        ) => {
            if !source.is_well_formed() || seed.len() != usize::from(*seed_len) {
                return None;
            }
            let mut sk =
                orchard::zip32_spending_key(seed, &KeySource::zip32_path(*coin_type, *account))?;
            let keys = from_sk(&sk);
            wipe(&mut sk);
            keys
        }
        (KeySource::QuantumSpendingKey, KeyWitness::QuantumSpendingKey { qsk, ak, nk }) => {
            let ak_point = Point::from_bytes_nonidentity(ak)?;
            let nk = Fp::from_bytes(nk)?;
            let ak = ak_point.extract();
            Some(Keys {
                ak_point,
                fvk: FullViewingKey {
                    ak,
                    nk,
                    rivk: orchard::h_rivk_ext(&orchard::h_qk(qsk), &ak, &nk),
                },
                ask: None,
            })
        }
        _ => None,
    }
}

// ============================================================================
// Relation inputs
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
enum Relation {
    Note(KeySource),
    Address(KeySource),
}

impl Relation {
    fn source(&self) -> &KeySource {
        match self {
            Self::Note(s) | Self::Address(s) => s,
        }
    }

    fn public_bits(&self) -> usize {
        match self {
            Self::Note(_) => 256 + 255 + 256 + 64,
            Self::Address(_) => 255 + 255 + 256,
        }
    }
}

/// The affine coordinates of a point, each 32 bytes little-endian.
type AffineBytes = ([u8; 32], [u8; 32]);

/// Every witness value of a relation. Erased on drop.
#[derive(Clone)]
struct Inputs {
    /// `sk`, the seed or `qsk`.
    secret: Vec<u8>,
    /// Affine `ak^P` and `nk` (QK branch only).
    ak: AffineBytes,
    nk: [u8; 32],
    internal: bool,
    alpha: [u8; 32],
    g_d: AffineBytes,
    rho: [u8; 32],
    rseed: [u8; 32],
    position: u32,
    path: [[u8; 32]; rehash::DEPTH],
}

impl Inputs {
    fn placeholder(relation: &Relation) -> Self {
        Self {
            secret: vec![0; relation.source().secret_bytes()],
            ak: ([0; 32], [0; 32]),
            nk: [0; 32],
            internal: false,
            alpha: [0; 32],
            g_d: ([0; 32], [0; 32]),
            rho: [0; 32],
            rseed: [0; 32],
            position: 0,
            path: [[0; 32]; rehash::DEPTH],
        }
    }

    fn keys(witness: &KeyWitness) -> (Vec<u8>, AffineBytes, [u8; 32]) {
        match witness {
            KeyWitness::SpendingKey(sk) => (sk.to_vec(), ([0; 32], [0; 32]), [0; 32]),
            KeyWitness::Zip32Seed(seed) => (seed.clone(), ([0; 32], [0; 32]), [0; 32]),
            KeyWitness::QuantumSpendingKey { qsk, ak, nk } => {
                let ak = Point::from_bytes(ak)
                    .and_then(|p| p.to_affine())
                    .map_or(([0; 32], [0; 32]), |(x, y)| (x.to_bytes(), y.to_bytes()));
                (qsk.to_vec(), ak, *nk)
            }
        }
    }
}

impl Drop for Inputs {
    fn drop(&mut self) {
        wipe(&mut self.secret);
        wipe(&mut self.nk);
        wipe(&mut self.alpha);
        wipe(&mut self.rseed);
    }
}

fn affine_bytes(p: &Point) -> Option<AffineBytes> {
    p.to_affine().map(|(x, y)| (x.to_bytes(), y.to_bytes()))
}

// ============================================================================
// Gadget helpers
// ============================================================================

/// `got = want` for Boolean bit strings, 60 bits per row.
fn pin(cs: &mut ConstraintSystem, got: &[Lc], want: &[Lc]) {
    assert_eq!(got.len(), want.len());
    for (g, w) in got.chunks(60).zip(want.chunks(60)) {
        cs.enforce_equal(&pack_bits(g), &pack_bits(w));
    }
}

/// The 32-byte little-endian encoding of a 255-bit element.
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

/// `ToScalar`: a 255-bit element congruent to the 512-bit integer modulo `q`.
fn to_scalar(cs: &mut ConstraintSystem, fq: &Field, wide: &[Lc], canonical: bool) -> Elem {
    let out = fq.reduce(cs, &Num::from_bits(wide));
    if canonical {
        fq.enforce_canonical(cs, &out);
    }
    out
}

/// `ToBase`: the canonical residue of the 512-bit integer modulo `p`.
fn to_base(cs: &mut ConstraintSystem, fp: &Field, wide: &[Lc]) -> Elem {
    fp.reduce_canonical(cs, &Num::from_bits(wide))
}

fn elem_of(point: &Pt) -> Elem {
    Elem {
        bits: point.x_bits.clone().expect("a witness coordinate"),
        limbs: point.x.clone(),
    }
}

/// The keys of the relation: `ak^P`, `ak`, `nk` (canonical) and `rivk_ext` (canonical).
fn key_part(
    cs: &mut ConstraintSystem,
    fp: &Field,
    fq: &Field,
    source: &KeySource,
    inputs: &Inputs,
) -> (Pt, Elem, Elem, Elem) {
    let secret = alloc_bits(cs, &inputs.secret);
    if matches!(source, KeySource::QuantumSpendingKey) {
        let qk = blake3::derive_key_32_gadget(cs, blake3::QK_CONTEXT, &secret);
        let ax = fp.alloc(cs, &inputs.ak.0);
        fp.enforce_canonical(cs, &ax);
        let ay = fp.alloc(cs, &inputs.ak.1);
        enforce_on_curve(cs, fp, &ax, &ay);
        let nk = fp.alloc(cs, &inputs.nk);
        fp.enforce_canonical(cs, &nk);
        let wide = prf_expand(
            cs,
            &qk,
            &[&const_bits(&[0x0d]), &bytes32(&ax), &bytes32(&nk)],
        );
        let rivk_ext = to_scalar(cs, fq, &wide, true);
        return (Pt::from_elems(&ax, true, &ay), ax, nk, rivk_ext);
    }
    let sk = match source {
        KeySource::Zip32Seed {
            coin_type, account, ..
        } => {
            let mut i = blake2b_512_gadget(cs, b"ZcashIP32Orchard", &secret);
            for index in KeySource::zip32_path(*coin_type, *account) {
                i = prf_expand(
                    cs,
                    &i[256..],
                    &[
                        &const_bits(&[0x81]),
                        &i[..256],
                        &const_bits(&index.to_le_bytes()),
                    ],
                );
            }
            i[..256].to_vec()
        }
        _ => secret,
    };
    let wide = prf_expand(cs, &sk, &[&const_bits(&[0x06])]);
    let ask = to_scalar(cs, fq, &wide, false);
    let ak_point = Base::SpendAuth.tables().mul(cs, fp, &ask.bits, true);
    let ak = elem_of(&ak_point);
    let wide = prf_expand(cs, &sk, &[&const_bits(&[0x07])]);
    let nk = to_base(cs, fp, &wide);
    let wide = prf_expand(cs, &sk, &[&const_bits(&[0x08])]);
    let rivk_ext = to_scalar(cs, fq, &wide, true);
    (ak_point, ak, nk, rivk_ext)
}

/// `ivk = Commit^ivk_rivk(ak, nk)` with `rivk` either `rivk_ext` or its internal
/// derivation, chosen by a witness bit. Returns the 255 bits of `ivk`.
fn ivk_part(
    cs: &mut ConstraintSystem,
    fp: &Field,
    fq: &Field,
    inputs: &Inputs,
    ak: &Elem,
    nk: &Elem,
    rivk_ext: &Elem,
) -> Vec<Lc> {
    let wide = prf_expand(
        cs,
        &bytes32(rivk_ext),
        &[&const_bits(&[0x83]), &bytes32(ak), &bytes32(nk)],
    );
    let rivk_int = to_scalar(cs, fq, &wide, false);
    let internal: Lc = cs
        .alloc(F::from_u64_reduced(u64::from(inputs.internal)))
        .into();
    cs.enforce_boolean(&internal);
    let rivk: Vec<Lc> = rivk_ext
        .bits
        .iter()
        .zip(&rivk_int.bits)
        .map(|(ext, int)| cs.select(&internal, int, ext))
        .collect();
    let message: Vec<Lc> = ak.bits.iter().chain(&nk.bits).cloned().collect();
    let ivk = sinsemilla_commit(
        cs,
        fp,
        &orchard::commit_ivk_domain().q(),
        Base::CommitIvkR,
        &message,
        &rivk,
    );
    // No point of Pallas has x = 0, so ivk is not zero.
    ivk.x_bits.expect("a witness coordinate")
}

/// The relation with its assignment, and the number of rows before padding.
fn build(relation: &Relation, public_bits: &[bool], inputs: &Inputs) -> (Shape, Vec<F>, usize) {
    assert_eq!(public_bits.len(), relation.public_bits());
    assert_eq!(inputs.secret.len(), relation.source().secret_bytes());
    let mut cs = ConstraintSystem::new();
    let public: Vec<Lc> = public_bits
        .iter()
        .map(|&b| cs.public_input(F::from_u64_reduced(u64::from(b))).into())
        .collect();
    let (fp, fq) = (Field::pallas_base(), Field::pallas_scalar());
    let cs = &mut cs;

    let (ak_point, ak, nk, rivk_ext) = key_part(cs, &fp, &fq, relation.source(), inputs);
    let ivk = ivk_part(cs, &fp, &fq, inputs, &ak, &nk, &rivk_ext);

    match relation {
        Relation::Address(_) => {
            // The verifier supplies g_d = DiversifyHash(d): canonical and on the curve.
            let gx = Elem::from_bits(public[..255].to_vec());
            let gy = Elem::from_bits(public[255..510].to_vec());
            let g_d = Pt::from_elems(&gx, true, &gy);
            let mut pk_d = var_base_mul(cs, &fp, &fq, &g_d, &ivk, true);
            let (px, py) = pk_d.canonical_coordinates(cs, &fp);
            pin(cs, &point_repr(&px, &py), &public[510..]);
        }
        Relation::Note(_) => {
            let (anchor, rest) = public.split_at(256);
            let (nullifier, rest) = rest.split_at(255);
            let (rk, value) = rest.split_at(256);

            // rk = ak^P + [alpha] G.
            let alpha = alloc_bits(cs, &inputs.alpha);
            let alpha_g = Base::SpendAuth.tables().mul(cs, &fp, &alpha[..255], true);
            cs.enforce_zero(alpha[255].clone());
            let mut rk_point = add(cs, &fp, &ak_point, &alpha_g, true, true);
            let (rx, ry) = rk_point.canonical_coordinates(cs, &fp);
            pin(cs, &point_repr(&rx, &ry), rk);

            // The address: g_d on the curve and pk_d = [ivk] g_d.
            let gx = fp.alloc(cs, &inputs.g_d.0);
            fp.enforce_canonical(cs, &gx);
            let gy = fp.alloc(cs, &inputs.g_d.1);
            fp.enforce_canonical(cs, &gy);
            enforce_on_curve(cs, &fp, &gx, &gy);
            let g_d = Pt::from_elems(&gx, true, &gy);
            let mut pk_d = var_base_mul(cs, &fp, &fq, &g_d, &ivk, true);
            let (px, py) = pk_d.canonical_coordinates(cs, &fp);
            let g_d_repr = point_repr(&gx, &gy);
            let pk_d_repr = point_repr(&px, &py);

            // The note: rho, psi, rcm, cm.
            let rho = fp.alloc(cs, &inputs.rho);
            fp.enforce_canonical(cs, &rho);
            let rho_bytes = bytes32(&rho);
            let rseed = alloc_bits(cs, &inputs.rseed);
            let wide = prf_expand(cs, &rseed, &[&const_bits(&[0x09]), &rho_bytes]);
            let psi = to_base(cs, &fp, &wide);
            let wide = prf_expand(
                cs,
                &rseed,
                &[
                    &const_bits(&[0x0b]),
                    &g_d_repr,
                    &pk_d_repr,
                    value,
                    &rho_bytes,
                    &bytes32(&psi),
                ],
            );
            let rcm = to_scalar(cs, &fq, &wide, false);
            let message: Vec<Lc> = g_d_repr
                .iter()
                .chain(&pk_d_repr)
                .chain(value)
                .chain(&rho.bits)
                .chain(&psi.bits)
                .cloned()
                .collect();
            let cm = sinsemilla_commit(
                cs,
                &fp,
                &orchard::note_commit_domain().q(),
                Base::NoteCommitR,
                &message,
                &rcm.bits,
            );
            let cmx = elem_of(&cm);

            // The path in the rehashed tree.
            let position = alloc_bits(cs, &inputs.position.to_le_bytes());
            let path: Vec<Vec<Lc>> = inputs.path.iter().map(|s| alloc_bits(cs, s)).collect();
            let leaf = rehash::leaf_hash_gadget(cs, &bytes32(&cmx), &rho_bytes);
            let root = rehash::root_gadget(cs, &leaf, &position, &path);
            pin(cs, &root, anchor);

            // nf = Extract([(Poseidon(nk, rho) + psi) mod p] K + cm).
            let prf = poseidon_hash2(cs, &fp, &nk.num(), &rho.num());
            let scalar = fp.reduce_canonical(cs, &prf.num().add(&psi.num()));
            let k_point = Base::Nullifier.tables().mul(cs, &fp, &scalar.bits, true);
            let nf = add(cs, &fp, &cm, &k_point, true, true);
            pin(cs, &nf.x_bits.expect("a witness coordinate"), nullifier);
        }
    }

    let rows = cs.num_rows();
    let (shape, assignment) = core::mem::take(cs).finish_v2();
    (shape, assignment, rows)
}

fn build_shape(relation: &Relation) -> Shape {
    let public = vec![false; relation.public_bits()];
    let (shape, mut assignment, _) = build(relation, &public, &Inputs::placeholder(relation));
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    shape
}

/// Shapes are a pure function of the relation; with `std` the most recent ones are kept.
#[cfg(feature = "std")]
fn shape_of(relation: &Relation) -> Arc<Shape> {
    use std::sync::{Mutex, PoisonError};
    const KEEP: usize = 2;
    static CACHE: Mutex<Vec<(Relation, Arc<Shape>)>> = Mutex::new(Vec::new());
    let find = |cache: &[(Relation, Arc<Shape>)]| {
        cache
            .iter()
            .find(|(r, _)| r == relation)
            .map(|(_, shape)| shape.clone())
    };
    if let Some(hit) = find(&CACHE.lock().unwrap_or_else(PoisonError::into_inner)) {
        return hit;
    }
    let shape = Arc::new(build_shape(relation));
    let mut cache = CACHE.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(hit) = find(&cache) {
        return hit;
    }
    if cache.len() == KEEP {
        cache.remove(0);
    }
    cache.push((relation.clone(), shape.clone()));
    shape
}

#[cfg(not(feature = "std"))]
fn shape_of(relation: &Relation) -> Arc<Shape> {
    Arc::new(build_shape(relation))
}

fn byte_bits(bytes: &[u8], n: usize) -> impl Iterator<Item = bool> + '_ {
    (0..n).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1)
}

fn to_field(bits: Vec<bool>) -> Vec<F> {
    bits.into_iter()
        .map(|b| F::from_u64_reduced(u64::from(b)))
        .collect()
}

// ============================================================================
// Errors
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecoveryError {
    /// The statement's parameters or encodings are outside the supported ranges.
    MalformedStatement,
    /// The witness does not produce the statement.
    WitnessMismatch,
    /// The key source has no spend authorizing key in the witness: the caller must supply
    /// the spend authorization signature.
    SignatureRequired,
    /// The supplied spend authorization signature does not verify under `rk`.
    BadSignature,
    Proof(ZkHemV2Error),
}

// ============================================================================
// Note recovery
// ============================================================================

/// The secret inputs of a note recovery.
#[derive(Clone)]
pub struct RecoveryWitness {
    pub key: KeyWitness,
    /// Whether the note was sent to the internal (change) incoming viewing key.
    pub internal: bool,
    /// The spend authorization randomizer, a canonical nonzero scalar. Uniform and
    /// secret.
    pub alpha: [u8; 32],
    /// The note. Its version must be [`NoteVersion::V3`].
    pub note: Note,
    /// Position of the note in the Ironwood note commitment tree.
    pub position: u32,
    /// Authentication path in the rehashed tree ([`rehash`]), from the leaf upward.
    pub path: [[u8; 32]; rehash::DEPTH],
}

impl Drop for RecoveryWitness {
    fn drop(&mut self) {
        wipe(&mut self.alpha);
        wipe(&mut self.note.rseed);
    }
}

/// What a witness determines.
struct NoteEvaluation {
    anchor: [u8; 32],
    nullifier: [u8; 32],
    rk: [u8; 32],
    value: u64,
    inputs: Inputs,
    /// `H^ask(sk) + alpha`, the signing key of `rk`, in the `SoK^sk` branch.
    signing_key: Option<Fq>,
}

fn evaluate_note(source: &KeySource, w: &RecoveryWitness) -> Option<NoteEvaluation> {
    if w.note.version != NoteVersion::V3 {
        return None;
    }
    let keys = resolve_keys(source, &w.key)?;
    let scope = if w.internal {
        orchard::Scope::Internal
    } else {
        orchard::Scope::External
    };
    let ivk = qsag_core::wipe::SecretBuffer(keys.fvk.ivk(scope)?);
    let d: [u8; 11] = w.note.recipient[..11].try_into().ok()?;
    let g_d = orchard::diversify_hash(&d);
    if g_d.mul(&Fq::from_base(*ivk)).to_bytes() != w.note.pk_d() {
        return None;
    }
    let cm = w.note.commitment()?;
    let cmx = cm.extract();
    let leaf = rehash::leaf_hash(&cmx.to_bytes(), &w.note.rho.to_bytes());
    let anchor = rehash::root_from_path(&leaf, w.position, &w.path);
    let nullifier = orchard::derive_nullifier(&keys.fvk.nk, &w.note.rho, &w.note.psi(), &cm);
    // The relation computes `[alpha] G` and `ak^P + [alpha] G` in affine coordinates.
    let alpha = Fq::from_bytes(&w.alpha).filter(|a| !a.is_zero())?;
    let rk = keys.ak_point.add(&orchard::spend_auth_base().mul(&alpha));
    if rk.is_identity() {
        return None;
    }
    let (secret, ak, nk) = Inputs::keys(&w.key);
    Some(NoteEvaluation {
        anchor,
        nullifier: nullifier.to_bytes(),
        rk: rk.to_bytes(),
        value: w.note.value,
        inputs: Inputs {
            secret,
            ak,
            nk,
            internal: w.internal,
            alpha: w.alpha,
            g_d: affine_bytes(&g_d)?,
            rho: w.note.rho.to_bytes(),
            rseed: w.note.rseed,
            position: w.position,
            path: w.path,
        },
        signing_key: keys.ask.map(|ask| ask + alpha),
    })
}

/// Public statement of the recovery of one Ironwood note.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveryStatement {
    pub key_source: KeySource,
    /// Root of the rehashed Ironwood note commitment tree ([`rehash`]).
    pub anchor: [u8; 32],
    /// The Orchard-protocol nullifier of the note, as the chain would see it in a spend.
    pub nullifier: [u8; 32],
    /// The randomized spend validating key `repr_P(ak^P + [alpha] G)`.
    pub rk: [u8; 32],
    /// The value of the note in zatoshi.
    pub value: u64,
    /// Commitment to the post-quantum destination (`registry::pq_commitment`).
    pub pq_commitment: [u8; 32],
    /// Replay domain of the migration campaign.
    pub migration_domain: [u8; 32],
    pub epoch: u64,
}

impl RecoveryStatement {
    /// The statement a holder derives from its witness. `None` when the witness is
    /// inconsistent: a key that does not fit `key_source`, a note that is not a version 3
    /// note, a note that was not sent to an address of the key, `alpha` not canonical.
    pub fn derive(
        key_source: &KeySource,
        witness: &RecoveryWitness,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        let e = evaluate_note(key_source, witness)?;
        Some(Self {
            key_source: key_source.clone(),
            anchor: e.anchor,
            nullifier: e.nullifier,
            rk: e.rk,
            value: e.value,
            pq_commitment,
            migration_domain,
            epoch,
        })
    }

    /// Whether the parameters are in range and the encodings canonical: the nullifier a
    /// base field element, `rk` a non-identity point.
    pub fn is_well_formed(&self) -> bool {
        self.key_source.is_well_formed()
            && Fp::from_bytes(&self.nullifier).is_some()
            && Point::from_bytes_nonidentity(&self.rk).is_some()
    }

    /// Canonical encoding; also the bytes the proof transcript absorbs and the spend
    /// authorization signature signs (through [`Self::sighash`]).
    ///
    /// `tag(29) || epoch(8, BE) || domain(32) || pq(32) || anchor(32) || nullifier(32) ||
    /// rk(32) || value(8, BE) || key source`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(220);
        out.extend_from_slice(NOTE_TAG);
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.migration_domain);
        out.extend_from_slice(&self.pq_commitment);
        out.extend_from_slice(&self.anchor);
        out.extend_from_slice(&self.nullifier);
        out.extend_from_slice(&self.rk);
        out.extend_from_slice(&self.value.to_be_bytes());
        self.key_source.encode(&mut out);
        out
    }

    /// Strict inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes.strip_prefix(NOTE_TAG.as_slice())?;
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, tail) = rest.split_at_checked(n)?;
            rest = tail;
            Some(head)
        };
        let epoch = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let migration_domain: [u8; 32] = take(32)?.try_into().ok()?;
        let pq_commitment: [u8; 32] = take(32)?.try_into().ok()?;
        let anchor: [u8; 32] = take(32)?.try_into().ok()?;
        let nullifier: [u8; 32] = take(32)?.try_into().ok()?;
        let rk: [u8; 32] = take(32)?.try_into().ok()?;
        let value = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let key_source = KeySource::decode(&mut rest)?;
        let statement = Self {
            key_source,
            anchor,
            nullifier,
            rk,
            value,
            pq_commitment,
            migration_domain,
            epoch,
        };
        (rest.is_empty() && statement.is_well_formed()).then_some(statement)
    }

    /// The message of the spend authorization signature under [`Self::rk`].
    pub fn sighash(&self) -> [u8; 32] {
        blake2b_256(SIGHASH_PERSONAL, &[&self.to_bytes()])
    }

    fn public_bits(&self) -> Vec<bool> {
        let mut out: Vec<bool> = byte_bits(&self.anchor, 256).collect();
        out.extend(byte_bits(&self.nullifier, 255));
        out.extend(byte_bits(&self.rk, 256));
        out.extend(byte_bits(&self.value.to_le_bytes(), 64));
        out
    }

    /// The relation's public inputs, one per bit: the anchor, the 255 bits of the
    /// nullifier, `rk`, the value (little-endian). `None` for a malformed statement.
    pub fn public_inputs(&self) -> Option<Vec<F>> {
        self.is_well_formed().then(|| to_field(self.public_bits()))
    }

    fn transcript(&self, regime: Profile) -> Vec<u8> {
        let mut out = self.to_bytes();
        out.push(regime.wire_tag());
        out
    }

    /// The binding a verified statement asks the registry to record. The registry
    /// nullifier is the note's nullifier and the legacy identifier is derived from it, so
    /// one note can be bound once, whatever the domain or epoch.
    #[cfg(feature = "std")]
    pub fn binding(&self) -> crate::hem::registry::MigrationBinding {
        crate::hem::registry::MigrationBinding {
            nullifier: self.nullifier,
            migration_domain: self.migration_domain,
            legacy_id: credential_identifier(LEGACY_TAG_IRONWOOD_NOTE, &self.nullifier),
            pq_commitment: self.pq_commitment,
            epoch: self.epoch,
            exposure: crate::hem::registry::KeyExposure::Hidden,
        }
    }
}

/// The public relation of a note recovery; it depends on the key source only.
pub fn recovery_shape(statement: &RecoveryStatement) -> Option<Arc<Shape>> {
    statement
        .is_well_formed()
        .then(|| shape_of(&Relation::Note(statement.key_source.clone())))
}

fn checked_note(
    statement: &RecoveryStatement,
    witness: &RecoveryWitness,
) -> Result<NoteEvaluation, RecoveryError> {
    if !statement.is_well_formed() {
        return Err(RecoveryError::MalformedStatement);
    }
    let e = evaluate_note(&statement.key_source, witness).ok_or(RecoveryError::WitnessMismatch)?;
    if e.anchor != statement.anchor
        || e.nullifier != statement.nullifier
        || e.rk != statement.rk
        || e.value != statement.value
    {
        return Err(RecoveryError::WitnessMismatch);
    }
    Ok(e)
}

/// The relation of `statement` with the assignment for `witness`, after checking natively
/// that the witness produces the statement. The assignment is secret. The transcript of a
/// proof over it must be [`recovery_transcript`].
pub fn synthesize_recovery(
    statement: &RecoveryStatement,
    witness: &RecoveryWitness,
) -> Result<(Shape, Vec<F>), RecoveryError> {
    let e = checked_note(statement, witness)?;
    let relation = Relation::Note(statement.key_source.clone());
    let (shape, assignment, _) = build(&relation, &statement.public_bits(), &e.inputs);
    Ok((shape, assignment))
}

/// The statement bytes [`prove_recovery`] and [`verify_recovery`] hand to zk-Hem.
pub fn recovery_transcript(statement: &RecoveryStatement, regime: Profile) -> Vec<u8> {
    statement.transcript(regime)
}

/// A recovery proof: the zk-Hem proof and the spend authorization signature under `rk`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveryProof {
    key_tag: u8,
    pub regime: Profile,
    /// `SpendAuthSig^Orchard` signature on [`RecoveryStatement::sighash`] under `rk`.
    pub spend_auth_sig: [u8; 64],
    pub proof: ZkHemV2Proof,
}

impl RecoveryProof {
    /// `magic(8) || key source tag || regime || signature(64) || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = NOTE_PROOF_MAGIC.to_vec();
        out.push(self.key_tag);
        out.push(self.regime.wire_tag());
        out.extend_from_slice(&self.spend_auth_sig);
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    /// Strict decoding against the statement the proof is for.
    pub fn from_bytes(bytes: &[u8], statement: &RecoveryStatement) -> Option<Self> {
        let rest = bytes.strip_prefix(NOTE_PROOF_MAGIC.as_slice())?;
        let (&key_tag, rest) = rest.split_first()?;
        let (&regime, rest) = rest.split_first()?;
        let (sig, rest) = rest.split_at_checked(64)?;
        if key_tag != statement.key_source.tag() {
            return None;
        }
        let regime = Profile::from_wire_tag(regime)?;
        let shape = recovery_shape(statement)?;
        let proof = ZkHemV2Proof::from_bytes(rest, &shape)?;
        (proof.profile == regime).then_some(Self {
            key_tag,
            regime,
            spend_auth_sig: sig.try_into().ok()?,
            proof,
        })
    }
}

/// Prove the recovery of a note. `seed` must be uniform and secret; it drives every mask
/// and blinder of the proof and the signing nonce.
///
/// `signature` is the spend authorization signature on [`RecoveryStatement::sighash`]
/// under `rk`. With a spending key or seed witness it may be `None`: the prover then signs
/// with `H^ask(sk) + alpha`. With a quantum spending key the holders of the spend
/// authorizing key (a FROST group, a hardware wallet) produce it and it is required.
pub fn prove_recovery(
    statement: &RecoveryStatement,
    witness: &RecoveryWitness,
    regime: Profile,
    seed: &[u8; 32],
    signature: Option<&[u8; 64]>,
) -> Result<RecoveryProof, RecoveryError> {
    let e = checked_note(statement, witness)?;
    let sighash = statement.sighash();
    let spend_auth_sig = match (signature, &e.signing_key) {
        (Some(sig), _) => *sig,
        (None, Some(key)) => {
            let mut wide = blake2b_512(SIGNING_NONCE_PERSONAL, &[seed, &sighash, &[0]]);
            let mut more = blake2b_512(SIGNING_NONCE_PERSONAL, &[seed, &sighash, &[1]]);
            let mut randomness = [0u8; 80];
            randomness[..64].copy_from_slice(&wide);
            randomness[64..].copy_from_slice(&more[..16]);
            let sig = orchard::redpallas_sign(key, &sighash, &randomness);
            wipe(&mut wide);
            wipe(&mut more);
            wipe(&mut randomness);
            sig
        }
        (None, None) => return Err(RecoveryError::SignatureRequired),
    };
    if !orchard::redpallas_verify(&statement.rk, &sighash, &spend_auth_sig) {
        return Err(RecoveryError::BadSignature);
    }
    let relation = Relation::Note(statement.key_source.clone());
    let (shape, assignment, _) = build(&relation, &statement.public_bits(), &e.inputs);
    let proof = protocol::prove(
        &shape,
        assignment,
        &statement.transcript(regime),
        regime,
        seed,
    )
    .map_err(RecoveryError::Proof)?;
    Ok(RecoveryProof {
        key_tag: statement.key_source.tag(),
        regime,
        spend_auth_sig,
        proof,
    })
}

/// Verify a recovery proof under the regime the verifier requires: the zk-Hem proof of
/// the relation and the spend authorization signature under `rk`. On `true`,
/// [`RecoveryStatement::binding`] is what the registry should record; the anchor, the
/// nullifier set and the value are the verifier's to check (see the module
/// documentation).
pub fn verify_recovery(
    statement: &RecoveryStatement,
    regime: Profile,
    proof: &RecoveryProof,
) -> bool {
    if proof.regime != regime || proof.key_tag != statement.key_source.tag() {
        return false;
    }
    let (Some(shape), Some(public_inputs)) = (recovery_shape(statement), statement.public_inputs())
    else {
        return false;
    };
    orchard::redpallas_verify(&statement.rk, &statement.sighash(), &proof.spend_auth_sig)
        && proof.proof.profile == regime
        && protocol::verify(
            &shape,
            &public_inputs,
            &statement.transcript(regime),
            regime,
            &proof.proof,
        )
}

// ============================================================================
// Address ownership
// ============================================================================

/// The secret inputs of an address ownership proof.
#[derive(Clone)]
pub struct AddressWitness {
    pub key: KeyWitness,
    /// Whether the address belongs to the internal incoming viewing key.
    pub internal: bool,
}

/// Public statement of ownership of an Orchard address: the prover knows the key
/// material behind the incoming viewing key of `address`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AddressStatement {
    pub key_source: KeySource,
    /// The raw Orchard address `d || pk_d` (the Orchard receiver of a unified address).
    pub address: [u8; 43],
    pub pq_commitment: [u8; 32],
    pub migration_domain: [u8; 32],
    pub epoch: u64,
}

fn address_points(address: &[u8; 43]) -> Option<(AffineBytes, [u8; 32])> {
    let d: [u8; 11] = address[..11].try_into().ok()?;
    let pk_d: [u8; 32] = address[11..].try_into().ok()?;
    Point::from_bytes_nonidentity(&pk_d)?;
    Some((affine_bytes(&orchard::diversify_hash(&d))?, pk_d))
}

fn address_of(source: &KeySource, w: &AddressWitness, d: &[u8; 11]) -> Option<[u8; 43]> {
    let keys = resolve_keys(source, &w.key)?;
    let scope = if w.internal {
        orchard::Scope::Internal
    } else {
        orchard::Scope::External
    };
    keys.fvk.address(d, scope)
}

impl AddressStatement {
    /// The statement for the address of the witness key at diversifier `d`.
    pub fn derive(
        key_source: &KeySource,
        witness: &AddressWitness,
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

    /// Whether the parameters are in range and `pk_d` is a non-identity point.
    pub fn is_well_formed(&self) -> bool {
        self.key_source.is_well_formed() && address_points(&self.address).is_some()
    }

    /// The registry nullifier: one value per address and domain,
    /// `BLAKE2b-256("QSAG_ZcashAddrNf", domain || address)`. It is public: an address is
    /// its own identifier.
    pub fn nullifier(&self) -> [u8; 32] {
        blake2b_256(
            ADDRESS_NULLIFIER_PERSONAL,
            &[&self.migration_domain, &self.address],
        )
    }

    /// `tag(29) || epoch(8, BE) || domain(32) || pq(32) || address(43) || key source`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(160);
        out.extend_from_slice(ADDRESS_TAG);
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.migration_domain);
        out.extend_from_slice(&self.pq_commitment);
        out.extend_from_slice(&self.address);
        self.key_source.encode(&mut out);
        out
    }

    /// Strict inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes.strip_prefix(ADDRESS_TAG.as_slice())?;
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, tail) = rest.split_at_checked(n)?;
            rest = tail;
            Some(head)
        };
        let epoch = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let migration_domain: [u8; 32] = take(32)?.try_into().ok()?;
        let pq_commitment: [u8; 32] = take(32)?.try_into().ok()?;
        let address: [u8; 43] = take(43)?.try_into().ok()?;
        let key_source = KeySource::decode(&mut rest)?;
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
        let ((gx, gy), pk_d) = address_points(&self.address)?;
        let mut out: Vec<bool> = byte_bits(&gx, 255).collect();
        out.extend(byte_bits(&gy, 255));
        out.extend(byte_bits(&pk_d, 256));
        Some(out)
    }

    /// The relation's public inputs, one per bit: the affine coordinates of
    /// `DiversifyHash(d)` (255 bits each) and `repr_P(pk_d)`.
    pub fn public_inputs(&self) -> Option<Vec<F>> {
        self.key_source
            .is_well_formed()
            .then(|| self.public_bits())
            .flatten()
            .map(to_field)
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
            legacy_id: credential_identifier(LEGACY_TAG_ORCHARD_ADDRESS, &self.address),
            pq_commitment: self.pq_commitment,
            epoch: self.epoch,
            exposure: crate::hem::registry::KeyExposure::Hidden,
        }
    }
}

/// The public relation of an address statement; it depends on the key source only.
pub fn address_shape(statement: &AddressStatement) -> Option<Arc<Shape>> {
    statement
        .is_well_formed()
        .then(|| shape_of(&Relation::Address(statement.key_source.clone())))
}

/// The relation of `statement` with the assignment for `witness`, after checking natively
/// that the witness owns the address.
pub fn synthesize_address(
    statement: &AddressStatement,
    witness: &AddressWitness,
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
    let relation = Relation::Address(statement.key_source.clone());
    let mut inputs = Inputs::placeholder(&relation);
    (inputs.secret, inputs.ak, inputs.nk) = Inputs::keys(&witness.key);
    inputs.internal = witness.internal;
    let (shape, assignment, _) = build(&relation, &public, &inputs);
    Ok((shape, assignment))
}

/// The statement bytes [`prove_address`] and [`verify_address`] hand to zk-Hem.
pub fn address_transcript(statement: &AddressStatement, regime: Profile) -> Vec<u8> {
    statement.transcript(regime)
}

/// An address ownership proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AddressProof {
    key_tag: u8,
    pub regime: Profile,
    pub proof: ZkHemV2Proof,
}

impl AddressProof {
    /// `magic(8) || key source tag || regime || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = ADDRESS_PROOF_MAGIC.to_vec();
        out.push(self.key_tag);
        out.push(self.regime.wire_tag());
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    /// Strict decoding against the statement the proof is for.
    pub fn from_bytes(bytes: &[u8], statement: &AddressStatement) -> Option<Self> {
        let rest = bytes.strip_prefix(ADDRESS_PROOF_MAGIC.as_slice())?;
        let (&key_tag, rest) = rest.split_first()?;
        let (&regime, rest) = rest.split_first()?;
        if key_tag != statement.key_source.tag() {
            return None;
        }
        let regime = Profile::from_wire_tag(regime)?;
        let shape = address_shape(statement)?;
        let proof = ZkHemV2Proof::from_bytes(rest, &shape)?;
        (proof.profile == regime).then_some(Self {
            key_tag,
            regime,
            proof,
        })
    }
}

/// Prove ownership of an address. `seed` must be uniform and secret.
pub fn prove_address(
    statement: &AddressStatement,
    witness: &AddressWitness,
    regime: Profile,
    seed: &[u8; 32],
) -> Result<AddressProof, RecoveryError> {
    let (shape, assignment) = synthesize_address(statement, witness)?;
    let proof = protocol::prove(
        &shape,
        assignment,
        &statement.transcript(regime),
        regime,
        seed,
    )
    .map_err(RecoveryError::Proof)?;
    Ok(AddressProof {
        key_tag: statement.key_source.tag(),
        regime,
        proof,
    })
}

/// Verify an address ownership proof under the regime the verifier requires.
pub fn verify_address(statement: &AddressStatement, regime: Profile, proof: &AddressProof) -> bool {
    if proof.regime != regime || proof.key_tag != statement.key_source.tag() {
        return false;
    }
    let (Some(shape), Some(public_inputs)) = (address_shape(statement), statement.public_inputs())
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

/// Row counts of a relation before padding, for reports: `(rows, variables)`.
pub fn relation_size(key_source: &KeySource, note: bool) -> (usize, usize) {
    let relation = if note {
        Relation::Note(key_source.clone())
    } else {
        Relation::Address(key_source.clone())
    };
    let public = vec![false; relation.public_bits()];
    let (shape, _, rows) = build(&relation, &public, &Inputs::placeholder(&relation));
    (rows, shape.num_vars)
}

#[cfg(test)]
mod tests {
    use super::super::vectors::{KEY_COMPONENTS, hex32};
    use super::*;
    use crate::hem::zcash::orchard::Scope;
    use std::println;
    use std::string::String;

    const REGIME: Profile = Profile::TurboShakeJohnson400;
    const PQ: [u8; 32] = [0x51; 32];
    const DOMAIN: [u8; 32] = [0x44; 32];
    const EPOCH: u64 = 7;

    fn sk(i: usize) -> [u8; 32] {
        hex32(KEY_COMPONENTS[i].sk)
    }

    fn seed() -> Vec<u8> {
        (0..32).map(|i| (i * 7 + 1) as u8).collect()
    }

    fn sample_fp(i: u64) -> Fp {
        let mut x = Fp::from_u64(0x0123_4567_89ab_cdef ^ i);
        for _ in 0..5 {
            x = x.square() + Fp::from_u64(i + 11);
        }
        x
    }

    fn alpha(i: u64) -> [u8; 32] {
        let mut x = Fq::from_u64(0xfeed_face_cafe_beef ^ i);
        for _ in 0..5 {
            x = x.square() + Fq::from_u64(i + 5);
        }
        x.to_bytes()
    }

    /// The key witness of a source and the full viewing key it resolves to.
    fn key(source: &KeySource) -> (KeyWitness, FullViewingKey) {
        let witness = match source {
            KeySource::SpendingKey => KeyWitness::SpendingKey(sk(0)),
            KeySource::Zip32Seed { .. } => KeyWitness::Zip32Seed(seed()),
            KeySource::QuantumSpendingKey => {
                // A key as ZIP 2005 derives it with use_qsk: nk and qsk from sk, ak from
                // an independent spend authorizing key.
                let ask = orchard::spend_authorizing_key(&sk(3)).unwrap();
                KeyWitness::QuantumSpendingKey {
                    qsk: *orchard::h_qsk(&sk(1)),
                    ak: orchard::redpallas_public_key(&ask),
                    nk: orchard::h_nk(&sk(1)).to_bytes(),
                }
            }
        };
        let fvk = resolve_keys(source, &witness).unwrap().fvk;
        (witness, fvk)
    }

    fn note_for(fvk: &FullViewingKey, internal: bool, version: NoteVersion) -> Note {
        let scope = if internal {
            Scope::Internal
        } else {
            Scope::External
        };
        let note = Note {
            recipient: fvk.default_address(scope).unwrap(),
            value: 1_234_567_890_123,
            rho: sample_fp(1),
            rseed: [0x5e; 32],
            version,
        };
        assert!(note.commitment().is_some());
        note
    }

    /// A rehashed tree with a few other leaves and `note` at `position`.
    fn tree(note: &Note, position: u32) -> ([[u8; 32]; rehash::DEPTH], [u8; 32]) {
        let mut leaves: Vec<[u8; 32]> = (0..position + 3)
            .map(|i| rehash::leaf_hash(&[i as u8 + 1; 32], &[0x77; 32]))
            .collect();
        leaves[position as usize] =
            rehash::leaf_hash(&note.cmx().unwrap().to_bytes(), &note.rho.to_bytes());
        rehash::witness(&leaves, position).unwrap()
    }

    fn witness(source: &KeySource, internal: bool) -> RecoveryWitness {
        let (key, fvk) = key(source);
        let note = note_for(&fvk, internal, NoteVersion::V3);
        let (path, _) = tree(&note, 5);
        RecoveryWitness {
            key,
            internal,
            alpha: alpha(1),
            note,
            position: 5,
            path,
        }
    }

    fn statement(source: &KeySource, w: &RecoveryWitness) -> RecoveryStatement {
        RecoveryStatement::derive(source, w, PQ, DOMAIN, EPOCH).unwrap()
    }

    /// The signature the holders of the spend authorizing key make in the QK branch.
    fn external_signature(st: &RecoveryStatement, w: &RecoveryWitness) -> [u8; 64] {
        let ask = orchard::spend_authorizing_key(&sk(3)).unwrap();
        let key = ask + Fq::from_bytes(&w.alpha).unwrap();
        orchard::redpallas_sign(&key, &st.sighash(), &[0x33; 80])
    }

    fn sources() -> [KeySource; 3] {
        [
            KeySource::SpendingKey,
            KeySource::mainnet_account(0),
            KeySource::QuantumSpendingKey,
        ]
    }

    #[test]
    fn statement_matches_the_native_protocol() {
        for source in sources() {
            let w = witness(&source, false);
            let st = statement(&source, &w);
            let (_, fvk) = key(&source);
            assert_eq!(st.value, w.note.value);
            assert_eq!(st.nullifier, w.note.nullifier(&fvk.nk).unwrap().to_bytes());
            assert_eq!(st.anchor, tree(&w.note, 5).1);
            assert!(st.is_well_formed());
            assert_eq!(st.public_inputs().unwrap().len(), 831);
        }
        // The seed source is the account key of ZIP 32.
        let (_, fvk) = key(&KeySource::mainnet_account(0));
        let account = orchard::ExtendedSpendingKey::account(&seed(), 133, 0).unwrap();
        assert_eq!(fvk, FullViewingKey::from_spending_key(&account.sk).unwrap());
        // In the SK branch rk is the randomization of [H^ask(sk)] G.
        let w = witness(&KeySource::SpendingKey, false);
        let st = statement(&KeySource::SpendingKey, &w);
        let signing = orchard::h_ask(&sk(0)) + Fq::from_bytes(&w.alpha).unwrap();
        assert_eq!(st.rk, orchard::redpallas_public_key(&signing));
    }

    #[test]
    fn inconsistent_witnesses_have_no_statement() {
        let source = KeySource::SpendingKey;
        let good = witness(&source, false);
        assert!(RecoveryStatement::derive(&source, &good, PQ, DOMAIN, EPOCH).is_some());
        let derive = |w: &RecoveryWitness| RecoveryStatement::derive(&source, w, PQ, DOMAIN, EPOCH);

        // A note of another key.
        let mut w = good.clone();
        w.key = KeyWitness::SpendingKey(sk(1));
        assert!(derive(&w).is_none());
        // The wrong scope.
        let mut w = good.clone();
        w.internal = true;
        assert!(derive(&w).is_none());
        // A pre-ZIP-2005 note (lead byte 0x02).
        let mut w = good.clone();
        w.note.version = NoteVersion::V2;
        assert!(derive(&w).is_none());
        // A randomizer that is not a canonical scalar, and the zero randomizer.
        let mut w = good.clone();
        w.alpha = [0xff; 32];
        assert!(derive(&w).is_none());
        w.alpha = [0; 32];
        assert!(derive(&w).is_none());
        // A witness of the wrong kind, a seed of the wrong length.
        assert!(
            RecoveryStatement::derive(&KeySource::QuantumSpendingKey, &good, PQ, DOMAIN, EPOCH)
                .is_none()
        );
        let mut w = good.clone();
        w.key = KeyWitness::Zip32Seed(vec![1; 33]);
        assert!(
            RecoveryStatement::derive(&KeySource::mainnet_account(0), &w, PQ, DOMAIN, EPOCH)
                .is_none()
        );
        // A changed note or path gives another statement, which the witness check of the
        // prover rejects.
        let st = derive(&good).unwrap();
        let mut w = good.clone();
        w.note.value += 1;
        assert_ne!(derive(&w).unwrap(), st);
        assert_eq!(
            synthesize_recovery(&st, &w).err(),
            Some(RecoveryError::WitnessMismatch)
        );
        let mut w = good.clone();
        w.path[3][0] ^= 1;
        assert_ne!(derive(&w).unwrap().anchor, st.anchor);
        let mut w = good.clone();
        w.position ^= 1;
        assert_ne!(derive(&w).unwrap().anchor, st.anchor);
    }

    #[test]
    fn note_statement_encoding_is_strict() {
        for source in sources() {
            let w = witness(&source, false);
            let st = statement(&source, &w);
            let bytes = st.to_bytes();
            assert_eq!(RecoveryStatement::from_bytes(&bytes), Some(st.clone()));
            assert!(RecoveryStatement::from_bytes(&bytes[..bytes.len() - 1]).is_none());
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(RecoveryStatement::from_bytes(&longer).is_none());
            let mut tag = bytes.clone();
            tag[28] ^= 1;
            assert!(RecoveryStatement::from_bytes(&tag).is_none());
            // Every field is in the encoding and in the signed message.
            let variants = [
                RecoveryStatement {
                    epoch: 8,
                    ..st.clone()
                },
                RecoveryStatement {
                    migration_domain: [1; 32],
                    ..st.clone()
                },
                RecoveryStatement {
                    pq_commitment: [1; 32],
                    ..st.clone()
                },
                RecoveryStatement {
                    anchor: [1; 32],
                    ..st.clone()
                },
                RecoveryStatement {
                    nullifier: [1; 32],
                    ..st.clone()
                },
                RecoveryStatement {
                    rk: st.nullifier,
                    ..st.clone()
                },
                RecoveryStatement {
                    value: st.value + 1,
                    ..st.clone()
                },
            ];
            for other in &variants {
                assert_ne!(other.to_bytes(), bytes);
                assert_ne!(other.sighash(), st.sighash());
            }
        }
        let st = statement(
            &KeySource::SpendingKey,
            &witness(&KeySource::SpendingKey, false),
        );
        // Non-canonical field element, identity and off-curve rk, unknown or bad key source.
        let at = |offset: usize| 29 + 8 + 32 + 32 + offset;
        let mut bad = st.to_bytes();
        bad[at(32)..at(64)].fill(0xff);
        assert!(RecoveryStatement::from_bytes(&bad).is_none());
        let mut bad = st.to_bytes();
        bad[at(64)..at(96)].fill(0);
        assert!(RecoveryStatement::from_bytes(&bad).is_none());
        let mut bad = st.to_bytes();
        *bad.last_mut().unwrap() = 9;
        assert!(RecoveryStatement::from_bytes(&bad).is_none());
        let seed_st = RecoveryStatement {
            key_source: KeySource::Zip32Seed {
                seed_len: 31,
                coin_type: 133,
                account: 0,
            },
            ..st.clone()
        };
        assert!(!seed_st.is_well_formed());
        assert!(RecoveryStatement::from_bytes(&seed_st.to_bytes()).is_none());
        assert!(seed_st.public_inputs().is_none());
        assert!(recovery_shape(&seed_st).is_none());
        let hardened = RecoveryStatement {
            key_source: KeySource::Zip32Seed {
                seed_len: 32,
                coin_type: 133,
                account: ZIP32_HARDENED,
            },
            ..st
        };
        assert!(RecoveryStatement::from_bytes(&hardened.to_bytes()).is_none());
    }

    #[test]
    fn address_statement_matches_the_native_protocol() {
        for source in sources() {
            let (key, fvk) = key(&source);
            for internal in [false, true] {
                let scope = if internal {
                    Scope::Internal
                } else {
                    Scope::External
                };
                let w = AddressWitness {
                    key: key.clone(),
                    internal,
                };
                let d = fvk.diversifier(&[3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], scope);
                let st = AddressStatement::derive(&source, &w, &d, PQ, DOMAIN, EPOCH).unwrap();
                assert_eq!(st.address, fvk.address(&d, scope).unwrap());
                assert_eq!(st.public_inputs().unwrap().len(), 766);
                let bytes = st.to_bytes();
                assert_eq!(AddressStatement::from_bytes(&bytes), Some(st.clone()));
                assert!(AddressStatement::from_bytes(&bytes[1..]).is_none());
                let mut longer = bytes.clone();
                longer.push(0);
                assert!(AddressStatement::from_bytes(&longer).is_none());
                // An address of another key or scope is not this witness's.
                let other = AddressStatement {
                    address: FullViewingKey::from_spending_key(&sk(5))
                        .unwrap()
                        .default_address(Scope::External)
                        .unwrap(),
                    ..st.clone()
                };
                assert_eq!(
                    synthesize_address(&other, &w).err(),
                    Some(RecoveryError::WitnessMismatch)
                );
                let flipped = AddressWitness {
                    key: key.clone(),
                    internal: !internal,
                };
                assert_eq!(
                    synthesize_address(&st, &flipped).err(),
                    Some(RecoveryError::WitnessMismatch)
                );
                assert_ne!(
                    st.nullifier(),
                    AddressStatement {
                        migration_domain: [9; 32],
                        ..st.clone()
                    }
                    .nullifier()
                );
            }
        }
        // pk_d must decode to a point other than the identity.
        let (key, fvk) = key(&KeySource::SpendingKey);
        let w = AddressWitness {
            key,
            internal: false,
        };
        let d = fvk.diversifier(&[0; 11], Scope::External);
        let st =
            AddressStatement::derive(&KeySource::SpendingKey, &w, &d, PQ, DOMAIN, EPOCH).unwrap();
        let mut zero = st.clone();
        zero.address[11..].fill(0);
        assert!(!zero.is_well_formed());
        assert!(AddressStatement::from_bytes(&zero.to_bytes()).is_none());
        let mut off = st;
        off.address[11..].fill(0xff);
        assert!(off.public_inputs().is_none());
    }

    #[cfg(feature = "std")]
    #[test]
    fn registry_bindings_identify_the_credential() {
        use crate::hem::registry::KeyExposure;
        let source = KeySource::SpendingKey;
        let w = witness(&source, false);
        let st = statement(&source, &w);
        let b = st.binding();
        assert_eq!(b.nullifier, st.nullifier);
        assert_eq!(b.exposure, KeyExposure::Hidden);
        assert_eq!(
            (b.pq_commitment, b.migration_domain, b.epoch),
            (PQ, DOMAIN, EPOCH)
        );
        // The same note in another domain or epoch has the same registry identifiers, so
        // the registry refuses a second binding.
        let again = RecoveryStatement {
            migration_domain: [1; 32],
            epoch: 9,
            ..st.clone()
        }
        .binding();
        assert_eq!(
            (again.nullifier, again.legacy_id),
            (b.nullifier, b.legacy_id)
        );
        // The identifier is not one a Bitcoin, Ethereum, Ed25519 or BLS credential can have.
        use crate::hem::relations::Credential;
        let mut twenty_bytes = [0u8; 20];
        twenty_bytes.copy_from_slice(&st.nullifier[..20]);
        for other in [
            Credential::BitcoinKeyHash(twenty_bytes),
            Credential::BitcoinTaproot(st.nullifier),
            Credential::EthereumAddress(twenty_bytes),
            Credential::Ed25519Key(st.nullifier),
            Credential::BitcoinScriptHash(twenty_bytes),
            Credential::BlsWithdrawal(st.nullifier),
        ] {
            assert_ne!(other.identifier(), b.legacy_id);
        }
        assert_ne!(
            credential_identifier(LEGACY_TAG_ORCHARD_ADDRESS, &st.nullifier),
            b.legacy_id
        );
    }

    // ------------------------------------------------------------------------
    // The relations themselves. Each build is a relation of up to 2^22 rows; these run
    // on a build host:
    // cargo test --release -p qsag-migrate --features std --lib -- \
    //     hem::zcash::recovery::tests::relation --ignored --nocapture --test-threads 1
    // ------------------------------------------------------------------------

    fn flip_public(shape: &Shape, z: &[F], at: usize) -> bool {
        let mut bad = z.to_vec();
        bad[1 + at] = F::ONE - bad[1 + at];
        shape.is_satisfied(&bad)
    }

    #[test]
    #[ignore = "builds 2^22-row relations"]
    fn relation_of_a_note_binds_every_public_input() {
        let source = KeySource::SpendingKey;
        let relation = Relation::Note(source.clone());
        let w = witness(&source, false);
        let st = statement(&source, &w);
        let e = evaluate_note(&source, &w).unwrap();
        let (shape, z, rows) = build(&relation, &st.public_bits(), &e.inputs);
        println!("note relation: {rows} rows, {} variables", shape.num_vars);
        assert!(shape.is_satisfied(&z));
        assert_eq!(
            shape.num_sbox, 0,
            "the collaborative prover needs mul rows only"
        );
        assert_eq!(shape.num_public, 831);
        // Anchor, nullifier, rk and value: a flipped bit anywhere is rejected.
        for at in [0, 100, 255, 256, 300, 510, 511, 600, 766, 767, 800, 830] {
            assert!(!flip_public(&shape, &z, at), "public bit {at}");
        }

        // The shape does not depend on the witness: another key, scope, note, position.
        assert_eq!(shape.digest(), recovery_shape(&st).unwrap().digest());
        let mut other = witness(&source, true);
        other.key = KeyWitness::SpendingKey(sk(4));
        let fvk = FullViewingKey::from_spending_key(&sk(4)).unwrap();
        other.note = note_for(&fvk, true, NoteVersion::V3);
        other.note.value = 5;
        other.note.rseed = [0x99; 32];
        other.position = 2;
        other.path = tree(&other.note, 2).0;
        other.alpha = alpha(2);
        let other_st = statement(&source, &other);
        let e2 = evaluate_note(&source, &other).unwrap();
        let (shape2, z2, _) = build(&relation, &other_st.public_bits(), &e2.inputs);
        assert!(shape2.is_satisfied(&z2));
        assert_eq!(shape2.digest(), shape.digest());

        // The first witness does not satisfy the second statement or the reverse.
        let (_, z_cross, _) = build(&relation, &other_st.public_bits(), &e.inputs);
        assert!(!shape.is_satisfied(&z_cross));
    }

    #[test]
    #[ignore = "builds 2^22-row relations"]
    fn relation_of_a_note_rejects_what_the_statement_excludes() {
        let source = KeySource::SpendingKey;
        let relation = Relation::Note(source.clone());
        let w = witness(&source, false);
        let st = statement(&source, &w);
        let good = evaluate_note(&source, &w).unwrap().inputs;
        let unsatisfied = |inputs: &Inputs| {
            let (shape, z, _) = build(&relation, &st.public_bits(), inputs);
            !shape.is_satisfied(&z)
        };

        // A key that does not own the note.
        let mut inputs = good.clone();
        inputs.secret = sk(1).to_vec();
        assert!(unsatisfied(&inputs), "foreign key");
        // The other scope of the right key.
        let mut inputs = good.clone();
        inputs.internal = true;
        assert!(unsatisfied(&inputs), "wrong scope");
        // A wrong sibling and a wrong position.
        let mut inputs = good.clone();
        inputs.path[7][3] ^= 0x10;
        assert!(unsatisfied(&inputs), "wrong path");
        let mut inputs = good.clone();
        inputs.position ^= 4;
        assert!(unsatisfied(&inputs), "wrong position");
        // Another rho, another rseed, another base point, another randomizer.
        let mut inputs = good.clone();
        inputs.rho = sample_fp(2).to_bytes();
        assert!(unsatisfied(&inputs), "wrong rho");
        let mut inputs = good.clone();
        inputs.rseed[0] ^= 1;
        assert!(unsatisfied(&inputs), "wrong rseed");
        let mut inputs = good.clone();
        inputs.g_d = affine_bytes(&orchard::diversify_hash(&[9; 11])).unwrap();
        assert!(unsatisfied(&inputs), "wrong g_d");
        let mut inputs = good.clone();
        inputs.alpha = alpha(3);
        assert!(unsatisfied(&inputs), "wrong alpha");

        // A note with the pre-ZIP-2005 derivation of rcm (lead byte 0x02), in a tree that
        // really contains it: the relation derives rcm from the note fields, so it does
        // not open.
        let fvk = FullViewingKey::from_spending_key(&sk(0)).unwrap();
        let legacy = note_for(&fvk, false, NoteVersion::V2);
        let (path, anchor) = tree(&legacy, 5);
        let nf = legacy.nullifier(&fvk.nk).unwrap().to_bytes();
        let legacy_st = RecoveryStatement {
            anchor,
            nullifier: nf,
            ..st.clone()
        };
        let mut inputs = good.clone();
        inputs.path = path;
        let (shape, z, _) = build(&relation, &legacy_st.public_bits(), &inputs);
        assert!(!shape.is_satisfied(&z), "pre-ZIP-2005 note");
    }

    #[test]
    #[ignore = "builds 2^22-row relations"]
    fn relation_of_a_note_accepts_every_key_source() {
        let mut digests = Vec::new();
        for source in sources() {
            for internal in [false, true] {
                let w = witness(&source, internal);
                let st = statement(&source, &w);
                let e = evaluate_note(&source, &w).unwrap();
                let relation = Relation::Note(source.clone());
                let (shape, z, rows) = build(&relation, &st.public_bits(), &e.inputs);
                println!("note relation {source:?} internal={internal}: {rows} rows");
                assert!(shape.is_satisfied(&z));
                assert_eq!(shape.num_sbox, 0);
                digests.push(shape.digest());
                if matches!(source, KeySource::QuantumSpendingKey) && !internal {
                    // qsk, nk and ak^P are each bound.
                    for change in 0..3 {
                        let mut inputs = e.inputs.clone();
                        match change {
                            0 => inputs.secret[0] ^= 1,
                            1 => inputs.nk = sample_fp(3).to_bytes(),
                            _ => {
                                let other = orchard::spend_auth_base().mul(&Fq::from_u64(77));
                                inputs.ak = affine_bytes(&other).unwrap();
                            }
                        }
                        let (shape, z, _) = build(&relation, &st.public_bits(), &inputs);
                        assert!(!shape.is_satisfied(&z), "QK change {change}");
                    }
                }
            }
        }
        // One shape per key source, the same for both scopes.
        assert_eq!(digests[0], digests[1]);
        assert_eq!(digests[2], digests[3]);
        assert_eq!(digests[4], digests[5]);
        assert_ne!(digests[0], digests[2]);
        assert_ne!(digests[0], digests[4]);
        assert_ne!(digests[2], digests[4]);
    }

    #[test]
    #[ignore = "builds 2^21-row relations"]
    fn relation_of_an_address() {
        let mut digests = Vec::new();
        for source in sources() {
            let (key, fvk) = key(&source);
            let w = AddressWitness {
                key,
                internal: false,
            };
            let d = fvk.diversifier(&[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], Scope::External);
            let st = AddressStatement::derive(&source, &w, &d, PQ, DOMAIN, EPOCH).unwrap();
            let (shape, z) = synthesize_address(&st, &w).unwrap();
            println!(
                "address relation {source:?}: 2^{} rows, {} variables",
                shape.log_rows, shape.num_vars
            );
            assert!(shape.is_satisfied(&z));
            assert_eq!(shape.num_sbox, 0);
            assert_eq!(shape.num_public, 766);
            assert_eq!(shape.digest(), address_shape(&st).unwrap().digest());
            for at in [0, 254, 255, 509, 510, 700, 765] {
                assert!(!flip_public(&shape, &z, at), "public bit {at}");
            }
            digests.push(shape.digest());
            if matches!(source, KeySource::SpendingKey) {
                // The other scope and another key do not satisfy the relation.
                let relation = Relation::Address(source.clone());
                let public = st.public_bits().unwrap();
                let mut inputs = Inputs::placeholder(&relation);
                inputs.secret = sk(0).to_vec();
                inputs.internal = true;
                let (s, z, _) = build(&relation, &public, &inputs);
                assert!(!s.is_satisfied(&z), "wrong scope");
                inputs.internal = false;
                inputs.secret = sk(2).to_vec();
                let (s, z, _) = build(&relation, &public, &inputs);
                assert!(!s.is_satisfied(&z), "foreign key");
                // The internal address of the same key has the same shape.
                let wi = AddressWitness {
                    key: KeyWitness::SpendingKey(sk(0)),
                    internal: true,
                };
                let di = fvk.diversifier(&[0; 11], Scope::Internal);
                let sti = AddressStatement::derive(&source, &wi, &di, PQ, DOMAIN, EPOCH).unwrap();
                let (si, zi) = synthesize_address(&sti, &wi).unwrap();
                assert!(si.is_satisfied(&zi));
                assert_eq!(si.digest(), shape.digest());
            }
        }
        assert_ne!(digests[0], digests[1]);
        assert_ne!(digests[0], digests[2]);
    }

    #[test]
    #[ignore = "proves 2^22-row relations"]
    fn relation_proofs_roundtrip_and_reject_tampering() {
        // A note recovered with a spending key.
        let source = KeySource::SpendingKey;
        let w = witness(&source, false);
        let st = statement(&source, &w);
        let proof = prove_recovery(&st, &w, REGIME, &[3; 32], None).unwrap();
        let bytes = proof.to_bytes();
        let decoded = RecoveryProof::from_bytes(&bytes, &st).unwrap();
        assert_eq!(decoded, proof);
        assert!(verify_recovery(&st, REGIME, &decoded));

        // Every public field is bound, through the relation or the transcript.
        let mut flipped_rk = st.rk;
        flipped_rk[31] ^= 0x80;
        for other in [
            RecoveryStatement {
                epoch: 8,
                ..st.clone()
            },
            RecoveryStatement {
                migration_domain: [1; 32],
                ..st.clone()
            },
            RecoveryStatement {
                pq_commitment: [1; 32],
                ..st.clone()
            },
            RecoveryStatement {
                anchor: tree(&w.note, 6).1,
                ..st.clone()
            },
            RecoveryStatement {
                nullifier: sample_fp(8).to_bytes(),
                ..st.clone()
            },
            RecoveryStatement {
                rk: flipped_rk,
                ..st.clone()
            },
            RecoveryStatement {
                value: st.value + 1,
                ..st.clone()
            },
            RecoveryStatement {
                key_source: KeySource::QuantumSpendingKey,
                ..st.clone()
            },
        ] {
            assert!(!verify_recovery(&other, REGIME, &proof), "{other:?}");
        }
        // Another regime, a bad signature, tampered proof bytes.
        assert!(!verify_recovery(&st, Profile::CshakeJohnson400, &proof));
        let mut bad = proof.clone();
        bad.spend_auth_sig[40] ^= 1;
        assert!(!verify_recovery(&st, REGIME, &bad));
        for at in [8, 9, 10, 74, 80, bytes.len() / 2, bytes.len() - 1] {
            let mut tampered = bytes.clone();
            tampered[at] ^= 1;
            assert!(
                RecoveryProof::from_bytes(&tampered, &st)
                    .is_none_or(|p| !verify_recovery(&st, REGIME, &p)),
                "byte {at}"
            );
        }
        assert!(RecoveryProof::from_bytes(&bytes[..bytes.len() - 1], &st).is_none());
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(RecoveryProof::from_bytes(&longer, &st).is_none());

        // The prover refuses a witness that does not produce the statement.
        let mut wrong = w.clone();
        wrong.key = KeyWitness::SpendingKey(sk(1));
        assert_eq!(
            prove_recovery(&st, &wrong, REGIME, &[3; 32], None).err(),
            Some(RecoveryError::WitnessMismatch)
        );

        // The QK branch needs the signature of the spend authorizing key holders.
        let source = KeySource::QuantumSpendingKey;
        let wq = witness(&source, true);
        let stq = statement(&source, &wq);
        assert_eq!(
            prove_recovery(&stq, &wq, REGIME, &[4; 32], None).err(),
            Some(RecoveryError::SignatureRequired)
        );
        assert_eq!(
            prove_recovery(&stq, &wq, REGIME, &[4; 32], Some(&[1; 64])).err(),
            Some(RecoveryError::BadSignature)
        );
        let sig = external_signature(&stq, &wq);
        let proof_q = prove_recovery(&stq, &wq, REGIME, &[4; 32], Some(&sig)).unwrap();
        assert!(verify_recovery(&stq, REGIME, &proof_q));
        // A proof is for its own statement and its own kind of statement.
        assert!(!verify_recovery(&st, REGIME, &proof_q));
        assert!(RecoveryProof::from_bytes(&proof_q.to_bytes(), &st).is_none());

        // An address of the same key.
        let (key, fvk) = key(&KeySource::SpendingKey);
        let wa = AddressWitness {
            key,
            internal: false,
        };
        let d = fvk.diversifier(&[0; 11], Scope::External);
        let sta =
            AddressStatement::derive(&KeySource::SpendingKey, &wa, &d, PQ, DOMAIN, EPOCH).unwrap();
        let proof_a = prove_address(&sta, &wa, REGIME, &[5; 32]).unwrap();
        let bytes_a = proof_a.to_bytes();
        assert!(verify_address(
            &sta,
            REGIME,
            &AddressProof::from_bytes(&bytes_a, &sta).unwrap()
        ));
        for other in [
            AddressStatement {
                epoch: 8,
                ..sta.clone()
            },
            AddressStatement {
                migration_domain: [1; 32],
                ..sta.clone()
            },
            AddressStatement {
                pq_commitment: [1; 32],
                ..sta.clone()
            },
            AddressStatement {
                address: fvk.default_address(Scope::Internal).unwrap(),
                ..sta.clone()
            },
            AddressStatement {
                key_source: KeySource::mainnet_account(0),
                ..sta.clone()
            },
        ] {
            assert!(!verify_address(&other, REGIME, &proof_a), "{other:?}");
        }
        let mut tampered = bytes_a.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 1;
        assert!(
            AddressProof::from_bytes(&tampered, &sta)
                .is_none_or(|p| !verify_address(&sta, REGIME, &p))
        );
        // A note proof is not an address proof and the reverse.
        assert!(AddressProof::from_bytes(&bytes, &sta).is_none());
        assert!(RecoveryProof::from_bytes(&bytes_a, &st).is_none());
    }

    fn peak_rss_mib() -> Option<u64> {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
        let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
        Some(kib / 1024)
    }

    /// `cargo test --release -p qsag-migrate --features std --lib --
    /// hem::zcash::recovery::tests::measure --ignored --nocapture --test-threads 1`
    #[test]
    #[ignore = "measurement"]
    fn measure_zcash_proofs() {
        println!(
            "cpus={}",
            std::thread::available_parallelism().map_or(0, |n| n.get())
        );
        let only = std::env::var("HEM_MEASURE_ONLY").ok();
        let skip = |name: &str| only.as_ref().is_some_and(|o| !name.contains(o.as_str()));
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
            let name = std::format!("orchard-address {source:?}");
            if skip(&name) {
                continue;
            }
            let (key, fvk) = key(&source);
            let w = AddressWitness {
                key,
                internal: false,
            };
            let d = fvk.diversifier(&[0; 11], Scope::External);
            let st = AddressStatement::derive(&source, &w, &d, PQ, DOMAIN, EPOCH).unwrap();
            let t = std::time::Instant::now();
            let (shape, _) = synthesize_address(&st, &w).unwrap();
            let synth_s = t.elapsed().as_secs_f64();
            let (rows, _) = relation_size(&source, false);
            let t = std::time::Instant::now();
            let proof = prove_address(&st, &w, REGIME, &[3; 32]).unwrap();
            let prove_s = t.elapsed().as_secs_f64();
            let bytes = proof.to_bytes();
            let t = std::time::Instant::now();
            assert!(verify_address(&st, REGIME, &proof));
            let cold = t.elapsed().as_secs_f64();
            let t = std::time::Instant::now();
            let decoded = AddressProof::from_bytes(&bytes, &st).unwrap();
            assert!(verify_address(&st, REGIME, &decoded));
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
        for source in sources() {
            let name = std::format!("ironwood-note {source:?}");
            if skip(&name) {
                continue;
            }
            let w = witness(&source, false);
            let st = statement(&source, &w);
            let t = std::time::Instant::now();
            let (shape, _) = synthesize_recovery(&st, &w).unwrap();
            let synth_s = t.elapsed().as_secs_f64();
            let (rows, _) = relation_size(&source, true);
            let sig = matches!(source, KeySource::QuantumSpendingKey)
                .then(|| external_signature(&st, &w));
            let t = std::time::Instant::now();
            let proof = prove_recovery(&st, &w, REGIME, &[3; 32], sig.as_ref()).unwrap();
            let prove_s = t.elapsed().as_secs_f64();
            let bytes = proof.to_bytes();
            let t = std::time::Instant::now();
            assert!(verify_recovery(&st, REGIME, &proof));
            let cold = t.elapsed().as_secs_f64();
            let t = std::time::Instant::now();
            let decoded = RecoveryProof::from_bytes(&bytes, &st).unwrap();
            assert!(verify_recovery(&st, REGIME, &decoded));
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
