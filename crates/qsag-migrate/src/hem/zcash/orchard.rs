//! The Orchard protocol natively: key components, addresses, notes, note commitments,
//! nullifiers, the note commitment tree, ZIP 32 derivation and RedPallas signatures.
//!
//! Section numbers refer to the Zcash protocol specification v2026.9.0 \[NU7\]
//! (`paperbin/zcash-protocol-spec-v2026.9.0-nu7`); "ZIP 2005" is "Ironwood Quantum
//! Recoverability" (status Final, activated with NU6.3;
//! `paperbin/zcash-zip-2005-ironwood-quantum-recoverability`).
//!
//! | here | specification |
//! |---|---|
//! | [`prf_expand`] | 5.4.2 `PRF^expand` |
//! | [`h_ask`], [`h_nk`], [`h_rivk`], [`h_qsk`], [`h_qk`], [`h_rivk_ext`], [`FullViewingKey`] | 4.2.3 Orchard key components (with the ZIP 2005 `qsk` branch) |
//! | [`commit_ivk`] | 5.4.8.5 `Commit^ivk` |
//! | [`diversify_hash`], [`FullViewingKey::address`] | 5.4.1.6, 4.2.3 |
//! | [`Note`] | 3.2, 4.7.3 (`rseed`, `psi`, `rcm`; lead byte `0x03` per ZIP 2005) |
//! | [`note_commitment`] | 5.4.8.4 `NoteCommit^Orchard` |
//! | [`derive_nullifier`] | 4.16 `DeriveNullifier` |
//! | [`merkle_crh`], [`merkle_root`] | 5.4.1.3 `MerkleCRH^Orchard`, 3.8 |
//! | [`ExtendedSpendingKey`] | ZIP 32, Orchard (hardened-only derivation) |
//! | [`redpallas_sign`], [`redpallas_verify`] | 5.4.7 RedDSA with `SpendAuthSig^Orchard` |
//!
//! The functions return plain byte arrays or the field and point types of
//! [`super::pallas`]; they are compared byte for byte with the Zcash test vectors here and
//! with the `orchard` crate in `validation/zcash`.

use alloc::vec::Vec;
use qsag_core::wipe::{SecretBuffer, SecretScratch};

use super::blake2::{Blake2b, blake2b_256, blake2b_512};
use super::blake3;
use super::ff1::ff1_aes256_encrypt_88;
use super::pallas::{Fp, Fq, Point, hash_to_curve};
use super::poseidon;
use super::sinsemilla::{CommitDomain, HashDomain};

/// Depth of the note commitment tree.
pub const MERKLE_DEPTH: usize = 32;

fn wipe(buf: &mut [u8]) {
    qsag_asm::volatile_fill(buf, 0);
}

/// `PRF^expand_key(t) = BLAKE2b-512("Zcash_ExpandSeed", key || t)`, with `t` given in
/// parts.
pub fn prf_expand(key: &[u8], parts: &[&[u8]]) -> [u8; 64] {
    let mut st = Blake2b::new(64, b"Zcash_ExpandSeed");
    st.update(key);
    for p in parts {
        st.update(p);
    }
    st.finalize()
}

fn to_scalar(mut wide: [u8; 64]) -> Fq {
    let out = Fq::from_bytes_wide(&wide);
    wipe(&mut wide);
    out
}

fn to_base(mut wide: [u8; 64]) -> Fp {
    let out = Fp::from_bytes_wide(&wide);
    wipe(&mut wide);
    out
}

// ============================================================================
// Domains and generators
// ============================================================================

/// `G^Orchard`, the spend authorization base.
pub fn spend_auth_base() -> Point {
    hash_to_curve("z.cash:Orchard", b"G")
}

/// `K^Orchard`, the nullifier base.
pub fn nullifier_base() -> Point {
    hash_to_curve("z.cash:Orchard", b"K")
}

/// The `Commit^ivk` domain.
pub fn commit_ivk_domain() -> CommitDomain {
    CommitDomain::new("z.cash:Orchard-CommitIvk")
}

/// The `NoteCommit^Orchard` domain.
pub fn note_commit_domain() -> CommitDomain {
    CommitDomain::new("z.cash:Orchard-NoteCommit")
}

/// The `MerkleCRH^Orchard` domain.
pub fn merkle_crh_domain() -> HashDomain {
    HashDomain::new("z.cash:Orchard-MerkleCRH")
}

// ============================================================================
// Key components
// ============================================================================

/// `H^ask(sk) = ToScalar(PRF^expand_sk([0x06]))`, before the sign normalization.
pub fn h_ask(sk: &[u8; 32]) -> Fq {
    to_scalar(prf_expand(sk, &[&[0x06]]))
}

/// `H^nk(sk) = ToBase(PRF^expand_sk([0x07]))`.
pub fn h_nk(sk: &[u8; 32]) -> Fp {
    to_base(prf_expand(sk, &[&[0x07]]))
}

/// `H^rivk(sk) = ToScalar(PRF^expand_sk([0x08]))` (`H^rivk_legacy` in ZIP 2005).
pub fn h_rivk(sk: &[u8; 32]) -> Fq {
    to_scalar(prf_expand(sk, &[&[0x08]]))
}

/// `H^qsk(sk) = truncate_32(PRF^expand_sk([0x0C]))` (ZIP 2005).
pub fn h_qsk(sk: &[u8; 32]) -> [u8; 32] {
    let mut wide = prf_expand(sk, &[&[0x0c]]);
    let out: [u8; 32] = wide[..32].try_into().unwrap();
    wipe(&mut wide);
    out
}

/// `H^qk(qsk) = BLAKE3.derive_key("Zcash ZIP 2005 qk-derivation v1", qsk, 32)` (ZIP 2005).
pub fn h_qk(qsk: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key_32(blake3::QK_CONTEXT, qsk)
}

/// `H^rivk_ext_qk(ak, nk) = ToScalar(PRF^expand_qk([0x0D] || ak || nk))` (ZIP 2005).
pub fn h_rivk_ext(qk: &[u8; 32], ak: &Fp, nk: &Fp) -> Fq {
    to_scalar(prf_expand(qk, &[&[0x0d], &ak.to_bytes(), &nk.to_bytes()]))
}

/// `H^rivk_int_rivk(ak, nk) = ToScalar(PRF^expand_rivk([0x83] || ak || nk))` (ZIP 32,
/// Orchard internal key derivation).
pub fn h_rivk_int(rivk_ext: &Fq, ak: &Fp, nk: &Fp) -> Fq {
    to_scalar(prf_expand(
        &rivk_ext.to_bytes(),
        &[&[0x83], &ak.to_bytes(), &nk.to_bytes()],
    ))
}

fn append_bits(bits: &mut SecretScratch<bool>, bytes: &[u8], count: usize) {
    bits.extend((0..count).map(|i| (bytes[i / 8] >> (i % 8)) & 1 != 0));
}

/// `Commit^ivk_rivk(ak, nk)`: `None` when the commitment is `⊥` or zero.
pub fn commit_ivk(ak: &Fp, nk: &Fp, rivk: &Fq) -> Option<Fp> {
    let mut bits = SecretScratch::new();
    append_bits(&mut bits, &ak.to_bytes(), 255);
    append_bits(&mut bits, &nk.to_bytes(), 255);
    commit_ivk_domain()
        .short_commit(&bits, rivk)
        .filter(|ivk| !ivk.is_zero())
}

/// The spend authorizing key of a spending key: `H^ask(sk)`, negated when the encoding of
/// `[ask] G` has its sign bit set. `None` when `H^ask(sk) = 0`.
pub fn spend_authorizing_key(sk: &[u8; 32]) -> Option<Fq> {
    let ask = h_ask(sk);
    if ask.is_zero() {
        return None;
    }
    let (_, y) = spend_auth_base().mul(&ask).to_affine()?;
    Some(Fq::select(y.is_odd(), -ask, ask))
}

/// Which incoming viewing key of a full viewing key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    External,
    Internal,
}

/// `DiversifyHash^Orchard(d)`.
pub fn diversify_hash(d: &[u8; 11]) -> Point {
    let p = hash_to_curve("z.cash:Orchard-gd", d);
    if p.is_identity() {
        hash_to_curve("z.cash:Orchard-gd", b"")
    } else {
        p
    }
}

/// An Orchard full viewing key `(ak, nk, rivk)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FullViewingKey {
    pub ak: Fp,
    pub nk: Fp,
    pub rivk: Fq,
}

impl FullViewingKey {
    /// The full viewing key of a spending key (the `use_qsk = false` derivation of 4.2.3,
    /// which every wallet used before ZIP 2005). `None` when the key must be discarded:
    /// `ask = 0` or an incoming viewing key is `0` or `⊥`.
    pub fn from_spending_key(sk: &[u8; 32]) -> Option<Self> {
        let ask = h_ask(sk);
        if ask.is_zero() {
            return None;
        }
        let fvk = Self {
            ak: spend_auth_base().mul(&ask).extract(),
            nk: h_nk(sk),
            rivk: h_rivk(sk),
        };
        fvk.validated()
    }

    /// The full viewing key of the `use_qsk = true` derivation of ZIP 2005: `ak` comes
    /// from elsewhere (a distributed key generation or a hardware wallet) and
    /// `rivk = H^rivk_ext_qk(ak, nk)` with `qk = H^qk(H^qsk(sk))`.
    pub fn from_qsk(sk: &[u8; 32], ak: &Fp) -> Option<Self> {
        let nk = h_nk(sk);
        let mut qsk = h_qsk(sk);
        let qk = SecretBuffer(h_qk(&qsk));
        wipe(&mut qsk);
        Self {
            ak: *ak,
            nk,
            rivk: h_rivk_ext(&qk, ak, &nk),
        }
        .validated()
    }

    fn validated(self) -> Option<Self> {
        (self.ivk(Scope::External).is_some() && self.ivk(Scope::Internal).is_some()).then_some(self)
    }

    /// `ak || nk || rivk`, the raw encoding (5.6.4.4) and the Orchard item of a unified
    /// full viewing key.
    pub fn to_bytes(&self) -> [u8; 96] {
        let mut out = [0u8; 96];
        out[..32].copy_from_slice(&self.ak.to_bytes());
        out[32..64].copy_from_slice(&self.nk.to_bytes());
        out[64..].copy_from_slice(&self.rivk.to_bytes());
        out
    }

    /// Strict decoding: canonical field elements, `ak` the `x` coordinate of a point (its
    /// sign bit clear), both incoming viewing keys valid.
    pub fn from_bytes(bytes: &[u8; 96]) -> Option<Self> {
        let ak_bytes: [u8; 32] = bytes[..32].try_into().unwrap();
        if ak_bytes[31] & 0x80 != 0 {
            return None;
        }
        Point::from_bytes_nonidentity(&ak_bytes)?;
        Self {
            ak: Fp::from_bytes(&ak_bytes)?,
            nk: Fp::from_bytes(bytes[32..64].try_into().unwrap())?,
            rivk: Fq::from_bytes(bytes[64..].try_into().unwrap())?,
        }
        .validated()
    }

    /// The `Commit^ivk` randomness of a scope.
    pub fn rivk(&self, scope: Scope) -> Fq {
        match scope {
            Scope::External => self.rivk,
            Scope::Internal => h_rivk_int(&self.rivk, &self.ak, &self.nk),
        }
    }

    /// The incoming viewing key (`KA^Orchard` private key) of a scope.
    pub fn ivk(&self, scope: Scope) -> Option<Fp> {
        commit_ivk(&self.ak, &self.nk, &self.rivk(scope))
    }

    /// `(dk, ovk)` of a scope: `PRF^expand_rivk([0x82] || ak || nk)` split in halves.
    pub fn dk_ovk(&self, scope: Scope) -> ([u8; 32], [u8; 32]) {
        let wide = SecretBuffer(prf_expand(
            &self.rivk(scope).to_bytes(),
            &[&[0x82], &self.ak.to_bytes(), &self.nk.to_bytes()],
        ));
        (
            wide[..32].try_into().unwrap(),
            wide[32..].try_into().unwrap(),
        )
    }

    /// The diversifier at an index: `FF1-AES256_dk("", I2LEBSP_88(index))`.
    pub fn diversifier(&self, index: &[u8; 11], scope: Scope) -> [u8; 11] {
        let keys = SecretBuffer(self.dk_ovk(scope));
        ff1_aes256_encrypt_88(&keys.0.0, index)
    }

    /// The raw address `d || pk_d` for a diversifier.
    pub fn address(&self, d: &[u8; 11], scope: Scope) -> Option<[u8; 43]> {
        let ivk = self.ivk(scope)?;
        let pk_d = diversify_hash(d).mul(&Fq::from_base(ivk));
        let mut out = [0u8; 43];
        out[..11].copy_from_slice(d);
        out[11..].copy_from_slice(&pk_d.to_bytes());
        Some(out)
    }

    /// The address at diversifier index 0.
    pub fn default_address(&self, scope: Scope) -> Option<[u8; 43]> {
        self.address(&self.diversifier(&[0; 11], scope), scope)
    }

    /// The ZIP 32 fingerprint `BLAKE2b-256("ZcashOrchardFVFP", ak || nk || rivk)`.
    pub fn fingerprint(&self) -> [u8; 32] {
        blake2b_256(b"ZcashOrchardFVFP", &[&self.to_bytes()])
    }
}

// ============================================================================
// Notes
// ============================================================================

/// The note plaintext version: lead byte `0x02` (Orchard pool) or `0x03` (Ironwood pool,
/// quantum-recoverable per ZIP 2005).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoteVersion {
    V2,
    V3,
}

impl NoteVersion {
    pub fn lead_byte(self) -> u8 {
        match self {
            Self::V2 => 0x02,
            Self::V3 => 0x03,
        }
    }
}

/// `H^psi_rseed(rho) = ToBase(PRF^expand_rseed([0x09] || rho))`.
pub fn note_psi(rseed: &[u8; 32], rho: &Fp) -> Fp {
    to_base(prf_expand(rseed, &[&[0x09], &rho.to_bytes()]))
}

/// `H^esk_rseed(rho) = ToScalar(PRF^expand_rseed([0x04] || rho))`.
pub fn note_esk(rseed: &[u8; 32], rho: &Fp) -> Fq {
    to_scalar(prf_expand(rseed, &[&[0x04], &rho.to_bytes()]))
}

/// The `pre_rcm` input of `H^rcm` (ZIP 2005):
/// `[0x0B] || g_d* || pk_d* || I2LEOSP_64(v) || rho || psi`, 137 bytes.
pub fn pre_rcm(g_d: &[u8; 32], pk_d: &[u8; 32], value: u64, rho: &Fp, psi: &Fp) -> [u8; 137] {
    let mut out = [0u8; 137];
    out[0] = 0x0b;
    out[1..33].copy_from_slice(g_d);
    out[33..65].copy_from_slice(pk_d);
    out[65..73].copy_from_slice(&value.to_le_bytes());
    out[73..105].copy_from_slice(&rho.to_bytes());
    out[105..].copy_from_slice(&psi.to_bytes());
    out
}

/// `Derive_rcm^Orchard`: for lead byte `0x02`, `ToScalar(PRF^expand_rseed([0x05] || rho))`;
/// for `0x03`, `H^rcm_rseed(g_d*, pk_d*, v, rho, psi)`.
pub fn note_rcm(
    version: NoteVersion,
    rseed: &[u8; 32],
    g_d: &[u8; 32],
    pk_d: &[u8; 32],
    value: u64,
    rho: &Fp,
    psi: &Fp,
) -> Fq {
    match version {
        NoteVersion::V2 => to_scalar(prf_expand(rseed, &[&[0x05], &rho.to_bytes()])),
        NoteVersion::V3 => to_scalar(prf_expand(rseed, &[&pre_rcm(g_d, pk_d, value, rho, psi)])),
    }
}

/// `NoteCommit^Orchard_rcm(g_d*, pk_d*, v, rho, psi)`; `None` is `⊥`.
pub fn note_commitment(
    g_d: &[u8; 32],
    pk_d: &[u8; 32],
    value: u64,
    rho: &Fp,
    psi: &Fp,
    rcm: &Fq,
) -> Option<Point> {
    let mut bits = SecretScratch::new();
    append_bits(&mut bits, g_d, 256);
    append_bits(&mut bits, pk_d, 256);
    append_bits(&mut bits, &value.to_le_bytes(), 64);
    append_bits(&mut bits, &rho.to_bytes(), 255);
    append_bits(&mut bits, &psi.to_bytes(), 255);
    note_commit_domain().commit(&bits, rcm)
}

/// `PRF^nfOrchard_nk(rho) = Poseidon(nk, rho)`.
pub fn prf_nf(nk: &Fp, rho: &Fp) -> Fp {
    poseidon::hash2(*nk, *rho)
}

/// `DeriveNullifier_nk(rho, psi, cm) = Extract_P([(PRF^nf_nk(rho) + psi) mod p] K + cm)`.
pub fn derive_nullifier(nk: &Fp, rho: &Fp, psi: &Fp, cm: &Point) -> Fp {
    let scalar = Fq::from_base(prf_nf(nk, rho) + *psi);
    nullifier_base().mul(&scalar).add(cm).extract()
}

/// An Orchard-protocol note.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Note {
    /// The recipient address `d || pk_d`.
    pub recipient: [u8; 43],
    pub value: u64,
    /// The nullifier of the note spent in the same Action.
    pub rho: Fp,
    pub rseed: [u8; 32],
    pub version: NoteVersion,
}

impl Note {
    /// `repr_P(g_d)`.
    pub fn g_d(&self) -> [u8; 32] {
        diversify_hash(self.recipient[..11].try_into().unwrap()).to_bytes()
    }

    /// `repr_P(pk_d)`.
    pub fn pk_d(&self) -> [u8; 32] {
        self.recipient[11..].try_into().unwrap()
    }

    pub fn psi(&self) -> Fp {
        note_psi(&self.rseed, &self.rho)
    }

    pub fn rcm(&self) -> Fq {
        note_rcm(
            self.version,
            &self.rseed,
            &self.g_d(),
            &self.pk_d(),
            self.value,
            &self.rho,
            &self.psi(),
        )
    }

    /// The note commitment `cm`; `None` is `⊥`.
    pub fn commitment(&self) -> Option<Point> {
        note_commitment(
            &self.g_d(),
            &self.pk_d(),
            self.value,
            &self.rho,
            &self.psi(),
            &self.rcm(),
        )
    }

    /// `cm_x = Extract_P(cm)`, the leaf of the note commitment tree.
    pub fn cmx(&self) -> Option<Fp> {
        self.commitment().map(|cm| cm.extract())
    }

    /// The nullifier under a nullifier deriving key.
    pub fn nullifier(&self, nk: &Fp) -> Option<Fp> {
        Some(derive_nullifier(
            nk,
            &self.rho,
            &self.psi(),
            &self.commitment()?,
        ))
    }
}

// ============================================================================
// The note commitment tree (Sinsemilla, as on chain today)
// ============================================================================

/// `MerkleCRH^Orchard(layer, left, right)` with `layer = 31 - l` the height of the
/// children: `SinsemillaHash` of `I2LEBSP_10(layer) || left || right`, and `0` for `⊥`.
pub fn merkle_crh(layer: u8, left: &Fp, right: &Fp) -> Fp {
    let mut bits = SecretScratch::new();
    append_bits(&mut bits, &[layer, 0], 10);
    append_bits(&mut bits, &left.to_bytes(), 255);
    append_bits(&mut bits, &right.to_bytes(), 255);
    merkle_crh_domain().hash(&bits).unwrap_or(Fp::ZERO)
}

/// `Uncommitted^Orchard = 2`, the value of an empty leaf.
pub fn uncommitted_leaf() -> Fp {
    Fp::from_u64(2)
}

/// Roots of the empty subtrees of height `0..=32`.
pub fn empty_roots() -> Vec<Fp> {
    let mut out = Vec::with_capacity(MERKLE_DEPTH + 1);
    let mut node = uncommitted_leaf();
    out.push(node);
    for layer in 0..MERKLE_DEPTH {
        node = merkle_crh(layer as u8, &node, &node);
        out.push(node);
    }
    out
}

/// The root of the subtree reached from a leaf at `position` along an authentication path
/// (siblings from the leaf upward); the whole tree for a path of [`MERKLE_DEPTH`] nodes.
pub fn merkle_root(leaf: &Fp, position: u32, path: &[Fp]) -> Fp {
    assert!(path.len() <= MERKLE_DEPTH);
    let mut node = *leaf;
    for (layer, sibling) in path.iter().enumerate() {
        node = if (position >> layer) & 1 == 0 {
            merkle_crh(layer as u8, &node, sibling)
        } else {
            merkle_crh(layer as u8, sibling, &node)
        };
    }
    node
}

// ============================================================================
// ZIP 32
// ============================================================================

/// First hardened child index.
pub const ZIP32_HARDENED: u32 = 0x8000_0000;
/// ZIP 32 purpose of shielded keys.
pub const ZIP32_PURPOSE: u32 = 32;
/// SLIP 44 coin type of Zcash mainnet; testnet uses 1.
pub const COIN_TYPE_MAINNET: u32 = 133;
/// Seed lengths ZIP 32 admits, in bytes.
pub const ZIP32_SEED_BYTES: core::ops::RangeInclusive<usize> = 32..=252;

/// An Orchard extended spending key. Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub struct ExtendedSpendingKey {
    pub depth: u8,
    pub parent_tag: [u8; 4],
    pub child_index: u32,
    pub chain_code: [u8; 32],
    pub sk: [u8; 32],
}

impl Drop for ExtendedSpendingKey {
    fn drop(&mut self) {
        wipe(&mut self.sk);
        wipe(&mut self.chain_code);
    }
}

impl ExtendedSpendingKey {
    fn from_i(mut i: [u8; 64], depth: u8, parent_tag: [u8; 4], child_index: u32) -> Self {
        let out = Self {
            depth,
            parent_tag,
            child_index,
            sk: i[..32].try_into().unwrap(),
            chain_code: i[32..].try_into().unwrap(),
        };
        wipe(&mut i);
        out
    }

    /// The master key: `I = BLAKE2b-512("ZcashIP32Orchard", seed)`, `sk = I_L`, `c = I_R`.
    /// `None` for a seed length outside 32..=252 bytes.
    pub fn master(seed: &[u8]) -> Option<Self> {
        ZIP32_SEED_BYTES
            .contains(&seed.len())
            .then(|| Self::from_i(blake2b_512(b"ZcashIP32Orchard", &[seed]), 0, [0; 4], 0))
    }

    /// The hardened child `i >= 2^31`:
    /// `I = PRF^expand_c([0x81] || sk || I2LEOSP_32(i))`. `None` for a non-hardened index
    /// or a parent that is not a valid spending key.
    pub fn child(&self, index: u32) -> Option<Self> {
        if index < ZIP32_HARDENED || self.depth == u8::MAX {
            return None;
        }
        let tag: [u8; 4] = FullViewingKey::from_spending_key(&self.sk)?.fingerprint()[..4]
            .try_into()
            .unwrap();
        let i = prf_expand(&self.chain_code, &[&[0x81], &self.sk, &index.to_le_bytes()]);
        Some(Self::from_i(i, self.depth + 1, tag, index))
    }

    /// The key at `m / path`.
    pub fn derive(seed: &[u8], path: &[u32]) -> Option<Self> {
        let mut key = Self::master(seed)?;
        for &index in path {
            key = key.child(index)?;
        }
        Some(key)
    }

    /// The account key `m / 32' / coin_type' / account'`.
    pub fn account(seed: &[u8], coin_type: u32, account: u32) -> Option<Self> {
        if coin_type >= ZIP32_HARDENED || account >= ZIP32_HARDENED {
            return None;
        }
        Self::derive(
            seed,
            &[
                ZIP32_PURPOSE | ZIP32_HARDENED,
                coin_type | ZIP32_HARDENED,
                account | ZIP32_HARDENED,
            ],
        )
    }

    /// `depth || parent tag || I2LEOSP_32(index) || c || sk`, 73 bytes.
    pub fn to_bytes(&self) -> [u8; 73] {
        let mut out = [0u8; 73];
        out[0] = self.depth;
        out[1..5].copy_from_slice(&self.parent_tag);
        out[5..9].copy_from_slice(&self.child_index.to_le_bytes());
        out[9..41].copy_from_slice(&self.chain_code);
        out[41..].copy_from_slice(&self.sk);
        out
    }
}

/// The spending key bytes along a hardened path, without the fingerprints: what the
/// relation computes. `None` for a seed of the wrong length or a non-hardened index.
pub fn zip32_spending_key(seed: &[u8], path: &[u32]) -> Option<[u8; 32]> {
    if !ZIP32_SEED_BYTES.contains(&seed.len()) || path.iter().any(|&i| i < ZIP32_HARDENED) {
        return None;
    }
    let mut i = blake2b_512(b"ZcashIP32Orchard", &[seed]);
    for index in path {
        let next = prf_expand(&i[32..], &[&[0x81], &i[..32], &index.to_le_bytes()]);
        wipe(&mut i);
        i = next;
    }
    let sk: [u8; 32] = i[..32].try_into().unwrap();
    wipe(&mut i);
    Some(sk)
}

// ============================================================================
// RedPallas
// ============================================================================

fn h_star(parts: &[&[u8]]) -> Fq {
    to_scalar(blake2b_512(b"Zcash_RedPallasH", parts))
}

/// The verification key `repr_P([sk] G^Orchard)` of a spend authorization signing key.
pub fn redpallas_public_key(sk: &Fq) -> [u8; 32] {
    spend_auth_base().mul(sk).to_bytes()
}

/// `SpendAuthSig^Orchard.Sign` (RedDSA, 5.4.7): `randomness` is 80 uniform secret bytes.
pub fn redpallas_sign(sk: &Fq, message: &[u8], randomness: &[u8; 80]) -> [u8; 64] {
    let vk = redpallas_public_key(sk);
    let nonce = SecretBuffer(h_star(&[randomness, &vk, message]));
    let r = spend_auth_base().mul(&nonce).to_bytes();
    let c = h_star(&[&r, &vk, message]);
    let s = *nonce + c * *sk;
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&r);
    out[32..].copy_from_slice(&s.to_bytes());
    out
}

/// `SpendAuthSig^Orchard.Validate`: `[S] G = R + [c] vk` with canonical `R`, `S` and `vk`.
pub fn redpallas_verify(vk: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    let r_bytes: [u8; 32] = signature[..32].try_into().unwrap();
    let (Some(a), Some(r), Some(s)) = (
        Point::from_bytes(vk),
        Point::from_bytes(&r_bytes),
        Fq::from_bytes(signature[32..].try_into().unwrap()),
    ) else {
        return false;
    };
    let c = h_star(&[&r_bytes, vk, message]);
    spend_auth_base().mul(&s) == r.add(&a.mul(&c))
}

#[cfg(test)]
mod tests {
    use super::super::vectors::{EMPTY_ROOTS, KEY_COMPONENTS, MERKLE_TREE, ZIP32, hex32, unhex};
    use super::*;

    fn fp(s: &str) -> Fp {
        Fp::from_bytes(&hex32(s)).unwrap()
    }

    #[test]
    fn key_components_vectors() {
        assert_eq!(KEY_COMPONENTS.len(), 10);
        for tv in KEY_COMPONENTS {
            let sk = hex32(tv.sk);
            let ask = spend_authorizing_key(&sk).unwrap();
            assert_eq!(ask.to_bytes(), hex32(tv.ask));
            let fvk = FullViewingKey::from_spending_key(&sk).unwrap();
            assert_eq!(fvk.ak.to_bytes(), hex32(tv.ak));
            assert_eq!(redpallas_public_key(&ask), hex32(tv.ak));
            assert_eq!(fvk.nk.to_bytes(), hex32(tv.nk));
            assert_eq!(fvk.rivk.to_bytes(), hex32(tv.rivk));
            assert_eq!(fvk.ivk(Scope::External).unwrap().to_bytes(), hex32(tv.ivk));
            let (dk, ovk) = fvk.dk_ovk(Scope::External);
            assert_eq!(dk, hex32(tv.dk));
            assert_eq!(ovk, hex32(tv.ovk));
            let address = fvk.default_address(Scope::External).unwrap();
            assert_eq!(address[..11], unhex(tv.default_d)[..]);
            assert_eq!(address[11..], hex32(tv.default_pk_d)[..]);
            assert_eq!(
                fvk.rivk(Scope::Internal).to_bytes(),
                hex32(tv.internal_rivk)
            );
            assert_eq!(
                fvk.ivk(Scope::Internal).unwrap().to_bytes(),
                hex32(tv.internal_ivk)
            );
            let (dk, ovk) = fvk.dk_ovk(Scope::Internal);
            assert_eq!(dk, hex32(tv.internal_dk));
            assert_eq!(ovk, hex32(tv.internal_ovk));
            assert_eq!(FullViewingKey::from_bytes(&fvk.to_bytes()), Some(fvk));

            // The vectors' notes use the lead byte 0x02 derivation of rcm.
            let note = Note {
                recipient: address,
                value: tv.note_v,
                rho: fp(tv.note_rho),
                rseed: hex32(tv.note_rseed),
                version: NoteVersion::V2,
            };
            assert_eq!(note.cmx().unwrap().to_bytes(), hex32(tv.note_cmx));
            assert_eq!(
                note.nullifier(&fvk.nk).unwrap().to_bytes(),
                hex32(tv.note_nf)
            );
            // The recoverable derivation commits to the same fields with another rcm.
            let v3 = Note {
                version: NoteVersion::V3,
                ..note
            };
            assert_ne!(v3.cmx(), note.cmx());
            assert_ne!(v3.nullifier(&fvk.nk), note.nullifier(&fvk.nk));
        }
    }

    #[test]
    fn full_viewing_key_decoding_is_strict() {
        let fvk = FullViewingKey::from_spending_key(&hex32(KEY_COMPONENTS[0].sk)).unwrap();
        let good = fvk.to_bytes();
        assert!(FullViewingKey::from_bytes(&good).is_some());
        let mut sign = good;
        sign[31] |= 0x80;
        assert!(FullViewingKey::from_bytes(&sign).is_none());
        let mut nk = good;
        nk[32..64].fill(0xff);
        assert!(FullViewingKey::from_bytes(&nk).is_none());
        let mut rivk = good;
        rivk[64..].fill(0xff);
        assert!(FullViewingKey::from_bytes(&rivk).is_none());
        let mut zero_ak = good;
        zero_ak[..32].fill(0);
        assert!(FullViewingKey::from_bytes(&zero_ak).is_none());
    }

    #[test]
    fn merkle_vectors() {
        assert_eq!(EMPTY_ROOTS.len(), MERKLE_DEPTH + 1);
        let roots = empty_roots();
        for (got, want) in roots.iter().zip(EMPTY_ROOTS) {
            assert_eq!(got.to_bytes(), hex32(want));
        }
        // Each vector is a subtree of height 4 over the listed leaves, with the path of
        // each leaf in turn.
        for (leaves, paths, root) in MERKLE_TREE {
            assert_eq!(leaves.len(), 16);
            for (position, (leaf, path)) in leaves.iter().zip(paths.iter()).enumerate() {
                let path: Vec<Fp> = path.iter().map(|s| fp(s)).collect();
                assert_eq!(path.len(), 4);
                assert_eq!(
                    merkle_root(&fp(leaf), position as u32, &path).to_bytes(),
                    hex32(root)
                );
                let mut wrong = path.clone();
                wrong[2] = wrong[2] + Fp::ONE;
                assert_ne!(
                    merkle_root(&fp(leaf), position as u32, &wrong).to_bytes(),
                    hex32(root)
                );
            }
        }
    }

    #[test]
    fn zip32_vectors() {
        let seed: Vec<u8> = (0..32).collect();
        let paths: [&[u32]; 4] = [
            &[],
            &[1 | ZIP32_HARDENED],
            &[1 | ZIP32_HARDENED, 2 | ZIP32_HARDENED],
            &[1 | ZIP32_HARDENED, 2 | ZIP32_HARDENED, 3 | ZIP32_HARDENED],
        ];
        assert_eq!(ZIP32.len(), paths.len());
        for (path, (sk, c, xsk, fingerprint)) in paths.iter().zip(ZIP32) {
            let key = ExtendedSpendingKey::derive(&seed, path).unwrap();
            assert_eq!(key.sk, hex32(sk));
            assert_eq!(key.chain_code, hex32(c));
            assert_eq!(key.to_bytes().to_vec(), unhex(xsk));
            assert_eq!(
                FullViewingKey::from_spending_key(&key.sk)
                    .unwrap()
                    .fingerprint(),
                hex32(fingerprint)
            );
            assert_eq!(zip32_spending_key(&seed, path), Some(hex32(sk)));
        }
        assert!(ExtendedSpendingKey::master(&seed[..31]).is_none());
        assert!(
            ExtendedSpendingKey::master(&seed)
                .unwrap()
                .child(5)
                .is_none()
        );
        assert!(zip32_spending_key(&seed, &[5]).is_none());
        assert_eq!(
            ExtendedSpendingKey::account(&seed, COIN_TYPE_MAINNET, 0)
                .unwrap()
                .sk,
            zip32_spending_key(
                &seed,
                &[32 | ZIP32_HARDENED, 133 | ZIP32_HARDENED, ZIP32_HARDENED]
            )
            .unwrap()
        );
    }

    #[test]
    fn redpallas_roundtrip_and_rejections() {
        let ask = spend_authorizing_key(&hex32(KEY_COMPONENTS[1].sk)).unwrap();
        let vk = redpallas_public_key(&ask);
        let sig = redpallas_sign(&ask, b"message", &[7; 80]);
        assert!(redpallas_verify(&vk, b"message", &sig));
        assert!(!redpallas_verify(&vk, b"messagf", &sig));
        for at in [0, 31, 32, 63] {
            let mut bad = sig;
            bad[at] ^= 1;
            assert!(!redpallas_verify(&vk, b"message", &bad), "byte {at}");
        }
        let other = redpallas_public_key(&(ask + Fq::ONE));
        assert!(!redpallas_verify(&other, b"message", &sig));
        // A rerandomized key verifies a signature made with the rerandomized secret.
        let alpha = Fq::from_u64(123_456_789);
        let rk = spend_auth_base()
            .mul(&ask)
            .add(&spend_auth_base().mul(&alpha))
            .to_bytes();
        let sig = redpallas_sign(&(ask + alpha), b"m", &[9; 80]);
        assert!(redpallas_verify(&rk, b"m", &sig));
        // A non-canonical S is rejected.
        let mut high = sig;
        high[32..].fill(0xff);
        assert!(!redpallas_verify(&rk, b"m", &high));
    }

    #[test]
    fn qsk_derivation_is_domain_separated() {
        let sk = hex32(KEY_COMPONENTS[2].sk);
        let legacy = FullViewingKey::from_spending_key(&sk).unwrap();
        let qsk = FullViewingKey::from_qsk(&sk, &legacy.ak).unwrap();
        assert_eq!(qsk.ak, legacy.ak);
        assert_eq!(qsk.nk, legacy.nk);
        assert_ne!(qsk.rivk, legacy.rivk);
        assert_ne!(qsk.ivk(Scope::External), legacy.ivk(Scope::External));
        // rivk depends on every input of H^rivk_ext.
        let qk = h_qk(&h_qsk(&sk));
        assert_eq!(qsk.rivk, h_rivk_ext(&qk, &legacy.ak, &legacy.nk));
        assert_ne!(qsk.rivk, h_rivk_ext(&qk, &legacy.nk, &legacy.ak));
        assert_ne!(h_qsk(&sk), sk);
    }
}
