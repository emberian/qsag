//! Ephemeral `Compact1122` Post-Quantum Biscuit public-key capability delegation chains.
//!
//! Each delegation hop carries a 32-byte `next_pk_root` commitment plus a 1,122-byte
//! `FrontierSumFts` (`FrontierFtsProfile::Compact1122`) signature (`1,154 B/hop` of
//! cryptographic witness overhead, 256-bit chain/tree nodes -> 128-bit Grover post-quantum
//! preimage security with zero lattice or number-theoretic assumptions) and conjunctive
//! first-party [`Caveat`] predicates.
//!
//! Security invariants:
//! - **Offline third-party public-key attenuation:** Any holder of the move-only
//!   [`PqBiscuitStepKey`] can append narrower [`Caveat`]s offline and delegate to a fresh
//!   ephemeral `Compact1122` hop key without contacting the issuer or sharing any symmetric
//!   secret with the verifier.
//! - **Compile-time & runtime one-time key discipline:** [`PqBiscuitStepKey::attenuate`] and
//!   [`PqBiscuitStepKey::seal`] consume `self` by value, and [`PqBiscuitAuthorityKey::mint`]
//!   monotonically advances `next_leaf` across a Merkle tree of up to `2^8` single-use
//!   `Compact1122` authority leaves under one persistent 105-byte [`PqBiscuitAuthorityPublicKey`].
//! - **Mandatory terminal sealing & optional PoP request binding:** Open chains cannot be
//!   verified until sealed by the final holder (`seal`), preventing in-transit caveat
//!   appendage; passing `Some(&request)` binds the terminal signature to the exact
//!   [`CapabilityRequest`].

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_accel::AcceleratorBackend;
use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::wipe::{SecretBuffer, SecretBytes, SecretVec};
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsPublicKey,
    FrontierFtsSignature, FrontierFtsSigningKey, FtsEpochWal, verify_frontier_fts,
};

use crate::macaroon::{CapabilityError, CapabilityRequest, Caveat, MAX_CAVEATS};

/// Exact cryptographic witness size per delegation hop: `32 B` `next_pk_root` + `1,122 B`
/// `Compact1122` signature (`1,154 B`).
pub const PQ_BISCUIT_HOP_CRYPTO_BYTES: usize = 32 + 1122;

/// Maximum number of public-key delegation blocks (`authority` + up to 15 attenuations).
pub const MAX_BISCUIT_HOPS: usize = 16;

/// Maximum Merkle height for a multi-mint [`PqBiscuitAuthorityKey`] (`2^8 = 256` root mints).
pub const MAX_AUTHORITY_TREE_HEIGHT: u8 = 8;

const BISCUIT_WIRE_MAGIC: &[u8; 8] = b"QSBSC001";
const AUTHORITY_PK_MAGIC: &[u8; 8] = b"QSBSCPK1";
const AUTHORITY_SK_MAGIC: &[u8; 8] = b"QSBSCAK1";
const STEP_SK_MAGIC: &[u8; 8] = b"QSBSCSK1";
const COMPACT1122_SIG_BYTES: usize = 1122;

struct OneShotEphemeralWal {
    expected_key: [u8; 32],
    spent: bool,
}

impl FtsEpochWal for OneShotEphemeralWal {
    fn uses_completed(&self, key: &[u8; 32]) -> Result<u8, FrontierFtsError> {
        if !ct_eq_bytes(key, &self.expected_key) {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        Ok(u8::from(self.spent))
    }

    fn reserve_use(&mut self, key: &[u8; 32], next: u8) -> Result<(), FrontierFtsError> {
        if self.spent || next != 1 || !ct_eq_bytes(key, &self.expected_key) {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        self.spent = true;
        Ok(())
    }
}

fn hop_pk_seed(token_id: &[u8; 32], audience: &[u8; 32], hop_index: u16) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.BISCUIT.HOP.PKSEED.V1",
        &[token_id, audience, &hop_index.to_be_bytes()],
    )
}

fn authority_leaf_seeds(
    master_seed: &[u8; 32],
    authority_id: &[u8; 32],
    leaf_index: u32,
) -> (SecretBytes<32>, SecretBytes<32>) {
    let idx_be = leaf_index.to_be_bytes();
    let sk_seed = SecretBuffer(cshake256_framed_32(
        b"QSAG.BISCUIT.AUTH.SKSEED.V1",
        &[master_seed, authority_id, &idx_be],
    ));
    let sk_prf = SecretBuffer(cshake256_framed_32(
        b"QSAG.BISCUIT.AUTH.SKPRF.V1",
        &[master_seed, authority_id, &idx_be],
    ));
    (sk_seed, sk_prf)
}

fn authority_merkle_leaf_hash(
    authority_id: &[u8; 32],
    pk_seed: &[u8; 32],
    leaf_index: u32,
    leaf_pk_root: &[u8; 32],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.BISCUIT.AUTH.LEAF.V1",
        &[
            authority_id,
            pk_seed,
            &leaf_index.to_be_bytes(),
            leaf_pk_root,
        ],
    )
}

fn authority_merkle_parent_hash(
    authority_id: &[u8; 32],
    layer: u8,
    left: &[u8; 32],
    right: &[u8; 32],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.BISCUIT.AUTH.NODE.V1",
        &[authority_id, &[layer], left, right],
    )
}

fn encode_first_party_caveats(caveats: &[Caveat]) -> Result<Vec<u8>, CapabilityError> {
    if caveats.len() > MAX_CAVEATS {
        return Err(CapabilityError::TooManyCaveats);
    }
    let mut out = Vec::with_capacity(caveats.len() * 18);
    for caveat in caveats {
        if matches!(caveat, Caveat::BindToParent(_) | Caveat::ThirdParty(_)) {
            return Err(CapabilityError::Denied);
        }
        let (buf, len) = caveat.encoded();
        out.extend_from_slice(&buf[..len]);
    }
    Ok(out)
}

fn decode_first_party_caveats(
    bytes: &[u8],
    pos: &mut usize,
    end: usize,
    count: usize,
) -> Result<Vec<Caveat>, CapabilityError> {
    if count > MAX_CAVEATS {
        return Err(CapabilityError::TooManyCaveats);
    }
    let bad = CapabilityError::Malformed;
    let mut caveats = Vec::with_capacity(count);
    for _ in 0..count {
        let header = bytes
            .get(*pos..*pos + 2)
            .filter(|_| *pos + 2 <= end)
            .ok_or(bad)?;
        let len = usize::from(header[1]);
        *pos += 2;
        let value = bytes
            .get(*pos..*pos + len)
            .filter(|_| *pos + len <= end)
            .ok_or(bad)?;
        let caveat = match (header[0], len) {
            (1, 8) => Caveat::ExpiresAt(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
            (2, 8) => Caveat::NotBefore(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
            (3, 32) => Caveat::Resource(value.try_into().map_err(|_| bad)?),
            (4, 8) => Caveat::Actions(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
            (5, 16) => Caveat::MaxAmount(u128::from_be_bytes(value.try_into().map_err(|_| bad)?)),
            _ => return Err(bad),
        };
        caveats.push(caveat);
        *pos += len;
    }
    Ok(caveats)
}

pub(crate) fn evaluate_first_party_caveat(caveat: &Caveat, r: &CapabilityRequest) -> bool {
    match caveat {
        Caveat::ExpiresAt(t) => r.now < *t,
        Caveat::NotBefore(t) => r.now >= *t,
        Caveat::Resource(v) => ct_eq_bytes(v, &r.resource),
        Caveat::Actions(mask) => r.actions & !mask == 0,
        Caveat::MaxAmount(max) => r.amount <= *max,
        Caveat::BindToParent(_) | Caveat::ThirdParty(_) => false,
    }
}

/// Canonical digest of a [`CapabilityRequest`] for Proof-of-Possession request-bound seals.
pub fn capability_request_digest(r: &CapabilityRequest) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.BISCUIT.REQ.V1",
        &[
            &r.audience,
            &r.resource,
            &r.actions.to_be_bytes(),
            &r.amount.to_be_bytes(),
            &r.now.to_be_bytes(),
        ],
    )
}

fn hop_signing_message(
    prev_chain_digest: &[u8; 32],
    token_id: &[u8; 32],
    audience: &[u8; 32],
    hop_index: u16,
    encoded_caveats: &[u8],
    next_pk_root: &[u8; 32],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.BISCUIT.HOP.MSG.V1",
        &[
            prev_chain_digest,
            token_id,
            audience,
            &hop_index.to_be_bytes(),
            encoded_caveats,
            next_pk_root,
        ],
    )
}

fn next_chain_digest(hop_msg: &[u8; 32], sig_bytes: &[u8; COMPACT1122_SIG_BYTES]) -> [u8; 32] {
    cshake256_framed_32(b"QSAG.BISCUIT.CHAIN.V1", &[hop_msg, sig_bytes])
}

fn seal_signing_message(
    chain_digest: &[u8; 32],
    hop_index: u16,
    bound_request_digest: Option<&[u8; 32]>,
) -> [u8; 32] {
    let mode = [u8::from(bound_request_digest.is_some())];
    let req = bound_request_digest.copied().unwrap_or([0u8; 32]);
    cshake256_framed_32(
        b"QSAG.BISCUIT.SEAL.MSG.V1",
        &[chain_digest, &hop_index.to_be_bytes(), &mode, &req],
    )
}

/// Sign `msg` once with the `Compact1122` key of `(sk_seed, sk_prf, pk_seed)` and return
/// its public root with the signature. The secrets are borrowed, so the only copies
/// made here are the ones the signing key owns and erases.
fn sign_one_shot_compact1122<B: AcceleratorBackend>(
    sk_seed: &[u8; 32],
    sk_prf: &[u8; 32],
    pk_seed: [u8; 32],
    dp: &FrontierDpTable,
    msg: &[u8],
    hedging_nonce: &[u8; 32],
    accel: &B,
) -> Result<([u8; 32], [u8; COMPACT1122_SIG_BYTES]), CapabilityError> {
    if dp.params != FrontierFtsProfile::Compact1122.params() {
        return Err(CapabilityError::Denied);
    }
    let key = FrontierFtsSigningKey::keygen(
        FrontierFtsProfile::Compact1122,
        *sk_seed,
        *sk_prf,
        pk_seed,
        false,
        accel,
    );
    let pk_root: [u8; 32] = key
        .pk
        .root
        .as_slice()
        .try_into()
        .map_err(|_| CapabilityError::Malformed)?;
    let wal_key = key.wal_key();
    let mut key = key
        .attach_wal(Box::new(OneShotEphemeralWal {
            expected_key: wal_key,
            spent: false,
        }))
        .map_err(|_| CapabilityError::Denied)?;
    let sig = key
        .sign(dp, msg, hedging_nonce)
        .map_err(|_| CapabilityError::Denied)?;
    let raw = sig.to_bytes(FrontierFtsProfile::Compact1122);
    let sig_arr: [u8; COMPACT1122_SIG_BYTES] = raw
        .as_slice()
        .try_into()
        .map_err(|_| CapabilityError::Malformed)?;
    Ok((pk_root, sig_arr))
}

fn verify_compact1122_bytes(
    pk_seed: [u8; 32],
    pk_root: [u8; 32],
    dp: &FrontierDpTable,
    msg: &[u8],
    sig_bytes: &[u8; COMPACT1122_SIG_BYTES],
) -> Result<(), CapabilityError> {
    if dp.params != FrontierFtsProfile::Compact1122.params() {
        return Err(CapabilityError::Denied);
    }
    let pk = FrontierFtsPublicKey {
        profile: FrontierFtsProfile::Compact1122,
        pk_seed,
        root: pk_root.to_vec(),
    };
    let sig = FrontierFtsSignature::from_bytes(FrontierFtsProfile::Compact1122, sig_bytes)
        .map_err(|_| CapabilityError::InvalidTag)?;
    verify_frontier_fts(&pk, dp, msg, &sig).map_err(|_| CapabilityError::InvalidTag)
}

/// Persistent 105-byte (`8 B magic + 97 B payload`) post-quantum Biscuit authority public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PqBiscuitAuthorityPublicKey {
    pub authority_id: [u8; 32],
    pub pk_seed: [u8; 32],
    pub tree_height: u8,
    pub merkle_root: [u8; 32],
}

impl PqBiscuitAuthorityPublicKey {
    pub fn to_bytes(&self) -> [u8; 105] {
        let mut out = [0u8; 105];
        out[..8].copy_from_slice(AUTHORITY_PK_MAGIC);
        out[8..40].copy_from_slice(&self.authority_id);
        out[40..72].copy_from_slice(&self.pk_seed);
        out[72] = self.tree_height;
        out[73..105].copy_from_slice(&self.merkle_root);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CapabilityError> {
        if bytes.len() != 105
            || &bytes[..8] != AUTHORITY_PK_MAGIC
            || bytes[72] > MAX_AUTHORITY_TREE_HEIGHT
        {
            return Err(CapabilityError::Malformed);
        }
        Ok(Self {
            authority_id: bytes[8..40]
                .try_into()
                .map_err(|_| CapabilityError::Malformed)?,
            pk_seed: bytes[40..72]
                .try_into()
                .map_err(|_| CapabilityError::Malformed)?,
            tree_height: bytes[72],
            merkle_root: bytes[73..105]
                .try_into()
                .map_err(|_| CapabilityError::Malformed)?,
        })
    }
}

/// Merkle-bundled root issuer key capable of minting `2^tree_height` distinct post-quantum
/// [`PqBiscuit`] capabilities without signing twice with a leaf in this instance.
/// Persist and externally anchor the advanced mint counter before releasing a token:
/// restoring or cloning a secret snapshot can otherwise reuse a one-time leaf.
pub struct PqBiscuitAuthorityKey {
    master_seed: SecretBytes<32>,
    pk: PqBiscuitAuthorityPublicKey,
    leaf_roots: Vec<[u8; 32]>,
    merkle_layers: Vec<Vec<[u8; 32]>>,
    next_leaf: u32,
}

impl fmt::Debug for PqBiscuitAuthorityKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqBiscuitAuthorityKey")
            .field("authority_id", &self.pk.authority_id)
            .field("tree_height", &self.pk.tree_height)
            .field("next_leaf", &self.next_leaf)
            .field("master_seed", &"<REDACTED>")
            .finish()
    }
}

impl PqBiscuitAuthorityKey {
    pub fn keygen<B: AcceleratorBackend>(
        mut master_seed: [u8; 32],
        authority_id: [u8; 32],
        tree_height: u8,
        accel: &B,
    ) -> Result<Self, CapabilityError> {
        // Erases the caller's by-value seed on every return, including the refusal below.
        let master = SecretBuffer(&mut master_seed);
        if tree_height > MAX_AUTHORITY_TREE_HEIGHT {
            return Err(CapabilityError::Malformed);
        }
        let pk_seed = cshake256_framed_32(
            b"QSAG.BISCUIT.AUTH.PKSEED.V1",
            &[&**master, &authority_id, &[tree_height]],
        );
        let num_leaves = 1usize << tree_height;
        let mut leaf_roots = Vec::with_capacity(num_leaves);
        let mut level0 = Vec::with_capacity(num_leaves);
        for idx in 0..num_leaves as u32 {
            let (sk_seed, sk_prf) = authority_leaf_seeds(&master, &authority_id, idx);
            let leaf_key = FrontierFtsSigningKey::keygen(
                FrontierFtsProfile::Compact1122,
                *sk_seed,
                *sk_prf,
                pk_seed,
                false,
                accel,
            );
            let root: [u8; 32] = leaf_key
                .pk
                .root
                .as_slice()
                .try_into()
                .map_err(|_| CapabilityError::Malformed)?;
            leaf_roots.push(root);
            level0.push(authority_merkle_leaf_hash(
                &authority_id,
                &pk_seed,
                idx,
                &root,
            ));
        }
        let mut merkle_layers = Vec::with_capacity(usize::from(tree_height) + 1);
        merkle_layers.push(level0);
        for layer in 0..tree_height {
            let cur = &merkle_layers[usize::from(layer)];
            let mut parents = Vec::with_capacity(cur.len() / 2);
            for pair in cur.as_chunks::<2>().0 {
                parents.push(authority_merkle_parent_hash(
                    &authority_id,
                    layer,
                    &pair[0],
                    &pair[1],
                ));
            }
            merkle_layers.push(parents);
        }
        let merkle_root = merkle_layers[usize::from(tree_height)][0];
        Ok(Self {
            master_seed: SecretBuffer(**master),
            pk: PqBiscuitAuthorityPublicKey {
                authority_id,
                pk_seed,
                tree_height,
                merkle_root,
            },
            leaf_roots,
            merkle_layers,
            next_leaf: 0,
        })
    }

    pub const fn public_key(&self) -> &PqBiscuitAuthorityPublicKey {
        &self.pk
    }

    pub const fn next_leaf(&self) -> u32 {
        self.next_leaf
    }

    pub const fn remaining_mints(&self) -> u32 {
        (1u32 << self.pk.tree_height).saturating_sub(self.next_leaf)
    }

    /// Ratchet `next_leaf` forward to a durably anchored floor on reload.
    pub fn advance_next_leaf(&mut self, min_next_leaf: u32) -> Result<(), CapabilityError> {
        let cap = 1u32 << self.pk.tree_height;
        if min_next_leaf < self.next_leaf || min_next_leaf > cap {
            return Err(CapabilityError::Denied);
        }
        self.next_leaf = min_next_leaf;
        Ok(())
    }

    /// Mint a fresh root [`PqBiscuit`] delegated to a newly generated move-only [`PqBiscuitStepKey`].
    #[allow(clippy::too_many_arguments)]
    pub fn mint<B: AcceleratorBackend>(
        &mut self,
        dp: &FrontierDpTable,
        token_id: [u8; 32],
        audience: [u8; 32],
        caveats: &[Caveat],
        mut next_step_entropy: [u8; 32],
        hedging_nonce: &[u8; 32],
        accel: &B,
    ) -> Result<(PqBiscuit, PqBiscuitStepKey), CapabilityError> {
        let next_step_entropy = SecretBuffer(&mut next_step_entropy);
        if dp.params != FrontierFtsProfile::Compact1122.params() {
            return Err(CapabilityError::Denied);
        }
        let cap = 1u32 << self.pk.tree_height;
        if self.next_leaf >= cap {
            return Err(CapabilityError::Denied);
        }
        let encoded_caveats = encode_first_party_caveats(caveats)?;
        let leaf_idx = self.next_leaf;
        self.next_leaf += 1;

        let step1 = PqBiscuitStepKey::derive(token_id, audience, 1, &next_step_entropy, accel)?;
        let hop0_msg = hop_signing_message(
            &self.pk.authority_id,
            &token_id,
            &audience,
            0,
            &encoded_caveats,
            &step1.pk_root,
        );
        let (sk_seed, sk_prf) =
            authority_leaf_seeds(&self.master_seed, &self.pk.authority_id, leaf_idx);
        let (computed_root, sig_bytes) = sign_one_shot_compact1122(
            &sk_seed,
            &sk_prf,
            self.pk.pk_seed,
            dp,
            &hop0_msg,
            hedging_nonce,
            accel,
        )?;
        if !ct_eq_bytes(&computed_root, &self.leaf_roots[leaf_idx as usize]) {
            return Err(CapabilityError::InvalidTag);
        }

        let mut siblings = Vec::with_capacity(usize::from(self.pk.tree_height));
        let mut idx = leaf_idx as usize;
        for layer in 0..usize::from(self.pk.tree_height) {
            siblings.push(self.merkle_layers[layer][idx ^ 1]);
            idx >>= 1;
        }

        let token = PqBiscuit {
            token_id,
            audience,
            authority_leaf_index: leaf_idx,
            authority_leaf_pk_root: computed_root,
            authority_merkle_siblings: siblings,
            blocks: vec![PqBiscuitHopBlock {
                caveats: caveats.to_vec(),
                next_pk_root: step1.pk_root,
                signature: sig_bytes,
            }],
            seal: None,
        };
        Ok((token, step1))
    }

    /// Secret snapshot for encrypted, rollback-protected custody. Its trailing
    /// digest detects corruption; it is not a keyed authenticator or a use ledger.
    pub fn to_secret_bytes(&self) -> SecretVec<u8> {
        let leaves_bytes = self.leaf_roots.len() * 32;
        let mut out = SecretBuffer(Vec::with_capacity(8 + 32 + 105 + 4 + leaves_bytes + 32));
        out.extend_from_slice(AUTHORITY_SK_MAGIC);
        out.extend_from_slice(&*self.master_seed);
        out.extend_from_slice(&self.pk.to_bytes());
        out.extend_from_slice(&self.next_leaf.to_be_bytes());
        for root in &self.leaf_roots {
            out.extend_from_slice(root);
        }
        let tag = cshake256_framed_32(b"QSAG.BISCUIT.AUTHSK.TAG.V1", &[&out]);
        out.extend_from_slice(&tag);
        out
    }

    pub fn from_secret_bytes(bytes: &[u8]) -> Result<Self, CapabilityError> {
        let bad = CapabilityError::Malformed;
        if bytes.len() < 8 + 32 + 105 + 4 + 32 + 32
            || bytes.len() > 149 + (1 << MAX_AUTHORITY_TREE_HEIGHT) * 32 + 32
            || &bytes[..8] != AUTHORITY_SK_MAGIC
        {
            return Err(bad);
        }
        let body = &bytes[..bytes.len() - 32];
        let tag = cshake256_framed_32(b"QSAG.BISCUIT.AUTHSK.TAG.V1", &[body]);
        if !ct_eq_bytes(&tag, &bytes[bytes.len() - 32..]) {
            return Err(CapabilityError::InvalidTag);
        }
        let mut master_seed = SecretBytes::<32>::zeroed();
        master_seed.copy_from_slice(&body[8..40]);
        let pk = PqBiscuitAuthorityPublicKey::from_bytes(&body[40..145])?;
        let expected_pk_seed = cshake256_framed_32(
            b"QSAG.BISCUIT.AUTH.PKSEED.V1",
            &[&*master_seed, &pk.authority_id, &[pk.tree_height]],
        );
        if !ct_eq_bytes(&expected_pk_seed, &pk.pk_seed) {
            return Err(CapabilityError::InvalidTag);
        }
        let next_leaf = u32::from_be_bytes(body[145..149].try_into().map_err(|_| bad)?);
        let num_leaves = 1usize << pk.tree_height;
        if next_leaf > num_leaves as u32 || body.len() != 149 + num_leaves * 32 {
            return Err(bad);
        }
        let mut leaf_roots = Vec::with_capacity(num_leaves);
        let mut level0 = Vec::with_capacity(num_leaves);
        for (idx, chunk) in body[149..].as_chunks::<32>().0.iter().enumerate() {
            leaf_roots.push(*chunk);
            level0.push(authority_merkle_leaf_hash(
                &pk.authority_id,
                &pk.pk_seed,
                idx as u32,
                chunk,
            ));
        }
        let mut merkle_layers = Vec::with_capacity(usize::from(pk.tree_height) + 1);
        merkle_layers.push(level0);
        for layer in 0..pk.tree_height {
            let cur = &merkle_layers[usize::from(layer)];
            let mut parents = Vec::with_capacity(cur.len() / 2);
            for pair in cur.as_chunks::<2>().0 {
                parents.push(authority_merkle_parent_hash(
                    &pk.authority_id,
                    layer,
                    &pair[0],
                    &pair[1],
                ));
            }
            merkle_layers.push(parents);
        }
        if !ct_eq_bytes(
            &merkle_layers[usize::from(pk.tree_height)][0],
            &pk.merkle_root,
        ) {
            return Err(CapabilityError::InvalidTag);
        }
        Ok(Self {
            master_seed,
            pk,
            leaf_roots,
            merkle_layers,
            next_leaf,
        })
    }
}

/// Move-only single-use ephemeral delegation key for hop `hop_index` (`>= 1`).
///
/// Consumed by value in [`Self::attenuate`] or [`Self::seal`], preventing accidental
/// two-time fan-out signing of the same `Compact1122` ephemeral key in memory.
/// Secret snapshots must be transferred/consumed with durable single-use custody;
/// reloading the same snapshot twice defeats the Rust move-only guarantee.
pub struct PqBiscuitStepKey {
    token_id: [u8; 32],
    audience: [u8; 32],
    hop_index: u16,
    pk_root: [u8; 32],
    sk_seed: SecretBytes<32>,
    sk_prf: SecretBytes<32>,
}

impl fmt::Debug for PqBiscuitStepKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqBiscuitStepKey")
            .field("token_id", &self.token_id)
            .field("hop_index", &self.hop_index)
            .field("pk_root", &self.pk_root)
            .field("sk_seed", &"<REDACTED>")
            .finish()
    }
}

impl PqBiscuitStepKey {
    fn derive<B: AcceleratorBackend>(
        token_id: [u8; 32],
        audience: [u8; 32],
        hop_index: u16,
        entropy: &[u8; 32],
        accel: &B,
    ) -> Result<Self, CapabilityError> {
        if hop_index == 0 || usize::from(hop_index) > MAX_BISCUIT_HOPS {
            return Err(CapabilityError::Denied);
        }
        let sk_seed = SecretBuffer(cshake256_framed_32(
            b"QSAG.BISCUIT.STEP.SKSEED.V1",
            &[entropy, &token_id, &audience, &hop_index.to_be_bytes()],
        ));
        let sk_prf = SecretBuffer(cshake256_framed_32(
            b"QSAG.BISCUIT.STEP.SKPRF.V1",
            &[entropy, &token_id, &audience, &hop_index.to_be_bytes()],
        ));
        let pk_seed = hop_pk_seed(&token_id, &audience, hop_index);
        let key = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact1122,
            *sk_seed,
            *sk_prf,
            pk_seed,
            false,
            accel,
        );
        let pk_root: [u8; 32] = key
            .pk
            .root
            .as_slice()
            .try_into()
            .map_err(|_| CapabilityError::Malformed)?;
        Ok(Self {
            token_id,
            audience,
            hop_index,
            pk_root,
            sk_seed,
            sk_prf,
        })
    }

    pub const fn hop_index(&self) -> u16 {
        self.hop_index
    }

    pub const fn pk_root(&self) -> &[u8; 32] {
        &self.pk_root
    }

    /// Offline third-party attenuation: appends `caveats` and delegates to a fresh ephemeral
    /// `Compact1122` step key (`1,154 B` hop overhead + encoded caveats), consuming `self`.
    pub fn attenuate<B: AcceleratorBackend>(
        self,
        token: &PqBiscuit,
        dp: &FrontierDpTable,
        caveats: &[Caveat],
        mut next_step_entropy: [u8; 32],
        hedging_nonce: &[u8; 32],
        accel: &B,
    ) -> Result<(PqBiscuit, PqBiscuitStepKey), CapabilityError> {
        let next_step_entropy = SecretBuffer(&mut next_step_entropy);
        if token.seal.is_some()
            || token.blocks.is_empty()
            || token.blocks.len() >= MAX_BISCUIT_HOPS
            || usize::from(self.hop_index) != token.blocks.len()
            || !ct_eq_bytes(&self.token_id, &token.token_id)
            || !ct_eq_bytes(&self.audience, &token.audience)
        {
            return Err(CapabilityError::Denied);
        }
        let total_caveats = token
            .blocks
            .iter()
            .map(|b| b.caveats.len())
            .sum::<usize>()
            .saturating_add(caveats.len());
        if total_caveats > MAX_CAVEATS {
            return Err(CapabilityError::TooManyCaveats);
        }
        let last_block = token.blocks.last().ok_or(CapabilityError::Malformed)?;
        if !ct_eq_bytes(&last_block.next_pk_root, &self.pk_root) {
            return Err(CapabilityError::Denied);
        }
        let encoded_caveats = encode_first_party_caveats(caveats)?;
        let chain_digest = token.compute_chain_digest()?;
        let next_hop = self
            .hop_index
            .checked_add(1)
            .ok_or(CapabilityError::Denied)?;
        let next_step = Self::derive(
            self.token_id,
            self.audience,
            next_hop,
            &next_step_entropy,
            accel,
        )?;
        let msg = hop_signing_message(
            &chain_digest,
            &self.token_id,
            &self.audience,
            self.hop_index,
            &encoded_caveats,
            &next_step.pk_root,
        );
        let pk_seed = hop_pk_seed(&self.token_id, &self.audience, self.hop_index);
        let (computed_root, sig_bytes) = sign_one_shot_compact1122(
            &self.sk_seed,
            &self.sk_prf,
            pk_seed,
            dp,
            &msg,
            hedging_nonce,
            accel,
        )?;
        if !ct_eq_bytes(&computed_root, &self.pk_root) {
            return Err(CapabilityError::InvalidTag);
        }
        let mut updated = token.clone();
        updated.blocks.push(PqBiscuitHopBlock {
            caveats: caveats.to_vec(),
            next_pk_root: next_step.pk_root,
            signature: sig_bytes,
        });
        Ok((updated, next_step))
    }

    /// Permanently seal `token` with this tail key (optionally binding to `bound_request` for
    /// Proof-of-Possession replay protection), consuming `self`.
    pub fn seal<B: AcceleratorBackend>(
        self,
        token: &PqBiscuit,
        dp: &FrontierDpTable,
        bound_request: Option<&CapabilityRequest>,
        hedging_nonce: &[u8; 32],
        accel: &B,
    ) -> Result<PqBiscuit, CapabilityError> {
        if token.seal.is_some()
            || token.blocks.is_empty()
            || usize::from(self.hop_index) != token.blocks.len()
            || !ct_eq_bytes(&self.token_id, &token.token_id)
            || !ct_eq_bytes(&self.audience, &token.audience)
        {
            return Err(CapabilityError::Denied);
        }
        if let Some(req) = bound_request
            && !ct_eq_bytes(&req.audience, &token.audience)
        {
            return Err(CapabilityError::Denied);
        }
        let last_block = token.blocks.last().ok_or(CapabilityError::Malformed)?;
        if !ct_eq_bytes(&last_block.next_pk_root, &self.pk_root) {
            return Err(CapabilityError::Denied);
        }
        let chain_digest = token.compute_chain_digest()?;
        let req_digest = bound_request.map(capability_request_digest);
        let msg = seal_signing_message(&chain_digest, self.hop_index, req_digest.as_ref());
        let pk_seed = hop_pk_seed(&self.token_id, &self.audience, self.hop_index);
        let (computed_root, sig_bytes) = sign_one_shot_compact1122(
            &self.sk_seed,
            &self.sk_prf,
            pk_seed,
            dp,
            &msg,
            hedging_nonce,
            accel,
        )?;
        if !ct_eq_bytes(&computed_root, &self.pk_root) {
            return Err(CapabilityError::InvalidTag);
        }
        let mut sealed = token.clone();
        sealed.seal = Some(PqBiscuitSeal {
            request_bound: req_digest.is_some(),
            signature: sig_bytes,
        });
        Ok(sealed)
    }

    /// Secret snapshot for encrypted, rollback-protected custody. Its trailing
    /// digest detects corruption; it is not a keyed authenticator or a use ledger.
    pub fn to_secret_bytes(&self) -> SecretVec<u8> {
        let mut out = SecretBuffer(Vec::with_capacity(8 + 32 + 32 + 2 + 32 + 32 + 32 + 32));
        out.extend_from_slice(STEP_SK_MAGIC);
        out.extend_from_slice(&self.token_id);
        out.extend_from_slice(&self.audience);
        out.extend_from_slice(&self.hop_index.to_be_bytes());
        out.extend_from_slice(&self.pk_root);
        out.extend_from_slice(&*self.sk_seed);
        out.extend_from_slice(&*self.sk_prf);
        let tag = cshake256_framed_32(b"QSAG.BISCUIT.STEPSK.TAG.V1", &[&out]);
        out.extend_from_slice(&tag);
        out
    }

    pub fn from_secret_bytes(bytes: &[u8]) -> Result<Self, CapabilityError> {
        let bad = CapabilityError::Malformed;
        if bytes.len() != 202 || &bytes[..8] != STEP_SK_MAGIC {
            return Err(bad);
        }
        let body = &bytes[..170];
        let tag = cshake256_framed_32(b"QSAG.BISCUIT.STEPSK.TAG.V1", &[body]);
        if !ct_eq_bytes(&tag, &bytes[170..]) {
            return Err(CapabilityError::InvalidTag);
        }
        let hop_index = u16::from_be_bytes([body[72], body[73]]);
        if hop_index == 0 || usize::from(hop_index) > MAX_BISCUIT_HOPS {
            return Err(bad);
        }
        let mut sk_seed = SecretBytes::<32>::zeroed();
        let mut sk_prf = SecretBytes::<32>::zeroed();
        sk_seed.copy_from_slice(&body[106..138]);
        sk_prf.copy_from_slice(&body[138..170]);
        Ok(Self {
            token_id: body[8..40].try_into().map_err(|_| bad)?,
            audience: body[40..72].try_into().map_err(|_| bad)?,
            hop_index,
            pk_root: body[74..106].try_into().map_err(|_| bad)?,
            sk_seed,
            sk_prf,
        })
    }
}

/// One public-key delegation hop (`32 B next_pk_root + 1,122 B Compact1122 signature = 1,154 B` + caveats).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PqBiscuitHopBlock {
    pub caveats: Vec<Caveat>,
    pub next_pk_root: [u8; 32],
    pub signature: [u8; COMPACT1122_SIG_BYTES],
}

/// Terminal `Compact1122` seal closing a [`PqBiscuit`] against further attenuation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PqBiscuitSeal {
    pub request_bound: bool,
    pub signature: [u8; COMPACT1122_SIG_BYTES],
}

/// Post-quantum public-key attenuated capability chain backed by ephemeral `Compact1122` hops.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PqBiscuit {
    token_id: [u8; 32],
    audience: [u8; 32],
    authority_leaf_index: u32,
    authority_leaf_pk_root: [u8; 32],
    authority_merkle_siblings: Vec<[u8; 32]>,
    blocks: Vec<PqBiscuitHopBlock>,
    seal: Option<PqBiscuitSeal>,
}

impl PqBiscuit {
    pub const fn token_id(&self) -> &[u8; 32] {
        &self.token_id
    }

    pub const fn audience(&self) -> &[u8; 32] {
        &self.audience
    }

    pub const fn authority_leaf_index(&self) -> u32 {
        self.authority_leaf_index
    }

    pub fn blocks(&self) -> &[PqBiscuitHopBlock] {
        &self.blocks
    }

    pub const fn is_sealed(&self) -> bool {
        self.seal.is_some()
    }

    pub const fn is_request_bound(&self) -> bool {
        match &self.seal {
            Some(seal) => seal.request_bound,
            None => false,
        }
    }

    fn compute_chain_digest(&self) -> Result<[u8; 32], CapabilityError> {
        if self.blocks.is_empty() || self.blocks.len() > MAX_BISCUIT_HOPS {
            return Err(CapabilityError::Malformed);
        }
        let authority_placeholder = cshake256_framed_32(
            b"QSAG.BISCUIT.ROOT.ANCHOR.V1",
            &[
                &self.token_id,
                &self.audience,
                &self.authority_leaf_index.to_be_bytes(),
                &self.authority_leaf_pk_root,
            ],
        );
        // Hop 0's `prev_chain_digest` is verified directly against `authority_pk.authority_id`
        // during `verify`; hops >= 1 chain deterministically from hop 0's `(root_anchor, sig_0)`.
        let mut chain = authority_placeholder;
        for (idx, block) in self.blocks.iter().enumerate() {
            let encoded = encode_first_party_caveats(&block.caveats)?;
            let hop_msg = if idx == 0 {
                // For chain-digest derivation across offline third parties (who need not hold
                // `authority_id` separately), bind `(authority_placeholder, sig_0)` at hop 0:
                cshake256_framed_32(
                    b"QSAG.BISCUIT.HOP0.CHAIN.V1",
                    &[&authority_placeholder, &encoded, &block.next_pk_root],
                )
            } else {
                hop_signing_message(
                    &chain,
                    &self.token_id,
                    &self.audience,
                    idx as u16,
                    &encoded,
                    &block.next_pk_root,
                )
            };
            chain = next_chain_digest(&hop_msg, &block.signature);
        }
        Ok(chain)
    }

    /// Verify every `Compact1122` hop signature from `authority_pk` to the terminal seal and
    /// evaluate all caveats across all hops conjunctively against `request`.
    pub fn verify(
        &self,
        authority_pk: &PqBiscuitAuthorityPublicKey,
        dp: &FrontierDpTable,
        request: &CapabilityRequest,
    ) -> Result<(), CapabilityError> {
        let seal = self.seal.as_ref().ok_or(CapabilityError::Denied)?;
        if !ct_eq_bytes(&self.audience, &request.audience) {
            return Err(CapabilityError::Denied);
        }
        if self.blocks.is_empty()
            || self.blocks.len() > MAX_BISCUIT_HOPS
            || authority_pk.tree_height > MAX_AUTHORITY_TREE_HEIGHT
            || self.authority_merkle_siblings.len() != usize::from(authority_pk.tree_height)
            || self.authority_leaf_index >= (1u32 << authority_pk.tree_height)
        {
            return Err(CapabilityError::Malformed);
        }
        let total_caveats: usize = self.blocks.iter().map(|b| b.caveats.len()).sum();
        if total_caveats > MAX_CAVEATS {
            return Err(CapabilityError::TooManyCaveats);
        }

        // Caveats are checked first because they are cheap; success still requires
        // every signature below.
        for block in &self.blocks {
            for caveat in &block.caveats {
                if !evaluate_first_party_caveat(caveat, request) {
                    return Err(CapabilityError::Denied);
                }
            }
        }

        // 1. Authenticate the authority's one-time Compact1122 leaf in `authority_pk.merkle_root`.
        let mut cur = authority_merkle_leaf_hash(
            &authority_pk.authority_id,
            &authority_pk.pk_seed,
            self.authority_leaf_index,
            &self.authority_leaf_pk_root,
        );
        let mut idx = self.authority_leaf_index as usize;
        for (layer, sib) in self.authority_merkle_siblings.iter().enumerate() {
            cur = if (idx & 1) == 0 {
                authority_merkle_parent_hash(&authority_pk.authority_id, layer as u8, &cur, sib)
            } else {
                authority_merkle_parent_hash(&authority_pk.authority_id, layer as u8, sib, &cur)
            };
            idx >>= 1;
        }
        if !ct_eq_bytes(&cur, &authority_pk.merkle_root) {
            return Err(CapabilityError::InvalidTag);
        }

        // 2. Verify hop 0 (root authority signature) and walk every subsequent `Compact1122` hop.
        let authority_placeholder = cshake256_framed_32(
            b"QSAG.BISCUIT.ROOT.ANCHOR.V1",
            &[
                &self.token_id,
                &self.audience,
                &self.authority_leaf_index.to_be_bytes(),
                &self.authority_leaf_pk_root,
            ],
        );
        let mut chain = authority_placeholder;
        for (hop_idx, block) in self.blocks.iter().enumerate() {
            let encoded = encode_first_party_caveats(&block.caveats)?;
            if hop_idx == 0 {
                let hop0_signed = hop_signing_message(
                    &authority_pk.authority_id,
                    &self.token_id,
                    &self.audience,
                    0,
                    &encoded,
                    &block.next_pk_root,
                );
                verify_compact1122_bytes(
                    authority_pk.pk_seed,
                    self.authority_leaf_pk_root,
                    dp,
                    &hop0_signed,
                    &block.signature,
                )?;
                let hop0_chain_msg = cshake256_framed_32(
                    b"QSAG.BISCUIT.HOP0.CHAIN.V1",
                    &[&authority_placeholder, &encoded, &block.next_pk_root],
                );
                chain = next_chain_digest(&hop0_chain_msg, &block.signature);
            } else {
                let prev_pk_root = self.blocks[hop_idx - 1].next_pk_root;
                let pk_seed = hop_pk_seed(&self.token_id, &self.audience, hop_idx as u16);
                let hop_msg = hop_signing_message(
                    &chain,
                    &self.token_id,
                    &self.audience,
                    hop_idx as u16,
                    &encoded,
                    &block.next_pk_root,
                );
                verify_compact1122_bytes(pk_seed, prev_pk_root, dp, &hop_msg, &block.signature)?;
                chain = next_chain_digest(&hop_msg, &block.signature);
            }
        }

        // 3. Verify terminal seal signature under the final hop's `next_pk_root`.
        let seal_hop = self.blocks.len() as u16;
        let seal_pk_seed = hop_pk_seed(&self.token_id, &self.audience, seal_hop);
        let seal_pk_root = self
            .blocks
            .last()
            .ok_or(CapabilityError::Malformed)?
            .next_pk_root;
        let req_digest = seal
            .request_bound
            .then(|| capability_request_digest(request));
        let seal_msg = seal_signing_message(&chain, seal_hop, req_digest.as_ref());
        verify_compact1122_bytes(seal_pk_seed, seal_pk_root, dp, &seal_msg, &seal.signature)?;

        Ok(())
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>, CapabilityError> {
        if self.blocks.is_empty()
            || self.blocks.len() > MAX_BISCUIT_HOPS
            || self.authority_merkle_siblings.len() > usize::from(MAX_AUTHORITY_TREE_HEIGHT)
        {
            return Err(CapabilityError::Malformed);
        }
        let seal_flag = match &self.seal {
            None => 0u8,
            Some(s) if !s.request_bound => 1u8,
            Some(_) => 2u8,
        };
        let mut out = Vec::with_capacity(
            8 + 64
                + 4
                + 32
                + 1
                + self.authority_merkle_siblings.len() * 32
                + 2
                + self.blocks.len() * (PQ_BISCUIT_HOP_CRYPTO_BYTES + 16)
                + COMPACT1122_SIG_BYTES,
        );
        out.extend_from_slice(BISCUIT_WIRE_MAGIC);
        out.push(seal_flag);
        out.push(self.authority_merkle_siblings.len() as u8);
        out.extend_from_slice(&(self.blocks.len() as u16).to_be_bytes());
        out.extend_from_slice(&self.token_id);
        out.extend_from_slice(&self.audience);
        out.extend_from_slice(&self.authority_leaf_index.to_be_bytes());
        out.extend_from_slice(&self.authority_leaf_pk_root);
        for sib in &self.authority_merkle_siblings {
            out.extend_from_slice(sib);
        }
        for block in &self.blocks {
            let encoded = encode_first_party_caveats(&block.caveats)?;
            out.extend_from_slice(&(block.caveats.len() as u16).to_be_bytes());
            out.extend_from_slice(&encoded);
            out.extend_from_slice(&block.next_pk_root);
            out.extend_from_slice(&block.signature);
        }
        if let Some(seal) = &self.seal {
            out.extend_from_slice(&seal.signature);
        }
        Ok(out)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CapabilityError> {
        let bad = CapabilityError::Malformed;
        if bytes.len() < 8 + 4 + 64 + 4 + 32 + 2 + PQ_BISCUIT_HOP_CRYPTO_BYTES
            || bytes.len()
                > 112
                    + usize::from(MAX_AUTHORITY_TREE_HEIGHT) * 32
                    + MAX_BISCUIT_HOPS * (2 + PQ_BISCUIT_HOP_CRYPTO_BYTES)
                    + MAX_CAVEATS * 34
                    + COMPACT1122_SIG_BYTES
            || &bytes[..8] != BISCUIT_WIRE_MAGIC
        {
            return Err(bad);
        }
        let seal_flag = bytes[8];
        if seal_flag > 2 {
            return Err(bad);
        }
        let tree_height = bytes[9];
        if tree_height > MAX_AUTHORITY_TREE_HEIGHT {
            return Err(bad);
        }
        let num_blocks = u16::from_be_bytes([bytes[10], bytes[11]]) as usize;
        if num_blocks == 0 || num_blocks > MAX_BISCUIT_HOPS {
            return Err(bad);
        }
        let token_id: [u8; 32] = bytes[12..44].try_into().map_err(|_| bad)?;
        let audience: [u8; 32] = bytes[44..76].try_into().map_err(|_| bad)?;
        let authority_leaf_index = u32::from_be_bytes(bytes[76..80].try_into().map_err(|_| bad)?);
        if authority_leaf_index >= (1u32 << tree_height) {
            return Err(bad);
        }
        let authority_leaf_pk_root: [u8; 32] = bytes[80..112].try_into().map_err(|_| bad)?;
        let mut pos = 112usize;
        let sib_end = pos.checked_add(usize::from(tree_height) * 32).ok_or(bad)?;
        if sib_end > bytes.len() {
            return Err(bad);
        }
        let authority_merkle_siblings = bytes[pos..sib_end].as_chunks::<32>().0.to_vec();
        pos = sib_end;

        let seal_len = if seal_flag == 0 {
            0
        } else {
            COMPACT1122_SIG_BYTES
        };
        if bytes.len() < pos + seal_len {
            return Err(bad);
        }
        let blocks_end = bytes.len() - seal_len;
        if num_blocks > (blocks_end - pos) / (2 + PQ_BISCUIT_HOP_CRYPTO_BYTES) {
            return Err(bad);
        }
        let mut blocks = Vec::with_capacity(num_blocks);
        let mut total_caveats = 0usize;
        for _ in 0..num_blocks {
            let hdr = bytes
                .get(pos..pos + 2)
                .filter(|_| pos + 2 <= blocks_end)
                .ok_or(bad)?;
            let cav_count = u16::from_be_bytes([hdr[0], hdr[1]]) as usize;
            pos += 2;
            total_caveats = total_caveats.saturating_add(cav_count);
            if total_caveats > MAX_CAVEATS {
                return Err(CapabilityError::TooManyCaveats);
            }
            let caveats = decode_first_party_caveats(bytes, &mut pos, blocks_end, cav_count)?;
            let crypto_end = pos
                .checked_add(PQ_BISCUIT_HOP_CRYPTO_BYTES)
                .filter(|&e| e <= blocks_end)
                .ok_or(bad)?;
            let next_pk_root: [u8; 32] = bytes[pos..pos + 32].try_into().map_err(|_| bad)?;
            let signature: [u8; COMPACT1122_SIG_BYTES] =
                bytes[pos + 32..crypto_end].try_into().map_err(|_| bad)?;
            pos = crypto_end;
            blocks.push(PqBiscuitHopBlock {
                caveats,
                next_pk_root,
                signature,
            });
        }
        if pos != blocks_end {
            return Err(bad);
        }
        let seal = if seal_flag == 0 {
            None
        } else {
            let signature: [u8; COMPACT1122_SIG_BYTES] =
                bytes[blocks_end..].try_into().map_err(|_| bad)?;
            Some(PqBiscuitSeal {
                request_bound: seal_flag == 2,
                signature,
            })
        };
        Ok(Self {
            token_id,
            audience,
            authority_leaf_index,
            authority_leaf_pk_root,
            authority_merkle_siblings,
            blocks,
            seal,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_accel::CpuReferenceBackend;

    fn sample_request() -> CapabilityRequest {
        CapabilityRequest {
            audience: [0x22; 32],
            resource: [0x33; 32],
            actions: 0b0011,
            amount: 500,
            now: 1_700_000_100,
        }
    }

    #[test]
    fn codec_bounds_and_caveat_framing() {
        let mut token = PqBiscuit {
            token_id: [1; 32],
            audience: [2; 32],
            authority_leaf_index: 0,
            authority_leaf_pk_root: [3; 32],
            authority_merkle_siblings: vec![],
            blocks: vec![PqBiscuitHopBlock {
                caveats: vec![Caveat::Resource([4; 32]); MAX_CAVEATS],
                next_pk_root: [5; 32],
                signature: [0; COMPACT1122_SIG_BYTES],
            }],
            seal: None,
        };
        let raw = token.to_bytes().unwrap();
        assert_eq!(PqBiscuit::from_bytes(&raw).unwrap(), token);
        token.blocks[0].caveats.push(Caveat::Actions(1));
        assert_eq!(token.to_bytes(), Err(CapabilityError::TooManyCaveats));
        token.blocks[0].caveats = vec![Caveat::ThirdParty([6; 32])];
        assert_eq!(token.to_bytes(), Err(CapabilityError::Denied));
        token.blocks[0].caveats.clear();
        token
            .blocks
            .resize(MAX_BISCUIT_HOPS, token.blocks[0].clone());
        assert_eq!(
            PqBiscuit::from_bytes(&token.to_bytes().unwrap()).unwrap(),
            token
        );
        token.blocks.push(token.blocks[0].clone());
        assert_eq!(token.to_bytes(), Err(CapabilityError::Malformed));
    }

    #[test]
    fn pq_biscuit_offline_attenuation_conjunctive_caveats_and_pop_seal() {
        let accel = CpuReferenceBackend::new();
        let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let mut authority =
            PqBiscuitAuthorityKey::keygen([0x11; 32], [0xAA; 32], 2, &accel).unwrap();
        let authority_pk = *authority.public_key();

        let (tok0, step1) = authority
            .mint(
                &dp,
                [0x44; 32],
                [0x22; 32],
                &[Caveat::Resource([0x33; 32]), Caveat::MaxAmount(1_000)],
                [0x51; 32],
                &[0x61; 32],
                &accel,
            )
            .unwrap();
        assert_eq!(authority.next_leaf(), 1);
        // Unsealed token cannot be verified.
        assert_eq!(
            tok0.verify(&authority_pk, &dp, &sample_request()),
            Err(CapabilityError::Denied)
        );

        // Offline third-party attenuation narrows MaxAmount to 600 and Actions to 0b0111.
        let step1_bytes = step1.to_secret_bytes();
        for cut in 0..step1_bytes.len() {
            assert!(PqBiscuitStepKey::from_secret_bytes(&step1_bytes[..cut]).is_err());
        }
        for hop in [0u16, MAX_BISCUIT_HOPS as u16 + 1, u16::MAX] {
            let mut bad = SecretBuffer(step1_bytes.to_vec());
            bad[72..74].copy_from_slice(&hop.to_be_bytes());
            let tag = cshake256_framed_32(b"QSAG.BISCUIT.STEPSK.TAG.V1", &[&bad[..170]]);
            bad[170..].copy_from_slice(&tag);
            assert!(PqBiscuitStepKey::from_secret_bytes(&bad).is_err());
        }
        let step1 = PqBiscuitStepKey::from_secret_bytes(&step1_bytes).unwrap();
        let (tok1, step2) = step1
            .attenuate(
                &tok0,
                &dp,
                &[Caveat::MaxAmount(600), Caveat::Actions(0b0111)],
                [0x52; 32],
                &[0x62; 32],
                &accel,
            )
            .unwrap();
        let raw_open = tok1.to_bytes().unwrap();
        let tok1_decoded = PqBiscuit::from_bytes(&raw_open).unwrap();
        assert_eq!(tok1_decoded, tok1);

        // Request-bound PoP seal by final holder.
        let req = sample_request();
        let sealed = step2
            .seal(&tok1_decoded, &dp, Some(&req), &[0x63; 32], &accel)
            .unwrap();
        assert!(sealed.is_sealed());
        assert!(sealed.is_request_bound());
        let wire = sealed.to_bytes().unwrap();
        // Hop 0 + Hop 1 + terminal seal + compact header/caveats: ~3.5 KiB total (~1,154 B/hop).
        assert_eq!(PQ_BISCUIT_HOP_CRYPTO_BYTES, 1154);
        let decoded = PqBiscuit::from_bytes(&wire).unwrap();
        decoded.verify(&authority_pk, &dp, &req).unwrap();
        let mut stripped_binding = decoded.clone();
        stripped_binding.seal.as_mut().unwrap().request_bound = false;
        assert_eq!(
            stripped_binding.verify(&authority_pk, &dp, &req),
            Err(CapabilityError::InvalidTag)
        );

        // Canonical wire framing: every truncation, trailing byte, invalid flag,
        // oversized hop count, leaf index and caveat length is rejected.
        for cut in 0..wire.len() {
            assert!(PqBiscuit::from_bytes(&wire[..cut]).is_err(), "cut={cut}");
        }
        let mut malformed = wire.clone();
        malformed.push(0);
        assert!(PqBiscuit::from_bytes(&malformed).is_err());
        for (offset, value) in [
            (8, 3),
            (9, 9),
            (10, 0xff),
            (76, 0xff),
            (178, 0xff),
            (179, 0),
        ] {
            let mut malformed = wire.clone();
            malformed[offset] = value;
            assert!(
                PqBiscuit::from_bytes(&malformed).is_err(),
                "offset={offset}"
            );
        }
        // Structurally valid substitutions must fail cryptographic verification.
        for offset in [8, 12, 44, 79, 80, 112, 144, 180, 235, wire.len() - 1] {
            let mut tampered = wire.clone();
            tampered[offset] ^= 1;
            assert!(
                PqBiscuit::from_bytes(&tampered)
                    .map_or(true, |b| b.verify(&authority_pk, &dp, &req).is_err()),
                "offset={offset}"
            );
        }
        for field in 0..5 {
            let mut changed = sample_request();
            match field {
                0 => changed.audience[0] ^= 1,
                1 => changed.resource[0] ^= 1,
                2 => changed.actions ^= 1,
                3 => changed.amount -= 1,
                _ => changed.now += 1,
            }
            assert!(decoded.verify(&authority_pk, &dp, &changed).is_err());
        }

        // Request-bound PoP seal rejects replay at a different amount or timestamp!
        let mut different_req = sample_request();
        different_req.amount = 400;
        assert_eq!(
            decoded.verify(&authority_pk, &dp, &different_req),
            Err(CapabilityError::InvalidTag)
        );

        // Tampering with any caveat byte invalidates the Compact1122 hop chain!
        let mut tampered = wire.clone();
        tampered[185] ^= 0x01;
        assert!(
            PqBiscuit::from_bytes(&tampered)
                .map_or(true, |b| b.verify(&authority_pk, &dp, &req).is_err())
        );

        // Authority secret serialization roundtrips and preserves `next_leaf`.
        let auth_bytes = authority.to_secret_bytes();
        let mut restored_auth = PqBiscuitAuthorityKey::from_secret_bytes(&auth_bytes).unwrap();
        assert_eq!(restored_auth.next_leaf(), 1);
        assert_eq!(
            restored_auth.advance_next_leaf(0),
            Err(CapabilityError::Denied)
        );
        assert_eq!(
            restored_auth.advance_next_leaf(5),
            Err(CapabilityError::Denied)
        );
        assert_eq!(restored_auth.next_leaf(), 1);
        // A valid digest cannot excuse malformed counters or inconsistent public seed.
        for (offset, value) in [(145, 0xff), (80, 0xff), (112, 9)] {
            let mut malformed = SecretBuffer(auth_bytes.to_vec());
            malformed[offset] = value;
            let end = malformed.len() - 32;
            let tag = cshake256_framed_32(b"QSAG.BISCUIT.AUTHSK.TAG.V1", &[&malformed[..end]]);
            malformed[end..].copy_from_slice(&tag);
            assert!(PqBiscuitAuthorityKey::from_secret_bytes(&malformed).is_err());
        }
        let (tok_b, step_b) = restored_auth
            .mint(
                &dp,
                [0x45; 32],
                [0x22; 32],
                &[Caveat::MaxAmount(200), Caveat::MaxAmount(9_999)],
                [0x71; 32],
                &[0x81; 32],
                &accel,
            )
            .unwrap();
        let bearer_sealed = step_b.seal(&tok_b, &dp, None, &[0x82; 32], &accel).unwrap();
        // Later permissive caveat (9_999) cannot widen earlier MaxAmount(200)!
        assert_eq!(
            bearer_sealed.verify(&authority_pk, &dp, &req),
            Err(CapabilityError::Denied)
        );
        let mut small_req = sample_request();
        small_req.amount = 150;
        bearer_sealed
            .verify(&authority_pk, &dp, &small_req)
            .unwrap();
        // Every mint has a distinct authenticated leaf, including after restore.
        let mut indices = vec![tok0.authority_leaf_index(), tok_b.authority_leaf_index()];
        while restored_auth.remaining_mints() != 0 {
            let (token, step) = restored_auth
                .mint(
                    &dp,
                    [0x46; 32],
                    [0x22; 32],
                    &[],
                    [0x72; 32],
                    &[0x83; 32],
                    &accel,
                )
                .unwrap();
            assert!(!indices.contains(&token.authority_leaf_index()));
            indices.push(token.authority_leaf_index());
            step.seal(&token, &dp, None, &[0x84; 32], &accel)
                .unwrap()
                .verify(&authority_pk, &dp, &small_req)
                .unwrap();
        }
        assert_eq!(indices, vec![0, 1, 2, 3]);
        assert!(
            restored_auth
                .mint(
                    &dp,
                    [0x47; 32],
                    [0x22; 32],
                    &[],
                    [0x73; 32],
                    &[0x85; 32],
                    &accel
                )
                .is_err()
        );
    }
}
