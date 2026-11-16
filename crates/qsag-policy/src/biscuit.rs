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
//!   `Compact1122` authority leaves under one persistent 65-byte [`PqBiscuitAuthorityPublicKey`].
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
use qsag_asm::wipe::{SecretBuffer, SecretBytes, SecretVec, wipe};
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
        &[authority_id, pk_seed, &leaf_index.to_be_bytes(), leaf_pk_root],
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

fn sign_one_shot_compact1122<B: AcceleratorBackend>(
    sk_seed: [u8; 32],
    sk_prf: [u8; 32],
    pk_seed: [u8; 32],
    dp: &FrontierDpTable,
    msg: &[u8],
    hedging_nonce: &[u8; 32],
    accel: &B,
) -> Result<([u8; 32], [u8; COMPACT1122_SIG_BYTES]), CapabilityError> {
    let key = FrontierFtsSigningKey::keygen(
        FrontierFtsProfile::Compact1122,
        sk_seed,
        sk_prf,
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
    let sig_arr: [u8; COMPACT1122_SIG_BYTES] =
        raw.as_slice().try_into().map_err(|_| CapabilityError::Malformed)?;
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

/// Persistent 73-byte (`8 B magic + 65 B payload`) post-quantum Biscuit authority public key.
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
            authority_id: bytes[8..40].try_into().map_err(|_| CapabilityError::Malformed)?,
            pk_seed: bytes[40..72].try_into().map_err(|_| CapabilityError::Malformed)?,
            tree_height: bytes[72],
            merkle_root: bytes[73..105]
                .try_into()
                .map_err(|_| CapabilityError::Malformed)?,
        })
    }
}

/// Merkle-bundled root issuer key capable of minting `2^tree_height` distinct post-quantum
/// [`PqBiscuit`] capabilities without ever signing twice with the same `Compact1122` leaf.
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
        master_seed: [u8; 32],
        authority_id: [u8; 32],
        tree_height: u8,
        accel: &B,
    ) -> Result<Self, CapabilityError> {
        if tree_height > MAX_AUTHORITY_TREE_HEIGHT {
            return Err(CapabilityError::Malformed);
        }
        let master = SecretBuffer(master_seed);
        let pk_seed = cshake256_framed_32(
            b"QSAG.BISCUIT.AUTH.PKSEED.V1",
            &[&*master, &authority_id, &[tree_height]],
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
            level0.push(authority_merkle_leaf_hash(&authority_id, &pk_seed, idx, &root));
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
            master_seed: master,
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
        next_step_entropy: [u8; 32],
        hedging_nonce: &[u8; 32],
        accel: &B,
    ) -> Result<(PqBiscuit, PqBiscuitStepKey), CapabilityError> {
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

        let step1 = PqBiscuitStepKey::derive(token_id, audience, 1, next_step_entropy, accel)?;
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
            *sk_seed,
            *sk_prf,
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
        if bytes.len() < 8 + 32 + 105 + 4 + 32 + 32 || &bytes[..8] != AUTHORITY_SK_MAGIC {
            return Err(bad);
        }
        let body = &bytes[..bytes.len() - 32];
        let tag = cshake256_framed_32(b"QSAG.BISCUIT.AUTHSK.TAG.V1", &[body]);
        if !ct_eq_bytes(&tag, &bytes[bytes.len() - 32..]) {
            return Err(CapabilityError::InvalidTag);
        }
        let mut raw_seed = [0u8; 32];
        raw_seed.copy_from_slice(&body[8..40]);
        let master_seed = SecretBuffer(raw_seed);
        wipe(&mut raw_seed);
        let pk = PqBiscuitAuthorityPublicKey::from_bytes(&body[40..145])?;
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
        if !ct_eq_bytes(&merkle_layers[usize::from(pk.tree_height)][0], &pk.merkle_root) {
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
/// two-time fan-out signing of the same `Compact1122` ephemeral key.
