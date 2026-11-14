//! Legacy key & BIP-32 / SLIP-0010 derivation commitments (`HASH160` P2PKH/P2WPKH, BIP-341
//! Taproot tweaked x-only key, `Keccak256` 20-byte EVM address, and `SLIP-0010` Ed25519 chain).
//!
//! Redacted secret formatting,
//! and `write_volatile` zeroization on `Drop`.

use core::fmt;

use qsag_accel::ct::{RedactedSecret, ct_select_u64, ct_zeroize_bytes};
use qsag_accel::goldilocks::pack_bytes32_to_limbs56;
use qsag_accel::keccak::keccak256;
use qsag_accel::sha2::{hash160, hmac_sha512, sha256_tagged, sha512};

use crate::secp256k1_ct::{
    SecpPoint, secp_scalar_add_mod_n, secp_scalar_is_canonical, secp_scalar_is_valid_nonzero,
    secp_scalar_neg_mod_n,
};

/// Supported classical-to-PQ migration target commitment kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LegacyCommitmentKind {
    /// Bitcoin `HASH160 = RIPEMD160(SHA256(compressed_pk_33))` (`20 B` P2PKH / P2WPKH).
    BitcoinHash160([u8; 20]),
    /// Bitcoin BIP-341 Taproot tweaked x-only output key `x(P_even + H_TapTweak(x(P_even)) * G)` (`32 B`).
    BitcoinTaprootXOnly([u8; 32]),
    /// Ethereum EOA `Keccak256(uncompressed_pk_64)[12..32]` (`20 B`).
    EthereumKeccak20([u8; 20]),
    /// SLIP-0010 Ed25519 hardened chain key commitment (RFC 8032 compressed public key, 32 bytes).
    Slip0010Ed25519([u8; 32]),
}

impl LegacyCommitmentKind {
    /// Canonical injective 5-limb 56-bit Goldilocks encoding of the public legacy commitment (`< 2^56 < p`).
    pub fn to_canonical_limbs56(&self) -> [u64; 6] {
        let (tag, bytes32) = match *self {
            Self::BitcoinHash160(h20) => {
                let mut b = [0u8; 32];
                b[..20].copy_from_slice(&h20);
                (1u64, b)
            }
            Self::BitcoinTaprootXOnly(x32) => (2u64, x32),
            Self::EthereumKeccak20(e20) => {
                let mut b = [0u8; 32];
                b[..20].copy_from_slice(&e20);
                (3u64, b)
            }
            Self::Slip0010Ed25519(s32) => (4u64, s32),
        };
        let l5 = pack_bytes32_to_limbs56(&bytes32);
        [tag, l5[0], l5[1], l5[2], l5[3], l5[4]]
    }
}

/// Optional hardened BIP-32 / SLIP-0010 parent derivation step (`index >= 0x8000_0000`).
pub struct HardenedChainStep {
    parent_key: RedactedSecret<32>,
    parent_chain_code: RedactedSecret<32>,
    pub hardened_child_index: u32,
}

impl fmt::Debug for HardenedChainStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HardenedChainStep")
            .field("parent_key", &"<REDACTED>")
            .field("parent_chain_code", &"<REDACTED>")
            .field("hardened_child_index", &self.hardened_child_index)
            .finish()
    }
}

impl HardenedChainStep {
    pub fn new(
        parent_key: [u8; 32],
        parent_chain_code: [u8; 32],
        hardened_child_index: u32,
    ) -> Option<Self> {
        if (hardened_child_index & 0x8000_0000) == 0 {
            return None;
        }
        Some(Self {
            parent_key: RedactedSecret::new(parent_key),
            parent_chain_code: RedactedSecret::new(parent_chain_code),
            hardened_child_index,
        })
    }

    /// Perform standard BIP-32 hardened child derivation `HMAC-SHA512(c_par, 0x00 || k_par || BE32(idx))`.
    pub fn derive_bip32_secp256k1_child(&self) -> Option<([u8; 32], [u8; 32])> {
        if !secp_scalar_is_valid_nonzero(self.parent_key.expose()) {
            return None;
        }
        let mut data = [0u8; 37];
        data[0] = 0x00;
        data[1..33].copy_from_slice(self.parent_key.expose());
        data[33..37].copy_from_slice(&self.hardened_child_index.to_be_bytes());
        let mut il_ir = hmac_sha512(self.parent_chain_code.expose(), &data);
        ct_zeroize_bytes(&mut data);

        let mut il = [0u8; 32];
        let mut ir = [0u8; 32];
        il.copy_from_slice(&il_ir[0..32]);
        ir.copy_from_slice(&il_ir[32..64]);
        ct_zeroize_bytes(&mut il_ir);

        if !secp_scalar_is_canonical(&il) {
            ct_zeroize_bytes(&mut il);
            ct_zeroize_bytes(&mut ir);
            return None;
        }
        let mut child_sk = secp_scalar_add_mod_n(&il, self.parent_key.expose());
        ct_zeroize_bytes(&mut il);
        if !secp_scalar_is_valid_nonzero(&child_sk) {
            ct_zeroize_bytes(&mut child_sk);
            ct_zeroize_bytes(&mut ir);
            return None;
        }
        Some((child_sk, ir))
    }

    /// Perform SLIP-0010 Ed25519 hardened child derivation `HMAC-SHA512(c_par, 0x00 || k_par || BE32(idx))`.
    pub fn derive_slip0010_ed25519_child(&self) -> ([u8; 32], [u8; 32]) {
        let mut data = [0u8; 37];
        data[0] = 0x00;
        data[1..33].copy_from_slice(self.parent_key.expose());
        data[33..37].copy_from_slice(&self.hardened_child_index.to_be_bytes());
        let mut il_ir = hmac_sha512(self.parent_chain_code.expose(), &data);
        ct_zeroize_bytes(&mut data);
        let mut il = [0u8; 32];
        let mut ir = [0u8; 32];
        il.copy_from_slice(&il_ir[0..32]);
        ir.copy_from_slice(&il_ir[32..64]);
        ct_zeroize_bytes(&mut il_ir);
        (il, ir)
    }
}

/// Secret classical ownership witness (`Redacted` `Debug`, `write_volatile` `Drop`).
pub struct LegacyOwnershipWitness {
    secret_scalar_or_seed: RedactedSecret<32>,
    chain_step: Option<HardenedChainStep>,
}

impl fmt::Debug for LegacyOwnershipWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LegacyOwnershipWitness")
            .field("secret_scalar_or_seed", &"<REDACTED>")
            .field("has_chain_step", &self.chain_step.is_some())
            .finish()
    }
}

impl LegacyOwnershipWitness {
    /// Construct from a standalone raw 32-byte `secp256k1` or `Ed25519` secret key (works for
    /// non-HD custodial keys before pubkey exposure!).
    pub const fn from_raw_secret(secret_32: [u8; 32]) -> Self {
        Self {
            secret_scalar_or_seed: RedactedSecret::new(secret_32),
            chain_step: None,
        }
    }

    /// Construct from a hardened BIP-32 (`secp256k1` / Taproot / EVM) parent key & chain code.
    pub fn from_bip32_hardened_step(step: HardenedChainStep) -> Option<Self> {
        let (child_sk, mut child_cc) = step.derive_bip32_secp256k1_child()?;
        ct_zeroize_bytes(&mut child_cc);
        Some(Self {
            secret_scalar_or_seed: RedactedSecret::new(child_sk),
            chain_step: Some(step),
        })
    }

    /// Construct from a hardened SLIP-0010 (`Ed25519`) parent seed & chain code.
    pub fn from_slip0010_hardened_step(step: HardenedChainStep) -> Self {
        let (child_seed, mut child_cc) = step.derive_slip0010_ed25519_child();
        ct_zeroize_bytes(&mut child_cc);
        Self {
            secret_scalar_or_seed: RedactedSecret::new(child_seed),
            chain_step: Some(step),
        }
    }

    pub const fn secret_bytes(&self) -> &[u8; 32] {
        self.secret_scalar_or_seed.expose()
    }

    /// Compute the Bitcoin `HASH160` (`P2PKH` / `P2WPKH`) commitment in constant time (`0` logs!).
    pub fn compute_bitcoin_hash160(&self) -> Option<LegacyCommitmentKind> {
        let sk = self.secret_scalar_or_seed.expose();
        if !secp_scalar_is_valid_nonzero(sk) {
            return None;
        }
        let mut pt = SecpPoint::generator_mul_ct(sk);
        let mut comp = pt.to_compressed_bytes()?;
        pt.wipe();
        let h20 = hash160(&comp);
        ct_zeroize_bytes(&mut comp);
        Some(LegacyCommitmentKind::BitcoinHash160(h20))
    }

    /// Compute the BIP-341 Taproot tweaked x-only public key commitment:
    /// `d_even = y(d*G) is even ? d : n - d`, `t = SHA256_tagged("TapTweak", x(d_even * G))`,
    /// `Q = (d_even + t mod n) * G` -> `x(Q)`!
    pub fn compute_taproot_tweaked_xonly(&self) -> Option<LegacyCommitmentKind> {
        let sk = self.secret_scalar_or_seed.expose();
        if !secp_scalar_is_valid_nonzero(sk) {
            return None;
        }
        let mut internal_pt = SecpPoint::generator_mul_ct(sk);
        let (ix, iy) = internal_pt.to_affine()?;
        internal_pt.wipe();

        let mut internal_x = ix.to_be_bytes();
        let mut neg_sk = secp_scalar_neg_mod_n(sk);
        let y_odd = iy.is_odd();
        let mut d_even = [0u8; 32];
        for (i, slot) in d_even.iter_mut().enumerate() {
            *slot = ct_select_u64(y_odd, neg_sk[i] as u64, sk[i] as u64) as u8;
        }
        ct_zeroize_bytes(&mut neg_sk);

        let mut tweak = sha256_tagged(b"TapTweak", &internal_x);
        ct_zeroize_bytes(&mut internal_x);
        if !secp_scalar_is_canonical(&tweak) {
            ct_zeroize_bytes(&mut d_even);
            ct_zeroize_bytes(&mut tweak);
            return None;
        }
        let mut tweaked_sk = secp_scalar_add_mod_n(&d_even, &tweak);
        ct_zeroize_bytes(&mut d_even);
        ct_zeroize_bytes(&mut tweak);

        let mut out_pt = SecpPoint::generator_mul_ct(&tweaked_sk);
        ct_zeroize_bytes(&mut tweaked_sk);
        let (qx, _) = out_pt.to_affine()?;
        out_pt.wipe();
        Some(LegacyCommitmentKind::BitcoinTaprootXOnly(qx.to_be_bytes()))
    }

    /// Compute the Ethereum 20-byte `Keccak256(uncompressed_pk_64)[12..32]` address commitment!
    pub fn compute_ethereum_keccak20(&self) -> Option<LegacyCommitmentKind> {
        let sk = self.secret_scalar_or_seed.expose();
        if !secp_scalar_is_valid_nonzero(sk) {
            return None;
        }
        let mut pt = SecpPoint::generator_mul_ct(sk);
        let mut uncomp = pt.to_uncompressed_64()?;
        pt.wipe();
        let mut k = keccak256(&uncomp);
        ct_zeroize_bytes(&mut uncomp);
        let mut addr20 = [0u8; 20];
        addr20.copy_from_slice(&k[12..32]);
        ct_zeroize_bytes(&mut k);
        Some(LegacyCommitmentKind::EthereumKeccak20(addr20))
    }

    /// Derive the RFC 8032 public key from the SLIP-0010 child seed.
    pub fn compute_slip0010_commitment(&self) -> LegacyCommitmentKind {
        let mut h = sha512(self.secret_scalar_or_seed.expose());
        // RFC 8032 Ed25519 scalar clamping on `h[0..32]`
        h[0] &= 248;
        h[31] &= 127;
        h[31] |= 64;
        let mut clamped = [0u8; 32];
        clamped.copy_from_slice(&h[0..32]);
        ct_zeroize_bytes(&mut h);

        let out = crate::ed25519_ct::public_key_from_clamped_scalar(&clamped);
        ct_zeroize_bytes(&mut clamped);
        LegacyCommitmentKind::Slip0010Ed25519(out)
    }

    /// Normalize the key to the nonzero subgroup scalar proved by migration.
    /// Taproot includes the key-path tweak and output parity normalization.
    pub fn spending_scalar(
        &self,
        kind: &LegacyCommitmentKind,
    ) -> Option<crate::scalar::SpendingScalar> {
        use crate::scalar::{self, ScalarGroup, SpendingScalar};
        let mut bytes = *self.secret_scalar_or_seed.expose();
        let group = match kind {
            LegacyCommitmentKind::Slip0010Ed25519(_) => {
                let mut digest = sha512(&bytes);
                digest[0] &= 248;
                digest[31] = (digest[31] & 127) | 64;
                bytes.copy_from_slice(&digest[..32]);
                ct_zeroize_bytes(&mut digest);
                bytes = scalar::encode(scalar::reduce(&bytes, scalar::ED_ORDER));
                ScalarGroup::Ed25519
            }
            LegacyCommitmentKind::BitcoinTaprootXOnly(_) => {
                if !secp_scalar_is_valid_nonzero(&bytes) {
                    ct_zeroize_bytes(&mut bytes);
                    return None;
                }
                let mut point = SecpPoint::generator_mul_ct(&bytes);
                let (x, y) = point.to_affine()?;
                point.wipe();
                let mut neg = secp_scalar_neg_mod_n(&bytes);
                for (b, n) in bytes.iter_mut().zip(&neg) {
                    *b = ct_select_u64(y.is_odd(), *n as u64, *b as u64) as u8;
                }
                ct_zeroize_bytes(&mut neg);
                let mut tweak = sha256_tagged(b"TapTweak", &x.to_be_bytes());
                if !secp_scalar_is_canonical(&tweak) {
                    ct_zeroize_bytes(&mut bytes);
                    ct_zeroize_bytes(&mut tweak);
                    return None;
                }
                bytes = secp_scalar_add_mod_n(&bytes, &tweak);
                ct_zeroize_bytes(&mut tweak);
                if !secp_scalar_is_valid_nonzero(&bytes) {
                    ct_zeroize_bytes(&mut bytes);
                    return None;
                }
                let mut output = SecpPoint::generator_mul_ct(&bytes);
                let (_, y) = output.to_affine()?;
                output.wipe();
                let mut neg = secp_scalar_neg_mod_n(&bytes);
                for (b, n) in bytes.iter_mut().zip(&neg) {
                    *b = ct_select_u64(y.is_odd(), *n as u64, *b as u64) as u8;
                }
                ct_zeroize_bytes(&mut neg);
                bytes.reverse();
                ScalarGroup::Secp256k1
            }
            _ => {
                bytes.reverse();
                ScalarGroup::Secp256k1
            }
        };
        let result = SpendingScalar::from_le_bytes(bytes, group);
        ct_zeroize_bytes(&mut bytes);
        result
    }

    /// Normalize the spending key for the selected legacy address format.
    /// This does not check the address bytes; use `matches_commitment` separately.
    pub fn normalize_spending_scalar(
        &self,
        kind: &LegacyCommitmentKind,
    ) -> Option<crate::scalar::SpendingScalar> {
        self.spending_scalar(kind)
    }

    /// Derive a nullifier from the normalized spending key, never from the seed,
    /// derivation path or untweaked Taproot internal key.
    /// This does not prove ownership or check the supplied commitment bytes.
    pub fn compute_nullifier(
        &self,
        kind: &LegacyCommitmentKind,
        migration_domain: &[u8; 32],
    ) -> Option<[u64; 4]> {
        Some(
            self.normalize_spending_scalar(kind)?
                .compute_nullifier(migration_domain),
        )
    }

    /// Verify locally that `self` matches `target` before running the PQ-ZK prover.
    pub fn matches_commitment(&self, target: &LegacyCommitmentKind) -> bool {
        let actual = match target {
            LegacyCommitmentKind::BitcoinHash160(_) => self.compute_bitcoin_hash160(),
            LegacyCommitmentKind::BitcoinTaprootXOnly(_) => self.compute_taproot_tweaked_xonly(),
            LegacyCommitmentKind::EthereumKeccak20(_) => self.compute_ethereum_keccak20(),
            LegacyCommitmentKind::Slip0010Ed25519(_) => Some(self.compute_slip0010_commitment()),
        };
        actual.as_ref() == Some(target)
    }
}
