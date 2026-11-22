//! Ownership statements over zk-Hem and their proofs.
//!
//! A statement says: the prover knows the secret behind one on-chain legacy credential,
//! and binds that knowledge to a post-quantum address commitment, a migration domain and
//! an epoch. It has two independent parts:
//!
//! * a [`Lock`]: how the chain derives the credential from a public key (P2PKH/P2WPKH,
//!   uncompressed P2PKH, P2SH-wrapped P2WPKH, Ethereum address, Taproot output key with or
//!   without a script tree, Ed25519 key, BLS12-381 `0x00` withdrawal credential);
//! * a [`KeySource`]: what the prover knows about that key. Either the signing key itself
//!   (`Secp256k1Key`, `Bls12381Key`), or a hash preimage the key is derived from: an RFC 8032 seed, a
//!   BIP-32 master seed or extended key with a path, a SLIP-0010 seed with a path, a
//!   BIP32-Ed25519 extended key with a path.
//!
//! Any lock of a curve combines with any source of that curve, so a seed proof can target
//! every credential type of its key. [`BatchStatement`] proves many credentials below one
//! BIP-32 node in one proof.
//!
//! # Which source is sound against which adversary
//!
//! A `Secp256k1Key` statement is sound only while the public key is not public: whoever
//! computes the discrete logarithm satisfies it. It is the hidden-key mode
//! (`KeyExposure::Hidden`). The one exception is a Taproot lock: the output key is public,
//! but the statement is knowledge of an internal key `k` (and merkle root `m`) with
//! `Q = lift_x([k]G) + H_TapTweak(x || m) G`. Knowing `log Q` does not give such a pair,
//! because `k` is under the hash; that statement fails only if the internal key itself
//! has been published (a script-path spend, an exported xpub), so it is also hidden-key
//! mode, about the internal key.
//!
//! The other sources are sound for revealed keys (`KeyExposure::Revealed`): their witness
//! is a preimage of the hash chain that produced the key.
//!
//! * `Ed25519Seed`, `Slip10`, `Bip32 { root: Seed }`: the chain starts at the seed.
//! * `Bip32 { root: ExtendedKey }` and `Bip32Ed25519` start at an extended private key.
//!   That is sound exactly when that node's chain code cannot be computed from public
//!   data, i.e. no extended public key at or above the start node was ever exported: with
//!   the chain code and the discrete logarithm of the node's public key an adversary has
//!   the whole witness. This is the unsoundness of last-step proofs in ZKPoSP
//!   (`2026-zkposp-pq-zk-proofs-hd-wallets-seed-provenance-2026-1508`, Proposition 6.1 and
//!   Remark 4.4), which is why that paper always goes back to the seed for non-hardened
//!   paths. The seed-rooted statement is the conservative choice; the extended-key root
//!   exists because it is four SHA-512 compressions cheaper per omitted step and because
//!   the root derivations deployed for BIP32-Ed25519 are not provable (Cardano's Icarus
//!   root is PBKDF2 with 4096 iterations).
//!
//! # The credential identifier prevents double migration; the nullifier does not
//!
//! Requirement A: the nullifier of a revealed key must not be computable from public data
//! plus discrete logarithms. Requirement B: a credential has one nullifier per domain
//! whichever statement proves it. Both cannot hold across hidden-key and seed statements
//! of the same key: a hidden-key statement's witness is the scalar alone, so its nullifier
//! is a function of the scalar, and B then makes every statement's nullifier that
//! function, which fails A for a revealed key.
//!
//! So uniqueness is carried by the on-chain credential, as in ePrint 2026/352 section 7.4
//! (`2026-pq-migration-bitcoin-ethereum-hidden-key-proofs-finalization-enforcement-2026-352`,
//! the registry record is keyed by the asset identifier): [`Credential::identifier`] is a
//! digest of what the chain holds, the registry refuses a second binding for it
//! (`LegacyConflict`), and every statement kind for one credential yields the same
//! identifier. Two credentials of one key (its P2PKH hash and its Ethereum address) are
//! two identifiers and migrate independently.
//!
//! The nullifier is the registry's record key and a commitment to the secret:
//! `SHA256(tag || kind || 00 00 || domain || credential identifier || 0^32 || secret)`,
//! tag `QSAG.MIGRATE.HEM.NULLIFIER/v2`. The first 128 bytes are public, so the verifier
//! supplies their SHA-256 chaining value and the relation runs one compression. `secret`
//! is, by source:
//!
//! | source | kind | secret |
//! |---|---|---|
//! | `Secp256k1Key` | 1 | the key, big-endian |
//! | `Bip32`, seed root | 2 | first 32 bytes of `SHA512((key ^ ipad) || seed)`, the inner digest of the master HMAC |
//! | `Ed25519Seed`, `Slip10` | 3 | the RFC 8032 seed of the leaf |
//! | `Bip32Ed25519` | 5 | the leaf's `k_R` |
//! | `Bls12381Key` | 6 | the key, big-endian |
//! | `Bip32`, extended-key root | 7 | the root chain code |
//!
//! For every revealed-key source the secret is not a function of public keys, chain codes
//! of exported extended public keys or discrete logarithms, so requirement A holds. It is
//! deterministic, so resubmitting a statement is idempotent, and a credential has one
//! nullifier per domain within a source (an Ed25519 key proved from its seed or through
//! SLIP-0010 has the same one). A hidden-key statement and a seed statement of the same
//! credential have different nullifiers and the same identifier; the second one to reach
//! a registry is refused by the identifier.
//!
//! # What is public and what is hidden
//!
//! Public inputs, one per bit: the credential value, the nullifier chaining value and the
//! nullifier. The post-quantum commitment and the epoch are bound through the transcript.
//! The seed length (16 to 64 bytes) is always hidden. A derivation path is public
//! ([`PathSpec::Public`], it selects the relation) or hidden up to a public maximum depth
//! ([`PathSpec::Hidden`]: indices, hardened flags and the actual depth are witness; every
//! step then costs a hardened step plus a public-key multiplication). BIP32-Ed25519 paths
//! are public only. Public keys, chain codes and all intermediate keys are never public.
//!
//! # Sizes, and what does not fit
//!
//! A statement costs about 44,000 rows per SHA-512 compression (one row per bit of every
//! three-input Boolean function and of every sum; the constraint system has no lookup
//! argument), four compressions per derivation step, about 32,500 rows per secp256k1
//! multiplication, and 17,200 for the nullifier. `m/44'/0'/0'/0/0` from the seed is 22
//! compressions and three multiplications, 1.106 million rows, 5 % over `2^20`. The
//! compressions are within 3 % of the one-row-per-bit floor, so the seed-rooted statement
//! cannot get under `2^20` on the hash side; it would take a multiplication of about
//! 14,000 rows. The same path from the master extended key is 1.019 million rows and fits.
//! When the first step is hardened, that statement differs from the seed-rooted one only
//! if the master extended public key has been exported, which wallets do not do.
//!
//! EIP-2333 seed provenance for BLS keys is not offered: one `derive_child_SK` is two
//! 255-block HKDF-SHA256 expansions, 510 chunk hashes and a 16,320-byte hash, measured
//! at 30.8 million rows, and the EIP-2334 withdrawal path has four of them (123 million
//! rows, `2^27`), which exceeds the largest table the commitment scheme supports once the
//! masks are added. A BLS withdrawal key is migrated in hidden-key mode, which is sound
//! while its public key is behind the `0x00` credential's hash.
//!
//! # BIP-39 is outside the relation
//!
//! A mnemonic maps to the seed by PBKDF2-HMAC-SHA512 with 2048 iterations (about 180
//! million rows). Proving it would add nothing: the seed is already a secret that no
//! public value determines, the statement is already unsatisfiable without a preimage of
//! the master HMAC, and whoever holds the mnemonic holds the seed. [`bip39_seed`] is the
//! native map a wallet runs before proving.
//!
//! # Relations contain multiplication rows only
//!
//! No S-box rows and no Poseidon2, so the collaborative prover of [`super::collab`] can
//! run them; [`synthesize_ownership`] is its entry point.

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use qsag_accel::keccak::{cshake256_framed_32, keccak256 as keccak256_native};
use qsag_accel::sha2 as sha2_native;
use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as protocol, ZkHemV2Error, ZkHemV2Proof};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Def, Definitions, Lc, Shape, Source};

use super::curve::{
    Element, Lazy, Modulus, bls12_381_enforce_scalar_range, bls12_381_g1_fixed_base_mul,
    ed25519_clamp, ed25519_fixed_base_mul, secp256k1_enforce_scalar_range,
    secp256k1_fixed_base_mul, secp256k1_taproot_tweak_x_only,
};
use super::hash::{
    HmacKey, Word, add_wide, alloc_bits, be_bits, be_words, const_bits, hash160, keccak256,
    pack_bits, select, sha256, sha256_from_midstate, sha256_midstate, sha512, sha512_compress,
};
use crate::ed25519_ct::public_key_from_clamped_scalar;
use crate::secp256k1_ct::{
    SecpPoint, secp_scalar_add_mod_n, secp_scalar_is_canonical, secp_scalar_is_valid_nonzero,
    secp_scalar_neg_mod_n,
};

type F = Goldilocks;

const NULLIFIER_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.NULLIFIER/v2";
const STATEMENT_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.OWNERSHIP/v2";
const BATCH_TAG: &[u8; 25] = b"QSAG.MIGRATE.HEM.BATCH/v1";
const PROOF_MAGIC: &[u8; 8] = b"QSHEMOW2";
const BIP32_MASTER_KEY: &[u8] = b"Bitcoin seed";
const SLIP10_ED25519_KEY: &[u8] = b"ed25519 seed";

/// First hardened child index.
pub const HARDENED: u32 = 0x8000_0000;
/// Longest derivation path, public or hidden.
pub const MAX_PATH_DEPTH: usize = 10;
/// Master seed lengths, in bytes (BIP-32 and SLIP-0010).
pub const SEED_BYTES: core::ops::RangeInclusive<usize> = 16..=64;
/// Most credentials one batch may carry.
pub const MAX_BATCH_ENTRIES: usize = 1024;

fn wipe(bytes: &mut [u8]) {
    qsag_asm::volatile_fill(bytes, 0);
}

fn fu(v: u64) -> F {
    F::from_u64_reduced(v)
}

// ============================================================================
// Credentials
// ============================================================================

/// What the chain holds for a legacy credential.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Credential {
    /// The 20-byte public-key hash of a P2PKH or P2WPKH output.
    BitcoinKeyHash([u8; 20]),
    /// The 32-byte x-only output key of a Taproot output.
    BitcoinTaproot([u8; 32]),
    /// The 20-byte Ethereum address.
    EthereumAddress([u8; 20]),
    /// A 32-byte Ed25519 public key.
    Ed25519Key([u8; 32]),
    /// The 20-byte script hash of a P2SH output.
    BitcoinScriptHash([u8; 20]),
    /// A 32-byte Ethereum consensus-layer `0x00` (BLS) withdrawal credential.
    BlsWithdrawal([u8; 32]),
}

/// Registry-wide identifier of a credential of type `tag` with on-chain bytes `value`.
/// The tags are [`Credential::tag`]; they are part of the registry's on-disk format.
pub fn credential_identifier(tag: u8, value: &[u8]) -> [u8; 32] {
    cshake256_framed_32(b"QSAG.MIGRATE.REGISTRY.LEGACY.V1", &[&[tag], value])
}

impl Credential {
    pub fn tag(&self) -> u8 {
        match self {
            Self::BitcoinKeyHash(_) => 1,
            Self::BitcoinTaproot(_) => 2,
            Self::EthereumAddress(_) => 3,
            Self::Ed25519Key(_) => 4,
            Self::BitcoinScriptHash(_) => 5,
            Self::BlsWithdrawal(_) => 6,
        }
    }

    /// The on-chain bytes.
    pub fn value(&self) -> &[u8] {
        match self {
            Self::BitcoinKeyHash(v) | Self::EthereumAddress(v) | Self::BitcoinScriptHash(v) => v,
            Self::BitcoinTaproot(v) | Self::Ed25519Key(v) | Self::BlsWithdrawal(v) => v,
        }
    }

    /// The identifier the registry keeps unique: one per on-chain credential, whichever
    /// statement migrates it.
    pub fn identifier(&self) -> [u8; 32] {
        credential_identifier(self.tag(), self.value())
    }
}

/// How the chain derives a credential from a public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Lock {
    /// `HASH160(compressed key)`: P2PKH and P2WPKH.
    P2pkh = 1,
    /// `HASH160(04 || x || y)`: P2PKH of an uncompressed key.
    P2pkhUncompressed = 2,
    /// `HASH160(00 14 || HASH160(compressed key))`: P2SH-wrapped P2WPKH (BIP-49).
    P2shP2wpkh = 3,
    /// Last 20 bytes of `Keccak256(x || y)`.
    Ethereum = 4,
    /// BIP-341 output key without a script tree (BIP-86): `lift_x(P) + H_TapTweak(x(P)) G`.
    TaprootKeyPath = 5,
    /// BIP-341 output key with a script tree whose merkle root is part of the witness:
    /// `lift_x(P) + H_TapTweak(x(P) || root) G`.
    TaprootScriptTree = 6,
    /// The Ed25519 public key itself.
    Ed25519 = 7,
    /// `00 || SHA256(compressed G1 key)[1..]`: the `0x00` withdrawal credential of a
    /// BLS12-381 key.
    BlsWithdrawal = 8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Curve {
    Secp256k1,
    Ed25519,
    Bls12381,
}

impl Lock {
    fn from_tag(tag: u8) -> Option<Self> {
        [
            Self::P2pkh,
            Self::P2pkhUncompressed,
            Self::P2shP2wpkh,
            Self::Ethereum,
            Self::TaprootKeyPath,
            Self::TaprootScriptTree,
            Self::Ed25519,
            Self::BlsWithdrawal,
        ]
        .into_iter()
        .find(|l| *l as u8 == tag)
    }

    fn curve(self) -> Curve {
        match self {
            Self::Ed25519 => Curve::Ed25519,
            Self::BlsWithdrawal => Curve::Bls12381,
            _ => Curve::Secp256k1,
        }
    }

    fn credential_bytes(self) -> usize {
        match self {
            Self::TaprootKeyPath
            | Self::TaprootScriptTree
            | Self::Ed25519
            | Self::BlsWithdrawal => 32,
            _ => 20,
        }
    }

    /// The credential type this lock produces, around its on-chain bytes.
    fn credential(self, value: &[u8]) -> Option<Credential> {
        Some(match self {
            Self::P2pkh | Self::P2pkhUncompressed => {
                Credential::BitcoinKeyHash(value.try_into().ok()?)
            }
            Self::P2shP2wpkh => Credential::BitcoinScriptHash(value.try_into().ok()?),
            Self::Ethereum => Credential::EthereumAddress(value.try_into().ok()?),
            Self::TaprootKeyPath | Self::TaprootScriptTree => {
                Credential::BitcoinTaproot(value.try_into().ok()?)
            }
            Self::Ed25519 => Credential::Ed25519Key(value.try_into().ok()?),
            Self::BlsWithdrawal => Credential::BlsWithdrawal(value.try_into().ok()?),
        })
    }
}

// ============================================================================
// Native reference functions
// ============================================================================

/// SEC1 compressed public key of a big-endian secp256k1 secret key; `None` unless
/// `1 <= k < n`.
pub fn secp256k1_public_key(key_be: &[u8; 32]) -> Option<[u8; 33]> {
    secp_scalar_is_valid_nonzero(key_be)
        .then(|| SecpPoint::generator_mul_ct(key_be).to_compressed_bytes())
        .flatten()
}

fn secp256k1_uncompressed(key_be: &[u8; 32]) -> Option<[u8; 64]> {
    secp_scalar_is_valid_nonzero(key_be)
        .then(|| SecpPoint::generator_mul_ct(key_be).to_uncompressed_64())
        .flatten()
}

/// BIP-341 `H_TapTweak(x || merkle_root)`.
pub fn taproot_tweak(internal_x: &[u8; 32], merkle_root: Option<&[u8; 32]>) -> [u8; 32] {
    let mut msg = internal_x.to_vec();
    if let Some(root) = merkle_root {
        msg.extend_from_slice(root);
    }
    sha2_native::sha256_tagged(b"TapTweak", &msg)
}

/// BIP-341 x-only output key for the internal key `[k]G`: `lift_x(P) + t G`. `None` when
/// the key is invalid, the tweak is not below the group order or the result is infinity.
pub fn taproot_output_key(key_be: &[u8; 32], merkle_root: Option<&[u8; 32]>) -> Option<[u8; 32]> {
    let internal = secp256k1_public_key(key_be)?;
    let x: [u8; 32] = internal[1..].try_into().ok()?;
    // `lift_x` takes the even point: its secret is `k` or `n - k`.
    let mut even = if internal[0] == 3 {
        secp_scalar_neg_mod_n(key_be)
    } else {
        *key_be
    };
    let tweak = taproot_tweak(&x, merkle_root);
    if !secp_scalar_is_canonical(&tweak) {
        return None;
    }
    let mut output = secp_scalar_add_mod_n(&even, &tweak);
    wipe(&mut even);
    let out = secp256k1_public_key(&output)?[1..].try_into().ok();
    wipe(&mut output);
    out
}

/// The credential a secp256k1 key has under `lock`. `merkle_root` is used by
/// [`Lock::TaprootScriptTree`] only.
pub fn secp256k1_credential(
    lock: Lock,
    key_be: &[u8; 32],
    merkle_root: Option<&[u8; 32]>,
) -> Option<Credential> {
    let compressed = secp256k1_public_key(key_be)?;
    Some(match lock {
        Lock::P2pkh => Credential::BitcoinKeyHash(sha2_native::hash160(&compressed)),
        Lock::P2pkhUncompressed => {
            let mut sec1 = vec![4u8];
            sec1.extend_from_slice(&secp256k1_uncompressed(key_be)?);
            Credential::BitcoinKeyHash(sha2_native::hash160(&sec1))
        }
        Lock::P2shP2wpkh => {
            let mut script = vec![0u8, 0x14];
            script.extend_from_slice(&sha2_native::hash160(&compressed));
            Credential::BitcoinScriptHash(sha2_native::hash160(&script))
        }
        Lock::Ethereum => {
            let digest = keccak256_native(&secp256k1_uncompressed(key_be)?);
            Credential::EthereumAddress(digest[12..].try_into().ok()?)
        }
        Lock::TaprootKeyPath => Credential::BitcoinTaproot(taproot_output_key(key_be, None)?),
        Lock::TaprootScriptTree => {
            Credential::BitcoinTaproot(taproot_output_key(key_be, Some(merkle_root?))?)
        }
        Lock::Ed25519 | Lock::BlsWithdrawal => return None,
    })
}

/// The BLS12-381 subgroup order, big-endian.
const BLS12_381_ORDER_BE: [u8; 32] = [
    0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
    0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
];

/// Compressed G1 public key of a big-endian BLS12-381 secret key; `None` unless
/// `1 <= k < r`.
///
/// The crate has no separate native G1 arithmetic: the value is read off the assignment
/// that [`bls12_381_g1_fixed_base_mul`] computes, whose encodings `hem::curve` tests
/// against recorded vectors.
pub fn bls12_381_public_key(key_be: &[u8; 32]) -> Option<[u8; 48]> {
    // Lexicographic comparison of big-endian bytes, without an early exit.
    let (mut below, mut equal, mut nonzero) = (0u8, 1u8, 0u8);
    for (&k, &r) in key_be.iter().zip(&BLS12_381_ORDER_BE) {
        below |= equal & u8::from(k < r);
        equal &= u8::from(k == r);
        nonzero |= k;
    }
    if below == 0 || nonzero == 0 {
        return None;
    }
    let mut cs = ConstraintSystem::new();
    let bits = reverse_bytes(&alloc_bits(&mut cs, key_be));
    let public_key = bls12_381_g1_fixed_base_mul(&mut cs, &bits[..255]);
    super::hash::bits_to_bytes(&cs, &flat(public_key.compressed_bits()))
        .try_into()
        .ok()
}

/// The `0x00` withdrawal credential of a BLS12-381 secret key.
pub fn bls_withdrawal_credential(key_be: &[u8; 32]) -> Option<Credential> {
    let mut digest = sha2_native::sha256(&bls12_381_public_key(key_be)?);
    digest[0] = 0;
    Some(Credential::BlsWithdrawal(digest))
}

/// RFC 8032 secret scalar of a seed: the clamped first half of `SHA512(seed)`,
/// little-endian.
pub fn ed25519_clamped_scalar(seed: &[u8; 32]) -> [u8; 32] {
    let mut digest = sha2_native::sha512(seed);
    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(&digest[..32]);
    wipe(&mut digest);
    scalar[0] &= 0xf8;
    scalar[31] &= 0x7f;
    scalar[31] |= 0x40;
    scalar
}

/// RFC 8032 public key of a seed.
pub fn ed25519_public_key(seed: &[u8; 32]) -> [u8; 32] {
    let mut scalar = ed25519_clamped_scalar(seed);
    let out = public_key_from_clamped_scalar(&scalar);
    wipe(&mut scalar);
    out
}

fn split64(mut i: [u8; 64]) -> ([u8; 32], [u8; 32]) {
    let (mut left, mut right) = ([0u8; 32], [0u8; 32]);
    left.copy_from_slice(&i[..32]);
    right.copy_from_slice(&i[32..]);
    wipe(&mut i);
    (left, right)
}

/// First 32 bytes of `SHA512((key ^ ipad) || seed)`: the inner digest of the master HMAC,
/// the nullifier secret of a seed-rooted BIP-32 statement.
fn master_inner_digest(hmac_key: &[u8], seed: &[u8]) -> [u8; 32] {
    let mut message = vec![0x36u8; 128];
    for (m, k) in message.iter_mut().zip(hmac_key) {
        *m ^= k;
    }
    message.extend_from_slice(seed);
    let mut digest = sha2_native::sha512(&message);
    wipe(&mut message);
    let out = digest[..32].try_into().expect("32 bytes");
    wipe(&mut digest);
    out
}

/// A private key with its chain code: a BIP-32 secp256k1 node (`private_key` big-endian)
/// or a SLIP-0010 Ed25519 node (`private_key` is an RFC 8032 seed). Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub struct HdNode {
    pub private_key: [u8; 32],
    pub chain_code: [u8; 32],
}

impl Drop for HdNode {
    fn drop(&mut self) {
        wipe(&mut self.private_key);
        wipe(&mut self.chain_code);
    }
}

/// BIP-32 master key of a seed; `None` when `I_L` is zero or not below the group order.
pub fn bip32_master(seed: &[u8]) -> Option<HdNode> {
    let (private_key, chain_code) = split64(sha2_native::hmac_sha512(BIP32_MASTER_KEY, seed));
    let node = HdNode {
        private_key,
        chain_code,
    };
    secp_scalar_is_valid_nonzero(&node.private_key).then_some(node)
}

/// BIP-32 private child derivation (`CKDpriv`); `None` when `I_L` is not below the group
/// order or the child key is zero.
pub fn bip32_child(parent: &HdNode, index: u32) -> Option<HdNode> {
    let mut data = [0u8; 37];
    if index >= HARDENED {
        data[1..33].copy_from_slice(&parent.private_key);
    } else {
        data[..33].copy_from_slice(&secp256k1_public_key(&parent.private_key)?);
    }
    data[33..].copy_from_slice(&index.to_be_bytes());
    let (mut tweak, chain_code) = split64(sha2_native::hmac_sha512(&parent.chain_code, &data));
    wipe(&mut data);
    let in_range = secp_scalar_is_canonical(&tweak);
    let node = HdNode {
        private_key: secp_scalar_add_mod_n(&tweak, &parent.private_key),
        chain_code,
    };
    wipe(&mut tweak);
    (in_range && secp_scalar_is_valid_nonzero(&node.private_key)).then_some(node)
}

/// The BIP-32 node at `path` below `root`.
pub fn bip32_descend(root: HdNode, path: &[u32]) -> Option<HdNode> {
    path.iter()
        .try_fold(root, |node, &index| bip32_child(&node, index))
}

/// The BIP-32 node at `m / path`.
pub fn bip32_derive(seed: &[u8], path: &[u32]) -> Option<HdNode> {
    bip32_descend(bip32_master(seed)?, path)
}

/// SLIP-0010 Ed25519 node at `m / path`; `None` unless every index is hardened.
pub fn slip10_ed25519_derive(seed: &[u8], path: &[u32]) -> Option<HdNode> {
    let (private_key, chain_code) = split64(sha2_native::hmac_sha512(SLIP10_ED25519_KEY, seed));
    let mut node = HdNode {
        private_key,
        chain_code,
    };
    for &index in path {
        if index < HARDENED {
            return None;
        }
        let mut data = [0u8; 37];
        data[1..33].copy_from_slice(&node.private_key);
        data[33..].copy_from_slice(&index.to_be_bytes());
        let (private_key, chain_code) = split64(sha2_native::hmac_sha512(&node.chain_code, &data));
        wipe(&mut data);
        node = HdNode {
            private_key,
            chain_code,
        };
    }
    Some(node)
}

/// A BIP32-Ed25519 extended private key `k_L || k_R || chain code` (Khovratovich and Law,
/// `2017-khovratovich-law-bip32-ed25519-hierarchical-deterministic-keys-nonlinear-keyspace`,
/// section V; the scheme Cardano deploys). Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub struct Ed25519ExtendedKey(pub [u8; 96]);

impl Drop for Ed25519ExtendedKey {
    fn drop(&mut self) {
        wipe(&mut self.0);
    }
}

impl Ed25519ExtendedKey {
    /// `[k_L] B`.
    pub fn public_key(&self) -> [u8; 32] {
        public_key_from_clamped_scalar(self.0[..32].try_into().expect("32 bytes"))
    }

    /// Child derivation: `Z = HMAC(c, 00 || k_L || k_R || i)` for a hardened index and
    /// `HMAC(c, 02 || A || i)` otherwise, `k_L' = k_L + 8 Z[0..28]`, `k_R' = k_R + Z[32..64]`
    /// (both modulo `2^256`, little-endian), and the chain code is the right half of the
    /// same HMAC with the tag `01` or `03`. The index is little-endian.
    pub fn child(&self, index: u32) -> Self {
        let (mut z_data, tag) = if index >= HARDENED {
            (self.0[..64].to_vec(), 0u8)
        } else {
            (self.public_key().to_vec(), 2u8)
        };
        z_data.insert(0, tag);
        z_data.extend_from_slice(&index.to_le_bytes());
        let mut z = sha2_native::hmac_sha512(&self.0[64..], &z_data);
        z_data[0] = tag + 1;
        let mut c = sha2_native::hmac_sha512(&self.0[64..], &z_data);
        wipe(&mut z_data);

        let mut out = [0u8; 96];
        let mut carry = 0u16;
        for i in 0..32 {
            let add = if i < 28 { u16::from(z[i]) << 3 } else { 0 };
            let v = u16::from(self.0[i]) + add + carry;
            out[i] = v as u8;
            carry = v >> 8;
        }
        carry = 0;
        for i in 32..64 {
            let v = u16::from(self.0[i]) + u16::from(z[i]) + carry;
            out[i] = v as u8;
            carry = v >> 8;
        }
        out[64..].copy_from_slice(&c[32..]);
        wipe(&mut z);
        wipe(&mut c);
        Self(out)
    }

    /// The key at `path` below this one.
    pub fn descend(&self, path: &[u32]) -> Self {
        path.iter().fold(self.clone(), |key, &i| key.child(i))
    }
}

/// BIP-39 seed of a mnemonic sentence and passphrase:
/// `PBKDF2-HMAC-SHA512(mnemonic, "mnemonic" || passphrase, 2048, 64)`. Both strings must
/// already be in Unicode NFKD form (ASCII text is).
pub fn bip39_seed(mnemonic_nfkd: &str, passphrase_nfkd: &str) -> [u8; 64] {
    let mut salt = b"mnemonic".to_vec();
    salt.extend_from_slice(passphrase_nfkd.as_bytes());
    salt.extend_from_slice(&1u32.to_be_bytes());
    let mut u = sha2_native::hmac_sha512(mnemonic_nfkd.as_bytes(), &salt);
    let mut out = u;
    for _ in 1..2048 {
        u = sha2_native::hmac_sha512(mnemonic_nfkd.as_bytes(), &u);
        for (o, x) in out.iter_mut().zip(&u) {
            *o ^= x;
        }
    }
    wipe(&mut u);
    wipe(&mut salt);
    out
}

/// The 128 public bytes that precede the secret in a nullifier preimage.
pub fn nullifier_prefix(
    kind: u8,
    migration_domain: &[u8; 32],
    credential: &Credential,
) -> [u8; 128] {
    let mut out = [0u8; 128];
    out[..29].copy_from_slice(NULLIFIER_TAG);
    out[29] = kind;
    out[32..64].copy_from_slice(migration_domain);
    out[64..96].copy_from_slice(&credential.identifier());
    out
}

/// The nullifier of `secret` (see the module documentation for what the secret is for
/// each `kind`) for one credential in one migration domain.
pub fn migration_nullifier(
    kind: u8,
    secret: &[u8; 32],
    migration_domain: &[u8; 32],
    credential: &Credential,
) -> [u8; 32] {
    let mut preimage = nullifier_prefix(kind, migration_domain, credential).to_vec();
    preimage.extend_from_slice(secret);
    let out = sha2_native::sha256(&preimage);
    wipe(&mut preimage);
    out
}

// ============================================================================
// Statements
// ============================================================================

/// A derivation path as part of a statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathSpec {
    /// The path is public and selects the relation.
    Public(Vec<u32>),
    /// The indices, their hardened flags and the depth (at most `max_depth`) are witness.
    Hidden { max_depth: u8 },
}

/// Where a BIP-32 statement starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Bip32Root {
    /// The master seed (16 to 64 bytes, length hidden).
    Seed = 0,
    /// An extended private key (key and chain code). Sound only while no extended public
    /// key at or above it has been exported; see the module documentation.
    ExtendedKey = 1,
}

/// What the prover knows about the key behind the credential.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeySource {
    /// The secp256k1 secret key (hidden-key mode).
    Secp256k1Key,
    /// A BIP-32 root and a path to the secp256k1 key.
    Bip32 { root: Bip32Root, path: PathSpec },
    /// The RFC 8032 seed of the Ed25519 key.
    Ed25519Seed,
    /// A SLIP-0010 master seed and an all-hardened path to the Ed25519 key.
    Slip10 { path: PathSpec },
    /// A BIP32-Ed25519 extended private key and a public path to the Ed25519 key.
    Bip32Ed25519 { path: Vec<u32> },
    /// The BLS12-381 secret key (hidden-key mode).
    Bls12381Key,
}

impl KeySource {
    fn tag(&self) -> u8 {
        match self {
            Self::Secp256k1Key => 1,
            Self::Bip32 { .. } => 2,
            Self::Ed25519Seed => 3,
            Self::Slip10 { .. } => 4,
            Self::Bip32Ed25519 { .. } => 5,
            Self::Bls12381Key => 6,
        }
    }

    fn curve(&self) -> Curve {
        match self {
            Self::Secp256k1Key | Self::Bip32 { .. } => Curve::Secp256k1,
            Self::Bls12381Key => Curve::Bls12381,
            _ => Curve::Ed25519,
        }
    }

    /// The `kind` byte of the nullifier preimage.
    fn nullifier_kind(&self) -> u8 {
        match self {
            Self::Secp256k1Key => 1,
            Self::Bip32 {
                root: Bip32Root::Seed,
                ..
            } => 2,
            Self::Ed25519Seed | Self::Slip10 { .. } => 3,
            Self::Bip32Ed25519 { .. } => 5,
            Self::Bls12381Key => 6,
            Self::Bip32 {
                root: Bip32Root::ExtendedKey,
                ..
            } => 7,
        }
    }

    /// Whether the statement stays sound once the public key is public.
    pub fn proves_seed_provenance(&self) -> bool {
        !matches!(self, Self::Secp256k1Key | Self::Bls12381Key)
    }

    fn is_well_formed(&self) -> bool {
        let spec_ok = |spec: &PathSpec, hardened_only: bool| match spec {
            PathSpec::Public(path) => {
                path.len() <= MAX_PATH_DEPTH
                    && (!hardened_only || path.iter().all(|&i| i >= HARDENED))
            }
            PathSpec::Hidden { max_depth } => {
                (1..=MAX_PATH_DEPTH).contains(&usize::from(*max_depth))
            }
        };
        match self {
            Self::Secp256k1Key | Self::Ed25519Seed | Self::Bls12381Key => true,
            Self::Bip32 { path, .. } => spec_ok(path, false),
            Self::Slip10 { path } => spec_ok(path, true),
            Self::Bip32Ed25519 { path } => path.len() <= MAX_PATH_DEPTH,
        }
    }

    fn encode(&self, out: &mut Vec<u8>) {
        let spec = |out: &mut Vec<u8>, spec: &PathSpec| match spec {
            PathSpec::Public(path) => {
                out.push(0);
                out.push(path.len() as u8);
                for index in path {
                    out.extend_from_slice(&index.to_be_bytes());
                }
            }
            PathSpec::Hidden { max_depth } => out.extend_from_slice(&[1, *max_depth]),
        };
        out.push(self.tag());
        match self {
            Self::Secp256k1Key | Self::Ed25519Seed | Self::Bls12381Key => {}
            Self::Bip32 { root, path } => {
                out.push(*root as u8);
                spec(out, path);
            }
            Self::Slip10 { path } => spec(out, path),
            Self::Bip32Ed25519 { path } => spec(out, &PathSpec::Public(path.clone())),
        }
    }

    fn decode(take: &mut dyn FnMut(usize) -> Option<Vec<u8>>) -> Option<Self> {
        let spec = |take: &mut dyn FnMut(usize) -> Option<Vec<u8>>| -> Option<PathSpec> {
            let head = take(2)?;
            match head[0] {
                0 => Some(PathSpec::Public(
                    take(4 * usize::from(head[1]))?
                        .chunks_exact(4)
                        .map(|c| u32::from_be_bytes([c[0], c[1], c[2], c[3]]))
                        .collect(),
                )),
                1 => Some(PathSpec::Hidden { max_depth: head[1] }),
                _ => None,
            }
        };
        Some(match take(1)?[0] {
            1 => Self::Secp256k1Key,
            2 => {
                let root = match take(1)?[0] {
                    0 => Bip32Root::Seed,
                    1 => Bip32Root::ExtendedKey,
                    _ => return None,
                };
                Self::Bip32 {
                    root,
                    path: spec(take)?,
                }
            }
            3 => Self::Ed25519Seed,
            4 => Self::Slip10 { path: spec(take)? },
            5 => match spec(take)? {
                PathSpec::Public(path) => Self::Bip32Ed25519 { path },
                PathSpec::Hidden { .. } => return None,
            },
            6 => Self::Bls12381Key,
            _ => return None,
        })
    }
}

/// The secret behind a credential. Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub struct OwnershipWitness {
    secret: Vec<u8>,
    path: Vec<u32>,
    merkle_root: Option<[u8; 32]>,
}

impl Drop for OwnershipWitness {
    fn drop(&mut self) {
        wipe(&mut self.secret);
        qsag_asm::volatile_fill(&mut self.path, 0);
        if let Some(root) = &mut self.merkle_root {
            wipe(root);
        }
    }
}

impl OwnershipWitness {
    fn new(secret: &[u8]) -> Self {
        Self {
            secret: secret.to_vec(),
            path: Vec::new(),
            merkle_root: None,
        }
    }

    /// A big-endian secp256k1 secret key, for [`KeySource::Secp256k1Key`].
    pub fn secp256k1_key(key_be: &[u8; 32]) -> Self {
        Self::new(key_be)
    }

    /// A big-endian BLS12-381 secret key, for [`KeySource::Bls12381Key`].
    pub fn bls12_381_key(key_be: &[u8; 32]) -> Self {
        Self::new(key_be)
    }

    /// An RFC 8032 seed, for [`KeySource::Ed25519Seed`].
    pub fn ed25519_seed(seed: &[u8; 32]) -> Self {
        Self::new(seed)
    }

    /// A master seed of 16 to 64 bytes, for seed-rooted [`KeySource::Bip32`] and for
    /// [`KeySource::Slip10`].
    pub fn seed(seed: &[u8]) -> Self {
        Self::new(seed)
    }

    /// A BIP-32 extended private key, for [`Bip32Root::ExtendedKey`].
    pub fn extended_key(node: &HdNode) -> Self {
        let mut secret = node.private_key.to_vec();
        secret.extend_from_slice(&node.chain_code);
        let out = Self::new(&secret);
        wipe(&mut secret);
        out
    }

    /// A BIP32-Ed25519 extended private key, for [`KeySource::Bip32Ed25519`].
    pub fn ed25519_extended_key(key: &Ed25519ExtendedKey) -> Self {
        Self::new(&key.0)
    }

    /// The derivation path, for a statement whose path is [`PathSpec::Hidden`].
    pub fn with_path(mut self, path: &[u32]) -> Self {
        self.path = path.to_vec();
        self
    }

    /// The script tree's merkle root, for [`Lock::TaprootScriptTree`].
    pub fn with_merkle_root(mut self, root: [u8; 32]) -> Self {
        self.merkle_root = Some(root);
        self
    }
}

/// What a witness yields natively.
struct Evaluated {
    credential: Credential,
    nullifier_secret: [u8; 32],
}

impl Drop for Evaluated {
    fn drop(&mut self) {
        wipe(&mut self.nullifier_secret);
    }
}

/// The path a witness takes through `spec`; `None` when it does not fit.
fn resolve_path<'a>(spec: &'a PathSpec, witness: &'a OwnershipWitness) -> Option<&'a [u32]> {
    match spec {
        PathSpec::Public(path) => Some(path),
        PathSpec::Hidden { max_depth } => {
            (witness.path.len() <= usize::from(*max_depth)).then_some(&witness.path)
        }
    }
}

fn bip32_root_node(root: Bip32Root, secret: &[u8]) -> Option<HdNode> {
    match root {
        Bip32Root::Seed => SEED_BYTES
            .contains(&secret.len())
            .then(|| bip32_master(secret))
            .flatten(),
        Bip32Root::ExtendedKey => {
            let node = HdNode {
                private_key: secret.get(..32)?.try_into().ok()?,
                chain_code: secret.get(32..)?.try_into().ok()?,
            };
            secp_scalar_is_valid_nonzero(&node.private_key).then_some(node)
        }
    }
}

fn bip32_nullifier_secret(root: Bip32Root, secret: &[u8]) -> [u8; 32] {
    match root {
        Bip32Root::Seed => master_inner_digest(BIP32_MASTER_KEY, secret),
        Bip32Root::ExtendedKey => secret[32..64].try_into().expect("checked length"),
    }
}

/// The credential and nullifier secret of a witness; `None` when the witness does not fit
/// the lock and source or is not a valid secret for them.
fn evaluate(lock: Lock, source: &KeySource, witness: &OwnershipWitness) -> Option<Evaluated> {
    if lock.curve() != source.curve() || !source.is_well_formed() {
        return None;
    }
    let secret = witness.secret.as_slice();
    let root = witness.merkle_root.as_ref();
    match source {
        KeySource::Secp256k1Key => {
            let key: [u8; 32] = secret.try_into().ok()?;
            Some(Evaluated {
                credential: secp256k1_credential(lock, &key, root)?,
                nullifier_secret: key,
            })
        }
        KeySource::Bip32 { root: start, path } => {
            let node = bip32_descend(
                bip32_root_node(*start, secret)?,
                resolve_path(path, witness)?,
            )?;
            Some(Evaluated {
                credential: secp256k1_credential(lock, &node.private_key, root)?,
                nullifier_secret: bip32_nullifier_secret(*start, secret),
            })
        }
        KeySource::Bls12381Key => {
            let key: [u8; 32] = secret.try_into().ok()?;
            Some(Evaluated {
                credential: bls_withdrawal_credential(&key)?,
                nullifier_secret: key,
            })
        }
        KeySource::Ed25519Seed => {
            let seed: [u8; 32] = secret.try_into().ok()?;
            Some(Evaluated {
                credential: Credential::Ed25519Key(ed25519_public_key(&seed)),
                nullifier_secret: seed,
            })
        }
        KeySource::Slip10 { path } => {
            if !SEED_BYTES.contains(&secret.len()) {
                return None;
            }
            let node = slip10_ed25519_derive(secret, resolve_path(path, witness)?)?;
            Some(Evaluated {
                credential: Credential::Ed25519Key(ed25519_public_key(&node.private_key)),
                nullifier_secret: node.private_key,
            })
        }
        KeySource::Bip32Ed25519 { path } => {
            let leaf = Ed25519ExtendedKey(secret.try_into().ok()?).descend(path);
            // A scalar that is zero modulo the group order has no public key in the relation.
            let public_key = leaf.public_key();
            let identity = {
                let mut id = [0u8; 32];
                id[0] = 1;
                id
            };
            (public_key != identity).then(|| Evaluated {
                credential: Credential::Ed25519Key(public_key),
                nullifier_secret: leaf.0[32..64].try_into().expect("32 bytes"),
            })
        }
    }
}

/// Public statement of an ownership proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnershipStatement {
    pub lock: Lock,
    pub source: KeySource,
    /// The on-chain credential; its type is the one `lock` produces.
    pub credential: Credential,
    /// Commitment to the post-quantum address the credential migrates to
    /// (`registry::pq_commitment`). Chosen by the caller; not derived from the secret.
    pub pq_commitment: [u8; 32],
    /// Replay domain of the migration campaign.
    pub migration_domain: [u8; 32],
    pub epoch: u64,
    /// [`migration_nullifier`] for this credential and domain.
    pub nullifier: [u8; 32],
}

fn byte_bits(bytes: &[u8]) -> impl Iterator<Item = bool> + '_ {
    bytes
        .iter()
        .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1 == 1))
}

/// Public inputs of one credential: its value, the nullifier chaining value (eight words,
/// each least significant bit first) and the nullifier. Bytes are least significant bit
/// first.
fn credential_public_bits(
    out: &mut Vec<bool>,
    kind: u8,
    credential: &Credential,
    migration_domain: &[u8; 32],
    nullifier: &[u8; 32],
) {
    out.extend(byte_bits(credential.value()));
    for word in sha256_midstate(&nullifier_prefix(kind, migration_domain, credential)) {
        out.extend((0..32).map(|i| (word >> i) & 1 == 1));
    }
    out.extend(byte_bits(nullifier));
}

impl OwnershipStatement {
    /// The statement a holder derives from its secret. `None` when the witness does not
    /// fit the lock and source or is not a valid secret for them (a scalar outside `1..n`,
    /// a seed of the wrong length, a derivation BIP-32 rejects, a path longer than the
    /// source admits, a missing merkle root).
    pub fn derive(
        lock: Lock,
        source: KeySource,
        witness: &OwnershipWitness,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        let evaluated = evaluate(lock, &source, witness)?;
        let nullifier = migration_nullifier(
            source.nullifier_kind(),
            &evaluated.nullifier_secret,
            &migration_domain,
            &evaluated.credential,
        );
        Some(Self {
            lock,
            credential: evaluated.credential,
            source,
            pq_commitment,
            migration_domain,
            epoch,
            nullifier,
        })
    }

    /// Whether lock, source and credential type fit together and the source's parameters
    /// are within the supported ranges.
    pub fn is_well_formed(&self) -> bool {
        self.lock.curve() == self.source.curve()
            && self.source.is_well_formed()
            && self.lock.credential(self.credential.value()) == Some(self.credential)
    }

    /// Whether the statement stays sound when the legacy public key is public
    /// (`KeyExposure::Revealed`).
    pub fn key_is_revealed(&self) -> bool {
        self.source.proves_seed_provenance()
    }

    /// Canonical encoding; also the bytes the proof transcript absorbs.
    ///
    /// `tag(29) || lock || exposure || epoch(8, BE) || domain(32) || pq(32) || nullifier(32)
    /// || credential value (20 or 32) || source`, where the source is its kind byte, for
    /// BIP-32 the root byte, and for sources with a path `00 || depth || depth * index(4,
    /// BE)` (public) or `01 || max_depth` (hidden).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(200);
        out.extend_from_slice(STATEMENT_TAG);
        out.push(self.lock as u8);
        out.push(u8::from(self.key_is_revealed()));
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.migration_domain);
        out.extend_from_slice(&self.pq_commitment);
        out.extend_from_slice(&self.nullifier);
        out.extend_from_slice(self.credential.value());
        self.source.encode(&mut out);
        out
    }

    /// Strict inverse of [`Self::to_bytes`]: rejects unknown kinds, an exposure byte that
    /// does not match the source, a lock and source of different curves, parameters
    /// outside the supported ranges and any byte missing or left over.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes.strip_prefix(STATEMENT_TAG.as_slice())?;
        let mut take = |n: usize| -> Option<Vec<u8>> {
            let (head, tail) = rest.split_at_checked(n)?;
            rest = tail;
            Some(head.to_vec())
        };
        let lock = Lock::from_tag(take(1)?[0])?;
        let exposure = take(1)?[0];
        let epoch = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let migration_domain: [u8; 32] = take(32)?.try_into().ok()?;
        let pq_commitment: [u8; 32] = take(32)?.try_into().ok()?;
        let nullifier: [u8; 32] = take(32)?.try_into().ok()?;
        let credential = lock.credential(&take(lock.credential_bytes())?)?;
        let source = KeySource::decode(&mut take)?;
        let statement = Self {
            lock,
            source,
            credential,
            pq_commitment,
            migration_domain,
            epoch,
            nullifier,
        };
        (rest.is_empty()
            && exposure == u8::from(statement.key_is_revealed())
            && statement.is_well_formed())
        .then_some(statement)
    }

    fn public_bits(&self) -> Vec<bool> {
        let mut out = Vec::with_capacity(8 * self.lock.credential_bytes() + 512);
        credential_public_bits(
            &mut out,
            self.source.nullifier_kind(),
            &self.credential,
            &self.migration_domain,
            &self.nullifier,
        );
        out
    }

    /// The relation's public inputs, one per bit. `None` for a malformed statement.
    pub fn public_inputs(&self) -> Option<Vec<F>> {
        self.is_well_formed().then(|| {
            self.public_bits()
                .into_iter()
                .map(|b| fu(u64::from(b)))
                .collect()
        })
    }

    /// The exposure mode the registry records for this statement.
    #[cfg(feature = "std")]
    pub fn exposure(&self) -> super::registry::KeyExposure {
        if self.key_is_revealed() {
            super::registry::KeyExposure::Revealed
        } else {
            super::registry::KeyExposure::Hidden
        }
    }

    /// The binding a verified statement asks the registry to record.
    #[cfg(feature = "std")]
    pub fn binding(&self) -> super::registry::MigrationBinding {
        super::registry::MigrationBinding {
            nullifier: self.nullifier,
            migration_domain: self.migration_domain,
            legacy_id: self.credential.identifier(),
            pq_commitment: self.pq_commitment,
            epoch: self.epoch,
            exposure: self.exposure(),
        }
    }
}

// ============================================================================
// Relation gadgets
// ============================================================================

/// Reverse the byte order of a byte string: a big-endian integer's bytes become its
/// little-endian bits and back.
fn reverse_bytes(bits: &[Lc]) -> Vec<Lc> {
    bits.chunks(8).rev().flatten().cloned().collect()
}

/// `got = want` for Boolean bit strings, 60 bits per row.
fn pin(cs: &mut ConstraintSystem, got: &[Lc], want: &[Lc]) {
    assert_eq!(got.len(), want.len());
    for (g, w) in got.chunks(60).zip(want.chunks(60)) {
        cs.enforce_equal(&pack_bits(g), &pack_bits(w));
    }
}

fn alloc_bool(cs: &mut ConstraintSystem, value: bool) -> Lc {
    let source = cs.source(|| Source::Input { bits: 1 });
    let bit: Lc = cs
        .alloc_defined(fu(u64::from(value)), || Def::Bits {
            source,
            lo: 0,
            width: 1,
        })
        .into();
    cs.enforce_boolean(&bit);
    bit
}

fn select_bits(cs: &mut ConstraintSystem, bit: &Lc, on_one: &[Lc], on_zero: &[Lc]) -> Vec<Lc> {
    assert_eq!(on_one.len(), on_zero.len());
    on_one
        .iter()
        .zip(on_zero)
        .map(|(a, b)| select(cs, bit, a, b))
        .collect()
}

fn flat(bytes: Vec<[Lc; 8]>) -> Vec<Lc> {
    bytes.into_iter().flatten().collect()
}

/// `bits <= n - 1` for little-endian bits and the secp256k1 group order.
fn enforce_below_order(cs: &mut ConstraintSystem, order: &Modulus, bits_le: &[Lc]) -> Element {
    let element = Element {
        bytes_le: bits_le.chunks(8).map(pack_bits).collect(),
        bits_le: bits_le.to_vec(),
    };
    order.enforce_canonical(cs, &element);
    element
}

/// One derivation step's index.
enum Step {
    Public(u32),
    /// `active` is zero for the unused tail of a hidden path; `bits` are the 32 index
    /// bits, least significant first.
    Hidden {
        active: Lc,
        bits: Vec<Lc>,
    },
}

impl Step {
    /// The index as four big-endian bytes.
    fn be_bits(&self) -> Vec<Lc> {
        match self {
            Self::Public(index) => const_bits(&index.to_be_bytes()),
            Self::Hidden { bits, .. } => reverse_bytes(bits),
        }
    }
}

/// The steps of a path. A hidden path's flags are a Boolean prefix indicator: once a step
/// is inactive every later one is. With `hardened_only` the top index bit is the
/// constant one.
fn alloc_steps(
    cs: &mut ConstraintSystem,
    spec: &PathSpec,
    witness_path: &[u32],
    hardened_only: bool,
) -> Vec<Step> {
    match spec {
        PathSpec::Public(path) => path.iter().map(|&i| Step::Public(i)).collect(),
        PathSpec::Hidden { max_depth } => {
            let mut previous: Option<Lc> = None;
            (0..usize::from(*max_depth))
                .map(|j| {
                    let index = witness_path.get(j).copied().unwrap_or(0);
                    let active = alloc_bool(cs, j < witness_path.len());
                    if let Some(before) = &previous {
                        cs.enforce_mul(
                            active.clone(),
                            Lc::constant(F::ONE).minus(before),
                            Lc::zero(),
                        );
                    }
                    previous = Some(active.clone());
                    let mut bits: Vec<Lc> = (0..31)
                        .map(|k| alloc_bool(cs, (index >> k) & 1 == 1))
                        .collect();
                    bits.push(if hardened_only {
                        Lc::constant(F::ONE)
                    } else {
                        alloc_bool(cs, index >= HARDENED)
                    });
                    Step::Hidden { active, bits }
                })
                .collect()
        }
    }
}

/// `HMAC-SHA512(hmac_key, seed)` for a constant key and a seed of hidden length in
/// [`SEED_BYTES`]: the 512 output bits and the 512 bits of the inner digest.
///
/// The seed is 64 witness bytes with every byte from its length on forced to zero, and a
/// one-hot length selector. The padding bit and the length field of the single message
/// block are linear in the selector, so hiding the length costs about a hundred rows.
fn seed_master(cs: &mut ConstraintSystem, hmac_key: &[u8], seed: &[u8]) -> (Vec<Lc>, Vec<Lc>) {
    let (min, max) = (*SEED_BYTES.start(), *SEED_BYTES.end());
    let mut padded = [0u8; 64];
    padded[..seed.len()].copy_from_slice(seed);
    let bits = alloc_bits(cs, &padded);
    wipe(&mut padded);
    let one_hot: Vec<Lc> = (min..=max)
        .map(|l| alloc_bool(cs, l == seed.len()))
        .collect();
    let ones: Vec<(F, &Lc)> = one_hot.iter().map(|b| (F::ONE, b)).collect();
    cs.enforce_equal(&Lc::combine(&ones), &Lc::constant(F::ONE));

    let mut block: Vec<Lc> = bits.clone();
    block.resize(1024, Lc::zero());
    // `longer` is one exactly when the length exceeds `j`.
    let mut longer = Lc::zero();
    for j in (min..max).rev() {
        longer = longer.plus(&one_hot[j + 1 - min]);
        cs.enforce_mul(
            Lc::constant(F::ONE).minus(&longer),
            pack_bits(&bits[8 * j..8 * j + 8]),
            Lc::zero(),
        );
    }
    // The `0x80` after the last seed byte; that byte is zero whenever its selector is set.
    for (l, selected) in (min..=max).zip(&one_hot) {
        block[8 * l + 7] = block[8 * l + 7].plus(selected);
    }
    // Bit length `1024 + 8 len` in the last two bytes, big-endian.
    for k in 0..7 {
        let parts: Vec<(F, &Lc)> = (min..=max)
            .zip(&one_hot)
            .filter(|(l, _)| (l >> k) & 1 == 1)
            .map(|(_, b)| (F::ONE, b))
            .collect();
        let at = 3 + k;
        let index = if at < 8 {
            8 * 127 + at
        } else {
            8 * 126 + at - 8
        };
        block[index] = Lc::combine(&parts);
    }
    block[8 * 126 + 2] = Lc::constant(F::ONE);

    let key = HmacKey::sha512(cs, &const_bits(hmac_key));
    let words = be_words(&block, 8);
    let words: &[Word; 16] = words.as_slice().try_into().expect("one block");
    let inner = be_bits(&sha512_compress(cs, key.inner_state(), words));
    (key.finish(cs, &inner), inner)
}

/// BIP-32 `k_child = (I_L + k_par) mod n` on little-endian bits, with the rejection rules
/// as constraints: `I_L <= n - 1` and `1 <= k_child <= n - 1`.
fn bip32_child_key(
    cs: &mut ConstraintSystem,
    order: &Modulus,
    tweak_le: &[Lc],
    parent_le: &[Lc],
) -> Vec<Lc> {
    let tweak = enforce_below_order(cs, order, tweak_le);
    let child = order.reduce(cs, &tweak.lazy().add(&Lazy::from_bits(parent_le)));
    secp256k1_enforce_scalar_range(cs, &child.bits_le);
    child.bits_le
}

/// A BIP-32 secp256k1 node: the key as little-endian bits, the chain code as a byte
/// string.
#[derive(Clone)]
struct SecpNode {
    key: Vec<Lc>,
    chain: Vec<Lc>,
}

/// A node prepared for deriving children: its HMAC key state and, once a non-hardened or
/// hidden step needs it, its compressed public key. Both are shared by all its children.
struct SecpParent {
    node: SecpNode,
    hmac: HmacKey,
    public_key: Option<Vec<Lc>>,
}

impl SecpParent {
    fn new(cs: &mut ConstraintSystem, node: SecpNode) -> Self {
        let hmac = HmacKey::sha512(cs, &node.chain);
        Self {
            node,
            hmac,
            public_key: None,
        }
    }

    fn public_key(&mut self, cs: &mut ConstraintSystem) -> Vec<Lc> {
        let key = &self.node.key;
        self.public_key
            .get_or_insert_with(|| flat(secp256k1_fixed_base_mul(cs, key).compressed_bits()))
            .clone()
    }

    fn child(&mut self, cs: &mut ConstraintSystem, order: &Modulus, step: &Step) -> SecpNode {
        let hardened_data = |key: &[Lc]| {
            let mut data = const_bits(&[0]);
            data.extend(reverse_bytes(key));
            data
        };
        let mut data = match step {
            Step::Public(index) if *index >= HARDENED => hardened_data(&self.node.key),
            Step::Public(_) => self.public_key(cs),
            Step::Hidden { bits, .. } => {
                let soft = self.public_key(cs);
                select_bits(cs, &bits[31], &hardened_data(&self.node.key), &soft)
            }
        };
        data.extend(step.be_bits());
        let i = self.hmac.mac(cs, &data);
        let key = bip32_child_key(cs, order, &reverse_bytes(&i[..256]), &self.node.key);
        let chain = i[256..].to_vec();
        match step {
            Step::Public(_) => SecpNode { key, chain },
            // An inactive step passes the node through. Its unused HMAC output is still
            // subject to the rejection rules, which fail with probability about 2^-127.
            Step::Hidden { active, .. } => SecpNode {
                key: select_bits(cs, active, &key, &self.node.key),
                chain: select_bits(cs, active, &chain, &self.node.chain),
            },
        }
    }
}

/// The root node of a BIP-32 statement and the nullifier secret of that root.
fn bip32_root(cs: &mut ConstraintSystem, root: Bip32Root, secret: &[u8]) -> (SecpNode, Vec<Lc>) {
    let (key, chain, nullifier_secret) = match root {
        Bip32Root::Seed => {
            let (i, inner) = seed_master(cs, BIP32_MASTER_KEY, secret);
            (
                reverse_bytes(&i[..256]),
                i[256..].to_vec(),
                inner[..256].to_vec(),
            )
        }
        Bip32Root::ExtendedKey => {
            let bits = alloc_bits(cs, secret);
            (
                reverse_bytes(&bits[..256]),
                bits[256..].to_vec(),
                bits[256..].to_vec(),
            )
        }
    };
    secp256k1_enforce_scalar_range(cs, &key);
    (SecpNode { key, chain }, nullifier_secret)
}

fn bip32_descend_gadget(
    cs: &mut ConstraintSystem,
    order: &Modulus,
    mut node: SecpNode,
    steps: &[Step],
) -> SecpNode {
    for step in steps {
        node = SecpParent::new(cs, node).child(cs, order, step);
    }
    node
}

/// The credential bits of a secp256k1 key (little-endian bits, in `1..n`) under `lock`.
fn secp_lock(cs: &mut ConstraintSystem, lock: Lock, key: &[Lc], merkle_root: &[u8; 32]) -> Vec<Lc> {
    let public_key = secp256k1_fixed_base_mul(cs, key);
    match lock {
        Lock::P2pkh => hash160(cs, &flat(public_key.compressed_bits())),
        Lock::P2pkhUncompressed => {
            let mut sec1 = const_bits(&[4]);
            sec1.extend(flat(public_key.uncompressed_bits()));
            hash160(cs, &sec1)
        }
        Lock::P2shP2wpkh => {
            let mut script = const_bits(&[0, 0x14]);
            script.extend(hash160(cs, &flat(public_key.compressed_bits())));
            hash160(cs, &script)
        }
        Lock::Ethereum => keccak256(cs, &flat(public_key.uncompressed_bits()))[96..].to_vec(),
        Lock::TaprootKeyPath | Lock::TaprootScriptTree => {
            let mut message = flat(public_key.x_only_bits());
            if lock == Lock::TaprootScriptTree {
                message.extend(alloc_bits(cs, merkle_root));
            }
            let tag = sha2_native::sha256(b"TapTweak");
            let midstate =
                sha256_midstate(&[tag, tag].concat()).map(|w| Word::constant(u64::from(w), 32));
            let tweak = reverse_bytes(&sha256_from_midstate(cs, &midstate, 64, &message));
            // BIP-341 fails for a tweak that is not below the group order; a zero tweak or
            // an output at infinity has no rows that hold.
            enforce_below_order(cs, &Modulus::secp256k1_order(), &tweak);
            let output = secp256k1_taproot_tweak_x_only(cs, &public_key, &tweak);
            reverse_bytes(&output.bits_le)
        }
        Lock::Ed25519 | Lock::BlsWithdrawal => unreachable!("a secp256k1 lock"),
    }
}

/// The Ed25519 public key of an RFC 8032 seed, as credential bits.
fn ed25519_seed_lock(cs: &mut ConstraintSystem, seed: &[Lc]) -> Vec<Lc> {
    let digest = sha512(cs, seed);
    ed25519_fixed_base_mul(cs, &ed25519_clamp(&digest[..256])).encoding_bits()
}

/// The witness in the shape the relation consumes.
struct RelationWitness<'a> {
    secret: &'a [u8],
    path: &'a [u32],
    merkle_root: [u8; 32],
}

/// Key derivation and lock of one statement: the credential bits and the nullifier
/// secret's bits.
fn credential_gadget(
    cs: &mut ConstraintSystem,
    lock: Lock,
    source: &KeySource,
    witness: &RelationWitness<'_>,
) -> (Vec<Lc>, Vec<Lc>) {
    match source {
        KeySource::Secp256k1Key => {
            let secret = alloc_bits(cs, witness.secret);
            let key = reverse_bytes(&secret);
            secp256k1_enforce_scalar_range(cs, &key);
            (secp_lock(cs, lock, &key, &witness.merkle_root), secret)
        }
        KeySource::Bip32 { root, path } => {
            let (node, nullifier_secret) = bip32_root(cs, *root, witness.secret);
            let steps = alloc_steps(cs, path, witness.path, false);
            let order = Modulus::secp256k1_order();
            let leaf = bip32_descend_gadget(cs, &order, node, &steps);
            (
                secp_lock(cs, lock, &leaf.key, &witness.merkle_root),
                nullifier_secret,
            )
        }
        KeySource::Bls12381Key => {
            let secret = alloc_bits(cs, witness.secret);
            let key = reverse_bytes(&secret);
            // The group order has 255 bits.
            cs.enforce_zero(key[255].clone());
            bls12_381_enforce_scalar_range(cs, &key[..255]);
            let public_key = bls12_381_g1_fixed_base_mul(cs, &key[..255]);
            let mut credential = sha256(cs, &flat(public_key.compressed_bits()));
            credential[..8].fill(Lc::zero());
            (credential, secret)
        }
        KeySource::Ed25519Seed => {
            let seed = alloc_bits(cs, witness.secret);
            (ed25519_seed_lock(cs, &seed), seed)
        }
        KeySource::Slip10 { path } => {
            let (i, _) = seed_master(cs, SLIP10_ED25519_KEY, witness.secret);
            let (mut key, mut chain) = (i[..256].to_vec(), i[256..].to_vec());
            for step in alloc_steps(cs, path, witness.path, true) {
                let mut data = const_bits(&[0]);
                data.extend(key.iter().cloned());
                data.extend(step.be_bits());
                let i = HmacKey::sha512(cs, &chain).mac(cs, &data);
                match &step {
                    Step::Public(_) => (key, chain) = (i[..256].to_vec(), i[256..].to_vec()),
                    Step::Hidden { active, .. } => {
                        key = select_bits(cs, active, &i[..256], &key);
                        chain = select_bits(cs, active, &i[256..], &chain);
                    }
                }
            }
            (ed25519_seed_lock(cs, &key), key)
        }
        KeySource::Bip32Ed25519 { path } => {
            let bits = alloc_bits(cs, witness.secret);
            let (mut kl, mut kr, mut chain) = (
                bits[..256].to_vec(),
                bits[256..512].to_vec(),
                bits[512..].to_vec(),
            );
            for &index in path {
                let mut data = if index >= HARDENED {
                    let mut data = const_bits(&[0]);
                    data.extend(kl.iter().chain(&kr).cloned());
                    data
                } else {
                    let mut data = const_bits(&[2]);
                    data.extend(ed25519_fixed_base_mul(cs, &kl).encoding_bits());
                    data
                };
                data.extend(const_bits(&index.to_le_bytes()));
                let hmac = HmacKey::sha512(cs, &chain);
                let z = hmac.mac(cs, &data);
                // The chain-code tag is the scalar tag plus one: only bit 0 of byte 0 differs.
                data[0] = Lc::constant(F::ONE);
                let c = hmac.mac(cs, &data);
                // `8 * Z[0..28]` as a 256-bit integer.
                let mut eight_zl = vec![Lc::zero(); 3];
                eight_zl.extend_from_slice(&z[..224]);
                eight_zl.resize(256, Lc::zero());
                kl = add_wide(cs, &kl, &eight_zl);
                kr = add_wide(cs, &kr, &z[256..]);
                chain = c[256..].to_vec();
            }
            (ed25519_fixed_base_mul(cs, &kl).encoding_bits(), kr)
        }
    }
}

/// Pin one credential's public inputs: its bits, and the nullifier of `nullifier_secret`
/// under the public chaining value.
fn bind_credential(
    cs: &mut ConstraintSystem,
    public: &[Lc],
    credential: &[Lc],
    nullifier_secret: &[Lc],
) {
    let (claimed, rest) = public.split_at(credential.len());
    let (midstate, nullifier) = rest.split_at(256);
    pin(cs, credential, claimed);
    let midstate: Vec<Word> = midstate
        .chunks(32)
        .map(|w| Word::from_bits(w.to_vec()))
        .collect();
    let midstate: &[Word; 8] = midstate.as_slice().try_into().expect("eight words");
    let digest = sha256_from_midstate(cs, midstate, 128, nullifier_secret);
    pin(cs, &digest, nullifier);
}

fn alloc_public(cs: &mut ConstraintSystem, bits: &[bool]) -> Vec<Lc> {
    bits.iter()
        .map(|&b| cs.public_input(fu(u64::from(b))).into())
        .collect()
}

/// The relation of one statement with its assignment, and the row count before padding.
fn build(
    lock: Lock,
    source: &KeySource,
    public_bits: &[bool],
    witness: &RelationWitness<'_>,
) -> (Shape, Vec<F>, usize) {
    let cs = build_in(ConstraintSystem::new(), lock, source, public_bits, witness);
    let rows = cs.num_rows();
    let (shape, assignment) = cs.finish_v2();
    (shape, assignment, rows)
}

fn build_in(
    mut cs: ConstraintSystem,
    lock: Lock,
    source: &KeySource,
    public_bits: &[bool],
    witness: &RelationWitness<'_>,
) -> ConstraintSystem {
    assert_eq!(public_bits.len(), 8 * lock.credential_bytes() + 512);
    let public = alloc_public(&mut cs, public_bits);
    let (credential, nullifier_secret) = credential_gadget(&mut cs, lock, source, witness);
    bind_credential(&mut cs, &public, &credential, &nullifier_secret);
    cs
}

/// The relation of `statement` with the definition of every variable in terms of
/// earlier ones, for a prover that holds the witness in shares. The first
/// [`Source::Input`] is the statement's secret, bit `k` of byte `i` at bit `8 i + k`.
/// `None` for a malformed statement.
pub fn ownership_definitions(statement: &OwnershipStatement) -> Option<(Shape, Definitions)> {
    if !statement.is_well_formed() {
        return None;
    }
    let mut secret = placeholder_secret(&statement.source);
    let cs = build_in(
        ConstraintSystem::new_recording(),
        statement.lock,
        &statement.source,
        &vec![false; 8 * statement.lock.credential_bytes() + 512],
        &RelationWitness {
            secret: &secret,
            path: &[],
            merkle_root: [0; 32],
        },
    );
    wipe(&mut secret);
    let (shape, mut assignment, definitions) = cs.finish_recorded();
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    Some((shape, definitions))
}

/// The inputs of the relation of `statement` after its secret, in the order of the
/// relation's [`Source::Input`]s, for a prover that holds the secret in shares: the
/// one-hot length of a master seed of `secret_bytes` bytes, the steps of a hidden
/// derivation path (active flag, 31 index bits and, where the relation has it, the
/// hardened flag of each of the `max_depth` steps), and the script-tree root. These are
/// witness to the verifier and known to every prover. The secret itself is the first
/// input, zero-padded to that input's width (a master seed to 64 bytes).
///
/// `None` for a malformed statement, a secret length the source does not take, a path
/// longer than the hidden depth or with an index the source forbids, and a script-tree
/// root that is missing or not called for.
pub fn ownership_auxiliary_inputs(
    statement: &OwnershipStatement,
    secret_bytes: usize,
    path: &[u32],
    merkle_root: Option<&[u8; 32]>,
) -> Option<Vec<Vec<bool>>> {
    if !statement.is_well_formed() {
        return None;
    }
    let mut out: Vec<Vec<bool>> = Vec::new();
    let seed_length = |out: &mut Vec<Vec<bool>>| {
        SEED_BYTES.contains(&secret_bytes).then(|| {
            out.extend(SEED_BYTES.map(|l| vec![l == secret_bytes]));
        })
    };
    let steps = |out: &mut Vec<Vec<bool>>, spec: &PathSpec, hardened_only: bool| match spec {
        PathSpec::Public(_) => path.is_empty().then_some(()),
        PathSpec::Hidden { max_depth } => {
            if path.len() > usize::from(*max_depth) {
                return None;
            }
            for j in 0..usize::from(*max_depth) {
                let index = path.get(j).copied().unwrap_or(0);
                out.push(vec![j < path.len()]);
                out.extend((0..31).map(|k| vec![(index >> k) & 1 == 1]));
                if !hardened_only {
                    out.push(vec![index >= HARDENED]);
                } else if j < path.len() && index < HARDENED {
                    return None;
                }
            }
            Some(())
        }
    };
    match &statement.source {
        KeySource::Bip32 { root, path: spec } => {
            match root {
                Bip32Root::Seed => seed_length(&mut out)?,
                Bip32Root::ExtendedKey => (secret_bytes == 64).then_some(())?,
            }
            steps(&mut out, spec, false)?;
        }
        KeySource::Slip10 { path: spec } => {
            seed_length(&mut out)?;
            steps(&mut out, spec, true)?;
        }
        KeySource::Secp256k1Key | KeySource::Bls12381Key | KeySource::Ed25519Seed => {
            (secret_bytes == 32 && path.is_empty()).then_some(())?;
        }
        KeySource::Bip32Ed25519 { .. } => (secret_bytes == 96 && path.is_empty()).then_some(())?,
    }
    match (statement.lock, merkle_root) {
        (Lock::TaprootScriptTree, Some(root)) => {
            out.push((0..256).map(|i| (root[i / 8] >> (i % 8)) & 1 == 1).collect());
        }
        (Lock::TaprootScriptTree, None) | (_, Some(_)) => return None,
        _ => {}
    }
    Some(out)
}

/// A valid secret for building a shape without a witness.
fn placeholder_secret(source: &KeySource) -> Vec<u8> {
    match source {
        KeySource::Secp256k1Key | KeySource::Bls12381Key => {
            let mut key = vec![0u8; 32];
            key[31] = 1;
            key
        }
        KeySource::Bip32 {
            root: Bip32Root::ExtendedKey,
            ..
        } => {
            let mut key = vec![0u8; 64];
            key[31] = 1;
            key
        }
        KeySource::Bip32 { .. } | KeySource::Slip10 { .. } => vec![0u8; 16],
        KeySource::Ed25519Seed => vec![0u8; 32],
        KeySource::Bip32Ed25519 { .. } => {
            let mut key = vec![0u8; 96];
            key[0] = 8;
            key
        }
    }
}

/// What selects a relation.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Relation {
    Single(Lock, KeySource),
    Batch {
        lock: Lock,
        root: Bip32Root,
        prefix: Vec<u32>,
        tails: Vec<Vec<u32>>,
    },
}

fn build_shape(relation: &Relation) -> Shape {
    let (shape, mut assignment, _) = match relation {
        Relation::Single(lock, source) => {
            let mut secret = placeholder_secret(source);
            let built = build(
                *lock,
                source,
                &vec![false; 8 * lock.credential_bytes() + 512],
                &RelationWitness {
                    secret: &secret,
                    path: &[],
                    merkle_root: [0; 32],
                },
            );
            wipe(&mut secret);
            built
        }
        Relation::Batch {
            lock,
            root,
            prefix,
            tails,
        } => {
            let source = KeySource::Bip32 {
                root: *root,
                path: PathSpec::Public(Vec::new()),
            };
            let mut secret = placeholder_secret(&source);
            let public = vec![false; tails.len() * (8 * lock.credential_bytes() + 512)];
            let built = build_batch(*lock, *root, prefix, tails, &public, &secret);
            wipe(&mut secret);
            built
        }
    };
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    shape
}

/// Matrix entries the shape cache may hold in total: about 1.5 GB. A shape larger than
/// this (a batch of more than about 30 entries) is built for its caller and not kept.
#[cfg(feature = "std")]
const SHAPE_CACHE_ENTRIES: usize = 1 << 27;

#[cfg(feature = "std")]
fn shape_entries(shape: &Shape) -> usize {
    shape.a.nnz() + shape.b.nnz() + shape.c.nnz()
}

/// Shapes are a pure function of the relation; with `std` the most recent ones are kept,
/// up to 32 of them and [`SHAPE_CACHE_ENTRIES`] matrix entries.
#[cfg(feature = "std")]
static SHAPE_CACHE: std::sync::Mutex<Vec<(Relation, Arc<Shape>)>> =
    std::sync::Mutex::new(Vec::new());

/// The kept shape of `relation`, if there is one.
#[cfg(feature = "std")]
fn kept_shape(relation: &Relation) -> Option<Arc<Shape>> {
    SHAPE_CACHE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .iter()
        .find(|(r, _)| r == relation)
        .map(|(_, shape)| shape.clone())
}

#[cfg(not(feature = "std"))]
fn kept_shape(_: &Relation) -> Option<Arc<Shape>> {
    None
}

/// Keep `shape`, the shape of `relation`, unless it is too large or one is already kept
/// (which is then returned).
#[cfg(feature = "std")]
fn keep_shape(relation: &Relation, shape: Shape) -> Arc<Shape> {
    const KEEP: usize = 32;
    let shape = Arc::new(shape);
    let size = shape_entries(&shape);
    if size > SHAPE_CACHE_ENTRIES {
        return shape;
    }
    let mut cache = SHAPE_CACHE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((_, hit)) = cache.iter().find(|(r, _)| r == relation) {
        return hit.clone();
    }
    while cache.len() == KEEP
        || cache.iter().map(|(_, s)| shape_entries(s)).sum::<usize>() + size > SHAPE_CACHE_ENTRIES
    {
        cache.remove(0);
    }
    cache.push((relation.clone(), shape.clone()));
    shape
}

#[cfg(not(feature = "std"))]
fn keep_shape(_: &Relation, shape: Shape) -> Arc<Shape> {
    Arc::new(shape)
}

fn shape_of(relation: &Relation) -> Arc<Shape> {
    kept_shape(relation).unwrap_or_else(|| keep_shape(relation, build_shape(relation)))
}

/// The shape of `relation` and the assignment `synthesize` produces. When the shape is
/// kept, only the assignment is computed (no matrices, no digest); otherwise both come
/// from one synthesis and the shape is kept for the next call. The shape does not depend
/// on the witness, so both ways give the same pair.
fn synthesize_shared(
    relation: &Relation,
    synthesize: impl Fn(ConstraintSystem) -> ConstraintSystem,
) -> (Arc<Shape>, Vec<F>) {
    match kept_shape(relation) {
        Some(shape) => {
            let assignment = synthesize(ConstraintSystem::witness_only())
                .finish_assignment(&shape)
                .expect("a relation's synthesis allocates the variables of its shape");
            (shape, assignment)
        }
        None => {
            let (shape, assignment) = synthesize(ConstraintSystem::new()).finish_v2();
            (keep_shape(relation, shape), assignment)
        }
    }
}

/// The public relation of a statement: it depends on the lock and the source (with its
/// path specification) and on nothing else. `None` for a malformed statement.
pub fn ownership_shape(statement: &OwnershipStatement) -> Option<Arc<Shape>> {
    statement
        .is_well_formed()
        .then(|| shape_of(&Relation::Single(statement.lock, statement.source.clone())))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipError {
    /// The statement's parts do not fit together or are outside the supported ranges.
    MalformedStatement,
    /// The witness does not produce the statement's credential and nullifier.
    WitnessMismatch,
    Proof(ZkHemV2Error),
}

/// The relation of `statement` with the assignment for `witness`, after checking natively
/// that the witness produces the statement. The assignment is secret. This is what a
/// prover that does not go through [`prove_ownership`] (the collaborative one) starts from;
/// its transcript statement is [`ownership_transcript`].
pub fn synthesize_ownership(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
) -> Result<(Shape, Vec<F>), OwnershipError> {
    check_ownership(statement, witness)?;
    let (shape, assignment, _) = build(
        statement.lock,
        &statement.source,
        &statement.public_bits(),
        &RelationWitness {
            secret: &witness.secret,
            path: &witness.path,
            merkle_root: witness.merkle_root.unwrap_or([0; 32]),
        },
    );
    Ok((shape, assignment))
}

/// That `statement` is well formed and `witness` produces it, natively.
fn check_ownership(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
) -> Result<(), OwnershipError> {
    if !statement.is_well_formed() {
        return Err(OwnershipError::MalformedStatement);
    }
    let derived = OwnershipStatement::derive(
        statement.lock,
        statement.source.clone(),
        witness,
        statement.pq_commitment,
        statement.migration_domain,
        statement.epoch,
    );
    if derived.as_ref() != Some(statement) {
        return Err(OwnershipError::WitnessMismatch);
    }
    Ok(())
}

/// [`synthesize_ownership`] with the relation's kept shape ([`synthesize_shared`]).
fn synthesize_ownership_shared(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
) -> Result<(Arc<Shape>, Vec<F>), OwnershipError> {
    check_ownership(statement, witness)?;
    let public_bits = statement.public_bits();
    let relation_witness = RelationWitness {
        secret: &witness.secret,
        path: &witness.path,
        merkle_root: witness.merkle_root.unwrap_or([0; 32]),
    };
    Ok(synthesize_shared(
        &Relation::Single(statement.lock, statement.source.clone()),
        |cs| {
            build_in(
                cs,
                statement.lock,
                &statement.source,
                &public_bits,
                &relation_witness,
            )
        },
    ))
}

fn with_regime(mut bytes: Vec<u8>, regime: Profile) -> Vec<u8> {
    bytes.push(regime.wire_tag());
    bytes
}

/// The statement bytes [`prove_ownership`] and [`verify_ownership`] hand to zk-Hem.
pub fn ownership_transcript(statement: &OwnershipStatement, regime: Profile) -> Vec<u8> {
    with_regime(statement.to_bytes(), regime)
}

// ============================================================================
// Batches
// ============================================================================

/// One credential of a batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchEntry {
    /// The path from the batch's shared node to this credential's key.
    pub tail: Vec<u32>,
    pub credential: Credential,
    pub pq_commitment: [u8; 32],
    pub nullifier: [u8; 32],
}

/// Many secp256k1 credentials below one BIP-32 node, proved together: the root step and
/// the shared `prefix` are proved once, and children of one node share its HMAC key state
/// and its public key. All paths are public.
///
/// Entry `i` is the same claim as the single statement [`Self::statement`]`(i)`, with the
/// same credential identifier and nullifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchStatement {
    pub lock: Lock,
    pub root: Bip32Root,
    pub prefix: Vec<u32>,
    pub entries: Vec<BatchEntry>,
    pub migration_domain: [u8; 32],
    pub epoch: u64,
}

impl BatchStatement {
    /// The batch a holder derives from its root secret for the given tails and target
    /// commitments. `None` under the conditions of [`OwnershipStatement::derive`], or when
    /// the batch is empty or too large.
    pub fn derive(
        lock: Lock,
        root: Bip32Root,
        prefix: &[u32],
        targets: &[(Vec<u32>, [u8; 32])],
        witness: &OwnershipWitness,
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        let kind = Self::source(root, Vec::new()).nullifier_kind();
        let shared = bip32_descend(bip32_root_node(root, &witness.secret)?, prefix)?;
        let mut secret = bip32_nullifier_secret(root, &witness.secret);
        let entries = targets
            .iter()
            .map(|(tail, pq_commitment)| {
                let leaf = bip32_descend(shared.clone(), tail)?;
                let credential = secp256k1_credential(lock, &leaf.private_key, None)?;
                Some(BatchEntry {
                    tail: tail.clone(),
                    credential,
                    pq_commitment: *pq_commitment,
                    nullifier: migration_nullifier(kind, &secret, &migration_domain, &credential),
                })
            })
            .collect::<Option<Vec<_>>>();
        wipe(&mut secret);
        let batch = Self {
            lock,
            root,
            prefix: prefix.to_vec(),
            entries: entries?,
            migration_domain,
            epoch,
        };
        batch.is_well_formed().then_some(batch)
    }

    fn source(root: Bip32Root, path: Vec<u32>) -> KeySource {
        KeySource::Bip32 {
            root,
            path: PathSpec::Public(path),
        }
    }

    /// Whether the lock is a secp256k1 lock without a witness of its own, the batch holds
    /// 1 to [`MAX_BATCH_ENTRIES`] entries and no path exceeds [`MAX_PATH_DEPTH`].
    pub fn is_well_formed(&self) -> bool {
        self.lock.curve() == Curve::Secp256k1
            && self.lock != Lock::TaprootScriptTree
            && (1..=MAX_BATCH_ENTRIES).contains(&self.entries.len())
            && self.entries.iter().all(|e| {
                self.prefix.len() + e.tail.len() <= MAX_PATH_DEPTH
                    && self.lock.credential(e.credential.value()) == Some(e.credential)
            })
    }

    /// The batch cut into consecutive batches of at most `max_entries` entries each, with
    /// the same lock, root, prefix, domain and epoch. Every entry keeps its credential,
    /// target and nullifier, so the pieces make exactly the claims of the whole: their
    /// [`Self::statement`]s, and with them the registry bindings, are those of the whole in
    /// order.
    ///
    /// Proving memory follows the padded row count of one proof, not the number of
    /// entries proved in total. With the P2PKH lock below a seed-rooted
    /// `m/44'/0'/0'/0`, a proof of up to 43 entries pads to 2^23 rows (11 GB measured at
    /// 30 entries), where one proof of 100 entries pads to 2^25. Each piece repeats the
    /// root and prefix derivation (about 0.93 million rows) and is its own proof of
    /// about 950 KiB.
    pub fn chunks(&self, max_entries: usize) -> Vec<BatchStatement> {
        assert!(max_entries > 0, "a batch holds at least one entry");
        self.entries
            .chunks(max_entries)
            .map(|entries| BatchStatement {
                lock: self.lock,
                root: self.root,
                prefix: self.prefix.clone(),
                entries: entries.to_vec(),
                migration_domain: self.migration_domain,
                epoch: self.epoch,
            })
            .collect()
    }

    /// The single statement that makes the same claim as entry `index`.
    pub fn statement(&self, index: usize) -> Option<OwnershipStatement> {
        let entry = self.entries.get(index)?;
        let mut path = self.prefix.clone();
        path.extend_from_slice(&entry.tail);
        Some(OwnershipStatement {
            lock: self.lock,
            source: Self::source(self.root, path),
            credential: entry.credential,
            pq_commitment: entry.pq_commitment,
            migration_domain: self.migration_domain,
            epoch: self.epoch,
            nullifier: entry.nullifier,
        })
    }

    fn encode_path(out: &mut Vec<u8>, path: &[u32]) {
        out.push(path.len() as u8);
        for index in path {
            out.extend_from_slice(&index.to_be_bytes());
        }
    }

    /// Canonical encoding; also the bytes the proof transcript absorbs.
    ///
    /// `tag(25) || lock || root || epoch(8, BE) || domain(32) || prefix || count(2, BE) ||
    /// count * (tail || credential value || pq(32) || nullifier(32))`, a path being
    /// `depth || depth * index(4, BE)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = BATCH_TAG.to_vec();
        out.push(self.lock as u8);
        out.push(self.root as u8);
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.migration_domain);
        Self::encode_path(&mut out, &self.prefix);
        out.extend_from_slice(&(self.entries.len() as u16).to_be_bytes());
        for entry in &self.entries {
            Self::encode_path(&mut out, &entry.tail);
            out.extend_from_slice(entry.credential.value());
            out.extend_from_slice(&entry.pq_commitment);
            out.extend_from_slice(&entry.nullifier);
        }
        out
    }

    /// Strict inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes.strip_prefix(BATCH_TAG.as_slice())?;
        let mut take = |n: usize| -> Option<Vec<u8>> {
            let (head, tail) = rest.split_at_checked(n)?;
            rest = tail;
            Some(head.to_vec())
        };
        let path = |take: &mut dyn FnMut(usize) -> Option<Vec<u8>>| -> Option<Vec<u32>> {
            let depth = usize::from(take(1)?[0]);
            Some(
                take(4 * depth)?
                    .chunks_exact(4)
                    .map(|c| u32::from_be_bytes([c[0], c[1], c[2], c[3]]))
                    .collect(),
            )
        };
        let lock = Lock::from_tag(take(1)?[0])?;
        let root = match take(1)?[0] {
            0 => Bip32Root::Seed,
            1 => Bip32Root::ExtendedKey,
            _ => return None,
        };
        let epoch = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let migration_domain: [u8; 32] = take(32)?.try_into().ok()?;
        let prefix = path(&mut take)?;
        let count = usize::from(u16::from_be_bytes(take(2)?.try_into().ok()?));
        let mut entries = Vec::with_capacity(count.min(MAX_BATCH_ENTRIES));
        for _ in 0..count {
            let tail = path(&mut take)?;
            entries.push(BatchEntry {
                tail,
                credential: lock.credential(&take(lock.credential_bytes())?)?,
                pq_commitment: take(32)?.try_into().ok()?,
                nullifier: take(32)?.try_into().ok()?,
            });
        }
        let batch = Self {
            lock,
            root,
            prefix,
            entries,
            migration_domain,
            epoch,
        };
        (rest.is_empty() && batch.is_well_formed()).then_some(batch)
    }

    fn relation(&self) -> Relation {
        Relation::Batch {
            lock: self.lock,
            root: self.root,
            prefix: self.prefix.clone(),
            tails: self.entries.iter().map(|e| e.tail.clone()).collect(),
        }
    }

    fn public_bits(&self) -> Vec<bool> {
        let kind = Self::source(self.root, Vec::new()).nullifier_kind();
        let mut out = Vec::new();
        for entry in &self.entries {
            credential_public_bits(
                &mut out,
                kind,
                &entry.credential,
                &self.migration_domain,
                &entry.nullifier,
            );
        }
        out
    }

    /// The relation's public inputs: those of each entry in order. `None` for a malformed
    /// batch.
    pub fn public_inputs(&self) -> Option<Vec<F>> {
        self.is_well_formed().then(|| {
            self.public_bits()
                .into_iter()
                .map(|b| fu(u64::from(b)))
                .collect()
        })
    }

    /// The bindings a verified batch asks the registry to record, one per entry.
    #[cfg(feature = "std")]
    pub fn bindings(&self) -> Vec<super::registry::MigrationBinding> {
        (0..self.entries.len())
            .filter_map(|i| self.statement(i))
            .map(|statement| statement.binding())
            .collect()
    }
}

/// The relation of a batch with its assignment, and the row count before padding.
fn build_batch(
    lock: Lock,
    root: Bip32Root,
    prefix: &[u32],
    tails: &[Vec<u32>],
    public_bits: &[bool],
    secret: &[u8],
) -> (Shape, Vec<F>, usize) {
    let cs = build_batch_in(
        ConstraintSystem::new(),
        lock,
        root,
        prefix,
        tails,
        public_bits,
        secret,
    );
    let rows = cs.num_rows();
    let (shape, assignment) = cs.finish_v2();
    (shape, assignment, rows)
}

fn build_batch_in(
    mut cs: ConstraintSystem,
    lock: Lock,
    root: Bip32Root,
    prefix: &[u32],
    tails: &[Vec<u32>],
    public_bits: &[bool],
    secret: &[u8],
) -> ConstraintSystem {
    let per_entry = 8 * lock.credential_bytes() + 512;
    assert_eq!(public_bits.len(), tails.len() * per_entry);
    let public = alloc_public(&mut cs, public_bits);
    let (node, nullifier_secret) = bip32_root(&mut cs, root, secret);
    let order = Modulus::secp256k1_order();
    let steps = |path: &[u32]| -> Vec<Step> { path.iter().map(|&i| Step::Public(i)).collect() };
    let shared = bip32_descend_gadget(&mut cs, &order, node, &steps(prefix));
    let mut parent = SecpParent::new(&mut cs, shared.clone());
    for (tail, public) in tails.iter().zip(public.chunks(per_entry)) {
        let leaf = match tail.split_first() {
            None => shared.clone(),
            Some((&first, rest)) => {
                let child = parent.child(&mut cs, &order, &Step::Public(first));
                bip32_descend_gadget(&mut cs, &order, child, &steps(rest))
            }
        };
        let credential = secp_lock(&mut cs, lock, &leaf.key, &[0; 32]);
        bind_credential(&mut cs, public, &credential, &nullifier_secret);
    }
    cs
}

/// The public relation of a batch. `None` for a malformed batch.
pub fn batch_shape(batch: &BatchStatement) -> Option<Arc<Shape>> {
    batch.is_well_formed().then(|| shape_of(&batch.relation()))
}

/// The relation of `batch` with the assignment for `witness`; see
/// [`synthesize_ownership`].
pub fn synthesize_batch(
    batch: &BatchStatement,
    witness: &OwnershipWitness,
) -> Result<(Shape, Vec<F>), OwnershipError> {
    let tails = check_batch(batch, witness)?;
    let (shape, assignment, _) = build_batch(
        batch.lock,
        batch.root,
        &batch.prefix,
        &tails,
        &batch.public_bits(),
        &witness.secret,
    );
    Ok((shape, assignment))
}

/// [`synthesize_batch`] with the relation's kept shape ([`synthesize_shared`]).
fn synthesize_batch_shared(
    batch: &BatchStatement,
    witness: &OwnershipWitness,
) -> Result<(Arc<Shape>, Vec<F>), OwnershipError> {
    let tails = check_batch(batch, witness)?;
    let public_bits = batch.public_bits();
    Ok(synthesize_shared(&batch.relation(), |cs| {
        build_batch_in(
            cs,
            batch.lock,
            batch.root,
            &batch.prefix,
            &tails,
            &public_bits,
            &witness.secret,
        )
    }))
}

/// That `batch` is well formed and `witness` produces it, natively; returns the tails.
fn check_batch(
    batch: &BatchStatement,
    witness: &OwnershipWitness,
) -> Result<Vec<Vec<u32>>, OwnershipError> {
    if !batch.is_well_formed() {
        return Err(OwnershipError::MalformedStatement);
    }
    let targets: Vec<(Vec<u32>, [u8; 32])> = batch
        .entries
        .iter()
        .map(|e| (e.tail.clone(), e.pq_commitment))
        .collect();
    let derived = BatchStatement::derive(
        batch.lock,
        batch.root,
        &batch.prefix,
        &targets,
        witness,
        batch.migration_domain,
        batch.epoch,
    );
    if derived.as_ref() != Some(batch) {
        return Err(OwnershipError::WitnessMismatch);
    }
    Ok(targets.into_iter().map(|(tail, _)| tail).collect())
}

/// The statement bytes [`prove_batch`] and [`verify_batch`] hand to zk-Hem.
pub fn batch_transcript(batch: &BatchStatement, regime: Profile) -> Vec<u8> {
    with_regime(batch.to_bytes(), regime)
}

// ============================================================================
// Proofs
// ============================================================================

/// An ownership proof, for one statement or one batch, under one regime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnershipProof {
    pub regime: Profile,
    pub proof: ZkHemV2Proof,
}

impl OwnershipProof {
    /// `magic(8) || regime || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = PROOF_MAGIC.to_vec();
        out.push(self.regime.wire_tag());
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    fn decode(bytes: &[u8], shape: Option<Arc<Shape>>) -> Option<Self> {
        let rest = bytes.strip_prefix(PROOF_MAGIC.as_slice())?;
        let (&regime, rest) = rest.split_first()?;
        let regime = Profile::from_wire_tag(regime)?;
        let proof = ZkHemV2Proof::from_bytes(rest, &*shape?)?;
        (proof.profile == regime).then_some(Self { regime, proof })
    }

    /// Strict decoding against the statement the proof is for: a known regime and a
    /// zk-Hem part that is canonical for the statement's relation, with no byte left over.
    pub fn from_bytes(bytes: &[u8], statement: &OwnershipStatement) -> Option<Self> {
        Self::decode(bytes, ownership_shape(statement))
    }

    /// [`Self::from_bytes`] for a batch proof.
    pub fn from_bytes_batch(bytes: &[u8], batch: &BatchStatement) -> Option<Self> {
        Self::decode(bytes, batch_shape(batch))
    }
}

fn prove(
    synthesized: Result<(Arc<Shape>, Vec<F>), OwnershipError>,
    transcript: &[u8],
    regime: Profile,
    seed: &[u8; 32],
) -> Result<OwnershipProof, OwnershipError> {
    let (shape, assignment) = synthesized?;
    let proof = protocol::prove(&shape, assignment, transcript, regime, seed)
        .map_err(OwnershipError::Proof)?;
    Ok(OwnershipProof { regime, proof })
}

/// Prove a statement. `seed` must be uniform and secret; it drives every mask and blinder
/// of the proof.
pub fn prove_ownership(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
    regime: Profile,
    seed: &[u8; 32],
) -> Result<OwnershipProof, OwnershipError> {
    prove(
        synthesize_ownership_shared(statement, witness),
        &ownership_transcript(statement, regime),
        regime,
        seed,
    )
}

/// Verify a proof against a statement under the regime the verifier requires. On `true`,
/// [`OwnershipStatement::binding`] is what the registry should record.
pub fn verify_ownership(
    statement: &OwnershipStatement,
    regime: Profile,
    proof: &OwnershipProof,
) -> bool {
    let (Some(shape), Some(public_inputs)) =
        (ownership_shape(statement), statement.public_inputs())
    else {
        return false;
    };
    proof.regime == regime
        && proof.proof.profile == regime
        && protocol::verify(
            &shape,
            &public_inputs,
            &ownership_transcript(statement, regime),
            regime,
            &proof.proof,
        )
}

/// Prove a batch; see [`prove_ownership`].
pub fn prove_batch(
    batch: &BatchStatement,
    witness: &OwnershipWitness,
    regime: Profile,
    seed: &[u8; 32],
) -> Result<OwnershipProof, OwnershipError> {
    prove(
        synthesize_batch_shared(batch, witness),
        &batch_transcript(batch, regime),
        regime,
        seed,
    )
}

/// Verify a batch proof. On `true`, [`BatchStatement::bindings`] is what the registry
/// should record.
pub fn verify_batch(
    batch: &BatchStatement,
    regime: Profile,
    proof: &OwnershipProof,
) -> bool {
    let (Some(shape), Some(public_inputs)) = (batch_shape(batch), batch.public_inputs()) else {
        return false;
    };
    proof.regime == regime
        && proof.proof.profile == regime
        && protocol::verify(
            &shape,
            &public_inputs,
            &batch_transcript(batch, regime),
            regime,
            &proof.proof,
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::println;
    use std::string::String;
    use std::sync::OnceLock;

    const REGIME: Profile = Profile::TurboShakeJohnson400;
    const PQ: [u8; 32] = [0x51; 32];
    const DOMAIN: [u8; 32] = [0xd0; 32];
    const EPOCH: u64 = 7;
    const H: u32 = HARDENED;

    fn hex(s: &str) -> Vec<u8> {
        let digits: Vec<u8> = s
            .bytes()
            .filter(|b| !b.is_ascii_whitespace())
            .map(|b| (b as char).to_digit(16).expect("hex digit") as u8)
            .collect();
        assert!(digits.len() % 2 == 0);
        digits.chunks(2).map(|p| (p[0] << 4) | p[1]).collect()
    }

    fn arr<const N: usize>(s: &str) -> [u8; N] {
        hex(s).try_into().expect("length")
    }

    /// Base58Check payload (checksum verified and removed).
    fn base58check(s: &str) -> Vec<u8> {
        const ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
        let mut out: Vec<u8> = Vec::new();
        for c in s.bytes() {
            let mut carry = ALPHABET.iter().position(|&a| a == c).expect("base58") as u32;
            for byte in out.iter_mut().rev() {
                carry += 58 * u32::from(*byte);
                *byte = carry as u8;
                carry >>= 8;
            }
            while carry > 0 {
                out.insert(0, carry as u8);
                carry >>= 8;
            }
        }
        let (payload, checksum) = out.split_at(out.len() - 4);
        let digest = sha2_native::sha256(&sha2_native::sha256(payload));
        assert_eq!(checksum, &digest[..4], "base58check checksum");
        payload.to_vec()
    }

    const KEY: [u8; 32] = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x0f, 0xed, 0xcb, 0xa9, 0x87, 0x65, 0x43,
        0x21, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x01,
    ];
    const ROOT: [u8; 32] = [0x3c; 32];

    fn seed(len: usize) -> Vec<u8> {
        (0..len as u8).map(|i| i.wrapping_mul(37) ^ 0x5a).collect()
    }

    /// The BIP32-Ed25519 root key of the reference implementation's test (`D1` of
    /// `rust-ed25519-bip32`, `src/tests.rs`).
    fn cardano_root() -> Ed25519ExtendedKey {
        Ed25519ExtendedKey(arr(
            "f8a29231ee38d6c5bf715d5bac21c750577aa3798b22d79d65bf97d6fadea15a
             dcd1ee1abdf78bd4be64731a12deb94d3671784112eb6f364b871851fd1c9a24
             7384db9ad6003bbd08b3b1ddc0d07a597293ff85e961bf252b331262eddfad0d",
        ))
    }

    fn bip32(root: Bip32Root, path: PathSpec) -> KeySource {
        KeySource::Bip32 { root, path }
    }

    fn public(path: &[u32]) -> PathSpec {
        PathSpec::Public(path.to_vec())
    }

    /// One case per lock and per source, with small paths.
    fn cases() -> Vec<(&'static str, Lock, KeySource, OwnershipWitness)> {
        let key = || OwnershipWitness::secp256k1_key(&KEY);
        let xprv = OwnershipWitness::extended_key(&bip32_derive(&seed(32), &[H + 1]).unwrap());
        vec![
            ("p2pkh/key", Lock::P2pkh, KeySource::Secp256k1Key, key()),
            (
                "p2pkh-uncompressed/key",
                Lock::P2pkhUncompressed,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "p2sh-p2wpkh/key",
                Lock::P2shP2wpkh,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "ethereum/key",
                Lock::Ethereum,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "taproot/key",
                Lock::TaprootKeyPath,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "taproot-tree/key",
                Lock::TaprootScriptTree,
                KeySource::Secp256k1Key,
                key().with_merkle_root(ROOT),
            ),
            (
                "ed25519/seed",
                Lock::Ed25519,
                KeySource::Ed25519Seed,
                OwnershipWitness::ed25519_seed(&KEY),
            ),
            (
                "ed25519/slip10",
                Lock::Ed25519,
                KeySource::Slip10 {
                    path: public(&[H, H + 1]),
                },
                OwnershipWitness::seed(&seed(16)),
            ),
            (
                "ed25519/slip10-hidden",
                Lock::Ed25519,
                KeySource::Slip10 {
                    path: PathSpec::Hidden { max_depth: 2 },
                },
                OwnershipWitness::seed(&seed(33)).with_path(&[H + 5]),
            ),
            (
                "ed25519/bip32-ed25519",
                Lock::Ed25519,
                KeySource::Bip32Ed25519 { path: vec![H, 1] },
                OwnershipWitness::ed25519_extended_key(&cardano_root()),
            ),
            (
                "p2pkh/bip32-seed",
                Lock::P2pkh,
                bip32(Bip32Root::Seed, public(&[H + 44])),
                OwnershipWitness::seed(&seed(64)),
            ),
            (
                "ethereum/bip32-seed",
                Lock::Ethereum,
                bip32(Bip32Root::Seed, public(&[3])),
                OwnershipWitness::seed(&seed(20)),
            ),
            (
                "taproot/bip32-xprv",
                Lock::TaprootKeyPath,
                bip32(Bip32Root::ExtendedKey, public(&[H + 86, 0])),
                xprv,
            ),
            (
                "p2pkh/bip32-hidden",
                Lock::P2pkh,
                bip32(Bip32Root::Seed, PathSpec::Hidden { max_depth: 2 }),
                OwnershipWitness::seed(&seed(64)).with_path(&[H + 44, 7]),
            ),
            (
                "bls-withdrawal/key",
                Lock::BlsWithdrawal,
                KeySource::Bls12381Key,
                OwnershipWitness::bls12_381_key(&KEY),
            ),
        ]
    }

    fn derive(lock: Lock, source: KeySource, witness: &OwnershipWitness) -> OwnershipStatement {
        OwnershipStatement::derive(lock, source, witness, PQ, DOMAIN, EPOCH).expect("valid witness")
    }

    fn relation_witness(w: &OwnershipWitness) -> RelationWitness<'_> {
        RelationWitness {
            secret: &w.secret,
            path: &w.path,
            merkle_root: w.merkle_root.unwrap_or([0; 32]),
        }
    }

    fn batch_case() -> (BatchStatement, OwnershipWitness) {
        let witness = OwnershipWitness::seed(&seed(64));
        let targets = vec![(vec![0], [0x61; 32]), (vec![1], [0x62; 32])];
        let batch = BatchStatement::derive(
            Lock::P2pkh,
            Bip32Root::Seed,
            &[H + 44],
            &targets,
            &witness,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        (batch, witness)
    }

    #[test]
    fn bip32_matches_test_vector_1() {
        // BIP-32, "Test vector 1": (path, ext pub, ext prv).
        let seed = hex("000102030405060708090a0b0c0d0e0f");
        let chain: [(&[u32], &str, &str); 6] = [
            (
                &[],
                "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8",
                "xprv9s21ZrQH143K3QTDL4LXw2F7HEK3wJUD2nW2nRk4stbPy6cq3jPPqjiChkVvvNKmPGJxWUtg6LnF5kejMRNNU3TGtRBeJgk33yuGBxrMPHi",
            ),
            (
                &[H],
                "xpub68Gmy5EdvgibQVfPdqkBBCHxA5htiqg55crXYuXoQRKfDBFA1WEjWgP6LHhwBZeNK1VTsfTFUHCdrfp1bgwQ9xv5ski8PX9rL2dZXvgGDnw",
                "xprv9uHRZZhk6KAJC1avXpDAp4MDc3sQKNxDiPvvkX8Br5ngLNv1TxvUxt4cV1rGL5hj6KCesnDYUhd7oWgT11eZG7XnxHrnYeSvkzY7d2bhkJ7",
            ),
            (
                &[H, 1],
                "xpub6ASuArnXKPbfEwhqN6e3mwBcDTgzisQN1wXN9BJcM47sSikHjJf3UFHKkNAWbWMiGj7Wf5uMash7SyYq527Hqck2AxYysAA7xmALppuCkwQ",
                "xprv9wTYmMFdV23N2TdNG573QoEsfRrWKQgWeibmLntzniatZvR9BmLnvSxqu53Kw1UmYPxLgboyZQaXwTCg8MSY3H2EU4pWcQDnRnrVA1xe8fs",
            ),
            (
                &[H, 1, H + 2],
                "xpub6D4BDPcP2GT577Vvch3R8wDkScZWzQzMMUm3PWbmWvVJrZwQY4VUNgqFJPMM3No2dFDFGTsxxpG5uJh7n7epu4trkrX7x7DogT5Uv6fcLW5",
                "xprv9z4pot5VBttmtdRTWfWQmoH1taj2axGVzFqSb8C9xaxKymcFzXBDptWmT7FwuEzG3ryjH4ktypQSAewRiNMjANTtpgP4mLTj34bhnZX7UiM",
            ),
            (
                &[H, 1, H + 2, 2],
                "xpub6FHa3pjLCk84BayeJxFW2SP4XRrFd1JYnxeLeU8EqN3vDfZmbqBqaGJAyiLjTAwm6ZLRQUMv1ZACTj37sR62cfN7fe5JnJ7dh8zL4fiyLHV",
                "xprvA2JDeKCSNNZky6uBCviVfJSKyQ1mDYahRjijr5idH2WwLsEd4Hsb2Tyh8RfQMuPh7f7RtyzTtdrbdqqsunu5Mm3wDvUAKRHSC34sJ7in334",
            ),
            (
                &[H, 1, H + 2, 2, 1_000_000_000],
                "xpub6H1LXWLaKsWFhvm6RVpEL9P4KfRZSW7abD2ttkWP3SSQvnyA8FSVqNTEcYFgJS2UaFcxupHiYkro49S8yGasTvXEYBVPamhGW6cFJodrTHy",
                "xprvA41z7zogVVwxVSgdKUHDy1SKmdb533PjDz7J6N6mV6uS3ze1ai8FHa8kmHScGpWmj4WggLyQjgPie1rFSruoUihUZREPSL39UNdE3BBDu76",
            ),
        ];
        for (path, xpub, xprv) in chain {
            // version(4) depth(1) fingerprint(4) child(4) chain code(32) key(33).
            let (xpub, xprv) = (base58check(xpub), base58check(xprv));
            assert_eq!((xpub.len(), xprv.len()), (78, 78));
            assert_eq!(usize::from(xpub[4]), path.len());
            let node = bip32_derive(&seed, path).expect("valid derivation");
            assert_eq!(node.chain_code[..], xpub[13..45], "chain code at {path:?}");
            assert_eq!(
                secp256k1_public_key(&node.private_key).unwrap()[..],
                xpub[45..],
                "public key at {path:?}"
            );
            assert_eq!(xprv[45], 0);
            assert_eq!(node.private_key[..], xprv[46..], "private key at {path:?}");
        }
    }

    #[test]
    fn slip10_matches_ed25519_test_vector_1() {
        // SLIP-0010, "Test vector 1 for ed25519": (path, chain code, private, public).
        let seed = hex("000102030405060708090a0b0c0d0e0f");
        let chain: [(&[u32], &str, &str, &str); 6] = [
            (
                &[],
                "90046a93de5380a72b5e45010748567d5ea02bbf6522f979e05c0d8d8ca9fffb",
                "2b4be7f19ee27bbf30c667b642d5f4aa69fd169872f8fc3059c08ebae2eb19e7",
                "a4b2856bfec510abab89753fac1ac0e1112364e7d250545963f135f2a33188ed",
            ),
            (
                &[H],
                "8b59aa11380b624e81507a27fedda59fea6d0b779a778918a2fd3590e16e9c69",
                "68e0fe46dfb67e368c75379acec591dad19df3cde26e63b93a8e704f1dade7a3",
                "8c8a13df77a28f3445213a0f432fde644acaa215fc72dcdf300d5efaa85d350c",
            ),
            (
                &[H, H + 1],
                "a320425f77d1b5c2505a6b1b27382b37368ee640e3557c315416801243552f14",
                "b1d0bad404bf35da785a64ca1ac54b2617211d2777696fbffaf208f746ae84f2",
                "1932a5270f335bed617d5b935c80aedb1a35bd9fc1e31acafd5372c30f5c1187",
            ),
            (
                &[H, H + 1, H + 2],
                "2e69929e00b5ab250f49c3fb1c12f252de4fed2c1db88387094a0f8c4c9ccd6c",
                "92a5b23c0b8a99e37d07df3fb9966917f5d06e02ddbd909c7e184371463e9fc9",
                "ae98736566d30ed0e9d2f4486a64bc95740d89c7db33f52121f8ea8f76ff0fc1",
            ),
            (
                &[H, H + 1, H + 2, H + 2],
                "8f6d87f93d750e0efccda017d662a1b31a266e4a6f5993b15f5c1f07f74dd5cc",
                "30d1dc7e5fc04c31219ab25a27ae00b50f6fd66622f6e9c913253d6511d1e662",
                "8abae2d66361c879b900d204ad2cc4984fa2aa344dd7ddc46007329ac76c429c",
            ),
            (
                &[H, H + 1, H + 2, H + 2, H + 1_000_000_000],
                "68789923a0cac2cd5a29172a475fe9e0fb14cd6adb5ad98a3fa70333e7afa230",
                "8f94d394a8e8fd6b1bc2f3f49f5c47e385281d5c17e65324b0f62483e37e8793",
                "3c24da049451555d51a7014a37337aa4e12d41e485abccfa46b47dfb2af54b7a",
            ),
        ];
        for (path, chain_code, private, public_key) in chain {
            let node = slip10_ed25519_derive(&seed, path).unwrap();
            assert_eq!(node.chain_code, arr::<32>(chain_code), "{path:?}");
            assert_eq!(node.private_key, arr::<32>(private), "{path:?}");
            assert_eq!(ed25519_public_key(&node.private_key), arr::<32>(public_key));
        }
        assert!(slip10_ed25519_derive(&seed, &[H, 1]).is_none());
    }

    #[test]
    fn bip32_ed25519_matches_the_reference_implementation() {
        // `D1` and `D1_H0` of `rust-ed25519-bip32` (`src/tests.rs`, `xprv_derive`):
        // the child at index 0x80000000.
        let child = cardano_root().child(H);
        assert_eq!(
            child.0,
            arr::<96>(
                "60d399da83ef80d8d4f8d223239efdc2b8fef387e1b5219137ffb4e8fbdea15a
                 dc9366b7d003af37c11396de9a83734e30e05e851efa32745c9cd7b42712c890
                 608763770eddf77248ab652984b21b849760d1da74a6f5bd633ce41adceef07a"
            )
        );
        // A soft step uses the public key and other tags, so it differs from the
        // hardened step of the same low index.
        let soft = cardano_root().child(0);
        assert_ne!(soft.0, child.0);
        assert_eq!(cardano_root().descend(&[H, 0]).0, child.child(0).0);
    }

    #[test]
    fn locks_match_published_vectors() {
        // RFC 8032 section 7.1, tests 1 and 2.
        for (seed, public) in [
            (
                "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            ),
            (
                "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            ),
        ] {
            assert_eq!(ed25519_public_key(&arr(seed)), arr::<32>(public));
        }
        // Secret key 1: the generator and its well-known addresses.
        let mut one = [0u8; 32];
        one[31] = 1;
        let credential = |lock| secp256k1_credential(lock, &one, None).unwrap();
        assert_eq!(
            secp256k1_public_key(&one).unwrap(),
            arr::<33>("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
        );
        assert_eq!(
            credential(Lock::P2pkh),
            Credential::BitcoinKeyHash(arr("751e76e8199196d454941c45d1b3a323f1433bd6"))
        );
        assert_eq!(
            credential(Lock::P2pkhUncompressed),
            Credential::BitcoinKeyHash(arr("91b24bf9f5288532960ac687abb035127b1d28a5"))
        );
        assert_eq!(
            credential(Lock::P2shP2wpkh),
            Credential::BitcoinScriptHash(arr("bcfeb728b584253d5f3f70bcb780e9ef218a68f4"))
        );
        assert_eq!(
            credential(Lock::Ethereum),
            Credential::EthereumAddress(arr("7e5f4552091a69125d5dfcb7b8c2659029395bdf"))
        );
        // Zero and the group order are not keys; a script tree needs its root.
        let order = arr::<32>("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        assert_eq!(secp256k1_credential(Lock::P2pkh, &[0; 32], None), None);
        assert_eq!(secp256k1_credential(Lock::Ethereum, &order, None), None);
        assert_eq!(
            secp256k1_credential(Lock::TaprootScriptTree, &one, None),
            None
        );
    }

    #[test]
    fn bls_withdrawal_credential_matches_the_generator_encoding() {
        // Secret key 1: the standard compressed encoding of the G1 generator.
        let mut one = [0u8; 32];
        one[31] = 1;
        let generator = arr::<48>(
            "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac58
             6c55e83ff97a1aeffb3af00adb22c6bb",
        );
        assert_eq!(bls12_381_public_key(&one), Some(generator));
        let mut want = sha2_native::sha256(&generator);
        assert_ne!(want[0], 0);
        want[0] = 0;
        assert_eq!(
            bls_withdrawal_credential(&one),
            Some(Credential::BlsWithdrawal(want))
        );
        // Zero and the group order are not keys.
        let order = arr::<32>("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001");
        assert_eq!(bls12_381_public_key(&[0; 32]), None);
        assert_eq!(bls12_381_public_key(&order), None);
        // In the relation, a key with bit 255 set is not a witness even though the
        // multiplication only reads 255 bits.
        let st = derive(
            Lock::BlsWithdrawal,
            KeySource::Bls12381Key,
            &OwnershipWitness::bls12_381_key(&one),
        );
        let mut high = one;
        high[0] |= 0x80;
        let forged = OwnershipWitness::bls12_381_key(&high);
        let mut bits = st.public_bits();
        let (shape, z, _) = build(
            Lock::BlsWithdrawal,
            &KeySource::Bls12381Key,
            &bits,
            &relation_witness(&forged),
        );
        assert!(!shape.is_satisfied(&z));
        // And the credential's first byte is pinned to zero.
        bits[0] = true;
        let honest = OwnershipWitness::bls12_381_key(&one);
        let (shape, z, _) = build(
            Lock::BlsWithdrawal,
            &KeySource::Bls12381Key,
            &bits,
            &relation_witness(&honest),
        );
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn taproot_matches_bip341_wallet_vectors() {
        // BIP-341 `wallet-test-vectors.json`, `keyPathSpending`, inputs 0, 1 and 3:
        // (internal private key, merkle root, tweak, tweaked private key, output key).
        let vectors: [(&str, Option<&str>, &str, &str, &str); 3] = [
            (
                "6b973d88838f27366ed61c9ad6367663045cb456e28335c109e30717ae0c6baa",
                None,
                "b86e7be8f39bab32a6f2c0443abbc210f0edac0e2c53d501b36b64437d9c6c70",
                "2405b971772ad26915c8dcdf10f238753a9b837e5f8e6a86fd7c0cce5b7296d9",
                "53a1f6e454df1aa2776a2814a721372d6258050de330b3c6d10ee8f4e0dda343",
            ),
            (
                "1e4da49f6aaf4e5cd175fe08a32bb5cb4863d963921255f33d3bc31e1343907f",
                Some("5b75adecf53548f3ec6ad7d78383bf84cc57b55a3127c72b9a2481752dd88b21"),
                "cbd8679ba636c1110ea247542cfbd964131a6be84f873f7f3b62a777528ed001",
                "ea260c3b10e60f6de018455cd0278f2f5b7e454be1999572789e6a9565d26080",
                "147c9c57132f6e7ecddba9800bb0c4449251c92a1e60371ee77557b6620f3ea3",
            ),
            (
                "d3c7af07da2d54f7a7735d3d0fc4f0a73164db638b2f2f7c43f711f6d4aa7e64",
                Some("c525714a7f49c28aedbbba78c005931a81c234b2f6c99a73e4d06082adc8bf2b"),
                "6af9e28dbf9d6aaf027696e2598a5b3d056f5fd2355a7fd5a37a0e5008132d30",
                "97323385e57015b75b0339a549c56a948eb961555973f0951f555ae6039ef00d",
                "e4d810fd50586274face62b8a807eb9719cef49c04177cc6b76a9a4251d5450e",
            ),
        ];
        let mut odd_internal_keys = 0;
        for (key, root, tweak, tweaked, output) in vectors {
            let key: [u8; 32] = arr(key);
            let root: Option<[u8; 32]> = root.map(arr);
            let internal = secp256k1_public_key(&key).unwrap();
            odd_internal_keys += usize::from(internal[0] == 3);
            let x: [u8; 32] = internal[1..].try_into().unwrap();
            assert_eq!(taproot_tweak(&x, root.as_ref()), arr::<32>(tweak));
            assert_eq!(
                taproot_output_key(&key, root.as_ref()).unwrap(),
                arr::<32>(output)
            );
            assert_eq!(
                secp256k1_public_key(&arr(tweaked)).unwrap()[1..],
                hex(output)[..]
            );
            let lock = if root.is_some() {
                Lock::TaprootScriptTree
            } else {
                Lock::TaprootKeyPath
            };
            assert_eq!(
                secp256k1_credential(lock, &key, root.as_ref()),
                Some(Credential::BitcoinTaproot(arr(output)))
            );
        }
        // The vectors exercise the negation of an odd internal key.
        assert!(odd_internal_keys >= 1);
    }

    #[test]
    fn bip39_seed_matches_the_reference_vectors() {
        // `python-mnemonic` `vectors.json` (passphrase "TREZOR"): mnemonic, seed, master xprv.
        let vectors = [
            (
                "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about",
                "c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04",
                "xprv9s21ZrQH143K3h3fDYiay8mocZ3afhfULfb5GX8kCBdno77K4HiA15Tg23wpbeF1pLfs1c5SPmYHrEpTuuRhxMwvKDwqdKiGJS9XFKzUsAF",
            ),
            (
                "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong",
                "ac27495480225222079d7be181583751e86f571027b0497b5b5d11218e0a8a13332572917f0f8e5a589620c6f15b11c61dee327651a14c34e18231052e48c069",
                "xprv9s21ZrQH143K2V4oox4M8Zmhi2Fjx5XK4Lf7GKRvPSgydU3mjZuKGCTg7UPiBUD7ydVPvSLtg9hjp7MQTYsW67rZHAXeccqYqrsx8LcXnyd",
            ),
            (
                "void come effort suffer camp survey warrior heavy shoot primary clutch crush open amazing screen patrol group space point ten exist slush involve unfold",
                "01f5bced59dec48e362f2c45b5de68b9fd6c92c6634f44d6d40aab69056506f0e35524a518034ddc1192e1dacd32c1ed3eaa3c3b131c88ed8e7e54c49a5d0998",
                "xprv9s21ZrQH143K39rnQJknpH1WEPFJrzmAqqasiDcVrNuk926oizzJDDQkdiTvNPr2FYDYzWgiMiC63YmfPAa2oPyNB23r2g7d1yiK6WpqaQS",
            ),
        ];
        for (mnemonic, seed, xprv) in vectors {
            let got = bip39_seed(mnemonic, "TREZOR");
            assert_eq!(got[..], hex(seed)[..]);
            let (xprv, master) = (base58check(xprv), bip32_master(&got).unwrap());
            assert_eq!(master.chain_code[..], xprv[13..45]);
            assert_eq!(master.private_key[..], xprv[46..]);
        }
        assert_ne!(
            bip39_seed(vectors[0].0, ""),
            bip39_seed(vectors[0].0, "TREZOR")
        );
    }

    #[test]
    fn nullifier_is_per_secret_credential_and_domain() {
        let credential = Credential::BitcoinKeyHash([7; 20]);
        let n = migration_nullifier(1, &KEY, &DOMAIN, &credential);
        // It is plain SHA-256 of the documented preimage.
        let mut preimage = b"QSAG.MIGRATE.HEM.NULLIFIER/v2\x01\0\0".to_vec();
        preimage.extend_from_slice(&DOMAIN);
        preimage.extend_from_slice(&credential.identifier());
        preimage.extend_from_slice(&[0; 32]);
        preimage.extend_from_slice(&KEY);
        assert_eq!(n, sha2_native::sha256(&preimage));

        let mut other_domain = DOMAIN;
        other_domain[31] ^= 1;
        let mut other_key = KEY;
        other_key[0] ^= 1;
        assert_ne!(n, migration_nullifier(1, &KEY, &other_domain, &credential));
        assert_ne!(n, migration_nullifier(2, &KEY, &DOMAIN, &credential));
        assert_ne!(n, migration_nullifier(1, &other_key, &DOMAIN, &credential));
        assert_ne!(
            n,
            migration_nullifier(1, &KEY, &DOMAIN, &Credential::EthereumAddress([7; 20]))
        );
        assert_ne!(
            n,
            migration_nullifier(1, &KEY, &DOMAIN, &Credential::BitcoinKeyHash([8; 20]))
        );

        // An Ed25519 key proved from its seed or through SLIP-0010 has one nullifier.
        let master = seed(16);
        let path = [H, H + 1];
        let leaf = slip10_ed25519_derive(&master, &path).unwrap();
        let via_slip10 = derive(
            Lock::Ed25519,
            KeySource::Slip10 {
                path: public(&path),
            },
            &OwnershipWitness::seed(&master),
        );
        let via_hidden_path = derive(
            Lock::Ed25519,
            KeySource::Slip10 {
                path: PathSpec::Hidden { max_depth: 3 },
            },
            &OwnershipWitness::seed(&master).with_path(&path),
        );
        let via_seed = derive(
            Lock::Ed25519,
            KeySource::Ed25519Seed,
            &OwnershipWitness::ed25519_seed(&leaf.private_key),
        );
        assert_eq!(via_slip10.credential, via_seed.credential);
        assert_eq!(via_slip10.nullifier, via_seed.nullifier);
        assert_eq!(via_slip10.nullifier, via_hidden_path.nullifier);

        // A revealed secp256k1 key: the seed statement's nullifier is not the function of
        // the signing key that the hidden-key statement uses, and not one of the leaf's
        // chain code either.
        let master = seed(64);
        let path = [H + 44, 5];
        let leaf = bip32_derive(&master, &path).unwrap();
        let seeded = derive(
            Lock::P2pkh,
            bip32(Bip32Root::Seed, public(&path)),
            &OwnershipWitness::seed(&master),
        );
        let hidden = derive(
            Lock::P2pkh,
            KeySource::Secp256k1Key,
            &OwnershipWitness::secp256k1_key(&leaf.private_key),
        );
        assert_eq!(seeded.credential, hidden.credential);
        assert_ne!(seeded.nullifier, hidden.nullifier);
        for kind in [1, 2, 7] {
            for secret in [&leaf.private_key, &leaf.chain_code] {
                assert_ne!(
                    seeded.nullifier,
                    migration_nullifier(kind, secret, &DOMAIN, &seeded.credential)
                );
            }
        }
        assert_eq!(
            seeded.nullifier,
            migration_nullifier(
                2,
                &master_inner_digest(BIP32_MASTER_KEY, &master),
                &DOMAIN,
                &seeded.credential
            )
        );
        // Two credentials of that seed are unlinkable by nullifier and by identifier.
        let ethereum = derive(
            Lock::Ethereum,
            bip32(Bip32Root::Seed, public(&path)),
            &OwnershipWitness::seed(&master),
        );
        assert_ne!(ethereum.nullifier, seeded.nullifier);
        assert_ne!(
            ethereum.credential.identifier(),
            seeded.credential.identifier()
        );
    }

    /// Row budget of the parts every statement shares.
    #[test]
    fn shared_parts_have_the_expected_row_counts() {
        let mut cs = ConstraintSystem::new();
        let public = alloc_public(&mut cs, &[false; 160 + 512]);
        let credential = alloc_bits(&mut cs, &[0; 20]);
        let secret = alloc_bits(&mut cs, &KEY);
        let before = cs.num_rows();
        bind_credential(&mut cs, &public, &credential, &secret);
        let binding = cs.num_rows() - before;
        std::println!("bind_credential rows: {binding}");
        // One SHA-256 compression with a variable chaining value, and the pins.
        assert!((12_000..18_000).contains(&binding), "{binding}");

        let mut cs = ConstraintSystem::new();
        let key = reverse_bytes(&alloc_bits(&mut cs, &KEY));
        let before = cs.num_rows();
        secp256k1_enforce_scalar_range(&mut cs, &key);
        let range = cs.num_rows() - before;
        let _ = secp256k1_fixed_base_mul(&mut cs, &key);
        let mul = cs.num_rows() - before - range;
        let _ = secp_lock(&mut cs, Lock::P2pkh, &key, &[0; 32]);
        let lock = cs.num_rows() - before - range - mul;
        std::println!("range {range}, mul {mul}, p2pkh lock with its own mul {lock}");
        assert!(mul > 30_000 && lock > mul + 30_000);
    }

    #[test]
    fn derive_rejects_unusable_witnesses() {
        let try_derive = |lock, source, w: &OwnershipWitness| {
            OwnershipStatement::derive(lock, source, w, PQ, DOMAIN, EPOCH)
        };
        let order = arr::<32>("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let key = OwnershipWitness::secp256k1_key(&KEY);
        let seed_root = |path| bip32(Bip32Root::Seed, path);
        assert!(
            try_derive(
                Lock::P2pkh,
                KeySource::Secp256k1Key,
                &OwnershipWitness::secp256k1_key(&[0; 32])
            )
            .is_none()
        );
        assert!(
            try_derive(
                Lock::Ethereum,
                KeySource::Secp256k1Key,
                &OwnershipWitness::secp256k1_key(&order)
            )
            .is_none()
        );
        // Lock and source of different curves.
        assert!(try_derive(Lock::Ed25519, KeySource::Secp256k1Key, &key).is_none());
        assert!(try_derive(Lock::P2pkh, KeySource::Ed25519Seed, &key).is_none());
        // A script tree without its root.
        assert!(try_derive(Lock::TaprootScriptTree, KeySource::Secp256k1Key, &key).is_none());
        // Seed lengths, path lengths, a hidden path longer than its bound.
        assert!(
            try_derive(
                Lock::P2pkh,
                seed_root(public(&[])),
                &OwnershipWitness::seed(&[1; 15])
            )
            .is_none()
        );
        assert!(
            try_derive(
                Lock::P2pkh,
                seed_root(public(&[])),
                &OwnershipWitness::seed(&[1; 65])
            )
            .is_none()
        );
        assert!(
            try_derive(
                Lock::P2pkh,
                seed_root(public(&[0; 11])),
                &OwnershipWitness::seed(&[1; 32])
            )
            .is_none()
        );
        assert!(
            try_derive(
                Lock::P2pkh,
                seed_root(public(&[0; 10])),
                &OwnershipWitness::seed(&[1; 16])
            )
            .is_some()
        );
        let hidden = |max_depth| seed_root(PathSpec::Hidden { max_depth });
        let walk = OwnershipWitness::seed(&[1; 32]).with_path(&[1, 2, 3]);
        assert!(try_derive(Lock::P2pkh, hidden(2), &walk).is_none());
        assert!(try_derive(Lock::P2pkh, hidden(3), &walk).is_some());
        assert!(try_derive(Lock::P2pkh, hidden(0), &walk).is_none());
        assert!(try_derive(Lock::P2pkh, hidden(11), &walk).is_none());
        // SLIP-0010 has hardened steps only.
        let slip = |path| KeySource::Slip10 { path };
        assert!(
            try_derive(
                Lock::Ed25519,
                slip(public(&[H, 1])),
                &OwnershipWitness::seed(&[1; 32])
            )
            .is_none()
        );
        assert!(
            try_derive(
                Lock::Ed25519,
                slip(PathSpec::Hidden { max_depth: 3 }),
                &walk
            )
            .is_none()
        );
        // An extended key is 64 bytes with a valid scalar.
        let xprv = |path| bip32(Bip32Root::ExtendedKey, path);
        assert!(
            try_derive(
                Lock::P2pkh,
                xprv(public(&[1])),
                &OwnershipWitness::seed(&[1; 32])
            )
            .is_none()
        );
        assert!(
            try_derive(
                Lock::P2pkh,
                xprv(public(&[1])),
                &OwnershipWitness::seed(&[0; 64])
            )
            .is_none()
        );
    }

    #[test]
    fn statement_encoding_is_canonical_and_strict() {
        for (name, lock, source, witness) in cases() {
            let st = derive(lock, source, &witness);
            let bytes = st.to_bytes();
            assert_eq!(
                OwnershipStatement::from_bytes(&bytes),
                Some(st.clone()),
                "{name}"
            );
            assert_eq!(bytes[29], lock as u8);
            assert_eq!(bytes[30], u8::from(st.source.proves_seed_provenance()));

            let mut longer = bytes.clone();
            longer.push(0);
            assert_eq!(OwnershipStatement::from_bytes(&longer), None, "{name}");
            assert_eq!(
                OwnershipStatement::from_bytes(&bytes[..bytes.len() - 1]),
                None,
                "{name}"
            );
            // The tag and the exposure byte are checked; every other byte is a field.
            for at in (0..29).chain([30]) {
                let mut bad = bytes.clone();
                bad[at] ^= 1;
                assert_eq!(
                    OwnershipStatement::from_bytes(&bad),
                    None,
                    "{name} byte {at}"
                );
            }
            for at in (29..bytes.len()).filter(|&at| at != 30) {
                let mut other = bytes.clone();
                other[at] ^= 0x40;
                assert_ne!(
                    OwnershipStatement::from_bytes(&other),
                    Some(st.clone()),
                    "{name} byte {at}"
                );
            }
        }
        // Parameters outside the supported ranges are malformed and do not decode.
        let (_, lock, _, witness) = cases().remove(0);
        let st = derive(lock, KeySource::Secp256k1Key, &witness);
        let with = |f: &dyn Fn(&mut OwnershipStatement)| {
            let mut bad = st.clone();
            f(&mut bad);
            (
                bad.is_well_formed(),
                OwnershipStatement::from_bytes(&bad.to_bytes()).is_some(),
            )
        };
        let source =
            |source: KeySource| move |s: &mut OwnershipStatement| s.source = source.clone();
        assert_eq!(with(&|_| {}), (true, true));
        assert_eq!(
            with(&source(bip32(Bip32Root::Seed, public(&[0; 11])))),
            (false, false)
        );
        assert_eq!(
            with(&source(bip32(Bip32Root::Seed, public(&[0; 10])))),
            (true, true)
        );
        assert_eq!(
            with(&source(bip32(
                Bip32Root::Seed,
                PathSpec::Hidden { max_depth: 0 }
            ))),
            (false, false)
        );
        assert_eq!(
            with(&source(bip32(
                Bip32Root::Seed,
                PathSpec::Hidden { max_depth: 11 }
            ))),
            (false, false)
        );
        assert_eq!(with(&source(KeySource::Ed25519Seed)), (false, false));
        assert_eq!(
            with(&source(KeySource::Slip10 { path: public(&[1]) })),
            (false, false)
        );
        // The wire carries the credential's bytes and the lock gives them their type, so a
        // mistyped credential is malformed in memory and cannot be expressed on the wire.
        assert_eq!(with(&|s| s.lock = Lock::Ethereum), (false, true));
        let mut mistyped = st.clone();
        mistyped.lock = Lock::Ethereum;
        let decoded = OwnershipStatement::from_bytes(&mistyped.to_bytes()).unwrap();
        assert!(matches!(decoded.credential, Credential::EthereumAddress(_)));
        assert_ne!(decoded, mistyped);
        assert_eq!(with(&|s| s.lock = Lock::P2pkhUncompressed), (true, true));
    }

    /// The relations themselves, without proofs: satisfied by the honest assignment, and
    /// unsatisfied when any public region or the witness is wrong.
    #[test]
    fn relations_accept_the_honest_assignment_only() {
        for (name, lock, source, witness) in cases() {
            let st = derive(lock, source.clone(), &witness);
            let public = st.public_bits();
            let (shape, z, rows) = build(lock, &source, &public, &relation_witness(&witness));
            assert!(shape.is_satisfied(&z), "{name}");
            assert_eq!(
                shape.num_sbox, 0,
                "the collaborative prover needs mul rows only"
            );
            assert_eq!(shape.num_public, public.len());
            assert!(
                rows > 80_000 && rows + 15 <= shape.num_rows(),
                "{name}: {rows}"
            );
            assert_eq!(st.public_inputs().unwrap(), z[1..=public.len()]);
            // The cached shape is built from a placeholder witness and zero public inputs.
            assert_eq!(
                shape.digest(),
                ownership_shape(&st).unwrap().digest(),
                "{name}"
            );

            // One wrong bit in the credential, in the chaining value, in the nullifier.
            let value_bits = 8 * lock.credential_bytes();
            for at in [
                3,
                value_bits - 1,
                value_bits + 5,
                value_bits + 255,
                value_bits + 256,
                public.len() - 1,
            ] {
                let mut wrong = public.clone();
                wrong[at] ^= true;
                let (shape, z, _) = build(lock, &source, &wrong, &relation_witness(&witness));
                assert!(!shape.is_satisfied(&z), "{name}, public bit {at}");
            }
            // Another secret under the honest public values.
            let mut other = witness.clone();
            other.secret[7] ^= 0x20;
            let (shape, z, _) = build(lock, &source, &public, &relation_witness(&other));
            assert!(!shape.is_satisfied(&z), "{name}, wrong secret");
            if !witness.path.is_empty() {
                let mut other = witness.clone();
                other.path[0] ^= 1;
                let (shape, z, _) = build(lock, &source, &public, &relation_witness(&other));
                assert!(!shape.is_satisfied(&z), "{name}, wrong hidden path");
            }
            if lock == Lock::TaprootScriptTree {
                let mut other = witness.clone();
                other.merkle_root = Some([0x3d; 32]);
                let (shape, z, _) = build(lock, &source, &public, &relation_witness(&other));
                assert!(!shape.is_satisfied(&z), "{name}, wrong merkle root");
            }
        }
    }

    #[test]
    fn public_paths_and_roots_select_the_relation() {
        let master = seed(64);
        let witness = OwnershipWitness::seed(&master);
        let honest = bip32(Bip32Root::Seed, public(&[H + 44, 1]));
        let st = derive(Lock::P2pkh, honest, &witness);
        let public_bits = st.public_bits();
        // Another index, swapped hardening, a shorter and a longer path: this key fails.
        for path in [
            vec![H + 45, 1],
            vec![44, H + 1],
            vec![H + 44],
            vec![H + 44, 1, 0],
        ] {
            let source = bip32(Bip32Root::Seed, PathSpec::Public(path));
            let (shape, z, _) = build(
                Lock::P2pkh,
                &source,
                &public_bits,
                &relation_witness(&witness),
            );
            assert!(!shape.is_satisfied(&z));
        }
        // The same leaf from an extended key one step up: a different relation with
        // another nullifier secret, satisfied for its own statement only.
        let parent = OwnershipWitness::extended_key(&bip32_derive(&master, &[H + 44]).unwrap());
        let from_parent = bip32(Bip32Root::ExtendedKey, public(&[1]));
        let st_parent = derive(Lock::P2pkh, from_parent.clone(), &parent);
        assert_eq!(st_parent.credential, st.credential);
        assert_ne!(st_parent.nullifier, st.nullifier);
        let run = |bits: &[bool]| {
            let (shape, z, _) = build(Lock::P2pkh, &from_parent, bits, &relation_witness(&parent));
            shape.is_satisfied(&z)
        };
        assert!(run(&st_parent.public_bits()));
        assert!(!run(&public_bits));
    }

    #[test]
    fn hidden_paths_and_seed_lengths_share_one_relation() {
        let source = bip32(Bip32Root::Seed, PathSpec::Hidden { max_depth: 2 });
        let mut digests = Vec::new();
        let mut credentials = Vec::new();
        for (len, path) in [
            (16usize, vec![]),
            (17, vec![9]),
            (40, vec![H + 3]),
            (64, vec![H, 0]),
            (63, vec![1, H + 2]),
        ] {
            let master = seed(len);
            let witness = OwnershipWitness::seed(&master).with_path(&path);
            let st = derive(Lock::P2pkh, source.clone(), &witness);
            // Native parity: the same leaf as the public-path statement.
            let leaf = bip32_derive(&master, &path).unwrap();
            assert_eq!(
                st.credential,
                secp256k1_credential(Lock::P2pkh, &leaf.private_key, None).unwrap()
            );
            let (shape, z, _) = build(
                Lock::P2pkh,
                &source,
                &st.public_bits(),
                &relation_witness(&witness),
            );
            assert!(shape.is_satisfied(&z), "seed {len}, path {path:?}");
            digests.push(shape.digest());
            credentials.push(st.credential);
            // The statement does not carry the path or the seed length.
            assert_eq!(st.source, source);

            // A seed with a nonzero byte past its length is not a witness.
            if len < 64 {
                let mut longer = master.clone();
                longer.push(1);
                let mut forged = witness.clone();
                forged.secret = longer;
                // Keep the selector at `len` by handing the relation the padded bytes.
                let mut cs = ConstraintSystem::new();
                let _ = seed_master(&mut cs, BIP32_MASTER_KEY, &master);
                let (shape, mut z) = cs.finish();
                assert!(shape.is_satisfied(&z));
                // Variable `1 + 8 * len` is the lowest bit of the first byte past the seed.
                z[1 + 8 * len] = F::ONE;
                assert!(
                    !shape.is_satisfied(&z),
                    "seed {len}: trailing byte accepted"
                );
            }
        }
        assert!(digests.windows(2).all(|w| w[0] == w[1]));
        assert!(credentials.windows(2).all(|w| w[0] != w[1]));

        // The master step with a hidden length equals HMAC-SHA512 for every length.
        for len in [16usize, 31, 32, 55, 56, 64] {
            let master = seed(len);
            let mut cs = ConstraintSystem::new();
            let (i, inner) = seed_master(&mut cs, SLIP10_ED25519_KEY, &master);
            assert_eq!(
                super::super::hash::bits_to_bytes(&cs, &i),
                sha2_native::hmac_sha512(SLIP10_ED25519_KEY, &master).to_vec(),
                "length {len}"
            );
            assert_eq!(
                super::super::hash::bits_to_bytes(&cs, &inner)[..32],
                master_inner_digest(SLIP10_ED25519_KEY, &master)
            );
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            // Two selectors set, or none, is not a length: variables 513.. are the one-hot.
            for change in [513 + len - 16, 513 + (len - 16 + 1) % 49] {
                let mut bad = z.clone();
                bad[change] = F::ONE - bad[change];
                assert!(!shape.is_satisfied(&bad), "length {len}, selector {change}");
            }
        }
    }

    #[test]
    fn bip32_child_key_enforces_the_rejection_rules() {
        let order_be =
            arr::<32>("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let sub = |a: &[u8; 32], b: u8| {
            let mut out = *a;
            let mut borrow = u16::from(b);
            for byte in out.iter_mut().rev() {
                let v = u16::from(*byte).wrapping_sub(borrow);
                *byte = v as u8;
                borrow = (v >> 8) & 1;
            }
            out
        };
        let small = |v: u8| {
            let mut out = [0u8; 32];
            out[31] = v;
            out
        };
        // (I_L, parent key, expected child or `None` when BIP-32 rejects).
        type Case = ([u8; 32], [u8; 32], Option<[u8; 32]>);
        let cases: [Case; 7] = [
            (small(5), small(9), Some(small(14))),
            (small(0), small(9), Some(small(9))),
            (sub(&order_be, 1), small(2), Some(small(1))),
            (sub(&order_be, 1), small(1), None),
            (sub(&order_be, 9), small(9), None),
            (order_be, small(9), None),
            ([0xff; 32], small(9), None),
        ];
        for (tweak, parent, want) in cases {
            let native_ok = secp_scalar_is_canonical(&tweak)
                && secp_scalar_is_valid_nonzero(&secp_scalar_add_mod_n(&tweak, &parent));
            assert_eq!(native_ok, want.is_some());

            let mut cs = ConstraintSystem::new();
            let tweak_bits = reverse_bytes(&alloc_bits(&mut cs, &tweak));
            let parent_bits = reverse_bytes(&alloc_bits(&mut cs, &parent));
            let order = Modulus::secp256k1_order();
            let child = bip32_child_key(&mut cs, &order, &tweak_bits, &parent_bits);
            assert_eq!(child.len(), 256);
            let child_be = super::super::hash::bits_to_bytes(&cs, &reverse_bytes(&child));
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), want.is_some(), "I_L {tweak:02x?}");
            if let Some(want) = want {
                assert_eq!(child_be, want);
                assert_eq!(secp_scalar_add_mod_n(&tweak, &parent), want);
            }
        }
    }

    #[test]
    fn prover_refuses_a_witness_that_does_not_match() {
        let (_, lock, source, witness) = cases().remove(0);
        let st = derive(lock, source, &witness);
        let mut wrong_key = KEY;
        wrong_key[3] ^= 1;
        let seed = [9; 32];
        assert_eq!(
            prove_ownership(
                &st,
                &OwnershipWitness::secp256k1_key(&wrong_key),
                REGIME,
                &seed
            ),
            Err(OwnershipError::WitnessMismatch)
        );
        // The right key cannot claim another nullifier, credential or domain.
        for field in 0..3 {
            let mut other = st.clone();
            match field {
                0 => other.nullifier[0] ^= 1,
                1 => other.migration_domain[0] ^= 1,
                _ => other.credential = Credential::BitcoinKeyHash([7; 20]),
            }
            assert_eq!(
                prove_ownership(&other, &witness, REGIME, &seed),
                Err(OwnershipError::WitnessMismatch),
                "field {field}"
            );
        }
        let mut malformed = st.clone();
        malformed.lock = Lock::Ed25519;
        assert_eq!(
            prove_ownership(&malformed, &witness, REGIME, &seed),
            Err(OwnershipError::MalformedStatement)
        );
        let (batch, batch_witness) = batch_case();
        let mut other = batch.clone();
        other.entries[1].nullifier[0] ^= 1;
        assert_eq!(
            prove_batch(&other, &batch_witness, REGIME, &seed),
            Err(OwnershipError::WitnessMismatch)
        );
        assert_eq!(
            prove_batch(&batch, &OwnershipWitness::seed(&[5; 64]), REGIME, &seed),
            Err(OwnershipError::WitnessMismatch)
        );
    }

    /// One honest proof per case, shared by the tests below.
    fn proven(index: usize) -> &'static (OwnershipStatement, OwnershipProof) {
        static PROOFS: [OnceLock<(OwnershipStatement, OwnershipProof)>; 15] =
            [const { OnceLock::new() }; 15];
        PROOFS[index].get_or_init(|| {
            let (_, lock, source, witness) = cases().remove(index);
            let st = derive(lock, source, &witness);
            let proof = prove_ownership(&st, &witness, REGIME, &[index as u8 + 1; 32]).unwrap();
            (st, proof)
        })
    }

    fn proven_batch() -> &'static (BatchStatement, OwnershipProof) {
        static PROOF: OnceLock<(BatchStatement, OwnershipProof)> = OnceLock::new();
        PROOF.get_or_init(|| {
            let (batch, witness) = batch_case();
            let proof = prove_batch(&batch, &witness, REGIME, &[77; 32]).unwrap();
            (batch, proof)
        })
    }

    /// Statements that differ from `st` in exactly one public field.
    fn variants(st: &OwnershipStatement) -> Vec<(&'static str, OwnershipStatement)> {
        let mut out: Vec<(&'static str, OwnershipStatement)> = Vec::new();
        let mut push = |name: &'static str, f: &dyn Fn(&mut OwnershipStatement)| {
            let mut other = st.clone();
            f(&mut other);
            assert_ne!(&other, st, "{name} must change the statement");
            out.push((name, other));
        };
        push("pq commitment", &|s| s.pq_commitment[31] ^= 1);
        push("migration domain", &|s| s.migration_domain[0] ^= 0x80);
        push("epoch", &|s| s.epoch += 1);
        push("nullifier", &|s| s.nullifier[16] ^= 4);
        push("credential value", &|s| {
            let mut value = s.credential.value().to_vec();
            value[0] ^= 1;
            s.credential = s.lock.credential(&value).unwrap();
        });
        // Another lock that yields the same credential type.
        match st.lock {
            Lock::P2pkh => push("lock", &|s| s.lock = Lock::P2pkhUncompressed),
            Lock::P2pkhUncompressed => push("lock", &|s| s.lock = Lock::P2pkh),
            Lock::TaprootKeyPath => push("lock", &|s| s.lock = Lock::TaprootScriptTree),
            Lock::TaprootScriptTree => push("lock", &|s| s.lock = Lock::TaprootKeyPath),
            _ => {}
        }
        let respec = |spec: &mut PathSpec, change: u8| match spec {
            PathSpec::Public(path) => match change {
                0 => path[0] ^= 1,
                1 => path.push(H),
                _ => {
                    path.pop();
                }
            },
            PathSpec::Hidden { max_depth } => *max_depth += 1,
        };
        match &st.source {
            KeySource::Secp256k1Key => push("source", &|s| {
                s.source = bip32(Bip32Root::ExtendedKey, public(&[]));
            }),
            KeySource::Bls12381Key => push("source", &|s| s.source = KeySource::Secp256k1Key),
            KeySource::Ed25519Seed => push("source", &|s| {
                s.source = KeySource::Slip10 { path: public(&[]) };
            }),
            KeySource::Bip32 { .. } => {
                for (name, change) in [("path index", 0), ("longer path", 1), ("shorter path", 2)] {
                    push(name, &|s| {
                        if let KeySource::Bip32 { path, .. } = &mut s.source {
                            respec(path, change);
                        }
                    });
                }
                push("root", &|s| {
                    if let KeySource::Bip32 { root, .. } = &mut s.source {
                        *root = match *root {
                            Bip32Root::Seed => Bip32Root::ExtendedKey,
                            Bip32Root::ExtendedKey => Bip32Root::Seed,
                        };
                    }
                });
                push("path privacy", &|s| {
                    if let KeySource::Bip32 { path, .. } = &mut s.source {
                        *path = match path {
                            PathSpec::Public(p) => PathSpec::Hidden {
                                max_depth: p.len() as u8,
                            },
                            PathSpec::Hidden { .. } => public(&[H + 44, 7]),
                        };
                    }
                });
            }
            KeySource::Slip10 { .. } => {
                for (name, change) in [("path index", 0), ("longer path", 1)] {
                    push(name, &|s| {
                        if let KeySource::Slip10 { path } = &mut s.source {
                            respec(path, change);
                        }
                    });
                }
            }
            KeySource::Bip32Ed25519 { .. } => {
                push("path index", &|s| {
                    if let KeySource::Bip32Ed25519 { path } = &mut s.source {
                        path[1] ^= 1;
                    }
                });
                push("path hardening", &|s| {
                    if let KeySource::Bip32Ed25519 { path } = &mut s.source {
                        path[0] ^= H;
                    }
                });
            }
        }
        out
    }

    /// Wire format: canonical, strict, and every sampled byte matters.
    fn check_wire(bytes: &[u8], accepted: &dyn Fn(&[u8]) -> bool, name: &str) {
        assert!(accepted(bytes), "{name}");
        let mut longer = bytes.to_vec();
        longer.push(0);
        assert!(!accepted(&longer), "{name}: trailing byte");
        assert!(!accepted(&bytes[..bytes.len() - 1]), "{name}: truncated");
        let mut tried = 0;
        for at in (0..9).chain((9..bytes.len()).step_by(bytes.len() / 61)) {
            let mut bad = bytes.to_vec();
            bad[at] ^= 1;
            assert!(!accepted(&bad), "{name}: byte {at} of {}", bytes.len());
            tried += 1;
        }
        assert!(tried >= 60);
    }

    /// Everything a verifier must reject, against one honest proof.
    fn check_proof(index: usize) {
        let name = cases()[index].0;
        let (st, proof) = proven(index);
        assert!(verify_ownership(st, REGIME, proof), "honest proof, {name}");
        for (field, other) in variants(st) {
            assert!(!verify_ownership(&other, REGIME, proof), "{field}, {name}");
        }
        // The regime is the verifier's choice and is bound.
        let other_regime = Profile::CshakeJohnson400;
        assert!(!verify_ownership(st, other_regime, proof));
        let mut relabelled = proof.clone();
        relabelled.regime = other_regime;
        assert!(!verify_ownership(st, other_regime, &relabelled));

        let bytes = proof.to_bytes();
        assert_eq!(OwnershipProof::from_bytes(&bytes, st).as_ref(), Some(proof));
        check_wire(
            &bytes,
            &|b| {
                OwnershipProof::from_bytes(b, st).is_some_and(|p| verify_ownership(st, REGIME, &p))
            },
            name,
        );
    }

    macro_rules! proof_tests {
        ($($test:ident = $index:expr;)*) => {$(
            #[test]
            fn $test() {
                check_proof($index);
            }
        )*};
    }

    proof_tests! {
        proof_p2pkh_from_key = 0;
        proof_uncompressed_p2pkh_from_key = 1;
        proof_p2sh_p2wpkh_from_key = 2;
        proof_ethereum_from_key = 3;
        proof_taproot_key_path_from_key = 4;
        proof_taproot_script_tree_from_key = 5;
        proof_ed25519_from_seed = 6;
        proof_ed25519_from_slip10 = 7;
        proof_ed25519_from_slip10_hidden_path = 8;
        proof_ed25519_from_bip32_ed25519 = 9;
        proof_p2pkh_from_bip32_seed = 10;
        proof_ethereum_from_bip32_seed = 11;
        proof_taproot_from_bip32_extended_key = 12;
        proof_p2pkh_from_bip32_hidden_path = 13;
        proof_bls_withdrawal_from_key = 14;
    }

    #[test]
    fn no_proof_verifies_as_another_statement_kind() {
        let count = cases().len();
        assert_eq!(count, 15);
        let (batch, batch_proof) = proven_batch();
        for i in 0..count {
            let (st, _) = proven(i);
            for j in 0..count {
                let (_, proof) = proven(j);
                assert_eq!(
                    verify_ownership(st, REGIME, proof),
                    i == j,
                    "proof {j} as statement {i}"
                );
                if i != j {
                    // Also with the other proof's own statement values under this kind.
                    let (other, _) = proven(j);
                    let mut crossed = other.clone();
                    crossed.lock = st.lock;
                    crossed.source = st.source.clone();
                    if let Some(credential) = st.lock.credential(other.credential.value()) {
                        crossed.credential = credential;
                        assert!(
                            !verify_ownership(&crossed, REGIME, proof),
                            "{j} relabelled as {i}"
                        );
                    }
                }
            }
            assert!(
                !verify_ownership(st, REGIME, batch_proof),
                "batch proof as {i}"
            );
            assert!(
                !verify_batch(batch, REGIME, &proven(i).1),
                "proof {i} as batch"
            );
        }
        // A batch proof is not a proof of one of its entries either.
        let entry = batch.statement(0).unwrap();
        assert!(!verify_ownership(&entry, REGIME, batch_proof));
    }

    #[cfg(feature = "std")]
    #[test]
    fn shape_cache_returns_the_same_shape_and_stays_within_its_budget() {
        let relation = Relation::Single(Lock::P2pkh, KeySource::Secp256k1Key);
        let first = shape_of(&relation);
        // Cached: the same allocation, not an equal rebuild.
        assert!(Arc::ptr_eq(&first, &shape_of(&relation)));
        let size = shape_entries(&first);
        assert!(
            size > 1 << 20 && size < SHAPE_CACHE_ENTRIES / 16,
            "{size} entries"
        );
        // The budget admits a batch of 10 and not a batch of 100 (47,846,552 and
        // 350,554,982 entries measured).
        const { assert!(47_846_552 < SHAPE_CACHE_ENTRIES && SHAPE_CACHE_ENTRIES < 350_554_982) };
    }

    /// The prover's synthesis gives the pair a full synthesis gives, whether the shape
    /// was kept (assignment only) or not, and proofs do not depend on which path ran.
    #[test]
    fn kept_shape_synthesis_is_the_full_synthesis() {
        let witness = OwnershipWitness::secp256k1_key(&KEY);
        let st = derive(Lock::P2pkhUncompressed, KeySource::Secp256k1Key, &witness);
        let (shape, assignment) = synthesize_ownership(&st, &witness).unwrap();
        // Twice: the second call finds the shape the first one kept.
        for _ in 0..2 {
            let (shared, z) = synthesize_ownership_shared(&st, &witness).unwrap();
            assert_eq!(*shared, shape);
            assert_eq!(shared.digest(), shape.digest());
            assert_eq!(z, assignment);
            assert!(Arc::ptr_eq(&shared, &ownership_shape(&st).unwrap()));
        }
        let direct = protocol::prove(
            &shape,
            assignment,
            &ownership_transcript(&st, REGIME),
            REGIME,
            &[9; 32],
        )
        .unwrap();
        let kept = prove_ownership(&st, &witness, REGIME, &[9; 32]).unwrap();
        assert_eq!(kept.proof.to_bytes(), direct.to_bytes());

        let (batch, witness) = batch_case();
        let (shape, assignment) = synthesize_batch(&batch, &witness).unwrap();
        for _ in 0..2 {
            let (shared, z) = synthesize_batch_shared(&batch, &witness).unwrap();
            assert_eq!(*shared, shape);
            assert_eq!(z, assignment);
        }
        // A witness for another statement is still refused before any synthesis.
        let other = OwnershipWitness::secp256k1_key(&[7; 32]);
        assert_eq!(
            synthesize_ownership_shared(&st, &other).err(),
            Some(OwnershipError::WitnessMismatch)
        );
    }

    /// The relation of every reference statement, bound by its digest. These values were
    /// computed at commit `f303896`; a change means every proof of that statement changes.
    #[test]
    fn ownership_shape_digests_are_pinned() {
        let hex =
            |bytes: [u8; 32]| -> String { bytes.iter().map(|b| std::format!("{b:02x}")).collect() };
        let mut got: Vec<(String, String)> = cases()
            .into_iter()
            .map(|(name, lock, source, witness)| {
                let st = derive(lock, source, &witness);
                (
                    String::from(name),
                    hex(ownership_shape(&st).unwrap().digest()),
                )
            })
            .collect();
        let (batch, _) = batch_case();
        got.push((
            String::from("batch"),
            hex(batch_shape(&batch).unwrap().digest()),
        ));
        let want: Vec<(String, String)> = PINNED_SHAPE_DIGESTS
            .iter()
            .map(|(name, digest)| (String::from(*name), String::from(*digest)))
            .collect();
        assert_eq!(got, want);
    }

    const PINNED_SHAPE_DIGESTS: &[(&str, &str)] = &[
        (
            "p2pkh/key",
            "71193bc85c2e47f90d295d258496ebb96ddf422a0dd77a52a6cdfa6b3f70b7ab",
        ),
        (
            "p2pkh-uncompressed/key",
            "c6f21cbf478a43beda62c6c13b7d7098f7c9277314bceb0eff54ac54b6d07214",
        ),
        (
            "p2sh-p2wpkh/key",
            "4de945a9723a55597b989d898d517eaa88417d09cf703e1228fa48956f3e9401",
        ),
        (
            "ethereum/key",
            "fd4ed9d655cd8b55bf02428f7a4ca8d253d95fd1793fc4b76cea49a8f9a11b89",
        ),
        (
            "taproot/key",
            "1c5810b03a98c227d3bad400106c5769dfb8deac17315007daa3e44e1fc30169",
        ),
        (
            "taproot-tree/key",
            "1c005bbbe6b1dd44d07425985605dad242e4366148926164cfda368be13bc254",
        ),
        (
            "ed25519/seed",
            "7a6bdcb632533a035af62eee82a452a1990ebc19efeaaad636ad192bee3edb78",
        ),
        (
            "ed25519/slip10",
            "551542ca4f0e57ffcd9839e4e51daf9c593befe460e6e8f25265e74d4a98a774",
        ),
        (
            "ed25519/slip10-hidden",
            "83974ea8da57c79208e4c2c18f0d91300dd2a8fc304e30a2611a207ac8da3dfc",
        ),
        (
            "ed25519/bip32-ed25519",
            "f94af36ca3634ffde480b7270c7e5a59a97882020ffb66c185d000bf731d6f85",
        ),
        (
            "p2pkh/bip32-seed",
            "559743eee89f77ae97cf8a063b2a753c8ec197897042154418ea71634111d535",
        ),
        (
            "ethereum/bip32-seed",
            "454ff078ca668b7a0f8241ebcb7101ecf47a8d99e7fe485d8446c3cc0b642029",
        ),
        (
            "taproot/bip32-xprv",
            "465db673fc9c5ccd6d04e95d5b5fd1ca08dc90091f2f39eb550580e8936eacb2",
        ),
        (
            "p2pkh/bip32-hidden",
            "3dc1ebbb0f6d78fb1af2a5b7373f6dd6aaa573a02b1097cfccb31089b81b004b",
        ),
        (
            "bls-withdrawal/key",
            "518e18cc1f9cf7e5f38b702bf73e24abc2a2dbce2378e4e927308ed6bee03e0b",
        ),
        (
            "batch",
            "aa463fcd6b9ffbd54077f148332571f74e09b6090d9b8aaa3ff28818f9c8bac2",
        ),
    ];

    #[test]
    fn batch_chunks_make_the_claims_of_the_whole() {
        let witness = OwnershipWitness::seed(&seed(32));
        let targets: Vec<(Vec<u32>, [u8; 32])> = (0..5).map(|i| (vec![i], [i as u8; 32])).collect();
        let batch = BatchStatement::derive(
            Lock::P2pkh,
            Bip32Root::Seed,
            &[H],
            &targets,
            &witness,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let pieces = batch.chunks(2);
        assert_eq!(
            pieces.iter().map(|p| p.entries.len()).collect::<Vec<_>>(),
            [2, 2, 1]
        );
        let mut statements = Vec::new();
        for (index, piece) in pieces.iter().enumerate() {
            assert!(piece.is_well_formed());
            // A piece is the batch its own targets derive: nothing of the whole is needed
            // to prove it.
            let derived = BatchStatement::derive(
                Lock::P2pkh,
                Bip32Root::Seed,
                &[H],
                &targets[2 * index..(2 * index + 2).min(5)],
                &witness,
                DOMAIN,
                EPOCH,
            );
            assert_eq!(derived.as_ref(), Some(piece));
            assert!(synthesize_batch(piece, &witness).is_ok());
            statements.extend((0..piece.entries.len()).map(|i| piece.statement(i).unwrap()));
        }
        let whole: Vec<_> = (0..5).map(|i| batch.statement(i).unwrap()).collect();
        assert_eq!(statements, whole);
        // A piece does not stand for the whole, and a credential of another path does not
        // fit an entry.
        assert_ne!(pieces[0].to_bytes(), batch.to_bytes());
        let mut foreign = pieces[0].clone();
        foreign.entries[1].credential = batch.entries[4].credential;
        assert_eq!(
            synthesize_batch(&foreign, &witness).err(),
            Some(OwnershipError::WitnessMismatch)
        );
        assert_eq!(batch.chunks(5).as_slice(), core::slice::from_ref(&batch));
        assert_eq!(batch.chunks(100).as_slice(), core::slice::from_ref(&batch));
    }

    #[test]
    fn batch_entries_are_the_single_statements() {
        let (batch, witness) = batch_case();
        assert_eq!(batch.entries.len(), 2);
        for (i, index) in [0u32, 1].into_iter().enumerate() {
            let single = derive(
                Lock::P2pkh,
                bip32(Bip32Root::Seed, public(&[H + 44, index])),
                &witness,
            );
            let mut entry = batch.statement(i).unwrap();
            assert_eq!(entry.pq_commitment, [0x61 + i as u8; 32]);
            entry.pq_commitment = PQ;
            assert_eq!(entry, single);
        }
        assert_ne!(batch.entries[0].credential, batch.entries[1].credential);
        assert_ne!(batch.entries[0].nullifier, batch.entries[1].nullifier);

        // The relation: honest assignment only; entries cannot be swapped.
        let tails: Vec<Vec<u32>> = batch.entries.iter().map(|e| e.tail.clone()).collect();
        let public_bits = batch.public_bits();
        let run = |bits: &[bool], secret: &[u8]| {
            let (shape, z, rows) = build_batch(
                Lock::P2pkh,
                Bip32Root::Seed,
                &batch.prefix,
                &tails,
                bits,
                secret,
            );
            (shape.is_satisfied(&z), shape, rows)
        };
        let (ok, shape, rows) = run(&public_bits, &witness.secret);
        assert!(ok);
        assert_eq!(shape.num_sbox, 0);
        assert_eq!(shape.digest(), batch_shape(&batch).unwrap().digest());
        let half = public_bits.len() / 2;
        let swapped = [&public_bits[half..], &public_bits[..half]].concat();
        assert!(!run(&swapped, &witness.secret).0);
        for at in [0, half - 1, half, public_bits.len() - 1] {
            let mut wrong = public_bits.clone();
            wrong[at] ^= true;
            assert!(!run(&wrong, &witness.secret).0, "public bit {at}");
        }
        assert!(!run(&public_bits, &seed(63)).0);
        // Sharing: two entries cost less than two single statements.
        let single = bip32(Bip32Root::Seed, public(&[H + 44, 0]));
        let st = derive(Lock::P2pkh, single.clone(), &witness);
        let (_, _, single_rows) = build(
            Lock::P2pkh,
            &single,
            &st.public_bits(),
            &relation_witness(&witness),
        );
        assert!(
            rows + 300_000 < 2 * single_rows,
            "{rows} vs 2 x {single_rows}"
        );

        // Encoding.
        let bytes = batch.to_bytes();
        assert_eq!(BatchStatement::from_bytes(&bytes), Some(batch.clone()));
        let mut longer = bytes.clone();
        longer.push(0);
        assert_eq!(BatchStatement::from_bytes(&longer), None);
        assert_eq!(BatchStatement::from_bytes(&bytes[..bytes.len() - 1]), None);
        for at in 0..bytes.len() {
            let mut other = bytes.clone();
            other[at] ^= 0x10;
            assert_ne!(
                BatchStatement::from_bytes(&other),
                Some(batch.clone()),
                "byte {at}"
            );
        }
        let mut empty = batch.clone();
        empty.entries.clear();
        assert!(!empty.is_well_formed() && BatchStatement::from_bytes(&empty.to_bytes()).is_none());
        let mut deep = batch.clone();
        deep.entries[0].tail = vec![0; MAX_PATH_DEPTH];
        assert!(!deep.is_well_formed());
        let mut tree = batch.clone();
        tree.lock = Lock::TaprootScriptTree;
        assert!(!tree.is_well_formed());
    }

    #[test]
    fn proof_batch_verifies_and_binds_every_entry() {
        let (batch, proof) = proven_batch();
        assert!(verify_batch(batch, REGIME, proof));
        let mut others: Vec<(&str, BatchStatement)> = Vec::new();
        let mut push = |name: &'static str, f: &dyn Fn(&mut BatchStatement)| {
            let mut other = batch.clone();
            f(&mut other);
            assert_ne!(&other, batch);
            others.push((name, other));
        };
        push("pq commitment", &|b| b.entries[1].pq_commitment[0] ^= 1);
        push("nullifier", &|b| b.entries[0].nullifier[31] ^= 1);
        push("credential", &|b| {
            b.entries[1].credential = Credential::BitcoinKeyHash([3; 20]);
        });
        push("tail", &|b| b.entries[0].tail[0] = 2);
        push("order", &|b| b.entries.swap(0, 1));
        push("fewer entries", &|b| {
            b.entries.pop();
        });
        push("prefix", &|b| b.prefix[0] += 1);
        push("root", &|b| b.root = Bip32Root::ExtendedKey);
        push("lock", &|b| b.lock = Lock::P2pkhUncompressed);
        push("domain", &|b| b.migration_domain[5] ^= 1);
        push("epoch", &|b| b.epoch ^= 1);
        for (name, other) in &others {
            assert!(!verify_batch(other, REGIME, proof), "{name}");
        }
        let bytes = proof.to_bytes();
        check_wire(
            &bytes,
            &|b| {
                OwnershipProof::from_bytes_batch(b, batch)
                    .is_some_and(|p| verify_batch(batch, REGIME, &p))
            },
            "batch",
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn bindings_are_what_the_registry_consumes() {
        use super::super::registry::KeyExposure;
        for (name, lock, source, witness) in cases() {
            let hidden = !source.proves_seed_provenance();
            let st = derive(lock, source, &witness);
            let binding = st.binding();
            assert_eq!(binding.nullifier, st.nullifier, "{name}");
            assert_eq!(binding.migration_domain, DOMAIN);
            assert_eq!(binding.pq_commitment, PQ);
            assert_eq!(binding.epoch, EPOCH);
            assert_eq!(binding.legacy_id, st.credential.identifier());
            let exposure = if hidden {
                KeyExposure::Hidden
            } else {
                KeyExposure::Revealed
            };
            assert_eq!(binding.exposure, exposure, "{name}");
        }
        let (batch, _) = batch_case();
        let bindings = batch.bindings();
        assert_eq!(bindings.len(), 2);
        for (i, binding) in bindings.iter().enumerate() {
            assert_eq!(*binding, batch.statement(i).unwrap().binding());
            assert_eq!(binding.pq_commitment, batch.entries[i].pq_commitment);
        }
    }

    fn peak_rss_mib() -> Option<u64> {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
        let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
        Some(kib / 1024)
    }

    /// Takes the shape by value and drops it before proving: the prover builds its own,
    /// and a second copy would be counted in the peak.
    fn report(
        name: &str,
        shape: Shape,
        rows: usize,
        synth_s: f64,
        prove: &dyn Fn() -> OwnershipProof,
        verify: &dyn Fn(&[u8]) -> bool,
    ) {
        let layout = protocol::layout_of(&shape).unwrap();
        let stages: Vec<String> = layout
            .schedule
            .stages
            .iter()
            .map(|s| std::format!("{}q@x{}/2^{}", s.num_queries, s.blowup, s.step_vars))
            .collect();
        let head = std::format!(
            "HEM_OWNERSHIP statement=\"{name}\" regime={} rows={rows} padded_rows=2^{} vars={} \
             public_inputs={} cells=2^{} nnz={} synth_s={synth_s:.2} synth_peak_rss_mib={}",
            REGIME.wire_tag(),
            shape.log_rows,
            shape.num_vars,
            shape.num_public,
            layout.log_cells,
            shape.a.nnz() + shape.b.nnz() + shape.c.nnz(),
            // Meaningful when one statement is measured per process (`HEM_MEASURE_ONLY`).
            peak_rss_mib().map_or_else(|| String::from("n/a"), |m| std::format!("{m}")),
        );
        drop(shape);
        if std::env::var("HEM_MEASURE_ROWS_ONLY").is_ok() {
            println!("{head}");
            return;
        }
        let t = std::time::Instant::now();
        let proof = prove();
        let prove_s = t.elapsed().as_secs_f64();
        let bytes = proof.to_bytes();
        // A second proof of the same relation: its shape is kept, unless it is too large.
        let again = std::env::var("HEM_MEASURE_AGAIN").is_ok().then(|| {
            let t = std::time::Instant::now();
            assert_eq!(prove().to_bytes(), bytes);
            std::format!(" prove_again_s={:.2}", t.elapsed().as_secs_f64())
        });
        // The first verification also builds and caches the shape.
        let t = std::time::Instant::now();
        assert!(verify(&bytes));
        let verify_cold_s = t.elapsed().as_secs_f64();
        let mut warm: Vec<f64> = (0..3)
            .map(|_| {
                let t = std::time::Instant::now();
                assert!(verify(&bytes));
                t.elapsed().as_secs_f64()
            })
            .collect();
        warm.sort_by(f64::total_cmp);
        println!(
            "{head} prove_s={prove_s:.2}{} verify_cold_s={verify_cold_s:.2} verify_warm_ms={:.1} \
             proof_bytes={} proof_kib={:.1} stages=[{}] early_stop_vars={} peak_rss_mib={}",
            again.unwrap_or_default(),
            warm[1] * 1e3,
            bytes.len(),
            bytes.len() as f64 / 1024.0,
            stages.join(" "),
            layout.schedule.early_stop_vars,
            peak_rss_mib().map_or_else(|| String::from("n/a"), |m| std::format!("{m}")),
        );
    }

    /// `cargo test --release -p qsag-migrate --features std --lib -- --ignored --nocapture
    /// --test-threads 1 hem::relations::tests::measure_ownership_proofs`. `HEM_MEASURE_ONLY`
    /// filters by name; `HEM_MEASURE_ROWS_ONLY` skips proving; `HEM_MEASURE_BATCH` lists
    /// batch sizes (default `1,10`); `HEM_MEASURE_AGAIN` times a second proof.
    #[test]
    #[ignore = "measurement"]
    fn measure_ownership_proofs() {
        let key = || OwnershipWitness::secp256k1_key(&KEY);
        let master = || OwnershipWitness::seed(&seed(64));
        let seeded = |path: &[u32]| bip32(Bip32Root::Seed, public(path));
        let standard = [H + 44, H, H, 0, 0];
        let account = OwnershipWitness::extended_key(&bip32_master(&seed(64)).unwrap());
        let cardano = [H + 1852, H + 1815, H, 0, 0];
        let singles: Vec<(&str, Lock, KeySource, OwnershipWitness)> = vec![
            ("p2pkh, key", Lock::P2pkh, KeySource::Secp256k1Key, key()),
            (
                "p2pkh uncompressed, key",
                Lock::P2pkhUncompressed,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "p2sh-p2wpkh, key",
                Lock::P2shP2wpkh,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "ethereum, key",
                Lock::Ethereum,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "taproot key path, key",
                Lock::TaprootKeyPath,
                KeySource::Secp256k1Key,
                key(),
            ),
            (
                "taproot script tree, key",
                Lock::TaprootScriptTree,
                KeySource::Secp256k1Key,
                key().with_merkle_root(ROOT),
            ),
            (
                "bls 0x00 withdrawal credential, key",
                Lock::BlsWithdrawal,
                KeySource::Bls12381Key,
                OwnershipWitness::bls12_381_key(&KEY),
            ),
            (
                "ed25519, rfc8032 seed",
                Lock::Ed25519,
                KeySource::Ed25519Seed,
                OwnershipWitness::ed25519_seed(&KEY),
            ),
            (
                "ed25519, slip10 m/44'/501'/0'/0'",
                Lock::Ed25519,
                KeySource::Slip10 {
                    path: public(&[H + 44, H + 501, H, H]),
                },
                master(),
            ),
            (
                "ed25519, slip10 hidden path (max 4)",
                Lock::Ed25519,
                KeySource::Slip10 {
                    path: PathSpec::Hidden { max_depth: 4 },
                },
                master().with_path(&[H + 44, H + 501, H, H]),
            ),
            (
                "ed25519, bip32-ed25519 m/1852'/1815'/0'/0/0",
                Lock::Ed25519,
                KeySource::Bip32Ed25519 {
                    path: cardano.to_vec(),
                },
                OwnershipWitness::ed25519_extended_key(&cardano_root()),
            ),
            (
                "p2pkh, bip32 seed m/44'",
                Lock::P2pkh,
                seeded(&[H + 44]),
                master(),
            ),
            (
                "p2pkh, bip32 seed m/44'/0'/0'/0/0",
                Lock::P2pkh,
                seeded(&standard),
                master(),
            ),
            (
                "p2pkh, bip32 master xprv m/44'/0'/0'/0/0",
                Lock::P2pkh,
                bip32(Bip32Root::ExtendedKey, public(&standard)),
                account.clone(),
            ),
            (
                "p2pkh, bip32 seed hidden path (max 5)",
                Lock::P2pkh,
                bip32(Bip32Root::Seed, PathSpec::Hidden { max_depth: 5 }),
                master().with_path(&standard),
            ),
            (
                "p2sh-p2wpkh, bip32 seed m/49'/0'/0'/0/0",
                Lock::P2shP2wpkh,
                seeded(&[H + 49, H, H, 0, 0]),
                master(),
            ),
            (
                "ethereum, bip32 seed m/44'/60'/0'/0/0",
                Lock::Ethereum,
                seeded(&[H + 44, H + 60, H, 0, 0]),
                master(),
            ),
            (
                "taproot key path, bip32 seed m/86'/0'/0'/0/0",
                Lock::TaprootKeyPath,
                seeded(&[H + 86, H, H, 0, 0]),
                master(),
            ),
        ];
        let only = std::env::var("HEM_MEASURE_ONLY").ok();
        let wanted = |name: &str| only.as_ref().is_none_or(|o| name.contains(o.as_str()));
        println!(
            "cpus={}",
            std::thread::available_parallelism().map_or(0, |n| n.get())
        );
        for (name, lock, source, witness) in singles {
            if !wanted(name) {
                continue;
            }
            let st = derive(lock, source.clone(), &witness);
            let t = std::time::Instant::now();
            let (shape, _, rows) = build(
                lock,
                &source,
                &st.public_bits(),
                &relation_witness(&witness),
            );
            let synth_s = t.elapsed().as_secs_f64();
            report(
                name,
                shape,
                rows,
                synth_s,
                &|| prove_ownership(&st, &witness, REGIME, &[3; 32]).unwrap(),
                &|bytes| {
                    OwnershipProof::from_bytes(bytes, &st)
                        .is_some_and(|p| verify_ownership(&st, REGIME, &p))
                },
            );
        }
        let sizes: Vec<u32> = std::env::var("HEM_MEASURE_BATCH")
            .unwrap_or_else(|_| String::from("1,10"))
            .split(',')
            .map(|t| t.trim().parse().unwrap())
            .collect();
        for n in sizes {
            let name = std::format!("batch of {n}: p2pkh, bip32 seed m/44'/0'/0'/0/i");
            if !wanted(&name) {
                continue;
            }
            let targets: Vec<(Vec<u32>, [u8; 32])> =
                (0..n).map(|i| (vec![i], [i as u8; 32])).collect();
            let witness = master();
            let prefix = [H + 44, H, H, 0];
            let batch = BatchStatement::derive(
                Lock::P2pkh,
                Bip32Root::Seed,
                &prefix,
                &targets,
                &witness,
                DOMAIN,
                EPOCH,
            )
            .unwrap();
            let tails: Vec<Vec<u32>> = targets.iter().map(|(t, _)| t.clone()).collect();
            let t = std::time::Instant::now();
            let (shape, _, rows) = build_batch(
                Lock::P2pkh,
                Bip32Root::Seed,
                &prefix,
                &tails,
                &batch.public_bits(),
                &witness.secret,
            );
            let synth_s = t.elapsed().as_secs_f64();
            report(
                &name,
                shape,
                rows,
                synth_s,
                &|| prove_batch(&batch, &witness, REGIME, &[4; 32]).unwrap(),
                &|bytes| {
                    OwnershipProof::from_bytes_batch(bytes, &batch)
                        .is_some_and(|p| verify_batch(&batch, REGIME, &p))
                },
            );
        }
    }

    /// Rows of an EIP-2333 `derive_child_SK` step, from the measured cost of its parts.
    #[test]
    #[ignore = "measurement"]
    fn measure_eip2333_child_step() {
        use super::super::hash::{sha256, sha256_compress, sha256_iv};
        let rows = |f: &dyn Fn(&mut ConstraintSystem)| {
            let mut cs = ConstraintSystem::new();
            f(&mut cs);
            cs.num_rows()
        };
        let input = |cs: &mut ConstraintSystem, len: usize| alloc_bits(cs, &seed(len));
        // One HKDF-Expand block `T(i) = HMAC(PRK, T(i-1) || i)` under a prepared key.
        let key_rows = rows(&|cs| {
            let prk = input(cs, 32);
            let before = cs.num_rows();
            let _ = HmacKey::sha256(cs, &prk);
            assert!(cs.num_rows() > before);
        }) - 256;
        let expand_block = rows(&|cs| {
            let (prk, t) = (input(cs, 32), input(cs, 33));
            let key = HmacKey::sha256(cs, &prk);
            let _ = key.mac(cs, &t);
        }) - key_rows
            - 8 * 65;
        let chunk_hash = rows(&|cs| {
            let chunk = input(cs, 32);
            let _ = sha256(cs, &chunk);
        }) - 256;
        let compression = rows(&|cs| {
            let block: Vec<Word> = (0..16).map(|i| Word::alloc(cs, i, 32)).collect();
            let _ = sha256_compress(cs, &sha256_iv(), block.as_slice().try_into().unwrap());
        }) - 512;
        // parent_SK_to_lamport_PK: two HKDF chains of 255 blocks, 510 chunk hashes, one hash
        // of 16,320 bytes (256 blocks); then HKDF_mod_r (about eight compressions).
        let lamport = 2 * (key_rows + 255 * expand_block) + 510 * chunk_hash + 256 * compression;
        let child = lamport + 8 * compression;
        println!(
            "EIP2333 hkdf_expand_block={expand_block} chunk_hash={chunk_hash} compression={compression} \
             derive_child_SK={child} rows; EIP-2334 withdrawal path m/12381/3600/i/0 = 4 steps = {} rows \
             (2^{:.1}), before the master step and the G1 multiplication",
            4 * child,
            ((4 * child) as f64).log2()
        );
    }
}
