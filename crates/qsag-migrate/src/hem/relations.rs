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
