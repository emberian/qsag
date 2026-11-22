//! `qsag migrate`: prove that the holder of a legacy or Zcash credential authorises a
//! post-quantum address, verify such a proof, and record each migration once.
//!
//! The statements and proofs are those of [`qsag_migrate::hem::relations`] and
//! [`qsag_migrate::hem::zcash`] over `zk-Hem v2` (`QuinticGoldilocks`, 400-bit digests,
//! 256-bit salts, DKT26 soundness); the registry is [`qsag_migrate::hem::registry`]. Read
//! `crates/qsag-migrate/SECURITY.md` and `crates/qsag-agg/SECURITY.md` for what each
//! statement proves and for the security bounds of the proof system.
//!
//! # Files
//!
//! A claim file (`qsag-migration-claim-v2`) and a proof file (`qsag-migration-proof-v2`)
//! are JSON. Their `statement` member is the canonical statement encoding and is the only
//! authority; every other member (kind, legacy value, nullifier, epoch, domain, target
//! address) is a rendering of it and is rejected unless it equals what the statement
//! renders to. The proof itself is the `proof` member in base64 (RFC 4648, padded,
//! canonical). One file rather than a JSON header beside a binary sidecar, because a proof
//! is meaningless without its statement and a pair of files can be separated or mixed up;
//! base64 rather than hex, because the proof is hundreds of kilobytes and hex doubles it
//! where base64 adds a third.
//!
//! # Statement kinds
//!
//! [`KINDS`] is the table of kinds the command line offers and [`kind_of`] maps a claim to
//! its entry with an exhaustive match, so a claim variant added to the library does not
//! compile here until it has an entry.

use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::QsagAddress;
use qsag_agg::zk_hem::v2::bounds;
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_migrate::hem::registry::{
    BindingStatus, MigrationBinding, NullifierRegistry, Receipt, RegisteredBinding, RegistryError,
    pq_commitment,
};
use qsag_migrate::hem::relations::{
    Bip32Root, Ed25519ExtendedKey, HARDENED as BIP32_HARDENED, HdNode, KeySource, Lock,
    MAX_PATH_DEPTH as MAX_BIP32_DEPTH, OwnershipError, OwnershipProof, OwnershipStatement,
    OwnershipWitness, PathSpec, SEED_BYTES as BIP32_SEED_BYTES, ownership_shape, prove_ownership,
    verify_ownership,
};
use qsag_migrate::hem::zcash::{
    encoding::Network,
    orchard::{
        self, FullViewingKey as OrchardFullViewingKey, Note as OrchardNote, NoteVersion,
        Scope as OrchardScope, ZIP32_HARDENED, ZIP32_PURPOSE, ZIP32_SEED_BYTES,
    },
    pallas::{Fp as PallasFp, Point as PallasPoint},
    recovery::{
        AddressProof, AddressStatement, AddressWitness, KeySource as OrchardKeySource,
        KeyWitness as OrchardKeyWitness, RecoveryError, RecoveryProof, RecoveryStatement,
        RecoveryWitness, address_shape, prove_address, prove_recovery, recovery_shape,
        verify_address, verify_recovery,
    },
    rehash,
    sapling::{self, SaplingExtendedSpendingKey},
    sapling_address::{
        SaplingAddressProof, SaplingAddressStatement, SaplingKeySource, SaplingKeyWitness,
        prove_sapling_address, sapling_address_shape, verify_sapling_address,
    },
    transparent::{
        KeyEncoding, TransparentProof, TransparentStatement, bip44_path,
        coin_type as zcash_coin_type, prove_transparent, verify_transparent,
    },
};

use crate::anchor::{AnchorConfig, AnchorRequirementError, FsExternalMountAnchor};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_text, write_new,
};
use crate::codec::{Json, from_hex, from_hex_exact, to_hex};
use crate::vault::{Vault, set};

const MIGRATE_HELP: &str = "\
qsag migrate <subcommand> [options]

Prove that the holder of a legacy or Zcash credential authorises a post-quantum address, and
record each migration once. Proofs are zk-Hem v2 ownership proofs; see
crates/qsag-migrate/SECURITY.md.

  claim     derive the statement (legacy value, nullifier, target) from a legacy secret file
            (alias: commit)
  prove     prove a statement
  verify    verify a proof against the epoch, domain and target the verifier expects;
            --register records it in a registry in the same step
  registry  init | register | enroll | finalize | lookup: the durable one-way registry

statement kinds (--kind):
";

const CLAIM_FORMAT: &str = "qsag-migration-claim-v2";
const PROOF_FORMAT: &str = "qsag-migration-proof-v2";
const REGISTRY_FORMAT: &str = "qsag-migration-registry-v1";
const REGISTRY_SCHEME: &str = "migration-registry";
const DEFAULT_DOMAIN_LABEL: &[u8] = b"QSAG.CLI.MIGRATE.DEFAULT_DOMAIN.V1";
/// The zk-Hem v2 profile every proof this command writes or accepts is made under.
const REGIME: Profile = Profile::TurboShakeJohnson400;
const REGIME_NAME: &str = "TurboShakeJohnson400";

// ============================================================================
// Statement kinds
// ============================================================================

/// What the secret file of a kind holds.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SecretForm {
    /// Exactly 32 bytes: raw, hex, or the `seed` of an unsealed JSON key file.
    Key32,
    /// A BIP-32 master seed of 16 to 64 bytes, as hex or as the `seed` of a JSON file.
    /// Raw bytes are not accepted: a 64-byte file would be ambiguous with 32 bytes of hex.
    HexSeed,
    /// A ZIP-32 master seed of 32 to 252 bytes, as hex or as the `seed` of a JSON file.
    Zip32Seed,
    /// A BIP-32 extended private key: an `xprv`/`tprv` string (BIP-32 serialization,
    /// Base58Check), or 64 bytes `private key || chain code` as hex or JSON `seed`.
    ExtendedKey,
    /// A BIP32-Ed25519 extended private key `k_L || k_R || chain code`: 96 bytes as hex or
    /// JSON `seed`.
    Ed25519ExtendedKey,
    /// Structured JSON recovery witness (Zcash Ironwood note).
    JsonNote,
}

/// The key sources the command line offers for [`OwnershipStatement`] entries.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Source {
    /// The signing key itself (hidden-key mode).
    Key,
    /// The RFC 8032 seed of an Ed25519 key.
    Ed25519Seed,
    /// A BIP-32 master seed and a public `--path`.
    Bip32,
    /// A SLIP-0010 master seed and an all-hardened `--path`.
    Slip10,
    /// A BIP32-Ed25519 (Khovratovich-Law, Cardano) extended private key and a `--path`.
    Bip32Ed25519,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum KindFamily {
    Ownership { lock: Lock, source: Source },
    ZcashIronwood,
    ZcashOrchard,
    ZcashSapling,
    ZcashTransparent,
}

/// One statement kind of the command line. To offer another combination, add one of these
/// to [`KINDS`].
struct KindSpec {
    name: &'static str,
    aliases: &'static [&'static str],
    summary: &'static str,
    secret: SecretForm,
    family: KindFamily,
    /// The primary member the on-chain credential renders to.
    member: &'static str,
}

/// The options that shape the key source of an [`OwnershipStatement`] beyond its kind.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct SourceOptions {
    /// `--root extended-key`: the secret is an extended private key, not a master seed.
    extended_root: bool,
    /// `--hidden-path-depth <n>`: the path is a witness of at most `n` levels.
    hidden_depth: Option<u8>,
}

impl SourceOptions {
    fn of(source: &KeySource) -> Self {
        let hidden = |spec: &PathSpec| match spec {
            PathSpec::Hidden { max_depth } => Some(*max_depth),
            PathSpec::Public(_) => None,
        };
        match source {
            KeySource::Bip32 { root, path } => Self {
                extended_root: *root == Bip32Root::ExtendedKey,
                hidden_depth: hidden(path),
            },
            KeySource::Slip10 { path } => Self {
                extended_root: false,
                hidden_depth: hidden(path),
            },
            _ => Self::default(),
        }
    }
}

impl KindSpec {
    fn ownership_parts(&self) -> Option<(Lock, Source)> {
        match self.family {
            KindFamily::Ownership { lock, source } => Some((lock, source)),
            _ => None,
        }
    }

    /// Whether the kind requires `--path` (for standard `Ownership` entries).
    fn derivation_path(&self) -> bool {
        matches!(
            self.family,
            KindFamily::Ownership {
                source: Source::Bip32 | Source::Slip10 | Source::Bip32Ed25519,
                ..
            }
        )
    }

    /// Whether the kind takes `--merkle-root`.
    fn script_tree(&self) -> bool {
        matches!(
            self.family,
            KindFamily::Ownership {
                lock: Lock::TaprootScriptTree,
                ..
            }
        )
    }

    /// Whether `options` apply to this `Ownership` kind.
    fn admits(&self, options: SourceOptions) -> bool {
        let Some((_, source)) = self.ownership_parts() else {
            return false;
        };
        (!options.extended_root || source == Source::Bip32)
            && (options.hidden_depth.is_none() || matches!(source, Source::Bip32 | Source::Slip10))
    }

    /// What the secret file holds under `options`.
    fn secret_form(&self, options: SourceOptions) -> SecretForm {
        if options.extended_root {
            SecretForm::ExtendedKey
        } else {
            self.secret
        }
    }

    fn key_source(&self, path: Vec<u32>, options: SourceOptions) -> Option<KeySource> {
        let (lock, source) = self.ownership_parts()?;
        let spec = match options.hidden_depth {
            Some(max_depth) => PathSpec::Hidden { max_depth },
            None => PathSpec::Public(path.clone()),
        };
        Some(match (source, lock) {
            (Source::Key, Lock::BlsWithdrawal) => KeySource::Bls12381Key,
            (Source::Key, _) => KeySource::Secp256k1Key,
            (Source::Ed25519Seed, _) => KeySource::Ed25519Seed,
            (Source::Bip32, _) => KeySource::Bip32 {
                root: if options.extended_root {
                    Bip32Root::ExtendedKey
                } else {
                    Bip32Root::Seed
                },
                path: spec,
            },
            (Source::Slip10, _) => KeySource::Slip10 { path: spec },
            (Source::Bip32Ed25519, _) => KeySource::Bip32Ed25519 { path },
        })
    }

    /// Whether `source` is this kind's key source under some options and path.
    fn offers(&self, source: &KeySource) -> bool {
        let Some((lock, kind_source)) = self.ownership_parts() else {
            return false;
        };
        matches!(
            (kind_source, lock, source),
            (Source::Key, Lock::BlsWithdrawal, KeySource::Bls12381Key)
                | (Source::Key, _, KeySource::Secp256k1Key)
                | (Source::Ed25519Seed, _, KeySource::Ed25519Seed)
                | (Source::Bip32, _, KeySource::Bip32 { .. })
                | (Source::Slip10, _, KeySource::Slip10 { .. })
                | (Source::Bip32Ed25519, _, KeySource::Bip32Ed25519 { .. })
        ) && (kind_source != Source::Key
            || (lock == Lock::BlsWithdrawal) == (*source == KeySource::Bls12381Key))
    }

    /// The witness for secret bytes of the length [`Self::secret_form`] admits.
    fn witness(&self, bytes: &[u8], options: SourceOptions) -> Option<OwnershipWitness> {
        let (lock, source) = self.ownership_parts()?;
        Some(match (source, lock) {
            (Source::Key, Lock::BlsWithdrawal) => {
                OwnershipWitness::bls12_381_key(bytes.try_into().ok()?)
            }
            (Source::Key, _) => OwnershipWitness::secp256k1_key(bytes.try_into().ok()?),
            (Source::Ed25519Seed, _) => OwnershipWitness::ed25519_seed(bytes.try_into().ok()?),
            (Source::Bip32, _) if options.extended_root => {
                OwnershipWitness::extended_key(&HdNode {
                    private_key: bytes.get(..32)?.try_into().ok()?,
                    chain_code: bytes.get(32..)?.try_into().ok()?,
                })
            }
            (Source::Bip32 | Source::Slip10, _) => OwnershipWitness::seed(bytes),
            (Source::Bip32Ed25519, _) => {
                OwnershipWitness::ed25519_extended_key(&Ed25519ExtendedKey(bytes.try_into().ok()?))
            }
        })
    }

    /// The public members an [`OwnershipStatement`] of this kind renders to.
    fn render_ownership(&self, statement: &OwnershipStatement) -> Vec<(&'static str, Json)> {
        let mut out = vec![(self.member, Json::hex(statement.credential.value()))];
        append_source_members(&mut out, &statement.source);
        out
    }
}

fn append_source_members(out: &mut Vec<(&'static str, Json)>, source: &KeySource) {
    let options = SourceOptions::of(source);
    if options.extended_root {
        out.push(("bip32_root", Json::str("extended-key")));
    }
    if let Some(path) = public_path(source) {
        out.push(("derivation_path", Json::str(format_path(path))));
    }
    if let Some(depth) = options.hidden_depth {
        out.push(("hidden_path_max_depth", Json::num(depth)));
    }
}

fn append_orchard_key_source_members(
    out: &mut Vec<(&'static str, Json)>,
    source: &OrchardKeySource,
) {
    match source {
        OrchardKeySource::SpendingKey => out.push(("zcash_key_source", Json::str("spending-key"))),
        OrchardKeySource::Zip32Seed {
            seed_len,
            coin_type,
            account,
        } => {
            out.push(("zcash_key_source", Json::str("zip32-seed")));
            out.push(("seed_bytes", Json::num(seed_len)));
            out.push(("coin_type", Json::num(coin_type)));
            out.push(("account", Json::num(account)));
        }
        OrchardKeySource::QuantumSpendingKey => {
            out.push(("zcash_key_source", Json::str("quantum-spending-key")));
        }
    }
}

fn append_sapling_key_source_members(
    out: &mut Vec<(&'static str, Json)>,
    source: &SaplingKeySource,
) {
    match source {
        SaplingKeySource::SpendingKey => out.push(("zcash_key_source", Json::str("spending-key"))),
        SaplingKeySource::Zip32Seed {
            seed_len,
            coin_type,
            account,
        } => {
            out.push(("zcash_key_source", Json::str("zip32-seed")));
            out.push(("seed_bytes", Json::num(seed_len)));
            out.push(("coin_type", Json::num(coin_type)));
            out.push(("account", Json::num(account)));
        }
    }
}

/// The public derivation path of a source, if it has one.
fn public_path(source: &KeySource) -> Option<&[u32]> {
    match source {
        KeySource::Bip32 {
            path: PathSpec::Public(path),
            ..
        }
        | KeySource::Slip10 {
            path: PathSpec::Public(path),
        }
        | KeySource::Bip32Ed25519 { path } => Some(path),
        _ => None,
    }
}

const fn kind(
    name: &'static str,
    aliases: &'static [&'static str],
    summary: &'static str,
    lock: Lock,
    source: Source,
    member: &'static str,
) -> KindSpec {
    KindSpec {
        name,
        aliases,
        summary,
        secret: match source {
            Source::Key | Source::Ed25519Seed => SecretForm::Key32,
            Source::Bip32 | Source::Slip10 => SecretForm::HexSeed,
            Source::Bip32Ed25519 => SecretForm::Ed25519ExtendedKey,
        },
        family: KindFamily::Ownership { lock, source },
        member,
    }
}

const fn zcash_kind(
    name: &'static str,
    aliases: &'static [&'static str],
    summary: &'static str,
    secret: SecretForm,
    family: KindFamily,
    member: &'static str,
) -> KindSpec {
    KindSpec {
        name,
        aliases,
        summary,
        secret,
        family,
        member,
    }
}

static KIND_TABLE: [KindSpec; KIND_COUNT] = [
    kind(
        "btc-hash160",
        &["btc-p2wpkh", "btc-p2pkh"],
        "Bitcoin P2WPKH / P2PKH: HASH160 of the compressed public key (hidden key)",
        Lock::P2pkh,
        Source::Key,
        "legacy_hash160",
    ),
    kind(
        "btc-p2pkh-uncompressed",
        &[],
        "Bitcoin P2PKH of an uncompressed public key (hidden key)",
        Lock::P2pkhUncompressed,
        Source::Key,
        "legacy_hash160",
    ),
    kind(
        "btc-p2sh-p2wpkh",
        &[],
        "Bitcoin P2SH-wrapped P2WPKH script hash (hidden key)",
        Lock::P2shP2wpkh,
        Source::Key,
        "legacy_script_hash",
    ),
    kind(
        "btc-taproot",
        &[],
        "Bitcoin Taproot output key without a script tree (hidden internal key)",
        Lock::TaprootKeyPath,
        Source::Key,
        "legacy_output_key",
    ),
    kind(
        "eth-eoa",
        &["ethereum"],
        "Ethereum externally owned account address (hidden key)",
        Lock::Ethereum,
        Source::Key,
        "legacy_address",
    ),
    kind(
        "bls-withdrawal",
        &[],
        "Ethereum 0x00 withdrawal credential of a BLS12-381 key (hidden key)",
        Lock::BlsWithdrawal,
        Source::Key,
        "legacy_withdrawal_credential",
    ),
    kind(
        "ed25519",
        &["ed25519-seed"],
        "Ed25519 public key, by knowledge of its RFC 8032 seed (revealed key)",
        Lock::Ed25519,
        Source::Ed25519Seed,
        "legacy_public_key",
    ),
    kind(
        "slip10-ed25519",
        &["slip10"],
        "Ed25519 public key at a hardened --path of a SLIP-0010 master seed (revealed key)",
        Lock::Ed25519,
        Source::Slip10,
        "legacy_public_key",
    ),
    kind(
        "bip32-secp256k1",
        &["bip32"],
        "Bitcoin P2WPKH / P2PKH of the key at --path of a BIP-32 master seed (revealed key)",
        Lock::P2pkh,
        Source::Bip32,
        "legacy_hash160",
    ),
    kind(
        "bip32-p2sh-p2wpkh",
        &[],
        "Bitcoin P2SH-wrapped P2WPKH of the key at --path of a BIP-32 master seed (revealed key)",
        Lock::P2shP2wpkh,
        Source::Bip32,
        "legacy_script_hash",
    ),
    kind(
        "bip32-taproot",
        &[],
        "Bitcoin Taproot output key (no script tree) for the key at --path of a BIP-32 master seed",
        Lock::TaprootKeyPath,
        Source::Bip32,
        "legacy_output_key",
    ),
    kind(
        "bip32-eth",
        &[],
        "Ethereum address of the key at --path of a BIP-32 master seed (revealed key)",
        Lock::Ethereum,
        Source::Bip32,
        "legacy_address",
    ),
    kind(
        "btc-taproot-tree",
        &[],
        "Bitcoin Taproot output key committing to a script tree; --merkle-root is the tree's root (hidden internal key)",
        Lock::TaprootScriptTree,
        Source::Key,
        "legacy_output_key",
    ),
    kind(
        "bip32-taproot-tree",
        &[],
        "Bitcoin Taproot output key with a script tree (--merkle-root) for the key at --path of a BIP-32 master seed",
        Lock::TaprootScriptTree,
        Source::Bip32,
        "legacy_output_key",
    ),
    kind(
        "bip32-ed25519",
        &["cardano-ed25519"],
        "Ed25519 public key at --path of a BIP32-Ed25519 (Khovratovich-Law) extended private key (revealed key)",
        Lock::Ed25519,
        Source::Bip32Ed25519,
        "legacy_public_key",
    ),
    zcash_kind(
        "ironwood",
        &["zip2005", "zcash-ironwood"],
        "Zcash NU7 Ironwood note recovery (ZIP 2005 Recovery Statement, hidden key + spend-auth signature)",
        SecretForm::JsonNote,
        KindFamily::ZcashIronwood,
        "anchor",
    ),
    zcash_kind(
        "orchard",
        &["zcash-orchard", "orchard-address"],
        "Zcash Orchard payment address ownership (hidden spending key, ZIP-32 seed or QSK)",
        SecretForm::Key32,
        KindFamily::ZcashOrchard,
        "legacy_orchard_address",
    ),
    zcash_kind(
        "sapling",
        &["zcash-sapling", "sapling-address"],
        "Zcash Sapling payment address ownership (hidden spending key or ZIP-32 seed)",
        SecretForm::Key32,
        KindFamily::ZcashSapling,
        "legacy_sapling_address",
    ),
    zcash_kind(
        "zcash-transparent",
        &["zip2007-t1", "zcash-t1"],
        "Zcash transparent P2PKH t1/tm address ownership (ZIP 2007 hidden key or BIP-32/BIP-44 seed)",
        SecretForm::Key32,
        KindFamily::ZcashTransparent,
        "legacy_zcash_address",
    ),
];

const KIND_COUNT: usize = 19;

const KINDS: &[&KindSpec] = &{
    let mut out = [&KIND_TABLE[0]; KIND_COUNT];
    let mut i = 0;
    while i < KIND_COUNT {
        out[i] = &KIND_TABLE[i];
        i += 1;
    }
    out
};

// ============================================================================
// Unified statement & witness sum types
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
enum Statement {
    Ownership(OwnershipStatement),
    ZcashIronwood(RecoveryStatement),
    ZcashOrchard(AddressStatement),
    ZcashSapling(SaplingAddressStatement),
    ZcashTransparent(TransparentStatement),
}

enum Witness {
    Ownership(OwnershipWitness),
    ZcashIronwood {
        witness: Box<RecoveryWitness>,
        spend_auth_sig: Option<[u8; 64]>,
    },
    ZcashOrchard(Box<AddressWitness>),
    ZcashSapling(SaplingKeyWitness),
    ZcashTransparent(OwnershipWitness),
}

impl Statement {
    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Self::Ownership(s) => s.to_bytes(),
            Self::ZcashIronwood(s) => s.to_bytes(),
            Self::ZcashOrchard(s) => s.to_bytes(),
            Self::ZcashSapling(s) => s.to_bytes(),
            Self::ZcashTransparent(s) => s.to_bytes(),
        }
    }

    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        OwnershipStatement::from_bytes(bytes)
            .map(Self::Ownership)
            .or_else(|| RecoveryStatement::from_bytes(bytes).map(Self::ZcashIronwood))
            .or_else(|| AddressStatement::from_bytes(bytes).map(Self::ZcashOrchard))
            .or_else(|| SaplingAddressStatement::from_bytes(bytes).map(Self::ZcashSapling))
            .or_else(|| TransparentStatement::from_bytes(bytes).map(Self::ZcashTransparent))
    }

    fn pq_commitment(&self) -> [u8; 32] {
        match self {
            Self::Ownership(s) => s.pq_commitment,
            Self::ZcashIronwood(s) => s.pq_commitment,
            Self::ZcashOrchard(s) => s.pq_commitment,
            Self::ZcashSapling(s) => s.pq_commitment,
            Self::ZcashTransparent(s) => s.ownership.pq_commitment,
        }
    }

    fn epoch(&self) -> u64 {
        match self {
            Self::Ownership(s) => s.epoch,
            Self::ZcashIronwood(s) => s.epoch,
            Self::ZcashOrchard(s) => s.epoch,
            Self::ZcashSapling(s) => s.epoch,
            Self::ZcashTransparent(s) => s.ownership.epoch,
        }
    }

    fn migration_domain(&self) -> [u8; 32] {
        match self {
            Self::Ownership(s) => s.migration_domain,
            Self::ZcashIronwood(s) => s.migration_domain,
            Self::ZcashOrchard(s) => s.migration_domain,
            Self::ZcashSapling(s) => s.migration_domain,
            Self::ZcashTransparent(s) => s.ownership.migration_domain,
        }
    }

    fn nullifier(&self) -> [u8; 32] {
        match self {
            Self::Ownership(s) => s.nullifier,
            Self::ZcashIronwood(s) => s.nullifier,
            Self::ZcashOrchard(s) => s.nullifier(),
            Self::ZcashSapling(s) => s.nullifier(),
            Self::ZcashTransparent(s) => s.ownership.nullifier,
        }
    }

    fn key_is_revealed(&self) -> bool {
        match self {
            Self::Ownership(s) => s.key_is_revealed(),
            Self::ZcashTransparent(s) => s.ownership.key_is_revealed(),
            Self::ZcashIronwood(_) | Self::ZcashOrchard(_) | Self::ZcashSapling(_) => false,
        }
    }

    fn binding(&self) -> Option<MigrationBinding> {
        match self {
            Self::Ownership(s) => Some(s.binding()),
            Self::ZcashIronwood(s) => Some(s.binding()),
            Self::ZcashOrchard(s) => Some(s.binding()),
            Self::ZcashSapling(s) => Some(s.binding()),
            Self::ZcashTransparent(s) => s.binding(),
        }
    }

    fn render_kind_members(&self, kind: &KindSpec) -> Vec<(&'static str, Json)> {
        match self {
            Self::Ownership(s) => kind.render_ownership(s),
            Self::ZcashIronwood(s) => {
                let mut out = vec![
                    ("anchor", Json::hex(&s.anchor)),
                    ("rk", Json::hex(&s.rk)),
                    ("value", Json::num(s.value)),
                ];
                append_orchard_key_source_members(&mut out, &s.key_source);
                out
            }
            Self::ZcashOrchard(s) => {
                let mut out = vec![("legacy_orchard_address", Json::hex(&s.address))];
                append_orchard_key_source_members(&mut out, &s.key_source);
                out
            }
            Self::ZcashSapling(s) => {
                let mut out = vec![("legacy_sapling_address", Json::hex(&s.address))];
                append_sapling_key_source_members(&mut out, &s.key_source);
                out
            }
            Self::ZcashTransparent(s) => {
                let mut out = Vec::new();
                if let Some(addr) = s.address() {
                    out.push(("legacy_zcash_address", Json::str(addr)));
                }
                if let Some(h) = s.hash160() {
                    out.push(("legacy_hash160", Json::hex(&h)));
                }
                out.push((
                    "network",
                    Json::str(match s.network {
                        Network::Main => "main",
                        Network::Test => "test",
                    }),
                ));
                if s.ownership.lock == Lock::P2pkhUncompressed {
                    out.push(("key_encoding", Json::str("uncompressed")));
                }
                append_source_members(&mut out, &s.ownership.source);
                out
            }
        }
    }
}

/// The table entry of a statement; `None` for a combination this command does not offer.
/// Exhaustive over [`Statement`] so any new variant must be wired into [`KINDS`].
fn kind_of(statement: &Statement) -> Option<&'static KindSpec> {
    match statement {
        Statement::Ownership(s) => KINDS.iter().copied().find(|kind| {
            matches!(kind.family, KindFamily::Ownership { lock, .. } if lock == s.lock && kind.offers(&s.source))
        }),
        Statement::ZcashIronwood(_) => KINDS
            .iter()
            .copied()
            .find(|k| k.family == KindFamily::ZcashIronwood),
        Statement::ZcashOrchard(_) => KINDS
            .iter()
            .copied()
            .find(|k| k.family == KindFamily::ZcashOrchard),
        Statement::ZcashSapling(_) => KINDS
            .iter()
            .copied()
            .find(|k| k.family == KindFamily::ZcashSapling),
        Statement::ZcashTransparent(s) => {
            let valid_source = matches!(
                s.ownership.source,
                KeySource::Secp256k1Key | KeySource::Bip32 { .. }
            );
            (s.is_well_formed() && valid_source)
                .then(|| {
                    KINDS
                        .iter()
                        .copied()
                        .find(|k| k.family == KindFamily::ZcashTransparent)
                })
                .flatten()
        }
    }
}

fn kind_by_name(name: &str) -> Result<&'static KindSpec, CliError> {
    KINDS
        .iter()
        .copied()
        .find(|kind| kind.name == name || kind.aliases.contains(&name))
        .ok_or_else(|| {
            let names: Vec<_> = KINDS.iter().map(|kind| kind.name).collect();
            CliError::usage(format!(
                "unsupported --kind '{name}' (expected one of: {})",
                names.join(", ")
            ))
        })
}

fn kinds_help() -> String {
    let mut out = String::new();
    for kind in KINDS {
        out.push_str(&format!("  {:<18} {}\n", kind.name, kind.summary));
        if !kind.aliases.is_empty() {
            out.push_str(&format!(
                "  {:<18} aliases: {}\n",
                "",
                kind.aliases.join(", ")
            ));
        }
    }
    out
}

/// The `migration` entry of `qsag info --json`.
pub fn info() -> Json {
    Json::object(vec![
        (
            "proof_system",
            Json::str(
                "zk-Hem v2 ownership relations over QuinticGoldilocks (400-bit digests, 256-bit salts, DKT26 soundness; see crates/qsag-migrate/SECURITY.md)",
            ),
        ),
        ("regime", Json::str(REGIME_NAME)),
        ("claim_format", Json::str(CLAIM_FORMAT)),
        ("proof_format", Json::str(PROOF_FORMAT)),
        ("registry_format", Json::str(REGISTRY_FORMAT)),
        (
            "statement_kinds",
            Json::Array(
                KINDS
                    .iter()
                    .map(|kind| {
                        Json::object(vec![
                            ("kind", Json::str(kind.name)),
                            (
                                "aliases",
                                Json::Array(kind.aliases.iter().map(|a| Json::str(*a)).collect()),
                            ),
                            ("statement", Json::str(kind.summary)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

/// The migration line of `qsag info`.
pub fn info_text() -> String {
    let names: Vec<_> = KINDS.iter().map(|kind| kind.name).collect();
    format!(
        "migration: zk-Hem v2 ownership proofs ({REGIME_NAME}) for {}; one-way registry\n",
        names.join(", ")
    )
}

fn kind_names() -> String {
    let names: Vec<_> = KINDS.iter().map(|kind| kind.name).collect();
    names.join("|")
}

/// `m/44'/0'/0'/0/0`: `'`, `h` or `H` marks a hardened index.
fn parse_path(text: &str) -> Result<Vec<u32>, CliError> {
    let bad = || {
        CliError::usage(format!(
            "--path '{text}' is not a BIP-32 path such as m/44'/0'/0'/0/0"
        ))
    };
    let mut parts = text.split('/');
    if parts.next() != Some("m") {
        return Err(bad());
    }
    let mut path = Vec::new();
    for part in parts {
        let (digits, hardened) = match part.strip_suffix(['\'', 'h', 'H']) {
            Some(digits) => (digits, BIP32_HARDENED),
            None => (part, 0),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(bad());
        }
        let index: u32 = digits.parse().map_err(|_| bad())?;
        if index >= BIP32_HARDENED {
            return Err(bad());
        }
        path.push(index | hardened);
    }
    if path.len() > MAX_BIP32_DEPTH {
        return Err(CliError::usage(format!(
            "--path has {} levels; at most {MAX_BIP32_DEPTH} are supported",
            path.len()
        )));
    }
    Ok(path)
}

fn format_path(path: &[u32]) -> String {
    let mut out = String::from("m");
    for &index in path {
        out.push('/');
        out.push_str(&(index & !BIP32_HARDENED).to_string());
        if index & BIP32_HARDENED != 0 {
            out.push('\'');
        }
    }
    out
}

// ============================================================================
// Legacy secrets
// ============================================================================

fn reject_sealed_legacy_key(json: &Json) -> Result<(), CliError> {
    if [
        "envelope",
        "salt",
        "envelope_tag",
        "envelope_salt",
        "envelope_nonce",
    ]
    .iter()
    .any(|key| json.get(key).is_some())
    {
        return Err(CliError::input(
            "sealed legacy keys are not supported by migrate; decrypt the key through an authenticated envelope reader before migration",
        ));
    }
    Ok(())
}

fn json_legacy_seed(json: &Json) -> Result<ZeroizingBuf, CliError> {
    reject_sealed_legacy_key(json)?;
    json.field_hex("seed")
}

/// `private key || chain code` of a BIP-32 serialized extended private key (`xprv` for
/// mainnet, `tprv` for testnet): Base58Check of
/// `version(4) depth(1) fingerprint(4) child(4) chain code(32) 0x00 key(32)`.
fn parse_extended_private_key(text: &str) -> Result<ZeroizingBuf, CliError> {
    const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let bad = |why: &str| CliError::input(format!("extended private key: {why}"));
    let mut number = ZeroizingBuf::new(vec![0u8; 82]);
    for c in text.bytes() {
        let digit = ALPHABET
            .iter()
            .position(|&a| a == c)
            .ok_or_else(|| bad("not Base58"))?;
        let mut carry = digit as u32;
        for byte in number.0.iter_mut() {
            carry += u32::from(*byte) * 58;
            *byte = carry as u8;
            carry >>= 8;
        }
        if carry != 0 {
            return Err(bad("too long"));
        }
    }
    number.0.reverse();
    let (payload, checksum) = number.0.split_at(78);
    let digest = qsag_accel::sha2::sha256(&qsag_accel::sha2::sha256(payload));
    if digest[..4] != *checksum {
        return Err(bad("checksum mismatch"));
    }
    if text.len() != 111 {
        return Err(bad("not a 78-byte BIP-32 serialization"));
    }
    if !matches!(
        payload[..4],
        [0x04, 0x88, 0xAD, 0xE4] | [0x04, 0x35, 0x83, 0x94]
    ) {
        return Err(bad("not an xprv or tprv version"));
    }
    if payload[45] != 0 {
        return Err(bad("the key field does not hold a private key"));
    }
    let mut out = ZeroizingBuf::new(vec![0u8; 64]);
    out.0[..32].copy_from_slice(&payload[46..78]);
    out.0[32..].copy_from_slice(&payload[13..45]);
    Ok(out)
}

/// Read the secret of a statement kind. The bytes stay in a wiping buffer.
fn read_legacy_secret(path: &str, form: SecretForm) -> Result<ZeroizingBuf, CliError> {
    let raw = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    let text = std::str::from_utf8(&raw.0).ok().map(str::trim);
    let hex = text
        .map(|text| text.strip_prefix("0x").unwrap_or(text))
        .filter(|hex| !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()));
    let secret = match (text, hex) {
        (Some(text), _) if text.starts_with('{') => json_legacy_seed(&Json::parse(text)?)?,
        (_, Some(hex)) => from_hex(hex)?,
        _ if form == SecretForm::Key32 && raw.0.len() == 32 => raw,
        (Some(text), _)
            if form == SecretForm::ExtendedKey
                && text.ends_with(|c: char| c.is_ascii_alphanumeric())
                && text.get(1..4) == Some("prv") =>
        {
            parse_extended_private_key(text)?
        }
        _ => {
            return Err(CliError::input(format!(
                "{path} must be hex or a JSON secret file{}",
                if form == SecretForm::Key32 {
                    ", or 32 raw bytes"
                } else {
                    ""
                }
            )));
        }
    };
    let accepted = match form {
        SecretForm::Key32 => secret.0.len() == 32,
        SecretForm::HexSeed => BIP32_SEED_BYTES.contains(&secret.0.len()),
        SecretForm::Zip32Seed => ZIP32_SEED_BYTES.contains(&secret.0.len()),
        SecretForm::ExtendedKey => secret.0.len() == 64,
        SecretForm::Ed25519ExtendedKey => secret.0.len() == 96,
        SecretForm::JsonNote => false,
    };
    if !accepted {
        return Err(CliError::input(match form {
            SecretForm::Key32 => format!("legacy secret must be 32 bytes (got {})", secret.0.len()),
            SecretForm::ExtendedKey => format!(
                "extended private key must be an xprv/tprv string or 64 bytes, private key then chain code (got {})",
                secret.0.len()
            ),
            SecretForm::Ed25519ExtendedKey => format!(
                "BIP32-Ed25519 extended private key must be 96 bytes, k_L || k_R || chain code (got {})",
                secret.0.len()
            ),
            SecretForm::HexSeed => format!(
                "BIP-32 seed must be {} to {} bytes (got {})",
                BIP32_SEED_BYTES.start(),
                BIP32_SEED_BYTES.end(),
                secret.0.len()
            ),
            SecretForm::Zip32Seed => format!(
                "ZIP-32 seed must be {} to {} bytes (got {})",
                ZIP32_SEED_BYTES.start(),
                ZIP32_SEED_BYTES.end(),
                secret.0.len()
            ),
            SecretForm::JsonNote => "Ironwood recovery expects a JSON witness file".into(),
        }));
    }
    Ok(secret)
}

// ============================================================================
// Statements
// ============================================================================

fn default_migration_domain() -> [u8; 32] {
    cshake256_framed_32(DEFAULT_DOMAIN_LABEL, &[b"qsag-mainnet-migration-v1"])
}

fn parse_domain(args: &Args) -> Result<[u8; 32], CliError> {
    match args.get("domain-hex") {
        Some(hex) => from_hex_exact::<32>(hex, "--domain-hex"),
        None => Ok(default_migration_domain()),
    }
}

fn required_epoch(args: &Args) -> Result<u64, CliError> {
    args.get_u64("epoch")?
        .ok_or_else(|| CliError::usage("missing required option --epoch"))
}

/// A target address and its canonical text.
fn parse_target(text: &str) -> Result<(QsagAddress, String), CliError> {
    let address = QsagAddress::decode(text)
        .map_err(|e| CliError::usage(format!("invalid --target address: {e:?}")))?;
    let canonical = address
        .encode()
        .map_err(|e| CliError::usage(format!("invalid --target address: {e:?}")))?;
    Ok((address, canonical))
}

/// The members a statement renders to, in file order. `target` is the canonical text of
/// the address `statement.pq_commitment()` commits to.
fn statement_members(
    statement: &Statement,
    target: &str,
) -> Result<Vec<(&'static str, Json)>, String> {
    let binding = statement
        .binding()
        .ok_or_else(|| String::from("statement has no canonical registry binding"))?;
    let mut members = vec![("kind", Json::str(kind_name(statement)))];
    if let Some(kind) = kind_of(statement) {
        members.extend(statement.render_kind_members(kind));
    }
    members.extend([
        (
            "key_exposure",
            Json::str(if statement.key_is_revealed() {
                "revealed"
            } else {
                "hidden"
            }),
        ),
        ("target_pq_address", Json::str(target)),
        ("pq_commitment", Json::hex(&statement.pq_commitment())),
        ("epoch", Json::num(statement.epoch())),
        ("migration_domain", Json::hex(&statement.migration_domain())),
        ("nullifier", Json::hex(&statement.nullifier())),
        ("legacy_id", Json::hex(&binding.legacy_id)),
        ("statement", Json::hex(&statement.to_bytes())),
    ]);
    Ok(members)
}

fn document(format: &str, mut members: Vec<(&'static str, Json)>) -> Json {
    members.insert(0, ("format", Json::str(format)));
    Json::object(members)
}

/// A statement read back from a claim or proof document.
struct LoadedStatement {
    statement: Statement,
    target: QsagAddress,
    target_text: String,
}

/// Decode the statement of a claim or proof document and check that the document says
/// nothing else: the target address must be the one the statement commits to, every
/// rendered member must equal its rendering, and no other member may be present beyond
/// `extra`.
fn load_statement(json: &Json, format: &str, extra: &[&str]) -> Result<LoadedStatement, String> {
    let Json::Object(members) = json else {
        return Err("not a JSON object".into());
    };
    let field = |name: &str| {
        json.get(name)
            .and_then(Json::as_str)
            .ok_or_else(|| format!("missing or non-string member \"{name}\""))
    };
    if field("format")? != format {
        return Err(format!("not a {format} file"));
    }
    let bytes = from_hex(field("statement")?).map_err(|e| e.message)?;
    let statement = Statement::from_bytes(&bytes.0)
        .ok_or("statement is not a canonical migration statement")?;
    if kind_of(&statement).is_none() {
        return Err("statement is of a kind this command does not offer".into());
    }
    let target_text = field("target_pq_address")?.to_owned();
    let target = QsagAddress::decode(&target_text)
        .map_err(|e| format!("invalid target_pq_address: {e:?}"))?;
    if target.encode().ok().as_deref() != Some(target_text.as_str()) {
        return Err("target_pq_address is not in canonical form".into());
    }
    if pq_commitment(&target) != statement.pq_commitment() {
        return Err("target_pq_address is not the address the statement commits to".into());
    }
    let rendered = statement_members(&statement, &target_text)?;
    for (name, value) in &rendered {
        if json.get(name) != Some(value) {
            return Err(format!("member \"{name}\" does not match the statement"));
        }
    }
    for (name, _) in members {
        let known = name == "format"
            || extra.contains(&name.as_str())
            || rendered.iter().any(|(rendered, _)| rendered == name);
        if !known {
            return Err(format!("unexpected member \"{name}\""));
        }
    }
    if members.len() != 1 + rendered.len() + extra.len() {
        return Err("missing or repeated member".into());
    }
    Ok(LoadedStatement {
        statement,
        target,
        target_text,
    })
}

const STATEMENT_OPTIONS: &[&str] = &[
    "kind",
    "legacy-secret",
    "path",
    "root",
    "hidden-path-depth",
    "merkle-root",
    "target",
    "epoch",
    "domain-hex",
    "out",
    "network",
    "account",
    "coin-type",
    "diversifier",
    "diversifier-index",
    "spend-auth-sig",
];

const ZCASH_ONLY_OPTIONS: &[&str] = &[
    "network",
    "account",
    "coin-type",
    "diversifier",
    "diversifier-index",
    "spend-auth-sig",
];

fn parse_network(args: &Args) -> Result<Network, CliError> {
    match args.get("network") {
        None | Some("main") | Some("mainnet") => Ok(Network::Main),
        Some("test") | Some("testnet") => Ok(Network::Test),
        Some(other) => Err(CliError::usage(format!(
            "--network '{other}' is not 'main' or 'test'"
        ))),
    }
}

fn parse_u32_option(args: &Args, name: &str) -> Result<Option<u32>, CliError> {
    args.get(name)
        .map(|s| {
            s.parse::<u32>()
                .map_err(|_| CliError::usage(format!("--{name} must be a 32-bit unsigned integer")))
        })
        .transpose()
}

fn orchard_fvk(
    source: &OrchardKeySource,
    witness: &OrchardKeyWitness,
) -> Option<OrchardFullViewingKey> {
    match (source, witness) {
        (OrchardKeySource::SpendingKey, OrchardKeyWitness::SpendingKey(sk)) => {
            OrchardFullViewingKey::from_spending_key(sk)
        }
        (
            OrchardKeySource::Zip32Seed {
                seed_len,
                coin_type,
                account,
            },
            OrchardKeyWitness::Zip32Seed(seed),
        ) => {
            if !source.is_well_formed() || seed.len() != usize::from(*seed_len) {
                return None;
            }
            let path = [
                ZIP32_PURPOSE | ZIP32_HARDENED,
                *coin_type | ZIP32_HARDENED,
                *account | ZIP32_HARDENED,
            ];
            let mut sk = orchard::zip32_spending_key(seed, &path)?;
            let fvk = OrchardFullViewingKey::from_spending_key(&sk);
            qsag_asm::volatile_fill(&mut sk, 0);
            fvk
        }
        (
            OrchardKeySource::QuantumSpendingKey,
            OrchardKeyWitness::QuantumSpendingKey { qsk, ak, nk },
        ) => {
            let ak_pt = PallasPoint::from_bytes_nonidentity(ak)?;
            let nk_fp = PallasFp::from_bytes(nk)?;
            let ak_fp = ak_pt.extract();
            let fvk = OrchardFullViewingKey {
                ak: ak_fp,
                nk: nk_fp,
                rivk: orchard::h_rivk_ext(&orchard::h_qk(qsk), &ak_fp, &nk_fp),
            };
            (fvk.ivk(OrchardScope::External).is_some() && fvk.ivk(OrchardScope::Internal).is_some())
                .then_some(fvk)
        }
        _ => None,
    }
}

fn parse_orchard_cli_key(
    args: &Args,
    secret_path: &str,
    default_coin: u32,
) -> Result<(OrchardKeySource, OrchardKeyWitness, ZeroizingBuf), CliError> {
    match args.get("root") {
        None | Some("spending-key") => {
            if args.get("account").is_some() || args.get("coin-type").is_some() {
                return Err(CliError::usage(
                    "--account and --coin-type require --root seed",
                ));
            }
            let secret = read_legacy_secret(secret_path, SecretForm::Key32)?;
            let sk: [u8; 32] = secret.0.as_slice().try_into().expect("32 bytes");
            Ok((
                OrchardKeySource::SpendingKey,
                OrchardKeyWitness::SpendingKey(sk),
                secret,
            ))
        }
        Some("seed") => {
            let secret = read_legacy_secret(secret_path, SecretForm::Zip32Seed)?;
            let coin_type = parse_u32_option(args, "coin-type")?.unwrap_or(default_coin);
            let account = parse_u32_option(args, "account")?.unwrap_or(0);
            let source = OrchardKeySource::Zip32Seed {
                seed_len: u8::try_from(secret.0.len()).expect("32..=252"),
                coin_type,
                account,
            };
            if !source.is_well_formed() {
                return Err(CliError::usage(
                    "--coin-type and --account must be below 2^31",
                ));
            }
            Ok((
                source,
                OrchardKeyWitness::Zip32Seed(secret.0.clone()),
                secret,
            ))
        }
        Some("qsk") => {
            if args.get("account").is_some() || args.get("coin-type").is_some() {
                return Err(CliError::usage(
                    "--account and --coin-type do not apply to --root qsk",
                ));
            }
            let raw = read_bounded_file(secret_path, MAX_KEY_FILE_BYTES)?;
            let text = std::str::from_utf8(&raw.0)
                .map_err(|_| CliError::input("QSK witness file must be UTF-8 JSON"))?;
            let json = Json::parse(text)?;
            reject_sealed_legacy_key(&json)?;
            let qsk_buf = json.field_hex("qsk")?;
            let qsk: [u8; 32] = qsk_buf
                .0
                .as_slice()
                .try_into()
                .map_err(|_| CliError::input("qsk must be 32 bytes of hex"))?;
            let ak = from_hex_exact::<32>(json.field_str("ak")?, "ak")?;
            let nk = from_hex_exact::<32>(json.field_str("nk")?, "nk")?;
            Ok((
                OrchardKeySource::QuantumSpendingKey,
                OrchardKeyWitness::QuantumSpendingKey { qsk, ak, nk },
                qsk_buf,
            ))
        }
        Some(other) => Err(CliError::usage(format!(
            "--root '{other}' is not 'spending-key', 'seed', or 'qsk'"
        ))),
    }
}

fn reject_options(args: &Args, kind_name: &str, disallowed: &[&str]) -> Result<(), CliError> {
    for &opt in disallowed {
        if args.get(opt).is_some() {
            return Err(CliError::usage(format!(
                "--{opt} does not apply to --kind {kind_name}"
            )));
        }
    }
    Ok(())
}

fn derive_zcash(
    kind: &'static KindSpec,
    args: &Args,
) -> Result<(LoadedStatement, Witness, ZeroizingBuf), CliError> {
    let secret_path = args.require("legacy-secret")?;
    let (target, target_text) = parse_target(args.require("target")?)?;
    let epoch = required_epoch(args)?;
    let domain = parse_domain(args)?;
    let pq = pq_commitment(&target);

    match kind.family {
        KindFamily::ZcashOrchard => {
            reject_options(
                args,
                kind.name,
                &["path", "hidden-path-depth", "merkle-root", "spend-auth-sig"],
            )?;
            if args.flag("uncompressed") {
                return Err(CliError::usage(
                    "--uncompressed does not apply to --kind orchard",
                ));
            }
            let network = parse_network(args)?;
            let (key_source, key_witness, secret) =
                parse_orchard_cli_key(args, secret_path, zcash_coin_type(network))?;
            let internal = args.flag("internal");
            let scope = if internal {
                OrchardScope::Internal
            } else {
                OrchardScope::External
            };
            let d: [u8; 11] =
                match (args.get("diversifier"), args.get_u64("diversifier-index")?) {
                    (Some(_), Some(_)) => {
                        return Err(CliError::usage(
                            "cannot combine --diversifier and --diversifier-index",
                        ));
                    }
                    (Some(hex), None) => from_hex_exact::<11>(hex, "--diversifier")?,
                    (None, idx_opt) => {
                        let fvk = orchard_fvk(&key_source, &key_witness).ok_or_else(|| {
                            CliError::input("legacy secret is not a valid Orchard key")
                        })?;
                        let mut j = [0u8; 11];
                        j[..8].copy_from_slice(&idx_opt.unwrap_or(0).to_le_bytes());
                        fvk.diversifier(&j, scope)
                    }
                };
            let witness = AddressWitness {
                key: key_witness,
                internal,
            };
            let stmt = AddressStatement::derive(&key_source, &witness, &d, pq, domain, epoch)
                .ok_or_else(|| {
                    CliError::input("legacy secret does not derive a valid Orchard address")
                })?;
            Ok((
                LoadedStatement {
                    statement: Statement::ZcashOrchard(stmt),
                    target,
                    target_text,
                },
                Witness::ZcashOrchard(Box::new(witness)),
                secret,
            ))
        }
        KindFamily::ZcashSapling => {
            reject_options(
                args,
                kind.name,
                &["path", "hidden-path-depth", "merkle-root", "spend-auth-sig"],
            )?;
            if args.flag("internal") || args.flag("uncompressed") {
                return Err(CliError::usage(
                    "--internal and --uncompressed do not apply to --kind sapling",
                ));
            }
            let network = parse_network(args)?;
            let default_coin = zcash_coin_type(network);
            let (key_source, key_witness, d, secret) = match args.get("root") {
                None | Some("spending-key") => {
                    if args.get("account").is_some()
                        || args.get("coin-type").is_some()
                        || args.get("diversifier-index").is_some()
                    {
                        return Err(CliError::usage(
                            "--account, --coin-type, and --diversifier-index require --root seed for --kind sapling",
                        ));
                    }
                    let secret = read_legacy_secret(secret_path, SecretForm::Key32)?;
                    let sk: [u8; 32] = secret.0.as_slice().try_into().expect("32 bytes");
                    let d = match args.get("diversifier") {
                        Some(hex) => from_hex_exact::<11>(hex, "--diversifier")?,
                        None => sapling::default_diversifier(&sk),
                    };
                    (
                        SaplingKeySource::SpendingKey,
                        SaplingKeyWitness::SpendingKey(sk),
                        d,
                        secret,
                    )
                }
                Some("seed") => {
                    let secret = read_legacy_secret(secret_path, SecretForm::Zip32Seed)?;
                    let coin_type = parse_u32_option(args, "coin-type")?.unwrap_or(default_coin);
                    let account = parse_u32_option(args, "account")?.unwrap_or(0);
                    let source = SaplingKeySource::Zip32Seed {
                        seed_len: u8::try_from(secret.0.len()).expect("32..=252"),
                        coin_type,
                        account,
                    };
                    if !source.is_well_formed() {
                        return Err(CliError::usage(
                            "--coin-type and --account must be below 2^31",
                        ));
                    }
                    let d = match (args.get("diversifier"), args.get_u64("diversifier-index")?) {
                        (Some(_), Some(_)) => {
                            return Err(CliError::usage(
                                "cannot combine --diversifier and --diversifier-index",
                            ));
                        }
                        (Some(hex), None) => from_hex_exact::<11>(hex, "--diversifier")?,
                        (None, idx_opt) => {
                            let extsk = SaplingExtendedSpendingKey::derive(
                                &secret.0,
                                &[
                                    32 | ZIP32_HARDENED,
                                    coin_type | ZIP32_HARDENED,
                                    account | ZIP32_HARDENED,
                                ],
                            )
                            .ok_or_else(|| {
                                CliError::input("seed does not derive a valid Sapling account key")
                            })?;
                            let efvk = extsk.to_extended_fvk();
                            match idx_opt {
                                Some(idx) => {
                                    let mut j = [0u8; 11];
                                    j[..8].copy_from_slice(&idx.to_le_bytes());
                                    efvk.diversifier(&j).ok_or_else(|| {
                                        CliError::input(format!(
                                            "diversifier index {idx} has no valid Sapling diversifier"
                                        ))
                                    })?
                                }
                                None => efvk.default_diversifier().1,
                            }
                        }
                    };
                    (
                        source,
                        SaplingKeyWitness::Zip32Seed(secret.0.clone()),
                        d,
                        secret,
                    )
                }
                Some(other) => {
                    return Err(CliError::usage(format!(
                        "--root '{other}' is not 'spending-key' or 'seed' for --kind sapling"
                    )));
                }
            };
            let stmt =
                SaplingAddressStatement::derive(&key_source, &key_witness, &d, pq, domain, epoch)
                    .ok_or_else(|| {
                    CliError::input(
                        "legacy secret or diversifier does not produce a valid Sapling address",
                    )
                })?;
            Ok((
                LoadedStatement {
                    statement: Statement::ZcashSapling(stmt),
                    target,
                    target_text,
                },
                Witness::ZcashSapling(key_witness),
                secret,
            ))
        }
        KindFamily::ZcashIronwood => {
            reject_options(
                args,
                kind.name,
                &["path", "hidden-path-depth", "merkle-root", "diversifier"],
            )?;
            if args.flag("uncompressed") {
                return Err(CliError::usage(
                    "--uncompressed does not apply to --kind ironwood",
                ));
            }
            let network = parse_network(args)?;
            let default_coin = zcash_coin_type(network);
            let raw = read_bounded_file(secret_path, MAX_KEY_FILE_BYTES)?;
            let text = std::str::from_utf8(&raw.0)
                .map_err(|_| CliError::input("Ironwood witness file must be UTF-8 JSON"))?;
            let json = Json::parse(text)?;
            reject_sealed_legacy_key(&json)?;

            let (key_source, key_witness, secret) = match args.get("root") {
                None | Some("spending-key") => {
                    if args.get("account").is_some() || args.get("coin-type").is_some() {
                        return Err(CliError::usage(
                            "--account and --coin-type require --root seed",
                        ));
                    }
                    let sk_buf = if json.get("spending_key").is_some() {
                        json.field_hex("spending_key")?
                    } else {
                        json.field_hex("seed")?
                    };
                    let sk: [u8; 32] = sk_buf.0.as_slice().try_into().map_err(|_| {
                        CliError::input("spending_key must be 32 bytes of hex")
                    })?;
                    (
                        OrchardKeySource::SpendingKey,
                        OrchardKeyWitness::SpendingKey(sk),
                        sk_buf,
                    )
                }
                Some("seed") => {
                    let seed_buf = json.field_hex("seed")?;
                    if !ZIP32_SEED_BYTES.contains(&seed_buf.0.len()) {
                        return Err(CliError::input(format!(
                            "ZIP-32 seed must be {} to {} bytes (got {})",
                            ZIP32_SEED_BYTES.start(),
                            ZIP32_SEED_BYTES.end(),
                            seed_buf.0.len()
                        )));
                    }
                    let coin_type = match parse_u32_option(args, "coin-type")? {
                        Some(v) => v,
                        None => json
                            .get("coin_type")
                            .and_then(Json::as_u64)
                            .and_then(|v| u32::try_from(v).ok())
                            .unwrap_or(default_coin),
                    };
                    let account = match parse_u32_option(args, "account")? {
                        Some(v) => v,
                        None => json
                            .get("account")
                            .and_then(Json::as_u64)
                            .and_then(|v| u32::try_from(v).ok())
                            .unwrap_or(0),
                    };
                    let source = OrchardKeySource::Zip32Seed {
                        seed_len: u8::try_from(seed_buf.0.len()).expect("32..=252"),
                        coin_type,
                        account,
                    };
                    if !source.is_well_formed() {
                        return Err(CliError::usage(
                            "--coin-type and --account must be below 2^31",
                        ));
                    }
                    (
                        source,
                        OrchardKeyWitness::Zip32Seed(seed_buf.0.clone()),
                        seed_buf,
                    )
                }
                Some("qsk") => {
                    let qsk_buf = json.field_hex("qsk")?;
                    let qsk: [u8; 32] = qsk_buf
                        .0
                        .as_slice()
                        .try_into()
                        .map_err(|_| CliError::input("qsk must be 32 bytes of hex"))?;
                    let ak = from_hex_exact::<32>(json.field_str("ak")?, "ak")?;
                    let nk = from_hex_exact::<32>(json.field_str("nk")?, "nk")?;
                    (
                        OrchardKeySource::QuantumSpendingKey,
                        OrchardKeyWitness::QuantumSpendingKey { qsk, ak, nk },
                        qsk_buf,
                    )
                }
                Some(other) => {
                    return Err(CliError::usage(format!(
                        "--root '{other}' is not 'spending-key', 'seed', or 'qsk'"
                    )));
                }
            };

            let internal = args.flag("internal")
                || json.get("internal").and_then(Json::as_bool).unwrap_or(false);
            let alpha = from_hex_exact::<32>(json.field_str("alpha")?, "alpha")?;
            let value = json.field_u64("value")?;
            let rho_bytes = from_hex_exact::<32>(json.field_str("rho")?, "rho")?;
            let rho = PallasFp::from_bytes(&rho_bytes).ok_or_else(|| {
                CliError::input("rho is not a canonical Pallas base-field element")
            })?;
            let rseed = from_hex_exact::<32>(json.field_str("rseed")?, "rseed")?;
            let recipient: [u8; 43] = if json.get("recipient").is_some() {
                from_hex_exact::<43>(json.field_str("recipient")?, "recipient")?
            } else {
                let fvk = orchard_fvk(&key_source, &key_witness)
                    .ok_or_else(|| CliError::input("invalid Orchard key in Ironwood witness"))?;
                let scope = if internal {
                    OrchardScope::Internal
                } else {
                    OrchardScope::External
                };
                let idx = match args.get_u64("diversifier-index")? {
                    Some(i) => i,
                    None => json
                        .get("diversifier_index")
                        .and_then(Json::as_u64)
                        .unwrap_or(0),
                };
                let mut j = [0u8; 11];
                j[..8].copy_from_slice(&idx.to_le_bytes());
                let d = fvk.diversifier(&j, scope);
                fvk.address(&d, scope).ok_or_else(|| {
                    CliError::input("could not derive Ironwood recipient address")
                })?
            };
            let note = OrchardNote {
                recipient,
                value,
                rho,
                rseed,
                version: NoteVersion::V3,
            };
            let position = u32::try_from(
                json.get("position")
                    .and_then(Json::as_u64)
                    .unwrap_or(0),
            )
            .map_err(|_| CliError::input("position exceeds u32::MAX"))?;

            let path: [[u8; 32]; rehash::DEPTH] = if let Some(arr) =
                json.get("merkle_path").and_then(Json::as_array)
            {
                if arr.len() != rehash::DEPTH {
                    return Err(CliError::input(format!(
                        "merkle_path must have {} siblings (got {})",
                        rehash::DEPTH,
                        arr.len()
                    )));
                }
                let mut siblings = [[0u8; 32]; rehash::DEPTH];
                for (slot, item) in siblings.iter_mut().zip(arr) {
                    let hex = item
                        .as_str()
                        .ok_or_else(|| CliError::input("merkle_path entries must be hex strings"))?;
                    *slot = from_hex_exact::<32>(hex, "merkle_path sibling")?;
                }
                siblings
            } else if let Some(arr) = json.get("leaves").and_then(Json::as_array) {
                let mut leaves = Vec::with_capacity(arr.len());
                for item in arr {
                    let hex = item
                        .as_str()
                        .ok_or_else(|| CliError::input("leaves entries must be 64-hex strings"))?;
                    leaves.push(from_hex_exact::<32>(hex, "leaf")?);
                }
                rehash::witness(&leaves, position)
                    .ok_or_else(|| CliError::input("position out of range for leaves"))?
                    .0
            } else if position == 0 {
                let cmx = note
                    .cmx()
                    .ok_or_else(|| CliError::input("note commitment is invalid"))?
                    .to_bytes();
                let leaf = rehash::leaf_hash(&cmx, &rho_bytes);
                rehash::witness(&[leaf], 0).expect("single leaf").0
            } else {
                return Err(CliError::input(
                    "Ironwood witness with position > 0 requires merkle_path or leaves",
                ));
            };

            let spend_auth_sig = match args.get("spend-auth-sig") {
                Some(hex) => Some(from_hex_exact::<64>(hex, "--spend-auth-sig")?),
                None => match json.get("spend_auth_sig").and_then(Json::as_str) {
                    Some(hex) => Some(from_hex_exact::<64>(hex, "spend_auth_sig")?),
                    None => None,
                },
            };

            let rec_witness = RecoveryWitness {
                key: key_witness,
                internal,
                alpha,
                note,
                position,
                path,
            };
            let stmt = RecoveryStatement::derive(&key_source, &rec_witness, pq, domain, epoch)
                .ok_or_else(|| {
                    CliError::input("Ironwood witness does not satisfy the ZIP 2005 note relation")
                })?;
            Ok((
                LoadedStatement {
                    statement: Statement::ZcashIronwood(stmt),
                    target,
                    target_text,
                },
                Witness::ZcashIronwood {
                    witness: Box::new(rec_witness),
                    spend_auth_sig,
                },
                secret,
            ))
        }
        KindFamily::ZcashTransparent => {
            reject_options(
                args,
                kind.name,
                &[
                    "merkle-root",
                    "coin-type",
                    "diversifier",
                    "diversifier-index",
                    "spend-auth-sig",
                ],
            )?;
            if args.flag("internal") {
                return Err(CliError::usage(
                    "--internal does not apply to --kind zcash-transparent",
                ));
            }
            let network = parse_network(args)?;
            let encoding = if args.flag("uncompressed") {
                KeyEncoding::Uncompressed
            } else {
                KeyEncoding::Compressed
            };
            let is_bip32 = args.get("root").is_some()
                || args.get("path").is_some()
                || args.get("hidden-path-depth").is_some()
                || args.get("account").is_some();

            if !is_bip32 {
                let secret = read_legacy_secret(secret_path, SecretForm::Key32)?;
                let key: [u8; 32] = secret.0.as_slice().try_into().expect("32 bytes");
                let witness = OwnershipWitness::secp256k1_key(&key);
                let stmt =
                    TransparentStatement::derive_hidden(network, encoding, &witness, pq, domain, epoch)
                        .ok_or_else(|| {
                            CliError::input(
                                "legacy secret is not a valid secp256k1 key (must be in 1..n)",
                            )
                        })?;
                return Ok((
                    LoadedStatement {
                        statement: Statement::ZcashTransparent(stmt),
                        target,
                        target_text,
                    },
                    Witness::ZcashTransparent(witness),
                    secret,
                ));
            }

            let extended_root = match args.get("root") {
                None | Some("seed") => false,
                Some("extended-key") => true,
                Some(other) => {
                    return Err(CliError::usage(format!(
                        "--root '{other}' is not 'seed' or 'extended-key'"
                    )));
                }
            };
            if args.get("path").is_some() && args.get("account").is_some() {
                return Err(CliError::usage(
                    "cannot combine --path and --account for --kind zcash-transparent",
                ));
            }
            let path = match args.get("path") {
                Some(p) => parse_path(p)?,
                None if !extended_root => {
                    let account = parse_u32_option(args, "account")?.unwrap_or(0);
                    bip44_path(network, account, 0, 0).ok_or_else(|| {
                        CliError::usage("--account must be below 2^31")
                    })?
                }
                None => {
                    return Err(CliError::usage(
                        "--root extended-key requires --path for --kind zcash-transparent",
                    ));
                }
            };
            let hidden_depth = match args.get("hidden-path-depth") {
                None => None,
                Some(text) => Some(
                    text.parse::<u8>()
                        .ok()
                        .filter(|d| (1..=MAX_BIP32_DEPTH).contains(&usize::from(*d)))
                        .ok_or_else(|| {
                            CliError::usage(format!(
                                "--hidden-path-depth must be 1 to {MAX_BIP32_DEPTH}"
                            ))
                        })?,
                ),
            };
            if hidden_depth.is_some_and(|d| path.len() > usize::from(d)) {
                return Err(CliError::usage(
                    "--path is longer than --hidden-path-depth allows",
                ));
            }
            let form = if extended_root {
                SecretForm::ExtendedKey
            } else {
                SecretForm::HexSeed
            };
            let secret = read_legacy_secret(secret_path, form)?;
            let mut witness = if extended_root {
                OwnershipWitness::extended_key(&HdNode {
                    private_key: secret.0[..32].try_into().expect("32 bytes"),
                    chain_code: secret.0[32..].try_into().expect("32 bytes"),
                })
            } else {
                OwnershipWitness::seed(&secret.0)
            };
            let spec = match hidden_depth {
                Some(max_depth) => {
                    witness = witness.with_path(&path);
                    PathSpec::Hidden { max_depth }
                }
                None => PathSpec::Public(path),
            };
            let source = KeySource::Bip32 {
                root: if extended_root {
                    Bip32Root::ExtendedKey
                } else {
                    Bip32Root::Seed
                },
                path: spec,
            };
            let stmt =
                TransparentStatement::derive(network, encoding, source, &witness, pq, domain, epoch)
                    .ok_or_else(|| {
                        CliError::input(
                            "legacy secret does not derive a valid Zcash transparent address",
                        )
                    })?;
            Ok((
                LoadedStatement {
                    statement: Statement::ZcashTransparent(stmt),
                    target,
                    target_text,
                },
                Witness::ZcashTransparent(witness),
                secret,
            ))
        }
        KindFamily::Ownership { .. } => unreachable!("handled by derive()"),
    }
}

/// The statement and witness the options describe.
fn derive(args: &Args) -> Result<(LoadedStatement, Witness, ZeroizingBuf), CliError> {
    let kind = kind_by_name(args.require("kind")?)?;
    if !matches!(kind.family, KindFamily::Ownership { .. }) {
        return derive_zcash(kind, args);
    }
    reject_options(args, kind.name, ZCASH_ONLY_OPTIONS)?;
    if args.flag("internal") || args.flag("uncompressed") {
        return Err(CliError::usage(format!(
            "--internal and --uncompressed do not apply to --kind {}",
            kind.name
        )));
    }
    let (lock, _) = kind.ownership_parts().expect("ownership kind");
    let path = match (kind.derivation_path(), args.get("path")) {
        (true, Some(path)) => parse_path(path)?,
        (true, None) => {
            return Err(CliError::usage(format!(
                "--kind {} requires --path (for example m/44'/0'/0'/0/0)",
                kind.name
            )));
        }
        (false, Some(_)) => {
            return Err(CliError::usage(format!(
                "--path does not apply to --kind {}",
                kind.name
            )));
        }
        (false, None) => Vec::new(),
    };
    let options = SourceOptions {
        extended_root: match args.get("root") {
            None | Some("seed") => false,
            Some("extended-key") => true,
            Some(other) => {
                return Err(CliError::usage(format!(
                    "--root '{other}' is not 'seed' or 'extended-key'"
                )));
            }
        },
        hidden_depth: match args.get("hidden-path-depth") {
            None => None,
            Some(text) => Some(
                text.parse::<u8>()
                    .ok()
                    .filter(|d| (1..=MAX_BIP32_DEPTH).contains(&usize::from(*d)))
                    .ok_or_else(|| {
                        CliError::usage(format!(
                            "--hidden-path-depth must be 1 to {MAX_BIP32_DEPTH}"
                        ))
                    })?,
            ),
        },
    };
    if !kind.admits(options) {
        return Err(CliError::usage(format!(
            "--root extended-key applies to BIP-32 secp256k1 kinds and --hidden-path-depth to BIP-32 and SLIP-0010 kinds, not to --kind {}",
            kind.name
        )));
    }
    if options
        .hidden_depth
        .is_some_and(|d| path.len() > usize::from(d))
    {
        return Err(CliError::usage(
            "--path is longer than --hidden-path-depth allows",
        ));
    }
    let merkle_root = match (kind.script_tree(), args.get("merkle-root")) {
        (true, Some(hex)) => Some(from_hex_exact::<32>(hex, "--merkle-root")?),
        (true, None) => {
            return Err(CliError::usage(format!(
                "--kind {} requires --merkle-root (the script tree's root, 64 hex characters)",
                kind.name
            )));
        }
        (false, Some(_)) => {
            return Err(CliError::usage(format!(
                "--merkle-root does not apply to --kind {}",
                kind.name
            )));
        }
        (false, None) => None,
    };
    let (target, target_text) = parse_target(args.require("target")?)?;
    let epoch = required_epoch(args)?;
    let domain = parse_domain(args)?;
    let secret = read_legacy_secret(args.require("legacy-secret")?, kind.secret_form(options))?;
    let mut witness = kind
        .witness(&secret.0, options)
        .ok_or_else(|| CliError::input("legacy secret has the wrong length for this kind"))?;
    if options.hidden_depth.is_some() {
        witness = witness.with_path(&path);
    }
    if let Some(root) = merkle_root {
        witness = witness.with_merkle_root(root);
    }
    let key_source = kind.key_source(path, options).expect("ownership kind");
    let statement = OwnershipStatement::derive(
        lock,
        key_source,
        &witness,
        pq_commitment(&target),
        domain,
        epoch,
    )
    .ok_or_else(|| {
        CliError::input(format!(
            "legacy secret is not a valid {} secret (a secp256k1 key must be in 1..n; a BIP-32 path must derive)",
            kind.name
        ))
    })?;
    Ok((
        LoadedStatement {
            statement: Statement::Ownership(statement),
            target,
            target_text,
        },
        Witness::Ownership(witness),
        secret,
    ))
}

fn kind_name(statement: &Statement) -> &'static str {
    kind_of(statement).map_or("unsupported", |kind| kind.name)
}

fn summary(loaded: &LoadedStatement) -> String {
    format!(
        "{} -> {} at epoch {} (nullifier {})",
        kind_name(&loaded.statement),
        loaded.target_text,
        loaded.statement.epoch(),
        to_hex(&loaded.statement.nullifier())
    )
}

fn claim(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        STATEMENT_OPTIONS,
        &["internal", "uncompressed", "json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag migrate claim --kind <{}> --legacy-secret <path> [--path <m/..>] [--root <seed|extended-key|spending-key|qsk>] [--hidden-path-depth <n>] [--merkle-root <64-hex>] [--network <main|test>] [--account <n>] [--diversifier <22-hex>] [--diversifier-index <n>] [--internal] [--uncompressed] --target <address> --epoch <n> [--domain-hex <64-hex>] [--out <path>] [--json]\n\n\
Derive the statement a proof will be about: the legacy or Zcash value, the nullifier in the\n\
migration domain, and the commitment to the target address. Nothing secret is written.\n\
--root extended-key reads an extended private key (xprv/tprv, or 64 bytes of hex: private key\n\
then chain code) instead of a master seed; sound only while no extended public key at or above\n\
it has been exported. --hidden-path-depth <n> keeps --path out of the statement: only the bound\n\
n is public. --merkle-root is the secret-side script tree root of a Taproot script-tree kind.\n\n{}",
            kind_names(),
            kinds_help()
        );
        return Ok(());
    }
    args.no_positionals()?;
    let (loaded, _witness, _secret) = derive(&args)?;
    let members = statement_members(&loaded.statement, &loaded.target_text)
        .map_err(CliError::input)?;
    let doc = document(CLAIM_FORMAT, members);
    if let Some(out) = args.get("out") {
        write_new(out, doc.to_pretty().as_bytes(), false)?;
    }
    if args.flag("json") {
        print!("{}", doc.to_pretty());
    } else {
        println!("claim {}", summary(&loaded));
    }
    Ok(())
}

// ============================================================================
// Proof files
// ============================================================================

const BASE64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn base64_len(bytes: usize) -> usize {
    bytes.div_ceil(3) * 4
}

fn to_base64(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(base64_len(bytes.len()));
    for chunk in bytes.chunks(3) {
        let word = chunk
            .iter()
            .enumerate()
            .fold(0u32, |word, (i, &b)| word | u32::from(b) << (16 - 8 * i));
        for i in 0..4 {
            out.push(if i <= chunk.len() {
                BASE64[(word >> (18 - 6 * i)) as usize & 63] as char
            } else {
                '='
            });
        }
    }
    out
}

/// Strict RFC 4648 base64: the standard alphabet, mandatory padding, no whitespace, and
/// zero bits in the unused tail of the last group, so each byte string has one encoding.
fn from_base64(text: &str) -> Option<Vec<u8>> {
    let text = text.as_bytes();
    if !text.len().is_multiple_of(4) {
        return None;
    }
    let sextet = |c: u8| BASE64.iter().position(|&a| a == c).map(|v| v as u32);
    let groups = text.len() / 4;
    let mut out = Vec::with_capacity(groups * 3);
    for (index, group) in text.as_chunks::<4>().0.iter().enumerate() {
        let padding = group.iter().rev().take_while(|&&c| c == b'=').count();
        if padding > 2 || (padding != 0 && index + 1 != groups) {
            return None;
        }
        let mut word = 0u32;
        for &c in &group[..4 - padding] {
            word = word << 6 | sextet(c)?;
        }
        word <<= 6 * padding;
        if word & ((1 << (8 * padding)) - 1) != 0 {
            return None;
        }
        out.extend_from_slice(&word.to_be_bytes()[1..4 - padding]);
    }
    Some(out)
}

/// An upper bound on the encoding of a proof for `statement`: the bound the `zk-Hem v2`
/// calculator states for the statement's relation, plus the envelope header bytes.
fn max_proof_bytes(statement: &Statement) -> Option<usize> {
    let (shape, overhead) = match statement {
        Statement::Ownership(s) => (ownership_shape(s)?, 9),
        Statement::ZcashIronwood(s) => (recovery_shape(s)?, 74),
        Statement::ZcashOrchard(s) => (address_shape(s)?, 10),
        Statement::ZcashSapling(s) => (sapling_address_shape(s)?, 10),
        Statement::ZcashTransparent(s) => (ownership_shape(&s.ownership)?, 9),
    };
    bounds::max_proof_bytes(REGIME, &shape).map(|n| n + overhead)
}

fn map_ownership_error(err: OwnershipError) -> CliError {
    match err {
        OwnershipError::MalformedStatement | OwnershipError::WitnessMismatch => {
            CliError::input(format!("migration witness error: {err:?}"))
        }
        OwnershipError::Proof(e) => CliError::input(format!("migration proving failed: {e:?}")),
    }
}

fn map_recovery_error(err: RecoveryError) -> CliError {
    match err {
        RecoveryError::MalformedStatement | RecoveryError::WitnessMismatch => {
            CliError::input(format!("Zcash migration witness error: {err:?}"))
        }
        RecoveryError::SignatureRequired => CliError::usage(
            "--kind ironwood with --root qsk requires --spend-auth-sig <128-hex>",
        ),
        RecoveryError::BadSignature => {
            CliError::input("Zcash spend authorization signature does not verify under rk")
        }
        RecoveryError::Proof(e) => {
            CliError::input(format!("Zcash migration proving failed: {e:?}"))
        }
    }
}

fn prove_statement_bytes(
    statement: &Statement,
    witness: &Witness,
    seed: &[u8; 32],
) -> Result<Vec<u8>, CliError> {
    match (statement, witness) {
        (Statement::Ownership(s), Witness::Ownership(w)) => {
            prove_ownership(s, w, REGIME, seed)
                .map(|p| p.to_bytes())
                .map_err(map_ownership_error)
        }
        (
            Statement::ZcashIronwood(s),
            Witness::ZcashIronwood {
                witness,
                spend_auth_sig,
            },
        ) => prove_recovery(s, witness, REGIME, seed, spend_auth_sig.as_ref())
            .map(|p| p.to_bytes())
            .map_err(map_recovery_error),
        (Statement::ZcashOrchard(s), Witness::ZcashOrchard(w)) => {
            prove_address(s, w, REGIME, seed)
                .map(|p| p.to_bytes())
                .map_err(map_recovery_error)
        }
        (Statement::ZcashSapling(s), Witness::ZcashSapling(w)) => {
            prove_sapling_address(s, w, REGIME, seed)
                .map(|p| p.to_bytes())
                .map_err(map_recovery_error)
        }
        (Statement::ZcashTransparent(s), Witness::ZcashTransparent(w)) => {
            prove_transparent(s, w, REGIME, seed)
                .map(|p| p.to_bytes())
                .map_err(map_ownership_error)
        }
        _ => Err(CliError::input("statement and witness kind mismatch")),
    }
}

fn verify_statement_bytes(statement: &Statement, bytes: &[u8]) -> Option<bool> {
    match statement {
        Statement::Ownership(s) => {
            OwnershipProof::from_bytes(bytes, s).map(|p| verify_ownership(s, REGIME, &p))
        }
        Statement::ZcashIronwood(s) => {
            RecoveryProof::from_bytes(bytes, s).map(|p| verify_recovery(s, REGIME, &p))
        }
        Statement::ZcashOrchard(s) => {
            AddressProof::from_bytes(bytes, s).map(|p| verify_address(s, REGIME, &p))
        }
        Statement::ZcashSapling(s) => SaplingAddressProof::from_bytes(bytes, s)
            .map(|p| verify_sapling_address(s, REGIME, &p)),
        Statement::ZcashTransparent(s) => {
            TransparentProof::from_bytes(bytes, s).map(|p| verify_transparent(s, REGIME, &p))
        }
    }
}

fn prove(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        STATEMENT_OPTIONS,
        &["internal", "uncompressed", "deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag migrate prove --kind <{}> --legacy-secret <path> [--path <m/..>] [--root <seed|extended-key|spending-key|qsk>] [--hidden-path-depth <n>] [--merkle-root <64-hex>] [--network <main|test>] [--account <n>] [--diversifier <22-hex>] [--diversifier-index <n>] [--spend-auth-sig <128-hex>] [--internal] [--uncompressed] --target <address> --epoch <n> [--domain-hex <64-hex>] --out <path> [--deterministic] [--json]\n\n\
Prove ownership of a legacy or Zcash credential and bind it to --target, --epoch and the\n\
migration domain. --deterministic derives the proof randomness from the secret and the statement.\n\n{}",
            kind_names(),
            kinds_help()
        );
        return Ok(());
    }
    args.no_positionals()?;
    let out_path = args.require("out")?;
    let (loaded, witness, secret) = derive(&args)?;
    let statement = &loaded.statement;
    let seed = Secret32::new(if args.flag("deterministic") {
        cshake256_framed_32(
            b"QSAG.CLI.MIGRATE.PROOF.SEED.V2",
            &[&secret.0, &statement.to_bytes(), &[REGIME as u8]],
        )
    } else {
        os_random_32()?
    });
    let bytes = prove_statement_bytes(statement, &witness, &seed.0)?;
    let cap = max_proof_bytes(statement).unwrap_or(0);
    if bytes.len() > cap || verify_statement_bytes(statement, &bytes) != Some(true) {
        return Err(CliError::verify(
            "the generated migration proof does not verify; nothing was written",
        ));
    }
    let mut members =
        statement_members(statement, &loaded.target_text).map_err(CliError::input)?;
    members.extend([
        ("regime", Json::str(REGIME_NAME)),
        ("proof_bytes", Json::num(bytes.len())),
        ("proof", Json::str(to_base64(&bytes))),
    ]);
    write_new(
        out_path,
        document(PROOF_FORMAT, members).to_pretty().as_bytes(),
        false,
    )?;
    if args.flag("json") {
        let mut report = vec![("operation", Json::str("migrate-prove"))];
        report.extend(
            statement_members(statement, &loaded.target_text).map_err(CliError::input)?,
        );
        report.extend([
            ("regime", Json::str(REGIME_NAME)),
            ("proof_bytes", Json::num(bytes.len())),
            ("proof_file", Json::str(out_path)),
        ]);
        print!("{}", Json::object(report).to_pretty());
    } else {
        println!(
            "proved {} ({} proof bytes) -> {out_path}",
            summary(&loaded),
            bytes.len()
        );
    }
    Ok(())
}

/// What the verifier requires of a proof, from its own options.
struct Expectation {
    epoch: u64,
    domain: [u8; 32],
    target: Option<QsagAddress>,
}

impl Expectation {
    fn from_args(args: &Args) -> Result<Self, CliError> {
        Ok(Self {
            epoch: required_epoch(args)?,
            domain: parse_domain(args)?,
            target: args
                .get("target")
                .map(|text| parse_target(text).map(|(address, _)| address))
                .transpose()?,
        })
    }
}

/// Parse a claim or proof file. A file that cannot be opened is an I/O error; anything
/// wrong with its content is returned as text for the caller to classify.
fn read_document(path: &str) -> Result<Result<Json, String>, CliError> {
    let raw = read_bounded_file(path, MAX_SIG_PROOF_BYTES)?;
    Ok(std::str::from_utf8(&raw.0)
        .map_err(|_| format!("{path} is not UTF-8"))
        .and_then(|text| Json::parse(text).map_err(|e| format!("{path}: {e}"))))
}

/// Read a proof file and verify it. Every failure is exit code 2.
fn load_verified(path: &str, expected: &Expectation) -> Result<LoadedStatement, CliError> {
    let json = read_document(path)?.map_err(CliError::verify)?;
    let loaded = load_statement(&json, PROOF_FORMAT, &["regime", "proof_bytes", "proof"])
        .map_err(|e| CliError::verify(format!("{path}: {e}")))?;
    let statement = &loaded.statement;
    if json.get("regime").and_then(Json::as_str) != Some(REGIME_NAME) {
        return Err(CliError::verify(format!(
            "{path}: proof is not under the {REGIME_NAME} regime"
        )));
    }
    if statement.migration_domain() != expected.domain {
        return Err(CliError::verify(
            "proof is for another migration domain (--domain-hex)",
        ));
    }
    if statement.epoch() != expected.epoch {
        return Err(CliError::verify(format!(
            "proof is for epoch {}, not --epoch {}",
            statement.epoch(),
            expected.epoch
        )));
    }
    if expected
        .target
        .as_ref()
        .is_some_and(|target| *target != loaded.target)
    {
        return Err(CliError::verify(
            "proof binds another target address than --target",
        ));
    }
    let encoded = json
        .get("proof")
        .and_then(Json::as_str)
        .ok_or_else(|| CliError::verify("migration proof file has no proof"))?;
    let cap = max_proof_bytes(statement)
        .ok_or_else(|| CliError::verify("statement has no ownership relation"))?;
    if encoded.len() > base64_len(cap) {
        return Err(CliError::verify(format!(
            "proof is larger than any proof of this statement ({cap} bytes)"
        )));
    }
    let bytes =
        from_base64(encoded).ok_or_else(|| CliError::verify("proof is not canonical base64"))?;
    if json.get("proof_bytes").and_then(Json::as_u64) != u64::try_from(bytes.len()).ok() {
        return Err(CliError::verify("proof_bytes does not match the proof"));
    }
    match verify_statement_bytes(statement, &bytes) {
        None => return Err(CliError::verify("proof is not a canonical migration proof")),
        Some(false) => return Err(CliError::verify("migration proof verification failed")),
        Some(true) => {}
    }
    Ok(loaded)
}

const VERIFY_OPTIONS: &[&str] = &["proof", "target", "epoch", "domain-hex"];
const VERIFY_HELP: &str = "\
  --epoch <n>            the epoch the verifier is in; the proof must be for it
  --domain-hex <64-hex>  the migration domain (default: the built-in QSAG domain)
  --target <address>     require this target address (default: accept the proof's own)
";

fn verify(raw: &[String]) -> Result<(), CliError> {
    let mut options = VERIFY_OPTIONS.to_vec();
    options.extend(REGISTRY_OPTIONS);
    let mut flags = REGISTRY_FLAGS.to_vec();
    flags.push("register");
    let args = Args::parse(raw, &options, &flags)?;
    if args.flag("help") {
        print!(
            "qsag migrate verify --proof <path> --epoch <n> [--domain-hex <64-hex>] [--target <address>] [--register --registry-dir <dir> ..] [--json]\n\n\
Verify a migration proof: the proof itself, that its target address is the one the statement\n\
commits to, and that epoch, domain and (if given) target are the ones expected.\n\
Exit code 2: the proof is refused. With --register, exit code 4: the proof is valid and the\n\
registry refuses it (the nullifier or the legacy credential is already bound elsewhere).\n\n\
{VERIFY_HELP}  --register             record the verified binding as finalized in --registry-dir\n{REGISTRY_HELP}"
        );
        return Ok(());
    }
    args.no_positionals()?;
    if !args.flag("register") {
        if let Some(option) = REGISTRY_OPTIONS.iter().find(|o| args.get(o).is_some()) {
            return Err(CliError::usage(format!(
                "--{option} applies only with --register"
            )));
        }
        let loaded = load_verified(args.require("proof")?, &Expectation::from_args(&args)?)?;
        if args.flag("json") {
            let mut report = vec![("valid", Json::Bool(true))];
            report.extend(
                statement_members(&loaded.statement, &loaded.target_text)
                    .map_err(CliError::verify)?,
            );
            print!("{}", Json::object(report).to_pretty());
        } else {
            println!("valid ({})", summary(&loaded));
        }
        return Ok(());
    }
    submit(&args, Submission::Register)
}

// ============================================================================
// Registry
// ============================================================================

const ROOT_NAME: &str = "registry.json";
const ANCHOR_DOMAIN: &str = "migration_registry";
const ANCHOR_SEAL_FIELD: &str = "anchor_registry_seal";

const REGISTRY_OPTIONS: &[&str] = &[
    "registry-dir",
    "anchor-dir",
    "anchor-tpm-nv",
    "anchor-tpm-device",
    "anchor-tpm-auth-env",
    "min-checkpoint",
    "passphrase-env",
    "passphrase-file",
];

const REGISTRY_FLAGS: &[&str] = &[
    "allow-single-disk-anchor",
    "anchor-vmgenid",
    "anchor-vmgenid-strict",
    "json",
    "help",
];

const REGISTRY_HELP: &str = "\
  --registry-dir <dir>          the registry directory
  --anchor-dir <dir>            the registry's external monotone anchor (required if it was
                                created with one)
  --allow-single-disk-anchor    permit --anchor-dir on the registry's filesystem device
  --min-checkpoint <n>:<hex>    for a registry without an anchor: refuse a log that is behind
                                this checkpoint (the checkpoint an earlier command printed)
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock a sealed registry key
  --json                        print the result as JSON
";

fn registry_error(err: RegistryError) -> CliError {
    match err {
        RegistryError::Io(e) => CliError::io("migration registry", e),
        other => CliError::state(format!("migration registry: {other}")),
    }
}

fn root_path(dir: &str) -> Result<String, CliError> {
    std::path::Path::new(dir)
        .join(ROOT_NAME)
        .to_str()
        .map(str::to_owned)
        .ok_or_else(|| CliError::usage("--registry-dir is not UTF-8"))
}

fn registry_secret(seed: &Secret32, label: &[u8]) -> Secret32 {
    Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.MIGRATE.REGISTRY.KDF.V1",
        &[&seed.0, label],
    ))
}

fn log_key(seed: &Secret32, anchored: bool) -> Secret32 {
    registry_secret(
        seed,
        if anchored {
            b"log mac, anchored"
        } else {
            b"log mac, unanchored"
        },
    )
}

fn registry_id(seed: &Secret32, nonce: &[u8]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.MIGRATE.REGISTRY.ID.V1",
        &[&registry_secret(seed, b"identifier").0, nonce],
    )
}

fn anchor_config(args: &Args, dir: &str) -> Result<Option<AnchorConfig>, CliError> {
    AnchorConfig::for_vault(args, dir, "anchor-dir", "allow-single-disk-anchor")
}

fn parse_checkpoint(text: &str) -> Result<qsag_core::LedgerCheckpoint, CliError> {
    let bad = || CliError::usage("--min-checkpoint must be <generation>:<64-hex tag>");
    let (generation, tag) = text.split_once(':').ok_or_else(bad)?;
    Ok(qsag_core::LedgerCheckpoint {
        generation: generation.parse().map_err(|_| bad())?,
        tag: from_hex_exact::<32>(tag, "--min-checkpoint tag").map_err(|_| bad())?,
    })
}

fn checkpoint_members(checkpoint: qsag_core::LedgerCheckpoint) -> Vec<(&'static str, Json)> {
    vec![(
        "checkpoint",
        Json::str(format!(
            "{}:{}",
            checkpoint.generation,
            to_hex(&checkpoint.tag)
        )),
    )]
}

const INIT_HELP: &str = "\
qsag migrate registry init --registry-dir <dir> (--anchor-dir <dir> | --ephemeral-unanchored)

Create an empty migration registry in a fresh owner-only directory. The registry records each
verified migration once: a nullifier, and the legacy credential behind it, stay bound to one
post-quantum address.

  --anchor-dir <dir>            ratchet the log's length and tip in an external monotone
                                anchor, so that restoring an old copy of the registry is refused
  --allow-single-disk-anchor    permit --anchor-dir on the registry's filesystem device
  --ephemeral-unanchored        create a registry without rollback protection (required when
                                no anchor is given); --min-checkpoint is then the only defence
  --passphrase-env <VAR> / --passphrase-file <PATH>  seal the registry key
  --json                        print the registry identifier as JSON
";

fn init(raw: &[String]) -> Result<(), CliError> {
    let mut flags = REGISTRY_FLAGS.to_vec();
    flags.push("ephemeral-unanchored");
    let args = Args::parse(raw, REGISTRY_OPTIONS, &flags)?;
    if args.flag("help") {
        print!("{INIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let dir = args.require("registry-dir")?;
    if args.get("min-checkpoint").is_some() {
        return Err(CliError::usage(
            "--min-checkpoint does not apply to registry init",
        ));
    }
    let anchor_cfg = anchor_config(&args, dir)?;
    crate::anchor::require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let passphrase = crate::envelope::passphrase(&args)?;

    private_dir(dir, true)?;
    let occupied = std::fs::read_dir(dir)
        .map_err(|e| CliError::io(format_args!("reading {dir}"), e))?
        .next()
        .is_some();
    if occupied {
        return Err(CliError::state(format!(
            "{dir} is not empty; a migration registry is created only in a fresh directory"
        )));
    }
    let root = root_path(dir)?;
    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&[&root], &[dir], true)?;
    }
    let mut vault = Vault::acquire(&root, true)?;
    let seed = Secret32::new(os_random_32()?);
    let nonce = os_random_32()?;
    let nonce = &nonce[..16];
    let id = registry_id(&seed, nonce);
    let key = log_key(&seed, anchor_cfg.is_some());

    let (registry, anchor_seal) = match &anchor_cfg {
        Some(cfg) => {
            let anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &[&root],
                &[dir],
                ANCHOR_DOMAIN,
                id,
                registry_secret(&seed, b"anchor mac").0,
            )?;
            let seal = anchor.lock_identity_seal();
            (
                NullifierRegistry::create_anchored(dir, key.0, Box::new(anchor)),
                Some(seal),
            )
        }
        None => (NullifierRegistry::create(dir, key.0), None),
    };
    let registry = registry.map_err(registry_error)?;

    let mut file = Json::object(vec![
        ("format", Json::str(REGISTRY_FORMAT)),
        ("scheme", Json::str(REGISTRY_SCHEME)),
        ("enrollment_nonce", Json::hex(nonce)),
        ("registry_id", Json::hex(&id)),
    ]);
    if let Some(seal) = &anchor_seal {
        set(&mut file, "anchor_required", Json::Bool(true));
        set(&mut file, ANCHOR_SEAL_FIELD, Json::hex(seal));
    }
    set(&mut file, "seed", Json::hex(&seed.0));
    vault.set_key_material(&crate::envelope::open(&file, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut file, pass)?;
    }
    vault.bind(&mut file)?;
    vault.seal(&mut file)?;
    let encoded = ZeroizingBuf::new(file.to_pretty().into_bytes());
    write_new(&root, &encoded.0, true)?;

    if args.flag("json") {
        let mut report = vec![
            ("registry_id", Json::hex(&id)),
            ("anchored", Json::Bool(anchor_cfg.is_some())),
        ];
        report.extend(checkpoint_members(registry.checkpoint()));
        print!("{}", Json::object(report).to_pretty());
    } else {
        println!("created migration registry {} in {dir}", to_hex(&id));
    }
    Ok(())
}

fn open_registry(args: &Args) -> Result<NullifierRegistry, CliError> {
    let dir = args.require("registry-dir")?;
    let passphrase = crate::envelope::passphrase(args)?;
    let anchor_cfg = anchor_config(args, dir)?;
    let minimum = args
        .get("min-checkpoint")
        .map(parse_checkpoint)
        .transpose()?;
    private_dir(dir, false)?;
    let root = root_path(dir)?;
    let mut vault = Vault::acquire(&root, false)?;
    let text = read_text(&root)?;
    let on_disk = Json::parse(&text)?;
    if on_disk.field_str("format")? != REGISTRY_FORMAT
        || on_disk.field_str("scheme")? != REGISTRY_SCHEME
    {
        return Err(CliError::input(format!(
            "{root} is not a {REGISTRY_FORMAT} file"
        )));
    }
    let opened = crate::envelope::open(&on_disk, passphrase.as_deref().map(Vec::as_slice))?;
    vault.set_key_material(&opened);
    vault.authenticate(&on_disk)?;
    let anchored = crate::anchor::anchor_requirement(&on_disk, anchor_cfg.is_some()).map_err(
        |e| match e {
            AnchorRequirementError::Malformed => crate::vault::corrupt(),
            AnchorRequirementError::AnchorMissing => CliError::state(
                "migration registry was created with an external anchor; its anchor directory is required",
            ),
            AnchorRequirementError::NotEnrolled => {
                CliError::state("migration registry was not created with an external anchor")
            }
        },
    )?;
    let seed = opened.seed()?;
    let nonce = on_disk.field_hex("enrollment_nonce")?;
    let id = registry_id(&seed, &nonce);
    let recorded: [u8; 32] = from_hex_exact(on_disk.field_str("registry_id")?, "registry_id")?;
    if id != recorded {
        return Err(crate::vault::corrupt());
    }
    let key = log_key(&seed, anchored);
    match (anchor_cfg, minimum) {
        (Some(_), Some(_)) => Err(CliError::usage(
            "--min-checkpoint applies to a registry without an anchor; the anchor already holds the checkpoint",
        )),
        (Some(cfg), None) => {
            let anchor = FsExternalMountAnchor::open_existing(
                &cfg,
                &[&root],
                &[dir],
                ANCHOR_DOMAIN,
                id,
                registry_secret(&seed, b"anchor mac").0,
            )?;
            anchor.verify_expected_seal(&on_disk, ANCHOR_SEAL_FIELD)?;
            NullifierRegistry::open_anchored(dir, key.0, Box::new(anchor)).map_err(registry_error)
        }
        (None, Some(minimum)) => {
            NullifierRegistry::open_at_least(dir, key.0, minimum).map_err(registry_error)
        }
        (None, None) => NullifierRegistry::open(dir, key.0).map_err(registry_error),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Submission {
    Register,
    Enroll,
    Finalize,
}

impl Submission {
    fn name(self) -> &'static str {
        match self {
            Self::Register => "register",
            Self::Enroll => "enroll",
            Self::Finalize => "finalize",
        }
    }
}

fn status_name(status: BindingStatus) -> &'static str {
    match status {
        BindingStatus::Enrolled => "enrolled",
        BindingStatus::Finalized => "finalized",
    }
}

fn submit(args: &Args, submission: Submission) -> Result<(), CliError> {
    args.require("registry-dir")?;
    let loaded = load_verified(args.require("proof")?, &Expectation::from_args(args)?)?;
    let binding = loaded
        .statement
        .binding()
        .ok_or_else(|| CliError::verify("statement has no canonical registry binding"))?;
    let mut registry = open_registry(args)?;
    let receipt: Receipt = match submission {
        Submission::Register => registry.register(&binding),
        Submission::Enroll => registry.enroll(&binding),
        Submission::Finalize => registry.finalize(&binding),
    }
    .map_err(registry_error)?;
    if args.flag("json") {
        let mut report = vec![
            ("valid", Json::Bool(true)),
            ("operation", Json::str(submission.name())),
            ("status", Json::str(status_name(receipt.status))),
            ("appended", Json::Bool(receipt.appended)),
        ];
        report.extend(checkpoint_members(receipt.checkpoint));
        report.extend(
            statement_members(&loaded.statement, &loaded.target_text).map_err(CliError::verify)?,
        );
        print!("{}", Json::object(report).to_pretty());
    } else {
        println!(
            "valid ({}); {} ({}); checkpoint {}:{}",
            summary(&loaded),
            status_name(receipt.status),
            if receipt.appended {
                "recorded"
            } else {
                "already recorded"
            },
            receipt.checkpoint.generation,
            to_hex(&receipt.checkpoint.tag)
        );
    }
    Ok(())
}

fn registry_submit(raw: &[String], submission: Submission) -> Result<(), CliError> {
    let mut options = VERIFY_OPTIONS.to_vec();
    options.extend(REGISTRY_OPTIONS);
    let args = Args::parse(raw, &options, REGISTRY_FLAGS)?;
    if args.flag("help") {
        let what = match submission {
            Submission::Register => {
                "Verify a migration proof and record its binding as finalized, in one step."
            }
            Submission::Enroll => {
                "Verify a migration proof and reserve its binding; legacy authorisation stays on\nuntil `finalize`."
            }
            Submission::Finalize => {
                "Verify the proof of an enrolled binding again and mark it finalized."
            }
        };
        print!(
            "qsag migrate registry {} --registry-dir <dir> --proof <path> --epoch <n> [--domain-hex <64-hex>] [--target <address>]\n\n\
{what}\nAn identical submission is accepted again without writing. Exit code 2: the proof is refused.\n\
Exit code 4: the registry refuses the binding or does not open.\n\n{VERIFY_HELP}{REGISTRY_HELP}",
            submission.name()
        );
        return Ok(());
    }
    args.no_positionals()?;
    submit(&args, submission)
}

fn binding_members(found: &RegisteredBinding) -> Vec<(&'static str, Json)> {
    let binding = &found.binding;
    vec![
        ("status", Json::str(status_name(found.status))),
        ("ordinal", Json::num(found.ordinal)),
        ("nullifier", Json::hex(&binding.nullifier)),
        ("legacy_id", Json::hex(&binding.legacy_id)),
        ("pq_commitment", Json::hex(&binding.pq_commitment)),
        ("epoch", Json::num(binding.epoch)),
        ("migration_domain", Json::hex(&binding.migration_domain)),
        (
            "key_exposure",
            Json::str(match binding.exposure {
                qsag_migrate::hem::registry::KeyExposure::Hidden => "hidden",
                qsag_migrate::hem::registry::KeyExposure::Revealed => "revealed",
            }),
        ),
    ]
}

fn lookup(raw: &[String]) -> Result<(), CliError> {
    let mut options = vec!["nullifier", "legacy-id", "statement"];
    options.extend(REGISTRY_OPTIONS);
    let args = Args::parse(raw, &options, REGISTRY_FLAGS)?;
    if args.flag("help") {
        print!(
            "qsag migrate registry lookup --registry-dir <dir> (--nullifier <64-hex> | --legacy-id <64-hex> | --statement <claim or proof file>)\n\n\
Report what the registry holds for a nullifier or for a legacy credential. --statement takes\n\
both from a claim or proof file, without verifying any proof. Exit code 0 whether or not a\n\
binding is recorded; the output says `absent` when none is.\n\n{REGISTRY_HELP}"
        );
        return Ok(());
    }
    args.no_positionals()?;
    args.require("registry-dir")?;
    let selectors = [
        args.get("nullifier"),
        args.get("legacy-id"),
        args.get("statement"),
    ];
    if selectors.iter().flatten().count() != 1 {
        return Err(CliError::usage(
            "lookup takes exactly one of --nullifier, --legacy-id and --statement",
        ));
    }
    let (nullifier, legacy_id) = match selectors {
        [Some(hex), _, _] => (Some(from_hex_exact::<32>(hex, "--nullifier")?), None),
        [_, Some(hex), _] => (None, Some(from_hex_exact::<32>(hex, "--legacy-id")?)),
        [_, _, Some(path)] => {
            let json = read_document(path)?.map_err(CliError::input)?;
            let loaded = load_statement(&json, CLAIM_FORMAT, &[])
                .or_else(|_| {
                    load_statement(&json, PROOF_FORMAT, &["regime", "proof_bytes", "proof"])
                })
                .map_err(|e| CliError::input(format!("{path}: {e}")))?;
            let binding = loaded
                .statement
                .binding()
                .ok_or_else(|| CliError::input("statement has no canonical registry binding"))?;
            (Some(binding.nullifier), Some(binding.legacy_id))
        }
        _ => (None, None),
    };
    let registry = open_registry(&args)?;
    let by_nullifier = nullifier
        .map(|n| registry.lookup(&n))
        .transpose()
        .map_err(registry_error)?
        .flatten();
    let by_legacy = legacy_id
        .map(|l| registry.lookup_legacy(&l))
        .transpose()
        .map_err(registry_error)?
        .flatten();
    let render = |found: &Option<RegisteredBinding>| match found {
        Some(found) => Json::object(binding_members(found)),
        None => Json::object(vec![("status", Json::str("absent"))]),
    };
    if args.flag("json") {
        let mut report = Vec::new();
        if nullifier.is_some() {
            report.push(("by_nullifier", render(&by_nullifier)));
        }
        if legacy_id.is_some() {
            report.push(("by_legacy_id", render(&by_legacy)));
        }
        report.extend(checkpoint_members(registry.checkpoint()));
        print!("{}", Json::object(report).to_pretty());
    } else {
        let line = |what: &str, found: &Option<RegisteredBinding>| match found {
            Some(found) => println!(
                "{what}: {} to {} at epoch {} (nullifier {}, record {})",
                status_name(found.status),
                to_hex(&found.binding.pq_commitment),
                found.binding.epoch,
                to_hex(&found.binding.nullifier),
                found.ordinal
            ),
            None => println!("{what}: absent"),
        };
        if nullifier.is_some() {
            line("nullifier", &by_nullifier);
        }
        if legacy_id.is_some() {
            line("legacy credential", &by_legacy);
        }
    }
    Ok(())
}

const REGISTRY_COMMAND_HELP: &str = "\
qsag migrate registry <subcommand> [options]

The durable one-way migration registry:
  init      create an empty registry (--anchor-dir, or --ephemeral-unanchored)
  register  verify a proof and record its binding as finalized
  enroll    verify a proof and reserve its binding
  finalize  verify the proof of an enrolled binding and mark it finalized
  lookup    report the binding of a nullifier or a legacy credential
";

fn registry(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{REGISTRY_COMMAND_HELP}");
        return Err(CliError::usage(
            "migrate registry requires a subcommand (try --help)",
        ));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{REGISTRY_COMMAND_HELP}");
            Ok(())
        }
        "init" => init(rest),
        "register" => registry_submit(rest, Submission::Register),
        "enroll" => registry_submit(rest, Submission::Enroll),
        "finalize" => registry_submit(rest, Submission::Finalize),
        "lookup" => lookup(rest),
        other => Err(CliError::usage(format!(
            "unknown migrate registry subcommand '{other}' (expected init, register, enroll, finalize, or lookup)"
        ))),
    }
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{MIGRATE_HELP}{}", kinds_help());
        return Err(CliError::usage(
            "migrate requires a subcommand (try --help)",
        ));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{MIGRATE_HELP}{}", kinds_help());
            Ok(())
        }
        "claim" | "commit" => claim(rest),
        "prove" => prove(rest),
        "verify" => verify(rest),
        "registry" => registry(rest),
        other => Err(CliError::usage(format!(
            "unknown migrate subcommand '{other}' (expected claim, prove, verify, or registry)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_addr::{KeyIdentityKind, WitnessSuiteTag};

    fn address(seed: u8) -> QsagAddress {
        QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            &[seed; 32],
        )
        .unwrap()
    }

    fn target() -> QsagAddress {
        address(7)
    }

    /// One statement per table entry across all 19 kinds, from fixed secrets.
    fn statements() -> Vec<(&'static KindSpec, Statement, Witness)> {
        let pq = pq_commitment(&target());
        let domain = [9u8; 32];
        let epoch = 3u64;
        KINDS
            .iter()
            .map(|&kind| match kind.family {
                KindFamily::Ownership { lock, source } => {
                    let secret: Vec<u8> = match kind.secret {
                        SecretForm::Key32 => (1..=32).collect(),
                        SecretForm::HexSeed => (1..=16).collect(),
                        SecretForm::ExtendedKey => (1..=64).collect(),
                        SecretForm::Ed25519ExtendedKey => {
                            let mut key: Vec<u8> = (1..=96).collect();
                            key[0] &= 0xf8;
                            key[31] = (key[31] & 0x1f) | 0x40;
                            key
                        }
                        SecretForm::Zip32Seed | SecretForm::JsonNote => unreachable!(),
                    };
                    let path = if source == Source::Slip10 {
                        parse_path("m/44'/501'").unwrap()
                    } else if kind.derivation_path() {
                        parse_path("m/44'/0'/0'/0/0").unwrap()
                    } else {
                        Vec::new()
                    };
                    let mut witness = kind.witness(&secret, SourceOptions::default()).unwrap();
                    if kind.script_tree() {
                        witness = witness.with_merkle_root([0x5a; 32]);
                    }
                    let statement = OwnershipStatement::derive(
                        lock,
                        kind.key_source(path, SourceOptions::default()).unwrap(),
                        &witness,
                        pq,
                        domain,
                        epoch,
                    )
                    .unwrap();
                    (
                        kind,
                        Statement::Ownership(statement),
                        Witness::Ownership(witness),
                    )
                }
                KindFamily::ZcashOrchard => {
                    let sk = [0x21u8; 32];
                    let fvk = OrchardFullViewingKey::from_spending_key(&sk).unwrap();
                    let d = fvk.diversifier(&[0; 11], OrchardScope::External);
                    let w = AddressWitness {
                        key: OrchardKeyWitness::SpendingKey(sk),
                        internal: false,
                    };
                    let stmt = AddressStatement::derive(
                        &OrchardKeySource::SpendingKey,
                        &w,
                        &d,
                        pq,
                        domain,
                        epoch,
                    )
                    .unwrap();
                    (
                        kind,
                        Statement::ZcashOrchard(stmt),
                        Witness::ZcashOrchard(Box::new(w)),
                    )
                }
                KindFamily::ZcashSapling => {
                    let sk = [0x31u8; 32];
                    let d = sapling::default_diversifier(&sk);
                    let w = SaplingKeyWitness::SpendingKey(sk);
                    let stmt = SaplingAddressStatement::derive(
                        &SaplingKeySource::SpendingKey,
                        &w,
                        &d,
                        pq,
                        domain,
                        epoch,
                    )
                    .unwrap();
                    (
                        kind,
                        Statement::ZcashSapling(stmt),
                        Witness::ZcashSapling(w),
                    )
                }
                KindFamily::ZcashIronwood => {
                    let sk = [0x41u8; 32];
                    let fvk = OrchardFullViewingKey::from_spending_key(&sk).unwrap();
                    let recipient = fvk.default_address(OrchardScope::External).unwrap();
                    let mut rho_bytes = [0u8; 32];
                    rho_bytes[0] = 7;
                    let rho = PallasFp::from_bytes(&rho_bytes).unwrap();
                    let note = OrchardNote {
                        recipient,
                        value: 125_000_000,
                        rho,
                        rseed: [0x55; 32],
                        version: NoteVersion::V3,
                    };
                    let cmx = note.cmx().unwrap().to_bytes();
                    let leaf = rehash::leaf_hash(&cmx, &rho_bytes);
                    let (path, _) = rehash::witness(&[leaf], 0).unwrap();
                    let mut alpha = [0u8; 32];
                    alpha[0] = 9;
                    let w = RecoveryWitness {
                        key: OrchardKeyWitness::SpendingKey(sk),
                        internal: false,
                        alpha,
                        note,
                        position: 0,
                        path,
                    };
                    let stmt = RecoveryStatement::derive(
                        &OrchardKeySource::SpendingKey,
                        &w,
                        pq,
                        domain,
                        epoch,
                    )
                    .unwrap();
                    (
                        kind,
                        Statement::ZcashIronwood(stmt),
                        Witness::ZcashIronwood {
                            witness: Box::new(w),
                            spend_auth_sig: None,
                        },
                    )
                }
                KindFamily::ZcashTransparent => {
                    let mut key = [0u8; 32];
                    key[31] = 1;
                    let w = OwnershipWitness::secp256k1_key(&key);
                    let stmt = TransparentStatement::derive_hidden(
                        Network::Main,
                        KeyEncoding::Compressed,
                        &w,
                        pq,
                        domain,
                        epoch,
                    )
                    .unwrap();
                    (
                        kind,
                        Statement::ZcashTransparent(stmt),
                        Witness::ZcashTransparent(w),
                    )
                }
            })
            .collect()
    }

    #[test]
    fn every_table_entry_derives_a_claim_that_maps_back_to_it_and_renders() {
        let all = statements();
        assert_eq!(all.len(), KIND_COUNT);
        let mut names = Vec::new();
        for (kind, statement, _) in all {
            assert!(
                std::ptr::eq(kind_of(&statement).unwrap(), kind),
                "{}",
                kind.name
            );
            let rendered = statement.render_kind_members(kind);
            assert_eq!(rendered[0].0, kind.member, "{}", kind.name);
            assert!(std::ptr::eq(kind_by_name(kind.name).unwrap(), kind));
            names.push(kind.name);
            for alias in kind.aliases {
                assert!(std::ptr::eq(kind_by_name(alias).unwrap(), kind));
                names.push(alias);
            }
            if let Statement::Ownership(s) = &statement {
                let claimed = KINDS
                    .iter()
                    .filter(|other| {
                        matches!(other.family, KindFamily::Ownership { lock, .. } if lock == s.lock && other.offers(&s.source))
                    })
                    .count();
                assert_eq!(claimed, 1, "{}", kind.name);
            }
        }
        let count = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(
            names.len(),
            count,
            "kind names and aliases must be distinct"
        );
        assert!(kind_by_name("btc-p2wsh").is_err());
    }

    #[test]
    fn roots_and_hidden_paths_are_options_of_a_kind_and_render() {
        let kind = kind_by_name("bip32-secp256k1").unwrap();
        let (lock, _) = kind.ownership_parts().unwrap();
        let path = parse_path("m/44'/0'/0'/0/0").unwrap();
        let node: Vec<u8> = (1..=64).collect();
        let seed: Vec<u8> = (1..=16).collect();
        let derive = |options: SourceOptions, secret: &[u8]| {
            let mut witness = kind.witness(secret, options).unwrap();
            if options.hidden_depth.is_some() {
                witness = witness.with_path(&path);
            }
            Statement::Ownership(
                OwnershipStatement::derive(
                    lock,
                    kind.key_source(path.clone(), options).unwrap(),
                    &witness,
                    pq_commitment(&target()),
                    [9; 32],
                    3,
                )
                .unwrap(),
            )
        };
        let names = |statement: &Statement| -> Vec<&'static str> {
            statement
                .render_kind_members(kind)
                .iter()
                .map(|(name, _)| *name)
                .collect()
        };
        let public = derive(SourceOptions::default(), &seed);
        let hidden = derive(
            SourceOptions {
                extended_root: false,
                hidden_depth: Some(6),
            },
            &seed,
        );
        let extended = derive(
            SourceOptions {
                extended_root: true,
                hidden_depth: None,
            },
            &node,
        );
        assert_eq!(names(&public), ["legacy_hash160", "derivation_path"]);
        assert_eq!(names(&hidden), ["legacy_hash160", "hidden_path_max_depth"]);
        assert_eq!(
            names(&extended),
            ["legacy_hash160", "bip32_root", "derivation_path"]
        );
        assert_ne!(public.to_bytes(), hidden.to_bytes());
        for statement in [&public, &hidden, &extended] {
            assert!(std::ptr::eq(kind_of(statement).unwrap(), kind));
            let text = target().encode().unwrap();
            let doc = document(
                CLAIM_FORMAT,
                statement_members(statement, &text).unwrap(),
            );
            assert_eq!(
                load_statement(&doc, CLAIM_FORMAT, &[]).unwrap().statement,
                *statement
            );
        }
        let key = kind_by_name("eth-eoa").unwrap();
        assert!(!key.admits(SourceOptions {
            extended_root: true,
            hidden_depth: None
        }));
        assert!(
            !kind_by_name("bip32-ed25519")
                .unwrap()
                .admits(SourceOptions {
                    extended_root: false,
                    hidden_depth: Some(3)
                })
        );
    }

    #[test]
    fn extended_private_keys_parse_bip32_test_vector_1_and_reject_damage() {
        let xprv = "xprv9s21ZrQH143K3QTDL4LXw2F7HEK3wJUD2nW2nRk4stbPy6cq3jPPqjiChkVvvNKmPGJxWUtg6LnF5kejMRNNU3TGtRBeJgk33yuGBxrMPHi";
        let node = parse_extended_private_key(xprv).unwrap();
        assert_eq!(
            to_hex(&node.0[..32]),
            "e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35"
        );
        assert_eq!(
            to_hex(&node.0[32..]),
            "873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508"
        );
        let xpub = "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8";
        assert!(parse_extended_private_key(xpub).is_err());
        let mut damaged = xprv.to_owned();
        damaged.replace_range(40..41, if &xprv[40..41] == "2" { "3" } else { "2" });
        assert!(parse_extended_private_key(&damaged).is_err());
        assert!(parse_extended_private_key(&xprv[..110]).is_err());
        assert!(parse_extended_private_key(&format!("1{xprv}")).is_err());
        assert!(parse_extended_private_key("xprv0OIl").is_err());
    }

    #[test]
    fn statement_documents_round_trip_and_reject_any_other_content() {
        let text = target().encode().unwrap();
        for (kind, statement, _) in statements() {
            let doc = document(
                CLAIM_FORMAT,
                statement_members(&statement, &text).unwrap(),
            );
            let loaded = load_statement(&doc, CLAIM_FORMAT, &[]).unwrap();
            assert_eq!(loaded.statement, statement, "{}", kind.name);
            assert_eq!(loaded.target, target());
            assert!(load_statement(&doc, PROOF_FORMAT, &[]).is_err());
            let Json::Object(members) = &doc else {
                unreachable!()
            };
            for index in 1..members.len() {
                let mut changed = members.clone();
                changed[index].1 = Json::str("00");
                assert!(
                    load_statement(&Json::Object(changed), CLAIM_FORMAT, &[]).is_err(),
                    "{} member {}",
                    kind.name,
                    members[index].0
                );
                let mut dropped = members.clone();
                dropped.remove(index);
                assert!(load_statement(&Json::Object(dropped), CLAIM_FORMAT, &[]).is_err());
            }
            let mut added = members.clone();
            added.push(("note".into(), Json::str("x")));
            assert!(load_statement(&Json::Object(added), CLAIM_FORMAT, &[]).is_err());
        }
        let (_, statement, _) = statements().remove(0);
        let other = address(8).encode().unwrap();
        let doc = document(
            CLAIM_FORMAT,
            statement_members(&statement, &other).unwrap(),
        );
        let err = load_statement(&doc, CLAIM_FORMAT, &[]).err().unwrap();
        assert!(err.contains("commits to"), "{err}");
    }

    #[test]
    fn base64_is_canonical_and_strict() {
        for (bytes, text) in [
            (&b""[..], ""),
            (b"f", "Zg=="),
            (b"fo", "Zm8="),
            (b"foo", "Zm9v"),
            (b"foob", "Zm9vYg=="),
            (b"fooba", "Zm9vYmE="),
            (b"foobar", "Zm9vYmFy"),
            (&[0xfb, 0xff, 0xfe], "+//+"),
        ] {
            assert_eq!(to_base64(bytes), text);
            assert_eq!(from_base64(text).as_deref(), Some(bytes));
            assert_eq!(base64_len(bytes.len()), text.len());
        }
        for bad in [
            "Zg", "Zg=", "Zg===", "Z===", "Zh==", "Zm9=", "Zm8=Zm8=", "Zm9v\n", " Zm9v", "Zm-v",
            "Zm_v", "=m9v", "Z=9v",
        ] {
            assert_eq!(from_base64(bad), None, "{bad:?}");
        }
        let all: Vec<u8> = (0..=255).collect();
        for len in 0..all.len() {
            assert_eq!(from_base64(&to_base64(&all[..len])).unwrap(), all[..len]);
        }
    }

    #[test]
    fn bip32_paths_parse_and_print() {
        let h = BIP32_HARDENED;
        for (text, path) in [
            ("m", vec![]),
            ("m/0", vec![0]),
            ("m/44'/0'/0'/0/0", vec![44 | h, h, h, 0, 0]),
            ("m/2147483647'/1", vec![0x7fff_ffff | h, 1]),
        ] {
            assert_eq!(parse_path(text).unwrap(), path);
            assert_eq!(format_path(&path), text);
        }
        assert_eq!(parse_path("m/44h/1H").unwrap(), vec![44 | h, 1 | h]);
        for bad in [
            "",
            "44'/0'",
            "m/",
            "m//0",
            "M/0",
            "m/2147483648",
            "m/-1",
            "m/+1",
            "m/0''",
            "m/x",
            "m/0/1/2/3/4/5/6/7/8/9/10",
        ] {
            assert!(parse_path(bad).is_err(), "{bad:?}");
        }
        assert_eq!(parse_path("m/0/1/2/3/4/5/6/7/8/9").unwrap().len(), 10);
    }

    #[test]
    fn registry_keys_are_separated_by_purpose_and_by_anchoring() {
        let seed = Secret32::new([3; 32]);
        let keys = [
            log_key(&seed, true).0,
            log_key(&seed, false).0,
            registry_secret(&seed, b"anchor mac").0,
            registry_secret(&seed, b"identifier").0,
            log_key(&Secret32::new([4; 32]), true).0,
        ];
        for (i, a) in keys.iter().enumerate() {
            for b in &keys[i + 1..] {
                assert_ne!(a, b);
            }
        }
        assert_ne!(registry_id(&seed, &[1; 16]), registry_id(&seed, &[2; 16]));
    }

    /// The bound must hold for every kind (all 15 legacy kinds + all 4 Zcash kinds), and
    /// must be a tight bound on this statement's proof, not a blanket ceiling.
    #[test]
    fn proof_size_bound_covers_every_kind_and_stays_within_a_factor_of_two() {
        for (kind, statement, witness) in statements() {
            let cap = max_proof_bytes(&statement).unwrap();
            let bytes = prove_statement_bytes(&statement, &witness, &[5; 32]).unwrap();
            let len = bytes.len();
            println!("{}: proof {len} bytes, bound {cap} bytes", kind.name);
            assert!(len <= cap, "{}: {len} > {cap}", kind.name);
            assert!(cap < 2 * len, "{}: bound {cap} for {len}", kind.name);
            assert_eq!(verify_statement_bytes(&statement, &bytes), Some(true), "{}", kind.name);
        }
    }
}
