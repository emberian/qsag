//! Ownership of a Zcash transparent P2PKH address.
//!
//! A transparent address is the Bitcoin construction with Zcash's two-byte Base58Check
//! prefix (protocol specification 5.6.1.1): `t1...` on mainnet and `tm...` on testnet
//! carry `HASH160` of a secp256k1 public key. The relations are those of
//! [`crate::hem::relations`]: the lock is [`Lock::P2pkh`] (compressed key, what every
//! wallet has produced for years) or [`Lock::P2pkhUncompressed`] (old imported keys; the
//! payload commits to one encoding of the key, so the statement names it), and the key
//! source is any secp256k1 source of that module. The two this module has constructors
//! for:
//!
//! * **Hidden key** ([`KeySource::Secp256k1Key`]): the prover knows `k` with `HASH160` of
//!   the encoding of `[k] G` equal to the address payload. The public key stays hidden,
//!   so a party that can compute discrete logarithms learns nothing to attack from the
//!   statement; the address must never have been spent from (a spend reveals the key on
//!   chain). This is the P2PKH statement that the discussion of ZIP 2007 (reserved;
//!   `zcash/zips` issue 1302) identifies as recoverable:
//!   `ZKPoK{(privkey): PubKeyHash = Hash160(PubKeyOf(privkey))}`.
//! * **Seed provenance** ([`KeySource::Bip32`] from the seed): the prover knows the
//!   BIP 32 seed whose key at the BIP 44 path `m / 44' / coin_type' / account' / change /
//!   index` (coin type 133 on mainnet, 1 on testnet; ZIP 32, transparent usage of BIP 44)
//!   hashes to the payload. The witness is a hash preimage, so this remains sound when
//!   the public key is known. The relations take seeds of 16 to 64 bytes; ZIP 32 allows
//!   up to 252.
//!
//! What this module adds to the underlying statement:
//!
//! * the network and the address encoding;
//! * its own proof transcript, which absorbs the tag `QSAG.MIGRATE.HEM.ZCASH.TADR/1` and
//!   the network, so a proof for a Bitcoin statement over the same key hash does not
//!   verify here, nor the reverse;
//! * its own registry identifier ([`TransparentStatement::binding`]): the Zcash address,
//!   not the Bitcoin key hash, so migrating the Bitcoin output of a key does not block
//!   its Zcash output. The nullifier is the underlying relation's and contains the
//!   migration domain; a Zcash campaign must use its own domain.
//!
//! P2SH addresses (`t3...`) are not covered: the hash commits to a redeem script, and a
//! statement has to rebuild the exact script bytes in the relation (issue 1302 lists the
//! wrapped P2PKH, wrapped P2PK and multisig forms). Nothing in this crate does that for
//! Zcash's script forms.

use alloc::string::String;
use alloc::vec::Vec;

use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as protocol, ZkHemV2Proof};

use super::encoding::{Network, TransparentKind, decode_transparent, encode_transparent};
use crate::hem::relations::{
    Bip32Root, Credential, HARDENED, KeySource, Lock, OwnershipError, OwnershipStatement,
    OwnershipWitness, PathSpec, credential_identifier, ownership_shape, synthesize_ownership,
};

const STATEMENT_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.ZCASH.TADR/1";
const PROOF_MAGIC: &[u8; 8] = b"QSHEMZT2";

/// Registry tag of a Zcash transparent P2PKH address (network byte, then the payload).
pub const LEGACY_TAG_TRANSPARENT_P2PKH: u8 = 18;

/// SLIP 44 coin type of a network.
pub fn coin_type(network: Network) -> u32 {
    match network {
        Network::Main => 133,
        Network::Test => 1,
    }
}

fn network_byte(network: Network) -> u8 {
    match network {
        Network::Main => 0,
        Network::Test => 1,
    }
}

/// The BIP 44 path `m / 44' / coin_type' / account' / change / index` of a transparent
/// address; `None` unless `account < 2^31`, `change <= 1` and `index < 2^31`.
pub fn bip44_path(network: Network, account: u32, change: u32, index: u32) -> Option<Vec<u32>> {
    (account < HARDENED && change <= 1 && index < HARDENED).then(|| {
        alloc::vec![
            44 | HARDENED,
            coin_type(network) | HARDENED,
            account | HARDENED,
            change,
            index,
        ]
    })
}

/// The encoding of the public key that a P2PKH payload is the `HASH160` of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeyEncoding {
    /// SEC1 compressed, 33 bytes.
    Compressed,
    /// SEC1 uncompressed, `04 || x || y`, 65 bytes.
    Uncompressed,
}

impl KeyEncoding {
    /// The lock of [`crate::hem::relations`] for this encoding.
    pub fn lock(self) -> Lock {
        match self {
            Self::Compressed => Lock::P2pkh,
            Self::Uncompressed => Lock::P2pkhUncompressed,
        }
    }
}

/// Public statement of ownership of a transparent P2PKH address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransparentStatement {
    pub network: Network,
    /// The underlying statement: lock [`Lock::P2pkh`] or [`Lock::P2pkhUncompressed`] with
    /// a secp256k1 key source.
    pub ownership: OwnershipStatement,
}

impl TransparentStatement {
    /// The statement of a witness for a key encoding and any secp256k1 key source.
    pub fn derive(
        network: Network,
        encoding: KeyEncoding,
        source: KeySource,
        witness: &OwnershipWitness,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        Some(Self {
            network,
            ownership: OwnershipStatement::derive(
                encoding.lock(),
                source,
                witness,
                pq_commitment,
                migration_domain,
                epoch,
            )?,
        })
    }

    /// The hidden-key statement of a secp256k1 secret key whose public key the address
    /// hashes in the given encoding.
    pub fn derive_hidden(
        network: Network,
        encoding: KeyEncoding,
        witness: &OwnershipWitness,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        Self::derive(
            network,
            encoding,
            KeySource::Secp256k1Key,
            witness,
            pq_commitment,
            migration_domain,
            epoch,
        )
    }

    /// The seed-provenance statement of a BIP 32 seed at the BIP 44 address path of the
    /// network, with the path public.
    #[allow(clippy::too_many_arguments)]
    pub fn derive_from_seed(
        network: Network,
        witness: &OwnershipWitness,
        account: u32,
        change: u32,
        index: u32,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        Self::derive(
            network,
            KeyEncoding::Compressed,
            KeySource::Bip32 {
                root: Bip32Root::Seed,
                path: PathSpec::Public(bip44_path(network, account, change, index)?),
            },
            witness,
            pq_commitment,
            migration_domain,
            epoch,
        )
    }

    /// The 20-byte payload of the address.
    pub fn hash160(&self) -> Option<[u8; 20]> {
        match (self.ownership.lock, &self.ownership.credential) {
            (Lock::P2pkh | Lock::P2pkhUncompressed, Credential::BitcoinKeyHash(h)) => Some(*h),
            _ => None,
        }
    }

    /// The address string (`t1...` or `tm...`).
    pub fn address(&self) -> Option<String> {
        self.hash160()
            .map(|h| encode_transparent(self.network, TransparentKind::P2pkh, &h))
    }

    /// Whether this statement is about `address`: a P2PKH address of the statement's
    /// network with the statement's payload.
    pub fn is_for_address(&self, address: &str) -> bool {
        match (decode_transparent(address), self.hash160()) {
            (Ok((network, TransparentKind::P2pkh, payload)), Some(h)) => {
                network == self.network && payload == h
            }
            _ => false,
        }
    }

    /// Whether the underlying statement is well formed and its lock is a P2PKH lock.
    pub fn is_well_formed(&self) -> bool {
        self.hash160().is_some() && self.ownership.is_well_formed()
    }

    /// `tag(29) || network || underlying statement`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = STATEMENT_TAG.to_vec();
        out.push(network_byte(self.network));
        out.extend_from_slice(&self.ownership.to_bytes());
        out
    }

    /// Strict inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let rest = bytes.strip_prefix(STATEMENT_TAG.as_slice())?;
        let (&network, rest) = rest.split_first()?;
        let network = match network {
            0 => Network::Main,
            1 => Network::Test,
            _ => return None,
        };
        let statement = Self {
            network,
            ownership: OwnershipStatement::from_bytes(rest)?,
        };
        statement.is_well_formed().then_some(statement)
    }

    fn transcript(&self, regime: Profile) -> Vec<u8> {
        let mut out = self.to_bytes();
        out.push(regime.wire_tag());
        out
    }

    /// The registry identifier of the address: network and payload under
    /// [`LEGACY_TAG_TRANSPARENT_P2PKH`].
    pub fn identifier(&self) -> Option<[u8; 32]> {
        let mut id = [0u8; 21];
        id[0] = network_byte(self.network);
        id[1..].copy_from_slice(&self.hash160()?);
        Some(credential_identifier(LEGACY_TAG_TRANSPARENT_P2PKH, &id))
    }

    /// The binding a verified statement asks the registry to record: the underlying
    /// one with the Zcash address as the legacy identifier.
    #[cfg(feature = "std")]
    pub fn binding(&self) -> Option<crate::hem::registry::MigrationBinding> {
        let mut binding = self.ownership.binding();
        binding.legacy_id = self.identifier()?;
        Some(binding)
    }
}

/// A transparent ownership proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransparentProof {
    pub regime: Profile,
    pub proof: ZkHemV2Proof,
}

impl TransparentProof {
    /// `magic(8) || regime || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = PROOF_MAGIC.to_vec();
        out.push(self.regime.wire_tag());
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    /// Strict decoding against the statement the proof is for.
    pub fn from_bytes(bytes: &[u8], statement: &TransparentStatement) -> Option<Self> {
        let rest = bytes.strip_prefix(PROOF_MAGIC.as_slice())?;
        let (&regime, rest) = rest.split_first()?;
        if !statement.is_well_formed() {
            return None;
        }
        let regime = Profile::from_wire_tag(regime)?;
        let shape = ownership_shape(&statement.ownership)?;
        let proof = ZkHemV2Proof::from_bytes(rest, &shape)?;
        (proof.profile == regime).then_some(Self {
            regime,
            proof,
        })
    }
}

/// Prove a statement. `seed` must be uniform and secret.
pub fn prove_transparent(
    statement: &TransparentStatement,
    witness: &OwnershipWitness,
    regime: Profile,
    seed: &[u8; 32],
) -> Result<TransparentProof, OwnershipError> {
    if !statement.is_well_formed() {
        return Err(OwnershipError::MalformedStatement);
    }
    let (shape, assignment) = synthesize_ownership(&statement.ownership, witness)?;
    let proof = protocol::prove(
        &shape,
        assignment,
        &statement.transcript(regime),
        regime,
        seed,
    )
    .map_err(OwnershipError::Proof)?;
    Ok(TransparentProof { regime, proof })
}

/// Verify a proof against a statement under the regime the verifier requires.
pub fn verify_transparent(
    statement: &TransparentStatement,
    regime: Profile,
    proof: &TransparentProof,
) -> bool {
    if !statement.is_well_formed() || proof.regime != regime {
        return false;
    }
    let (Some(shape), Some(public_inputs)) = (
        ownership_shape(&statement.ownership),
        statement.ownership.public_inputs(),
    ) else {
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

#[cfg(test)]
mod tests {
    use super::super::vectors::unhex;
    use super::*;
    use crate::hem::relations::{OwnershipProof, bip32_derive, prove_ownership, verify_ownership};

    const REGIME: Profile = Profile::TurboShakeJohnson400;
    const PQ: [u8; 32] = [0x51; 32];
    const DOMAIN: [u8; 32] = [0x2c; 32];
    const EPOCH: u64 = 7;
    const KEY: [u8; 32] = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x0f, 0xed, 0xcb, 0xa9, 0x87, 0x65, 0x43,
        0x21, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x01,
    ];

    // zcash-test-vectors unified_address.json: the P2PKH receiver for the root seed
    // 00 01 .. 1f at (account, address index).
    const P2PKH_VECTORS: [(u32, u32, &str); 3] = [
        (0, 0, "7bb83570b8fae146e03c5331a020b1e0892f631d"),
        (0, 3, "a7244a362f49f29644a955cf0039b88a61657861"),
        (0, 4, "e256dcb03e05dde7c91212b47a7461311c415059"),
    ];

    fn seed() -> Vec<u8> {
        (0..32).collect()
    }

    fn hidden(encoding: KeyEncoding, key: &[u8; 32]) -> TransparentStatement {
        TransparentStatement::derive_hidden(
            Network::Main,
            encoding,
            &OwnershipWitness::secp256k1_key(key),
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap()
    }

    fn from_seed(index: u32) -> TransparentStatement {
        TransparentStatement::derive_from_seed(
            Network::Main,
            &OwnershipWitness::seed(&seed()),
            0,
            0,
            index,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap()
    }

    #[test]
    fn seed_addresses_match_the_zcash_vectors() {
        for (account, index, want) in P2PKH_VECTORS {
            assert_eq!(account, 0);
            let st = from_seed(index);
            assert_eq!(st.hash160().unwrap().to_vec(), unhex(want));
            let address = st.address().unwrap();
            assert!(address.starts_with("t1"), "{address}");
            assert!(st.is_for_address(&address));
            assert!(st.is_well_formed());
            assert_eq!(TransparentStatement::from_bytes(&st.to_bytes()), Some(st));
        }
        assert!(bip44_path(Network::Main, 0, 2, 0).is_none());
        assert!(bip44_path(Network::Main, HARDENED, 0, 0).is_none());
        assert_eq!(
            bip44_path(Network::Test, 3, 1, 9).unwrap(),
            [44 | HARDENED, 1 | HARDENED, 3 | HARDENED, 1, 9]
        );
    }

    #[test]
    fn key_encodings_and_addresses() {
        // The secret key 1: HASH160 of the compressed and of the uncompressed generator,
        // the payloads of the Bitcoin addresses 1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH and
        // 1EHNa6Q4Jz2uvNExL497mE43ikXhwF6kZm.
        let mut one = [0u8; 32];
        one[31] = 1;
        assert_eq!(
            hidden(KeyEncoding::Compressed, &one)
                .hash160()
                .unwrap()
                .to_vec(),
            unhex("751e76e8199196d454941c45d1b3a323f1433bd6")
        );
        assert_eq!(
            hidden(KeyEncoding::Uncompressed, &one)
                .hash160()
                .unwrap()
                .to_vec(),
            unhex("91b24bf9f5288532960ac687abb035127b1d28a5")
        );

        let st = hidden(KeyEncoding::Compressed, &KEY);
        let address = st.address().unwrap();
        assert!(address.starts_with("t1"));
        assert!(st.is_for_address(&address));
        let test = TransparentStatement {
            network: Network::Test,
            ..st.clone()
        };
        assert!(test.address().unwrap().starts_with("tm"));
        assert!(!test.is_for_address(&address));
        assert!(!st.is_for_address(&encode_transparent(
            Network::Main,
            TransparentKind::P2sh,
            &st.hash160().unwrap()
        )));
        assert!(!st.is_for_address("t1invalid"));
        assert!(!hidden(KeyEncoding::Uncompressed, &KEY).is_for_address(&address));
        // A zero key has no statement.
        assert!(
            TransparentStatement::derive_hidden(
                Network::Main,
                KeyEncoding::Compressed,
                &OwnershipWitness::secp256k1_key(&[0; 32]),
                PQ,
                DOMAIN,
                EPOCH
            )
            .is_none()
        );
    }

    #[test]
    fn statement_encoding_is_strict() {
        let st = hidden(KeyEncoding::Compressed, &KEY);
        let bytes = st.to_bytes();
        assert_eq!(TransparentStatement::from_bytes(&bytes), Some(st.clone()));
        assert_ne!(
            TransparentStatement {
                network: Network::Test,
                ..st.clone()
            }
            .to_bytes(),
            bytes
        );
        assert_ne!(hidden(KeyEncoding::Uncompressed, &KEY).to_bytes(), bytes);
        assert!(TransparentStatement::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut bad = bytes.clone();
        bad[29] = 2;
        assert!(TransparentStatement::from_bytes(&bad).is_none());
        // The underlying statement's own encoding is not this statement's.
        assert!(TransparentStatement::from_bytes(&st.ownership.to_bytes()).is_none());

        // Locks that are not P2PKH are not transparent Zcash statements.
        for lock in [Lock::Ethereum, Lock::P2shP2wpkh, Lock::TaprootKeyPath] {
            let other = OwnershipStatement::derive(
                lock,
                KeySource::Secp256k1Key,
                &OwnershipWitness::secp256k1_key(&KEY),
                PQ,
                DOMAIN,
                EPOCH,
            )
            .unwrap();
            let wrapped = TransparentStatement {
                network: Network::Main,
                ownership: other,
            };
            assert!(!wrapped.is_well_formed(), "{lock:?}");
            assert!(wrapped.address().is_none());
            assert!(wrapped.identifier().is_none());
            assert!(TransparentStatement::from_bytes(&wrapped.to_bytes()).is_none());
            assert_eq!(
                prove_transparent(
                    &wrapped,
                    &OwnershipWitness::secp256k1_key(&KEY),
                    REGIME,
                    &[3; 32]
                )
                .err(),
                Some(OwnershipError::MalformedStatement)
            );
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn registry_identifier_is_the_zcash_address() {
        let st = hidden(KeyEncoding::Compressed, &KEY);
        let binding = st.binding().unwrap();
        // The same key hash as a Bitcoin credential has another identifier, and so does
        // the testnet address.
        assert_ne!(binding.legacy_id, st.ownership.binding().legacy_id);
        assert_eq!(binding.nullifier, st.ownership.nullifier);
        let test = TransparentStatement {
            network: Network::Test,
            ..st.clone()
        };
        assert_ne!(test.binding().unwrap().legacy_id, binding.legacy_id);
        // Seed provenance and the hidden-key statement of the same address have the same
        // identifier, so the registry accepts only one of them.
        let seed_st = from_seed(0);
        let key = bip32_derive(&seed(), &bip44_path(Network::Main, 0, 0, 0).unwrap()).unwrap();
        let same = hidden(KeyEncoding::Compressed, &key.private_key);
        assert_eq!(seed_st.hash160(), same.hash160());
        assert_eq!(
            seed_st.binding().unwrap().legacy_id,
            same.binding().unwrap().legacy_id
        );
        assert_ne!(
            seed_st.binding().unwrap().exposure,
            same.binding().unwrap().exposure
        );
    }

    #[test]
    fn hidden_key_proof_roundtrip_and_separation() {
        for encoding in [KeyEncoding::Compressed, KeyEncoding::Uncompressed] {
            let w = OwnershipWitness::secp256k1_key(&KEY);
            let st = hidden(encoding, &KEY);
            let proof = prove_transparent(&st, &w, REGIME, &[3; 32]).unwrap();
            let bytes = proof.to_bytes();
            let decoded = TransparentProof::from_bytes(&bytes, &st).unwrap();
            assert_eq!(decoded, proof);
            assert!(verify_transparent(&st, REGIME, &decoded));

            // Network, every field of the underlying statement, the regime.
            let o = &st.ownership;
            let mut other_claim = st.hash160().unwrap();
            other_claim[0] ^= 1;
            for other in [
                TransparentStatement {
                    network: Network::Test,
                    ..st.clone()
                },
                TransparentStatement {
                    ownership: OwnershipStatement {
                        epoch: 8,
                        ..o.clone()
                    },
                    ..st.clone()
                },
                TransparentStatement {
                    ownership: OwnershipStatement {
                        migration_domain: [1; 32],
                        ..o.clone()
                    },
                    ..st.clone()
                },
                TransparentStatement {
                    ownership: OwnershipStatement {
                        pq_commitment: [1; 32],
                        ..o.clone()
                    },
                    ..st.clone()
                },
                TransparentStatement {
                    ownership: OwnershipStatement {
                        nullifier: [1; 32],
                        ..o.clone()
                    },
                    ..st.clone()
                },
                TransparentStatement {
                    ownership: OwnershipStatement {
                        credential: Credential::BitcoinKeyHash(other_claim),
                        ..o.clone()
                    },
                    ..st.clone()
                },
            ] {
                assert!(!verify_transparent(&other, REGIME, &proof), "{other:?}");
            }
            assert!(!verify_transparent(
                &st,
                Profile::CshakeJohnson400,
                &proof
            ));
            for at in [8, bytes.len() / 2, bytes.len() - 1] {
                let mut tampered = bytes.clone();
                tampered[at] ^= 1;
                assert!(
                    TransparentProof::from_bytes(&tampered, &st)
                        .is_none_or(|p| !verify_transparent(&st, REGIME, &p)),
                    "byte {at}"
                );
            }

            // The payload claimed for the other encoding is another statement: the proof
            // does not decode or verify for it, and the key does not produce it.
            let other_lock = match encoding {
                KeyEncoding::Compressed => Lock::P2pkhUncompressed,
                KeyEncoding::Uncompressed => Lock::P2pkh,
            };
            let relabelled = TransparentStatement {
                ownership: OwnershipStatement {
                    lock: other_lock,
                    ..o.clone()
                },
                ..st.clone()
            };
            assert!(
                TransparentProof::from_bytes(&bytes, &relabelled)
                    .is_none_or(|p| !verify_transparent(&relabelled, REGIME, &p))
            );
            assert_eq!(
                prove_transparent(&relabelled, &w, REGIME, &[3; 32]).err(),
                Some(OwnershipError::WitnessMismatch)
            );

            // A Bitcoin proof for the same key hash is not a Zcash proof, and the reverse.
            let bitcoin = prove_ownership(o, &w, REGIME, &[3; 32]).unwrap();
            assert!(verify_ownership(o, REGIME, &bitcoin));
            assert!(TransparentProof::from_bytes(&bitcoin.to_bytes(), &st).is_none());
            let moved = TransparentProof {
                regime: REGIME,
                proof: bitcoin.proof.clone(),
            };
            assert!(!verify_transparent(&st, REGIME, &moved));
            assert!(OwnershipProof::from_bytes(&bytes, o).is_none());
            let as_bitcoin = OwnershipProof {
                regime: REGIME,
                proof: proof.proof.clone(),
            };
            assert!(!verify_ownership(o, REGIME, &as_bitcoin));

            // A witness for another key is refused.
            let mut other_key = KEY;
            other_key[31] ^= 1;
            assert_eq!(
                prove_transparent(
                    &st,
                    &OwnershipWitness::secp256k1_key(&other_key),
                    REGIME,
                    &[3; 32]
                )
                .err(),
                Some(OwnershipError::WitnessMismatch)
            );
        }
    }

    /// The BIP 44 relation has two non-hardened steps and is over `2^20` rows; run with
    /// the measurements on a build host:
    /// `cargo test --release -p qsag-migrate --features std --lib --
    /// hem::zcash::transparent::tests::seed_provenance --ignored --nocapture`
    #[test]
    #[ignore = "a 2^21-row relation"]
    fn seed_provenance_proof_roundtrip() {
        let w = OwnershipWitness::seed(&seed());
        let st = from_seed(3);
        let t = std::time::Instant::now();
        let proof = prove_transparent(&st, &w, REGIME, &[3; 32]).unwrap();
        let prove_s = t.elapsed().as_secs_f64();
        let bytes = proof.to_bytes();
        let decoded = TransparentProof::from_bytes(&bytes, &st).unwrap();
        let t = std::time::Instant::now();
        assert!(verify_transparent(&st, REGIME, &decoded));
        let shape = ownership_shape(&st.ownership).unwrap();
        std::println!(
            "HEM_ZCASH statement=\"transparent-p2pkh seed m/44'/133'/0'/0/3\" regime={} \
             padded_rows=2^{} vars={} prove_s={prove_s:.2} verify_warm_ms={:.1} proof_bytes={}",
            REGIME as u8,
            shape.log_rows,
            shape.num_vars,
            t.elapsed().as_secs_f64() * 1e3,
            bytes.len()
        );
        // Another index of the same seed is another statement.
        assert!(!verify_transparent(&from_seed(4), REGIME, &proof));
        assert_eq!(
            prove_transparent(&st, &OwnershipWitness::seed(&[9; 32]), REGIME, &[3; 32]).err(),
            Some(OwnershipError::WitnessMismatch)
        );
    }
}
