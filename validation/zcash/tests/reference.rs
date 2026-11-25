//! Byte-for-byte agreement of the native Zcash layer with the reference crates, and
//! acceptance by the recovery statement of notes created by the real `orchard` code.

use qsag_migrate::hem::zcash::encoding::{
    Network, Receiver, TransparentKind, decode_unified_address, encode_transparent,
    encode_unified_address,
};
use qsag_migrate::hem::zcash::orchard as native;
use qsag_migrate::hem::zcash::pallas::{Fp, Fq};
use qsag_migrate::hem::zcash::recovery::{
    KeySource, KeyWitness, RecoveryStatement, RecoveryWitness, synthesize_recovery,
};
use qsag_migrate::hem::zcash::rehash;
use qsag_validation_zcash::Stream;

use ff::PrimeField;
use incrementalmerkletree::{Hashable, Level};
use orchard::keys::{FullViewingKey, Scope, SpendAuthorizingKey, SpendingKey};
use orchard::note::{ExtractedNoteCommitment, RandomSeed, Rho};
use orchard::primitives::redpallas;
use orchard::tree::{MerkleHashOrchard, MerklePath};
use orchard::value::NoteValue;
use orchard::{Address, Note, NoteVersion};
use pasta_curves::pallas;
use zcash_address::ZcashAddress;
use zcash_address::unified::{self, Encoding};
use zcash_protocol::consensus::NetworkType;

const SCOPES: [(Scope, native::Scope); 2] = [
    (Scope::External, native::Scope::External),
    (Scope::Internal, native::Scope::Internal),
];

fn spending_key(stream: &mut Stream) -> ([u8; 32], SpendingKey) {
    loop {
        let bytes: [u8; 32] = stream.bytes();
        if let Some(sk) = SpendingKey::from_bytes(bytes).into_option() {
            return (bytes, sk);
        }
    }
}

/// A note of the reference implementation and the same note in the native layer.
fn note(stream: &mut Stream, recipient: Address, version: NoteVersion) -> (Note, native::Note) {
    loop {
        let mut rho_bytes: [u8; 32] = stream.bytes();
        rho_bytes[31] &= 0x3f;
        let Some(rho) = Rho::from_bytes(&rho_bytes).into_option() else {
            continue;
        };
        let rseed_bytes: [u8; 32] = stream.bytes();
        let Some(rseed) = RandomSeed::from_bytes(rseed_bytes, &rho).into_option() else {
            continue;
        };
        let value = stream.next_u64() >> 11;
        let Some(reference) =
            Note::from_parts(recipient, NoteValue::from_raw(value), rho, rseed, version)
                .into_option()
        else {
            continue;
        };
        let ours = native::Note {
            recipient: recipient.to_raw_address_bytes(),
            value,
            rho: Fp::from_bytes(&rho_bytes).unwrap(),
            rseed: rseed_bytes,
            version: match version {
                NoteVersion::V2 => native::NoteVersion::V2,
                NoteVersion::V3 => native::NoteVersion::V3,
            },
        };
        return (reference, ours);
    }
}

#[test]
fn keys_and_addresses_agree() {
    let mut stream = Stream(1);
    for _ in 0..40 {
        let (bytes, sk) = spending_key(&mut stream);
        let reference = FullViewingKey::from(&sk);
        let ours = native::FullViewingKey::from_spending_key(&bytes).expect("a valid key");
        assert_eq!(ours.to_bytes(), reference.to_bytes());
        assert_eq!(
            native::FullViewingKey::from_bytes(&reference.to_bytes()).as_ref(),
            Some(&ours)
        );

        // The spend authorizing key has the reference's verification key.
        let ask = native::spend_authorizing_key(&bytes).unwrap();
        let reference_ask = SpendAuthorizingKey::from(&sk);
        let vk: [u8; 32] =
            (&redpallas::VerificationKey::from(&reference_ask.randomize(&pallas::Scalar::zero())))
                .into();
        assert_eq!(native::redpallas_public_key(&ask), vk);

        for (scope, our_scope) in SCOPES {
            assert_eq!(
                ours.ivk(our_scope).unwrap().to_bytes(),
                reference.to_ivk(scope).to_bytes()[32..]
            );
            for index in [0u32, 1, 2, 77, u32::MAX] {
                let mut index_bytes = [0u8; 11];
                index_bytes[..4].copy_from_slice(&index.to_le_bytes());
                let address = reference.address_at(index, scope);
                let d = ours.diversifier(&index_bytes, our_scope);
                assert_eq!(d, *address.diversifier().as_array());
                assert_eq!(
                    ours.address(&d, our_scope).unwrap(),
                    address.to_raw_address_bytes()
                );
            }
        }
    }
    // The two implementations discard the same spending keys.
    for _ in 0..200 {
        let bytes: [u8; 32] = stream.bytes();
        assert_eq!(
            SpendingKey::from_bytes(bytes).into_option().is_some(),
            native::FullViewingKey::from_spending_key(&bytes).is_some()
        );
    }
}

#[test]
fn zip32_account_keys_agree() {
    let mut stream = Stream(2);
    for case in 0..12u32 {
        let seed: [u8; 64] = stream.bytes();
        let seed = &seed[..32 + (case as usize * 3) % 33];
        for (coin_type, account) in [(133u32, 0u32), (133, 5), (1, 0), (1, 0x7fff_ffff)] {
            let reference = SpendingKey::from_zip32_seed(
                seed,
                coin_type,
                zip32::AccountId::try_from(account).unwrap(),
            )
            .unwrap();
            let ours = native::ExtendedSpendingKey::account(seed, coin_type, account).unwrap();
            assert_eq!(&ours.sk, reference.to_bytes());
            let path = [
                32 | native::ZIP32_HARDENED,
                coin_type | native::ZIP32_HARDENED,
                account | native::ZIP32_HARDENED,
            ];
            assert_eq!(
                native::zip32_spending_key(seed, &path).unwrap(),
                *reference.to_bytes()
            );
        }
    }
}

#[test]
fn note_commitments_and_nullifiers_agree() {
    let mut stream = Stream(3);
    for i in 0..24 {
        let (bytes, sk) = spending_key(&mut stream);
        let fvk = FullViewingKey::from(&sk);
        let ours = native::FullViewingKey::from_spending_key(&bytes).unwrap();
        let (scope, _) = SCOPES[i % 2];
        let recipient = fvk.address_at(i as u32, scope);
        for version in [NoteVersion::V2, NoteVersion::V3] {
            let (reference, native_note) = note(&mut stream, recipient, version);
            let cmx = ExtractedNoteCommitment::from(reference.commitment()).to_bytes();
            assert_eq!(native_note.cmx().unwrap().to_bytes(), cmx, "{version:?}");
            assert_eq!(
                native_note.nullifier(&ours.nk).unwrap().to_bytes(),
                reference.nullifier(&fvk).to_bytes(),
                "{version:?}"
            );
        }
        // The two versions of the same note fields commit differently.
        let (_, v2) = note(&mut Stream(100 + i as u64), recipient, NoteVersion::V2);
        let (_, v3) = note(&mut Stream(100 + i as u64), recipient, NoteVersion::V3);
        assert_eq!((v2.value, v2.rho, v2.rseed), (v3.value, v3.rho, v3.rseed));
        assert_ne!(v2.cmx(), v3.cmx());
    }
}

#[test]
fn merkle_tree_agrees() {
    let mut stream = Stream(4);
    let leaf = |stream: &mut Stream| loop {
        let mut b: [u8; 32] = stream.bytes();
        b[31] &= 0x3f;
        if let Some(h) = MerkleHashOrchard::from_bytes(&b).into_option() {
            return (h, Fp::from_bytes(&b).unwrap());
        }
    };
    // Node hashes at every level.
    for level in 0..32u8 {
        let ((a, fa), (b, fb)) = (leaf(&mut stream), leaf(&mut stream));
        assert_eq!(
            MerkleHashOrchard::combine(Level::from(level), &a, &b).to_bytes(),
            native::merkle_crh(level, &fa, &fb).to_bytes()
        );
    }
    assert_eq!(
        MerkleHashOrchard::empty_leaf().to_bytes(),
        native::uncommitted_leaf().to_bytes()
    );
    let empty = native::empty_roots();
    assert_eq!(
        MerkleHashOrchard::empty_root(Level::from(32)).to_bytes(),
        empty[32].to_bytes()
    );
    // Roots from random paths.
    for _ in 0..3 {
        let position = stream.next_u64() as u32;
        let (cmx, fcmx) = leaf(&mut stream);
        let path: Vec<(MerkleHashOrchard, Fp)> = (0..32).map(|_| leaf(&mut stream)).collect();
        let reference_path: [MerkleHashOrchard; 32] = core::array::from_fn(|i| path[i].0);
        let ours: Vec<Fp> = path.iter().map(|p| p.1).collect();
        let cmx = ExtractedNoteCommitment::from_bytes(&cmx.to_bytes()).unwrap();
        assert_eq!(
            MerklePath::from_parts(position, reference_path)
                .root(cmx)
                .to_bytes(),
            native::merkle_root(&fcmx, position, &ours).to_bytes()
        );
    }
}

#[test]
fn redpallas_signatures_cross_verify() {
    let mut stream = Stream(5);
    for _ in 0..8 {
        let (bytes, sk) = spending_key(&mut stream);
        let ask = native::spend_authorizing_key(&bytes).unwrap();
        let alpha_bytes: [u8; 64] = stream.bytes();
        let alpha = Fq::from_bytes_wide(&alpha_bytes);
        let reference_alpha = pallas::Scalar::from_repr(alpha.to_bytes()).unwrap();
        let signing = SpendAuthorizingKey::from(&sk).randomize(&reference_alpha);
        let rk: [u8; 32] = (&redpallas::VerificationKey::from(&signing)).into();
        let randomized = ask + alpha;
        assert_eq!(native::redpallas_public_key(&randomized), rk);
        let message: [u8; 40] = stream.bytes();

        // Ours verifies under the reference.
        let ours = native::redpallas_sign(&randomized, &message, &stream.bytes());
        let vk = redpallas::VerificationKey::<redpallas::SpendAuth>::try_from(rk).unwrap();
        assert!(
            vk.verify(&message, &redpallas::Signature::from(ours))
                .is_ok()
        );
        // The reference's verifies under ours.
        let rng = rand::rand_core::UnwrapErr(rand::rngs::SysRng);
        let theirs: [u8; 64] = (&signing.sign(rng, &message)).into();
        assert!(native::redpallas_verify(&rk, &message, &theirs));
        let mut bad = theirs;
        bad[5] ^= 1;
        assert!(!native::redpallas_verify(&rk, &message, &bad));
        assert!(
            vk.verify(&message, &redpallas::Signature::from(bad))
                .is_err()
        );
    }
}

#[test]
fn address_encodings_agree() {
    let mut stream = Stream(6);
    for i in 0..8u32 {
        let (_, sk) = spending_key(&mut stream);
        let orchard_receiver = FullViewingKey::from(&sk)
            .address_at(i, Scope::External)
            .to_raw_address_bytes();
        let p2pkh: [u8; 20] = stream.bytes();

        for (network, reference_network) in [
            (Network::Main, NetworkType::Main),
            (Network::Test, NetworkType::Test),
        ] {
            // Unified address with an Orchard receiver, with and without a transparent one.
            for with_transparent in [false, true] {
                let mut ours = vec![Receiver::Orchard(orchard_receiver)];
                let mut items = vec![unified::Uitem::Data(unified::Receiver::Orchard(
                    orchard_receiver,
                ))];
                if with_transparent {
                    ours.push(Receiver::P2pkh(p2pkh));
                    items.push(unified::Uitem::Data(unified::Receiver::P2pkh(p2pkh)));
                }
                let reference = unified::Address::try_from_items(unified::Revision::R0, items)
                    .unwrap()
                    .encode(&reference_network);
                let encoded = encode_unified_address(network, &ours).unwrap();
                assert_eq!(encoded, reference);
                let (decoded_network, decoded) = decode_unified_address(&reference).unwrap();
                assert_eq!(decoded_network, network);
                assert!(decoded.contains(&Receiver::Orchard(orchard_receiver)));
                assert!(ZcashAddress::try_from_encoded(&encoded).is_ok());
            }
            // Transparent addresses.
            let t = encode_transparent(network, TransparentKind::P2pkh, &p2pkh);
            let parsed = ZcashAddress::try_from_encoded(&t).unwrap();
            assert_eq!(parsed.encode(), t);
            assert!(parsed.is_transparent_only());
        }
    }
}

/// A version 3 note made by the reference implementation is accepted by the recovery
/// statement, with the reference's nullifier; a version 2 note is not a recoverable note.
#[test]
fn reference_notes_and_the_recovery_statement() {
    let mut stream = Stream(7);
    let (bytes, sk) = spending_key(&mut stream);
    let fvk = FullViewingKey::from(&sk);
    for (i, (scope, our_scope)) in SCOPES.into_iter().enumerate() {
        let recipient = fvk.address_at(3u32, scope);
        let (reference, native_note) = note(&mut stream, recipient, NoteVersion::V3);
        let witness = recovery_witness(&mut stream, bytes, native_note, our_scope, 9 + i as u32);
        let statement =
            RecoveryStatement::derive(&KeySource::SpendingKey, &witness, [1; 32], [2; 32], 3)
                .expect("a version 3 note of the key");
        assert_eq!(statement.nullifier, reference.nullifier(&fvk).to_bytes());
        assert_eq!(statement.value, reference.value().inner());

        let (_, legacy) = note(&mut stream, recipient, NoteVersion::V2);
        let witness = recovery_witness(&mut stream, bytes, legacy, our_scope, 9);
        assert!(
            RecoveryStatement::derive(&KeySource::SpendingKey, &witness, [1; 32], [2; 32], 3)
                .is_none()
        );
    }
}

fn recovery_witness(
    stream: &mut Stream,
    sk: [u8; 32],
    note: native::Note,
    scope: native::Scope,
    position: u32,
) -> RecoveryWitness {
    let mut leaves: Vec<[u8; 32]> = (0..position + 2).map(|_| stream.bytes()).collect();
    leaves[position as usize] =
        rehash::leaf_hash(&note.cmx().unwrap().to_bytes(), &note.rho.to_bytes());
    let (path, _) = rehash::witness(&leaves, position).unwrap();
    RecoveryWitness {
        key: KeyWitness::SpendingKey(sk),
        internal: scope == native::Scope::Internal,
        alpha: Fq::from_bytes_wide(&stream.bytes()).to_bytes(),
        note,
        position,
        path,
    }
}

/// The relation itself on a note of the reference implementation. Builds a relation of
/// 2^22 rows (about 20 GiB): run on a build host.
#[test]
#[ignore = "builds a 2^22-row relation"]
fn reference_note_satisfies_the_relation() {
    let mut stream = Stream(8);
    let (bytes, sk) = spending_key(&mut stream);
    let fvk = FullViewingKey::from(&sk);
    let recipient = fvk.address_at(1u32, Scope::External);
    let (reference, native_note) = note(&mut stream, recipient, NoteVersion::V3);
    let witness = recovery_witness(&mut stream, bytes, native_note, native::Scope::External, 4);
    let statement =
        RecoveryStatement::derive(&KeySource::SpendingKey, &witness, [1; 32], [2; 32], 3).unwrap();
    assert_eq!(statement.nullifier, reference.nullifier(&fvk).to_bytes());
    let (shape, assignment) = synthesize_recovery(&statement, &witness).unwrap();
    assert!(shape.is_satisfied(&assignment));
    // The nullifier of the reference implementation is the only one accepted.
    let mut bad = assignment.clone();
    let nullifier_bit = 1 + 256;
    bad[nullifier_bit] = if bad[nullifier_bit] == bad[0] {
        bad[0] - bad[0]
    } else {
        bad[0]
    };
    assert!(!shape.is_satisfied(&bad));
}
