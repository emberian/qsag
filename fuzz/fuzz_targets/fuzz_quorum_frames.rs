// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder and verifier fuzzer for `qsag-quorum`:
//!
//! 1. `wire_channel` frame headers and frames (hostile framing, canonical re-encoding and
//!    valid-frame payload coverage).
//! 2. `access::PersonalLatchAck::from_bytes` and `dzk::decode_elements`.
//! 3. The `HemDynamicShamirQuorum` wire forms: `HemQuorumPublicDirectory::from_bytes_canonical`
//!    (+ `verify_consistency`), `HemShamirCustodianShare::from_vault_bytes`, and the quorum's
//!    `HemJortsPublicKey` / `HemJortsSignature` codecs (+ `verify_hem_jorts_signature`).
//! 4. `volatile_coupon::BaggySig::from_wire_bytes` (+ `baggy_verify`) and the root
//!    certificate codec it embeds, `qsag_core::baggy::BaggySig::from_wire_bytes`
//!    (+ `qsag_core::baggy::baggy_verify`). Linux only, as the module is.
//!
//! `HemSpdzSeedQuorum` has no byte decoder of its own: it publishes the same
//! `HemJortsPublicKey` and `HemJortsSignature` covered here and exchanges its rounds in
//! `wire_channel` frames.
//!
//! Real values built in `LLVMFuzzerInitialize` (the `init:` block) seed sparse-edit
//! mutations, so the verifiers run on inputs one field away from valid.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_core::poseidon2_mpc::{
    HEM_JORTS_PK_BYTES, HemJortsPublicKey, HemJortsSignature, verify_hem_jorts_signature,
};
use qsag_quorum::access::PersonalLatchAck;
use qsag_quorum::dzk::{decode_elements, encode_elements};
use qsag_quorum::wire_channel::{FrameHeader, decode_frame, decode_header, encode_frame};
use qsag_quorum::{HemDynamicShamirQuorum, HemQuorumPublicDirectory, HemShamirCustodianShare};

const QUORUM_MESSAGE: &[u8] = b"fuzz-hem-quorum-message";

struct Fixtures {
    public_key: HemJortsPublicKey,
    directory_wire: Vec<u8>,
    share_wire: Vec<u8>,
    signature_wire: Vec<u8>,
    #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
    coupon: coupon::Fixture,
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        // A staged 2-of-3 quorum with two leaves: its directory, one signature (which burns
        // leaf 0), and a custodian share that still holds leaf 1.
        let mut quorum =
            HemDynamicShamirQuorum::stage([0x41; 32], 2, 3, 2).expect("staged 2-of-3 quorum");
        let public_key = quorum.public_key();
        let directory = quorum.public_directory().clone();
        assert!(directory.verify_consistency());
        let directory_wire = directory.to_bytes();
        assert_eq!(
            HemQuorumPublicDirectory::from_bytes_canonical(&directory_wire).ok(),
            Some(directory)
        );
        let (_, signature) = quorum
            .sign_quorum(&[0, 2], &[0, 1, 2], QUORUM_MESSAGE)
            .expect("quorum signature");
        assert!(verify_hem_jorts_signature(&public_key, QUORUM_MESSAGE, &signature));
        let share_wire = quorum.custodian_shares()[1]
            .to_vault_bytes()
            .expect("custodian share vault bytes");

        Fixtures {
            public_key,
            directory_wire,
            share_wire,
            signature_wire: signature.to_bytes(),
            #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
            coupon: coupon::Fixture::build(),
        }
    })
}

/// `seed` with sparse `(offset: u32 LE, xor: u8)` edits applied.
fn edited(seed: &[u8], edits: &[u8]) -> Vec<u8> {
    let mut candidate = seed.to_vec();
    for edit in edits.as_chunks::<5>().0 {
        let offset = u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize;
        let index = offset % candidate.len();
        candidate[index] ^= edit[4];
    }
    candidate
}

fn check_directory(fx: &Fixtures, bytes: &[u8]) {
    let Ok(directory) = HemQuorumPublicDirectory::from_bytes_canonical(bytes) else {
        return;
    };
    assert_eq!(directory.to_bytes(), bytes);
    let _ = directory.verify_consistency();
    // A directory is the public half of one key: the fixture signature verifies under the
    // key it names exactly when that is the fixture key.
    let signature =
        HemJortsSignature::from_bytes_canonical(&fx.signature_wire).expect("seed signature");
    assert_eq!(
        verify_hem_jorts_signature(&directory.pk, QUORUM_MESSAGE, &signature),
        directory.pk == fx.public_key
    );
}

fn check_share(bytes: &[u8]) {
    let Ok(share) = HemShamirCustodianShare::from_vault_bytes(bytes) else {
        return;
    };
    let reencoded = share.to_vault_bytes().expect("decoded share re-encodes");
    assert_eq!(reencoded, bytes);
}

fn check_signature(fx: &Fixtures, bytes: &[u8]) {
    let Some(signature) = HemJortsSignature::from_bytes_canonical(bytes) else {
        return;
    };
    assert_eq!(signature.to_bytes(), bytes);
    // One signature was ever made with this key, on one message.
    let verified = verify_hem_jorts_signature(&fx.public_key, QUORUM_MESSAGE, &signature);
    assert_eq!(verified, bytes == fx.signature_wire, "forged quorum signature");
    assert!(!verify_hem_jorts_signature(&fx.public_key, b"another message", &signature));
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
mod coupon {
    use qsag_core::baggy::{
        BaggyParams, BaggyPublicKey, BaggySig as RootSignature, baggy_reference_keygen,
        baggy_reference_sign, baggy_verify as verify_root,
    };
    use qsag_core::tsw_baggy::PqSecretKey;
    use qsag_quorum::quorum_jorts::WOTS_CHAINS;
    use qsag_quorum::volatile_coupon::{BaggySig, CouponDescriptor, baggy_verify};

    const PARAMS: BaggyParams = BaggyParams::TEST_SMALL;
    const COUPON_MESSAGE: &[u8] = b"fuzz-coupon-message";

    pub struct Fixture {
        parent: BaggyPublicKey,
        certificate_message: Vec<u8>,
        pub certificate_wire: Vec<u8>,
        /// A coupon signature whose root certificate is real and whose one-time opening is
        /// not: it decodes, and must not verify.
        pub coupon_wire: Vec<u8>,
    }

    impl Fixture {
        pub fn build() -> Self {
            let secret = PqSecretKey {
                sk_seed: [0x91; 32],
                sk_prf: [0x92; 32],
                pk_seed: [0x93; 32],
            };
            let parent = baggy_reference_keygen(&PARAMS, &secret).expect("root key");
            let descriptor = CouponDescriptor {
                parent,
                threshold: 2,
                parties: 3,
                members: vec![0, 2],
                pk_seed: [0x94; 32],
                leaf: 7,
                chain_ends: (0..WOTS_CHAINS as u8).map(|i| [i; 32]).collect(),
                expires_at: u64::MAX,
            };
            let certificate_message = descriptor.certificate_message().expect("descriptor");
            let certificate = baggy_reference_sign(&PARAMS, &secret, &parent, &certificate_message)
                .expect("root certificate");
            assert!(verify_root(&PARAMS, &parent, &certificate_message, &certificate));
            let certificate_wire = certificate.to_wire_bytes();

            // The coupon wire form, assembled as its documentation states it.
            let mut coupon_wire = Vec::new();
            coupon_wire.extend_from_slice(&(descriptor.threshold as u16).to_be_bytes());
            coupon_wire.extend_from_slice(&(descriptor.parties as u16).to_be_bytes());
            for member in &descriptor.members {
                coupon_wire.extend_from_slice(&member.to_be_bytes());
            }
            coupon_wire.extend_from_slice(&descriptor.pk_seed);
            coupon_wire.extend_from_slice(&descriptor.leaf.to_be_bytes());
            coupon_wire.extend_from_slice(&descriptor.expires_at.to_be_bytes());
            coupon_wire.extend_from_slice(descriptor.chain_ends.as_flattened());
            coupon_wire.extend_from_slice(&(certificate_wire.len() as u32).to_be_bytes());
            coupon_wire.extend_from_slice(&certificate_wire);
            coupon_wire.extend_from_slice(&0u32.to_be_bytes());
            coupon_wire.extend_from_slice(&[0x5A; 32 * WOTS_CHAINS]);
            let decoded = BaggySig::from_wire_bytes(&parent, &PARAMS, &coupon_wire);
            assert!(decoded.is_ok(), "certified coupon decodes");

            Self {
                parent,
                certificate_message,
                certificate_wire,
                coupon_wire,
            }
        }

        /// A root certificate: canonical re-encoding, then the verifier. Only the real
        /// certificate verifies; the key signed nothing else.
        pub fn check_certificate(&self, bytes: &[u8]) {
            let Some(certificate) = RootSignature::from_wire_bytes(&PARAMS, bytes) else {
                return;
            };
            assert_eq!(certificate.to_wire_bytes(), bytes);
            let verified =
                verify_root(&PARAMS, &self.parent, &self.certificate_message, &certificate);
            assert_eq!(verified, bytes == self.certificate_wire, "forged root certificate");
            assert!(!verify_root(&PARAMS, &self.parent, COUPON_MESSAGE, &certificate));
        }

        /// A coupon signature. Decoding already verifies the embedded certificate against
        /// the pinned root key; no opening was ever produced, so none verifies.
        pub fn check_coupon(&self, bytes: &[u8]) {
            let Ok(signature) = BaggySig::from_wire_bytes(&self.parent, &PARAMS, bytes) else {
                return;
            };
            let reencoded = signature.to_wire_bytes().expect("decoded coupon re-encodes");
            assert_eq!(reencoded, bytes);
            assert!(!baggy_verify(&self.parent, &PARAMS, COUPON_MESSAGE, &signature));
            // A key that did not certify the coupon refuses it at decode.
            let stranger = BaggyPublicKey {
                pk_seed: self.parent.pk_seed,
                pk_root: [0x77; 32],
            };
            assert!(BaggySig::from_wire_bytes(&stranger, &PARAMS, bytes).is_err());
        }
    }
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    // 1. `wire_channel` framing.
    let _ = decode_header(data);
    if let Ok((header, payload)) = decode_frame(data) {
        assert_eq!(encode_frame(&header, payload).unwrap(), data);
    }
    let header = FrameHeader { session_id: [0x51; 32], from: 0, to: 1,
        round_tag: 3, seq: data.first().copied().unwrap_or(0) as u64 };
    if let Ok(encoded) = encode_frame(&header, data) {
        let (decoded, payload) = decode_frame(&encoded).unwrap();
        assert_eq!(decoded, header);
        assert_eq!(payload, data);
        let mut invalid = encoded;
        invalid.push(0);
        assert!(decode_frame(&invalid).is_err());
    }

    // 2. Fixed-size acknowledgements and field-element vectors.
    if let Some(ack) = PersonalLatchAck::from_bytes(data) {
        assert_eq!(ack.to_bytes().as_slice(), data);
    }
    let count = data.len() / 16;
    match decode_elements(data, count) {
        Some(elements) => {
            assert_eq!(elements.len(), count);
            assert_eq!(encode_elements(&elements), data);
        }
        None => assert!(!data.len().is_multiple_of(16)),
    }
    assert!(decode_elements(data, count + 1).is_none());

    // 3. Hem quorum wire forms from raw bytes.
    check_directory(fx, data);
    check_share(data);
    check_signature(fx, data);
    if let Some(raw) = data.first_chunk::<HEM_JORTS_PK_BYTES>()
        && let Some(pk) = HemJortsPublicKey::from_bytes_canonical(raw)
    {
        assert_eq!(&pk.to_bytes(), raw);
        // The fixture signature is bound to the fixture key.
        let signature =
            HemJortsSignature::from_bytes_canonical(&fx.signature_wire).expect("seed signature");
        assert_eq!(
            verify_hem_jorts_signature(&pk, QUORUM_MESSAGE, &signature),
            pk == fx.public_key
        );
    }
    #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
    {
        fx.coupon.check_certificate(data);
        fx.coupon.check_coupon(data);
    }

    // 4. Sparse edits of the real values: `[0xed, kind]` then `(offset, xor)` records.
    if let [0xed, kind, edits @ ..] = data {
        match kind % 5 {
            0 => check_directory(fx, &edited(&fx.directory_wire, edits)),
            1 => check_share(&edited(&fx.share_wire, edits)),
            2 => check_signature(fx, &edited(&fx.signature_wire, edits)),
            #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
            3 => fx.coupon.check_certificate(&edited(&fx.coupon.certificate_wire, edits)),
            #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
            4 => fx.coupon.check_coupon(&edited(&fx.coupon.coupon_wire, edits)),
            _ => {}
        }
    }
});
