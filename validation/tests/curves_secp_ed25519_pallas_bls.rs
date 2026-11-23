// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Legacy Curve & Post-Quantum Migration Ceremonies Differential Validation
//!
//! Cross-validates `qsag-migrate` (`secp256k1_ct`, `ed25519_ct`, `legacy`, `pallas`, `bls12_381`,
//! and `zk-Hem v2` ownership proofs) against independent upstream ecosystem
//! cryptography crates:
//! - `k256` + `sha2` + `ripemd` + `sha3` + `hmac` (Bitcoin P2PKH/P2WPKH `HASH160`, BIP-341 Taproot
//!   tweaked x-only key, Ethereum `Keccak256` 20-byte EOA, and hardened BIP-32 derivation),
//! - `ed25519-dalek` + `curve25519-dalek` (RFC 8032 SHA-512 clamping, Edwards basepoint scalar
//!   multiplication, and hardened SLIP-0010 derivation),
//! - `pasta_curves` + `group` + `ff` (Zcash Orchard `Pallas` `Fp`/`Fq` fields, `GroupHash`
//!   `SpendAuthG` generator, `[ask] SpendAuthG` `ak`, and `RedPallas` rerandomized `rk`),
//! - `blstrs` (Ethereum Beacon Chain `BLS12-381` `Fr`/`G1`, 48-byte IETF compressed `G1` keys,
//!   `0x00` withdrawal credentials, subgroup membership checks, and torsion rejection).

use blstrs::{G1Affine as BlsRefG1Affine, G1Projective as BlsRefG1Proj, Scalar as BlsRefScalar};
use curve25519_dalek::edwards::EdwardsPoint;
use ed25519_dalek::SigningKey as DalekEdSigningKey;
use ff::{Field as FfField, FromUniformBytes, PrimeField};
use group::{Group, GroupEncoding};
use hmac::{Hmac, Mac};
use k256::elliptic_curve::sec1::ToEncodedPoint;
use k256::{ProjectivePoint as K256Proj, Scalar as K256Scalar, SecretKey as K256SecretKey};
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::pallas::{
    Base as PallasRefFp, Point as PallasRefPoint, Scalar as PallasRefFq,
};
use proptest::prelude::*;
use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_migrate::{
    BlsG1Point, BlsOwnershipWitness, BlsValidatorCommitment, FpBls381, FpPallas, FqPallas,
    ClassicalCommitmentKind, ClassicalOwnershipWitness, FrBls381, HardenedChainStep,
    PallasCommitmentKind, PallasOwnershipWitness, PallasPoint,
    compute_bls_0x00_withdrawal_credentials, ed25519_ct::public_key_from_clamped_scalar,
    hem::{
        registry::pq_commitment,
        relations::{
            Credential, KeySource, Lock, OwnershipError, OwnershipProof, OwnershipStatement,
            OwnershipWitness, prove_ownership, verify_ownership,
        },
    },
    secp256k1_ct::SecpPoint,
};
use ripemd::Ripemd160;
use sha2::{Digest as Sha2Digest, Sha256, Sha512};
use sha3::Keccak256;

type HmacSha512 = Hmac<Sha512>;

fn sample_pq_destination(tag_seed: &[u8]) -> QsagAddress {
    QsagAddress::from_pubkey_poseidon2(
        "qsp",
        WitnessSuiteTag::MlDsa65,
        KeyIdentityKind::SingleOrThreshold,
        tag_seed,
    )
    .expect("valid Poseidon2 v2 PQ destination address")
}

/// Independent BIP-340 / BIP-341 tagged SHA-256 `SHA256(SHA256(tag) || SHA256(tag) || msg)`
/// using upstream RustCrypto `sha2::Sha256`.
fn ref_tagged_sha256(tag: &[u8], msg: &[u8]) -> [u8; 32] {
    let tag_hash = Sha256::digest(tag);
    let mut h = Sha256::new();
    h.update(tag_hash);
    h.update(tag_hash);
    h.update(msg);
    h.finalize().into()
}

/// Independent Bitcoin `HASH160 = RIPEMD160(SHA256(pk33))` using upstream `sha2` + `ripemd`.
fn ref_bitcoin_hash160(pk_compressed_33: &[u8]) -> [u8; 20] {
    let sha = Sha256::digest(pk_compressed_33);
    Ripemd160::digest(sha).into()
}

/// Independent BIP-341 key-path Taproot tweaked x-only output key using upstream `k256` + `sha2`.
fn ref_taproot_tweaked_xonly(sk: &K256SecretKey) -> [u8; 32] {
    let d: K256Scalar = *sk.to_nonzero_scalar().as_ref();
    let internal_aff = (K256Proj::GENERATOR * d).to_affine();
    let internal_enc = internal_aff.to_encoded_point(false);
    let x_bytes: [u8; 32] = internal_enc
        .x()
        .expect("affine generator multiple has x")
        .as_slice()
        .try_into()
        .unwrap();
    let y_bytes: [u8; 32] = internal_enc
        .y()
        .expect("affine generator multiple has y")
        .as_slice()
        .try_into()
        .unwrap();
    let d_even = if (y_bytes[31] & 1) == 1 { -d } else { d };
    let tweak_bytes = ref_tagged_sha256(b"TapTweak", &x_bytes);
    let tweak = Option::<K256Scalar>::from(K256Scalar::from_repr(tweak_bytes.into()))
        .expect("TapTweak digest < secp256k1 order");
    let out_aff = (K256Proj::GENERATOR * (d_even + tweak)).to_affine();
    let out_enc = out_aff.to_encoded_point(false);
    out_enc
        .x()
        .expect("tweaked output point is non-identity")
        .as_slice()
        .try_into()
        .unwrap()
}

/// Independent Ethereum 20-byte EOA address `Keccak256(uncompressed_pk_64)[12..32]`
/// using upstream `k256` + `sha3::Keccak256`.
fn ref_ethereum_keccak20(sk: &K256SecretKey) -> [u8; 20] {
    let pub_enc = sk.public_key().to_encoded_point(false);
    let uncomp_bytes = pub_enc.as_bytes();
    assert_eq!(uncomp_bytes.len(), 65);
    assert_eq!(uncomp_bytes[0], 0x04);
    let digest = Keccak256::digest(&uncomp_bytes[1..65]);
    digest[12..32].try_into().unwrap()
}

// ============================================================================
// 5A. Property-Based Differential Tests: `secp256k1`, `Ed25519`, `BIP-32`, `SLIP-0010`
// ============================================================================

/// Order `n` of the secp256k1 group (SEC 2 §2.4.1), big-endian.
const SECP256K1_N_BE: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
    0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
];

/// Order `r` of the BLS12-381 prime-order subgroups, big-endian.
const BLS12_381_R_BE: [u8; 32] = [
    0x73, 0xED, 0xA7, 0x53, 0x29, 0x9D, 0x7D, 0x48, 0x33, 0x39, 0xD8, 0x08, 0x09, 0xA1, 0xD8, 0x05,
    0x53, 0xBD, 0xA4, 0x02, 0xFF, 0xFE, 0x5B, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x01,
];

/// Big-endian 256-bit `value + delta` for a small signed `delta` (panics on overflow).
fn be256_offset(value: &[u8; 32], delta: i8) -> [u8; 32] {
    let mut out = *value;
    let mut carry = i16::from(delta);
    for byte in out.iter_mut().rev() {
        let t = i16::from(*byte) + carry;
        *byte = t.rem_euclid(256) as u8;
        carry = t.div_euclid(256);
    }
    assert_eq!(carry, 0, "offset left the 256-bit range");
    out
}

fn be256_small(value: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[31] = value;
    out
}

/// Uniform scalar in `[1, order - 1]` by rejection: 32 uniform bytes are kept exactly when
/// they are nonzero and below `order` (big-endian arrays order as the integers they encode).
/// No byte is masked, reduced or forced, so every valid scalar is equally likely.
fn uniform_nonzero_scalar_below(order_be: [u8; 32]) -> impl Strategy<Value = [u8; 32]> {
    any::<[u8; 32]>().prop_filter("scalar outside [1, order - 1]", move |bytes| {
        *bytes != [0u8; 32] && *bytes < order_be
    })
}

/// secp256k1 key `sk_be` in `[1, n - 1]`: fixed-base multiplication, the three commitment
/// kinds and hardened BIP-32 derivation against `k256`, `sha2`, `ripemd`, `sha3`, `hmac`.
fn check_secp256k1_scalar_against_k256(
    sk_be: [u8; 32],
    chain_code: [u8; 32],
    child_low: u32,
) -> Result<(), TestCaseError> {
    let ref_sk = K256SecretKey::from_slice(&sk_be).expect("canonical nonzero secp256k1 scalar");
    let ref_pk = ref_sk.public_key();
    let ref_comp33: [u8; 33] = ref_pk.to_encoded_point(true).as_bytes().try_into().unwrap();
    let ref_uncomp65 = ref_pk.to_encoded_point(false);
    let ref_uncomp64: [u8; 64] = ref_uncomp65.as_bytes()[1..65].try_into().unwrap();

    // 1. Constant-time generator multiplication compressed + uncompressed match `k256`
    let mut qsag_pt = SecpPoint::generator_mul_ct(&sk_be);
    prop_assert_eq!(qsag_pt.to_compressed_bytes(), Some(ref_comp33));
    prop_assert_eq!(qsag_pt.to_uncompressed_64(), Some(ref_uncomp64));
    qsag_pt.wipe();

    // 2. All three secp256k1 commitment kinds match independent `k256` + `sha2`/`ripemd`/`sha3`
    let wit = ClassicalOwnershipWitness::from_raw_secret(sk_be);
    prop_assert_eq!(
        wit.compute_bitcoin_hash160(),
        Some(ClassicalCommitmentKind::BitcoinHash160(ref_bitcoin_hash160(&ref_comp33)))
    );
    prop_assert_eq!(
        wit.compute_taproot_tweaked_xonly(),
        Some(ClassicalCommitmentKind::BitcoinTaprootXOnly(ref_taproot_tweaked_xonly(&ref_sk)))
    );
    prop_assert_eq!(
        wit.compute_ethereum_keccak20(),
        Some(ClassicalCommitmentKind::EthereumKeccak20(ref_ethereum_keccak20(&ref_sk)))
    );

    // 3. Hardened BIP-32 child derivation matches independent `Hmac<Sha512>` + `k256::Scalar`
    let hardened_idx = child_low | 0x8000_0000;
    let step = HardenedChainStep::new(sk_be, chain_code, hardened_idx)
        .expect("hardened index accepted");
    let mut mac = HmacSha512::new_from_slice(&chain_code).unwrap();
    mac.update(&[0x00]);
    mac.update(&sk_be);
    mac.update(&hardened_idx.to_be_bytes());
    let il_ir = mac.finalize().into_bytes();
    let il_bytes: [u8; 32] = il_ir[0..32].try_into().unwrap();
    let ir_bytes: [u8; 32] = il_ir[32..64].try_into().unwrap();

    if let Some(il_scalar) = Option::<K256Scalar>::from(K256Scalar::from_repr(il_bytes.into())) {
        let parent_scalar: K256Scalar = *ref_sk.to_nonzero_scalar().as_ref();
        let child_scalar = il_scalar + parent_scalar;
        if !bool::from(child_scalar.is_zero()) {
            let expected_child_sk: [u8; 32] = child_scalar.to_bytes().into();
            let (got_sk, got_cc) = step
                .derive_bip32_secp256k1_child()
                .expect("valid hardened BIP-32 child");
            prop_assert_eq!(got_sk, expected_child_sk);
            prop_assert_eq!(got_cc, ir_bytes);
        }
    }
    Ok(())
}

/// The explicit ends of the secp256k1 scalar range. `1`, `2`, `n - 2`, `n - 1` go through
/// the full differential check; `0`, `n`, `n + 1` and `2^256 - 1` must be refused by every
/// API that validates a secret key. A validator that compares only the top limb, or one
/// that accepts `n` (whose public key is the identity), fails here.
#[test]
fn secp256k1_edge_scalars_and_out_of_range_refusal() {
    let n = SECP256K1_N_BE;
    for (index, sk_be) in [be256_small(1), be256_small(2), be256_offset(&n, -2), be256_offset(&n, -1)]
        .into_iter()
        .enumerate()
    {
        for child_low in [0u32, 1, 0x7FFF_FFFF] {
            check_secp256k1_scalar_against_k256(sk_be, [0x30 + index as u8; 32], child_low)
                .unwrap_or_else(|e| panic!("edge scalar {sk_be:02x?}: {e}"));
        }
    }
    // `[1] G` is the generator and `[n - 1] G` is its negation: same x, opposite parity.
    let g = K256Proj::GENERATOR.to_affine().to_encoded_point(true);
    let one = SecpPoint::generator_mul_ct(&be256_small(1)).to_compressed_bytes().unwrap();
    let minus_one = SecpPoint::generator_mul_ct(&be256_offset(&n, -1)).to_compressed_bytes().unwrap();
    assert_eq!(one.as_slice(), g.as_bytes());
    assert_eq!(one[1..], minus_one[1..]);
    assert_eq!(one[0] ^ minus_one[0], 0x01);

    for bad in [[0u8; 32], n, be256_offset(&n, 1), [0xFF; 32]] {
        assert!(K256SecretKey::from_slice(&bad).is_err());
        let wit = ClassicalOwnershipWitness::from_raw_secret(bad);
        assert_eq!(wit.compute_bitcoin_hash160(), None, "{bad:02x?}");
        assert_eq!(wit.compute_taproot_tweaked_xonly(), None, "{bad:02x?}");
        assert_eq!(wit.compute_ethereum_keccak20(), None, "{bad:02x?}");
        let step = HardenedChainStep::new(bad, [0x77; 32], 0x8000_0001).expect("hardened index");
        assert_eq!(step.derive_bip32_secp256k1_child(), None, "{bad:02x?}");
    }
    // The raw fixed-base multiplier does not validate: it computes `[k mod n] G`, so `0` and
    // `n` give the identity (no encoding) and `n + 1` gives the generator.
    assert_eq!(SecpPoint::generator_mul_ct(&[0u8; 32]).to_compressed_bytes(), None);
    assert_eq!(SecpPoint::generator_mul_ct(&n).to_compressed_bytes(), None);
    assert_eq!(
        SecpPoint::generator_mul_ct(&be256_offset(&n, 1)).to_compressed_bytes().unwrap().as_slice(),
        g.as_bytes()
    );
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        max_shrink_iters: 128,
        .. ProptestConfig::default()
    })]

    #[test]
    fn pbt_secp256k1_ct_and_legacy_commitments_match_k256(
        sk_be in uniform_nonzero_scalar_below(SECP256K1_N_BE),
        chain_code in any::<[u8; 32]>(),
        child_low in 0u32..0x8000_0000u32,
    ) {
        check_secp256k1_scalar_against_k256(sk_be, chain_code, child_low)?;
    }

    #[test]
    fn pbt_ed25519_ct_and_slip0010_match_dalek(
        seed in any::<[u8; 32]>(),
        mut raw_clamped in any::<[u8; 32]>(),
        chain_code in any::<[u8; 32]>(),
        child_low in 0u32..0x8000_0000u32,
    ) {
        // 1. RFC 8032 seed -> SHA-512 -> clamp -> compressed Edwards pubkey vs `ed25519-dalek`
        let dalek_sk = DalekEdSigningKey::from_bytes(&seed);
        let dalek_pk_bytes = dalek_sk.verifying_key().to_bytes();
        let wit = ClassicalOwnershipWitness::from_raw_secret(seed);
        prop_assert_eq!(
            wit.compute_slip0010_commitment(),
            ClassicalCommitmentKind::Slip0010Ed25519(dalek_pk_bytes)
        );

        // 2. Direct clamped scalar basepoint mul vs `curve25519-dalek`
        raw_clamped[0] &= 248;
        raw_clamped[31] = (raw_clamped[31] & 127) | 64;
        let dalek_pt = EdwardsPoint::mul_base_clamped(raw_clamped);
        let qsag_pk = public_key_from_clamped_scalar(&raw_clamped);
        prop_assert_eq!(qsag_pk, dalek_pt.compress().to_bytes());

        // 3. Hardened SLIP-0010 derivation vs `Hmac<Sha512>` + `ed25519-dalek`
        let hardened_idx = child_low | 0x8000_0000;
        let step = HardenedChainStep::new(seed, chain_code, hardened_idx).unwrap();
        let child_wit = ClassicalOwnershipWitness::from_slip0010_hardened_step(step);

        let mut mac = HmacSha512::new_from_slice(&chain_code).unwrap();
        mac.update(&[0x00]);
        mac.update(&seed);
        mac.update(&hardened_idx.to_be_bytes());
        let il_ir = mac.finalize().into_bytes();
        let child_seed: [u8; 32] = il_ir[0..32].try_into().unwrap();
        let expected_pk = DalekEdSigningKey::from_bytes(&child_seed).verifying_key().to_bytes();
        prop_assert_eq!(
            child_wit.compute_slip0010_commitment(),
            ClassicalCommitmentKind::Slip0010Ed25519(expected_pk)
        );
    }
}

// ============================================================================
// 5B. Property-Based Differential Tests: Zcash Orchard `Pallas` & `RedPallas` vs `pasta_curves`
// ============================================================================

#[test]
fn orchard_generators_match_pasta_curves_group_hash() {
    let ref_spend_auth_g = PallasRefPoint::hash_to_curve("z.cash:Orchard")(b"G");
    assert_eq!(
        PallasPoint::ORCHARD_SPEND_AUTH_G.to_compressed_bytes(),
        ref_spend_auth_g.to_bytes(),
        "ORCHARD_SPEND_AUTH_G must match GroupHash^Pallas(\"z.cash:Orchard\", \"G\") bit-for-bit"
    );
    assert_eq!(
        PallasPoint::PASTA_GENERATOR.to_compressed_bytes(),
        PallasRefPoint::generator().to_bytes(),
        "PASTA_GENERATOR must match pasta_curves::pallas::Point::generator() bit-for-bit"
    );
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        max_shrink_iters: 128,
        .. ProptestConfig::default()
    })]

    #[test]
    fn pbt_pallas_fields_group_and_redpallas_match_pasta_curves(
        wide_ask in prop::array::uniform32(any::<u8>()),
        wide_ask_hi in prop::array::uniform32(any::<u8>()),
        wide_alpha in prop::array::uniform32(any::<u8>()),
        wide_alpha_hi in prop::array::uniform32(any::<u8>()),
        wide_fp_a in prop::array::uniform32(any::<u8>()),
        wide_fp_a_hi in prop::array::uniform32(any::<u8>()),
        wide_fp_b in prop::array::uniform32(any::<u8>()),
        wide_fp_b_hi in prop::array::uniform32(any::<u8>()),
    ) {
        let mut ask_64 = [0u8; 64];
        ask_64[..32].copy_from_slice(&wide_ask);
        ask_64[32..].copy_from_slice(&wide_ask_hi);
        let mut ref_ask = PallasRefFq::from_uniform_bytes(&ask_64);
        if bool::from(ref_ask.is_zero()) {
            ref_ask = PallasRefFq::ONE;
        }

        let mut alpha_64 = [0u8; 64];
        alpha_64[..32].copy_from_slice(&wide_alpha);
        alpha_64[32..].copy_from_slice(&wide_alpha_hi);
        let mut ref_alpha = PallasRefFq::from_uniform_bytes(&alpha_64);
        if bool::from((ref_ask + ref_alpha).is_zero()) {
            ref_alpha += PallasRefFq::ONE;
        }

        // 1. Base field FpPallas vs `pasta_curves::pallas::Base`
        let mut fp_a_64 = [0u8; 64];
        fp_a_64[..32].copy_from_slice(&wide_fp_a);
        fp_a_64[32..].copy_from_slice(&wide_fp_a_hi);
        let mut fp_b_64 = [0u8; 64];
        fp_b_64[..32].copy_from_slice(&wide_fp_b);
        fp_b_64[32..].copy_from_slice(&wide_fp_b_hi);
        let ref_a = PallasRefFp::from_uniform_bytes(&fp_a_64);
        let ref_b = PallasRefFp::from_uniform_bytes(&fp_b_64);
        let qa = FpPallas::from_le_bytes(&ref_a.to_repr()).expect("canonical FpPallas a");
        let qb = FpPallas::from_le_bytes(&ref_b.to_repr()).expect("canonical FpPallas b");
        prop_assert_eq!((qa + qb).to_le_bytes(), (ref_a + ref_b).to_repr());
        prop_assert_eq!((qa - qb).to_le_bytes(), (ref_a - ref_b).to_repr());
        prop_assert_eq!((qa * qb).to_le_bytes(), (ref_a * ref_b).to_repr());
        let ref_inv_a = Option::<PallasRefFp>::from(ref_a.invert()).unwrap_or(PallasRefFp::ZERO);
        prop_assert_eq!(qa.inv_or_zero().to_le_bytes(), ref_inv_a.to_repr());

        // 2. Scalar field FqPallas vs `pasta_curves::pallas::Scalar`
        let ask_le = ref_ask.to_repr();
        let alpha_le = ref_alpha.to_repr();
        let q_ask = FqPallas::from_nonzero_le_bytes(&ask_le).expect("nonzero FqPallas");
        let q_alpha = FqPallas::from_le_bytes(&alpha_le).expect("canonical FqPallas");
        prop_assert_eq!(q_ask.add_mod(&q_alpha).to_le_bytes(), (ref_ask + ref_alpha).to_repr());
        prop_assert_eq!(q_ask.sub_mod(&q_alpha).to_le_bytes(), (ref_ask - ref_alpha).to_repr());
        prop_assert_eq!(q_ask.mul_mod(&q_alpha).to_le_bytes(), (ref_ask * ref_alpha).to_repr());
        prop_assert_eq!(q_ask.inv_or_zero().to_le_bytes(), ref_ask.invert().unwrap().to_repr());

        // 3. Orchard `ak = [ask] SpendAuthG` & `RedPallas` `rk = [ask + alpha] SpendAuthG`
        let spend_auth_g = PallasRefPoint::hash_to_curve("z.cash:Orchard")(b"G");
        let ref_ak_pt = spend_auth_g * ref_ask;
        let ref_rk_pt = spend_auth_g * (ref_ask + ref_alpha);
        let ref_ak_bytes = ref_ak_pt.to_bytes();
        let ref_rk_bytes = ref_rk_pt.to_bytes();

        let wit_ak = PallasOwnershipWitness::from_spend_auth_scalar_le(ask_le).unwrap();
        prop_assert_eq!(
            wit_ak.compute_spend_auth_key(),
            Some(PallasCommitmentKind::OrchardSpendAuthKey(ref_ak_bytes))
        );

        let wit_rk = PallasOwnershipWitness::from_rerandomized_le(ask_le, alpha_le).unwrap();
        prop_assert_eq!(
            wit_rk.compute_rerandomized_rk(),
            Some(PallasCommitmentKind::OrchardRedPallasRk(ref_rk_bytes))
        );

        // 4. Complete point addition (`P + Q`, doubling `P + P`, `P + (-P) = O`) & decompression
        let p1 = PallasPoint::from_nonidentity_bytes(&ref_ak_bytes).expect("valid compressed ak");
        let p2 = PallasPoint::from_nonidentity_bytes(&ref_rk_bytes).expect("valid compressed rk");
        prop_assert_eq!(p1.complete_add(&p2).to_compressed_bytes(), (ref_ak_pt + ref_rk_pt).to_bytes());
        prop_assert_eq!(p1.complete_add(&p1).to_compressed_bytes(), (ref_ak_pt.double()).to_bytes());
    }
}

// ============================================================================
// 5C. Property-Based Differential Tests: Ethereum Beacon `BLS12-381` vs `blstrs`
// ============================================================================

/// BLS12-381 secret scalars in `[1, r - 1]`: generator multiplication, the 48-byte IETF
/// encoding, `0x00` withdrawal credentials, complete addition and doubling against `blstrs`.
fn check_bls12_381_scalars_against_blstrs(
    sk1_be: [u8; 32],
    sk2_be: [u8; 32],
) -> Result<(), TestCaseError> {
    let ref_sk1 = BlsRefScalar::from_bytes_be(&sk1_be).expect("canonical BlsRefScalar");
    let ref_sk2 = BlsRefScalar::from_bytes_be(&sk2_be).expect("canonical BlsRefScalar");

    // 1. Scalar arithmetic vs `blstrs::Scalar`
    let q_sk1 = FrBls381::from_nonzero_be_bytes(&sk1_be).expect("nonzero FrBls381");
    let q_sk2 = FrBls381::from_nonzero_be_bytes(&sk2_be).expect("nonzero FrBls381");
    let ref_pt1 = BlsRefG1Proj::generator() * ref_sk1;
    let ref_pt2 = BlsRefG1Proj::generator() * ref_sk2;
    let ref_pk48_1 = BlsRefG1Affine::from(ref_pt1).to_compressed();
    let ref_pk48_2 = BlsRefG1Affine::from(ref_pt2).to_compressed();

    // 2. Generator scalar mul & 48-byte IETF compressed encoding vs `blstrs`
    let wit1 = BlsOwnershipWitness::from_secret_scalar_be(sk1_be).unwrap();
    prop_assert_eq!(wit1.compute_validator_pubkey_48(), Some(ref_pk48_1));
    prop_assert_eq!(
        wit1.compute_operator_commitment(),
        Some(BlsValidatorCommitment::OperatorSigningPubkey(ref_pk48_1))
    );

    // 3. `0x00` `BLS_WITHDRAWAL_PREFIX` credential vs `sha2::Sha256`
    let mut ref_cred32: [u8; 32] = Sha256::digest(ref_pk48_1).into();
    ref_cred32[0] = 0x00;
    prop_assert_eq!(compute_bls_0x00_withdrawal_credentials(&ref_pk48_1), ref_cred32);
    prop_assert_eq!(
        wit1.compute_withdrawal_commitment(),
        Some(BlsValidatorCommitment::BlsWithdrawalCredential(ref_cred32))
    );

    // 4. Complete addition, doubling, & compressed 48-byte roundtrip
    let qp1 = BlsG1Point::from_validator_pubkey_48(&ref_pk48_1).expect("valid G1 pubkey 1");
    let qp2 = BlsG1Point::from_validator_pubkey_48(&ref_pk48_2).expect("valid G1 pubkey 2");
    prop_assert_eq!(qp1.clone(), BlsG1Point::generator_mul_ct(&q_sk1));
    prop_assert_eq!(qp2.clone(), BlsG1Point::generator_mul_ct(&q_sk2));
    prop_assert_eq!(
        qp1.complete_add(&qp2).to_compressed_48(),
        BlsRefG1Affine::from(ref_pt1 + ref_pt2).to_compressed()
    );
    prop_assert_eq!(
        qp1.complete_add(&qp1).to_compressed_48(),
        BlsRefG1Affine::from(ref_pt1.double()).to_compressed()
    );
    Ok(())
}

/// The explicit ends of the BLS12-381 scalar range. `1`, `2`, `r - 2`, `r - 1` go through
/// the full differential check in every ordered pair (so `[1] G + [r - 1] G` exercises the
/// identity result of complete addition); `0`, `r`, `r + 1` and `2^256 - 1` must be refused.
/// The removed `sk[0] %= 0x73` sampling could never produce a scalar whose top byte is
/// `0x73`, so the band `[0x73 << 248, r - 1]` next to the modulus was never tested.
#[test]
fn bls12_381_edge_scalars_and_out_of_range_refusal() {
    let r = BLS12_381_R_BE;
    let edges = [be256_small(1), be256_small(2), be256_offset(&r, -2), be256_offset(&r, -1)];
    for sk1_be in edges {
        for sk2_be in edges {
            check_bls12_381_scalars_against_blstrs(sk1_be, sk2_be)
                .unwrap_or_else(|e| panic!("edge scalars {sk1_be:02x?}, {sk2_be:02x?}: {e}"));
        }
    }
    for bad in [[0u8; 32], r, be256_offset(&r, 1), [0xFF; 32]] {
        assert!(FrBls381::from_nonzero_be_bytes(&bad).is_none(), "{bad:02x?}");
        assert!(BlsOwnershipWitness::from_secret_scalar_be(bad).is_none(), "{bad:02x?}");
        let mut bad_le = bad;
        bad_le.reverse();
        assert!(FrBls381::from_nonzero_le_bytes(&bad_le).is_none(), "{bad:02x?}");
        assert!(BlsOwnershipWitness::from_secret_scalar_le(bad_le).is_none(), "{bad:02x?}");
    }
    // Zero is a canonical field element (only the secret-key parser refuses it); `r` is not.
    assert!(FrBls381::from_be_bytes(&[0u8; 32]).is_some());
    assert!(FrBls381::from_be_bytes(&r).is_none());
    assert!(bool::from(BlsRefScalar::from_bytes_be(&r).is_none()));
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        max_shrink_iters: 128,
        .. ProptestConfig::default()
    })]

    #[test]
    fn pbt_bls12_381_g1_and_validator_commitments_match_blstrs(
        sk1_be in uniform_nonzero_scalar_below(BLS12_381_R_BE),
        sk2_be in uniform_nonzero_scalar_below(BLS12_381_R_BE),
    ) {
        check_bls12_381_scalars_against_blstrs(sk1_be, sk2_be)?;
    }
}

// ============================================================================

// ============================================================================
// 5D. End-to-End `zk-Hem v2` Ownership Migration Proofs + Adversarial Rejection
//     Using Upstream-Generated Keys Across Bitcoin, Ethereum, Ed25519, & BLS12-381
// ============================================================================

#[test]
fn e2e_zkhem_v2_migration_proofs_from_upstream_crates_and_adversarial_rejection() {
    let profile = Profile::TurboShakeJohnson400;
    let domain = [0x5Au8; 32];
    let epoch = 20_260_501_u64;

    // 1. Upstream `k256` key -> Bitcoin HASH160, BIP-341 Taproot, Ethereum Keccak20
    let sk_bytes = [0x42u8; 32];
    let ref_k256 = K256SecretKey::from_slice(&sk_bytes).unwrap();
    let ref_pk33: [u8; 33] = ref_k256
        .public_key()
        .to_encoded_point(true)
        .as_bytes()
        .try_into()
        .unwrap();
    let upstream_btc = Credential::BitcoinKeyHash(ref_bitcoin_hash160(&ref_pk33));
    let upstream_taproot = Credential::BitcoinTaproot(ref_taproot_tweaked_xonly(&ref_k256));
    let upstream_eth = Credential::EthereumAddress(ref_ethereum_keccak20(&ref_k256));

    // 2. Upstream `ed25519-dalek` key -> RFC 8032 Ed25519
    let ed_seed = [0x73u8; 32];
    let ref_ed_pk = DalekEdSigningKey::from_bytes(&ed_seed)
        .verifying_key()
        .to_bytes();
    let upstream_ed = Credential::Ed25519Key(ref_ed_pk);

    // 3. Upstream `blstrs` key -> Ethereum Beacon `0x00` BLS withdrawal credential
    let mut bls_sk_be = [0x6Cu8; 32];
    bls_sk_be[0] = 0x51;
    let ref_bls_sk = BlsRefScalar::from_bytes_be(&bls_sk_be).expect("canonical BlsRefScalar");
    let ref_bls_pk48 = BlsRefG1Affine::from(BlsRefG1Proj::generator() * ref_bls_sk).to_compressed();
    let mut ref_cred_0x00: [u8; 32] = Sha256::digest(ref_bls_pk48).into();
    ref_cred_0x00[0] = 0x00;
    let upstream_bls = Credential::BlsWithdrawal(ref_cred_0x00);

    let wrong_secp = OwnershipWitness::secp256k1_key(&[0x99u8; 32]);

    for (label, lock, source, witness, expected_cred) in [
        (
            "BitcoinHash160",
            Lock::P2pkh,
            KeySource::Secp256k1Key,
            OwnershipWitness::secp256k1_key(&sk_bytes),
            upstream_btc,
        ),
        (
            "BitcoinTaprootXOnly",
            Lock::TaprootKeyPath,
            KeySource::Secp256k1Key,
            OwnershipWitness::secp256k1_key(&sk_bytes),
            upstream_taproot,
        ),
        (
            "EthereumKeccak20",
            Lock::Ethereum,
            KeySource::Secp256k1Key,
            OwnershipWitness::secp256k1_key(&sk_bytes),
            upstream_eth,
        ),
        (
            "Ed25519Seed",
            Lock::Ed25519,
            KeySource::Ed25519Seed,
            OwnershipWitness::ed25519_seed(&ed_seed),
            upstream_ed,
        ),
        (
            "BlsWithdrawalCredential",
            Lock::BlsWithdrawal,
            KeySource::Bls12381Key,
            OwnershipWitness::bls12_381_key(&ref_bls_sk.to_bytes_be()),
            upstream_bls,
        ),
    ] {
        let target_pq = pq_commitment(&sample_pq_destination(label.as_bytes()));
        let stmt = OwnershipStatement::derive(lock, source, &witness, target_pq, domain, epoch)
            .expect(label);
        assert_eq!(
            stmt.credential, expected_cred,
            "derived credential must match upstream reference crate for {label}"
        );

        // Wrong witness must fail before proof emission
        assert_eq!(
            prove_ownership(&stmt, &wrong_secp, profile, &[0x11; 32]),
            Err(OwnershipError::WitnessMismatch),
            "wrong secret key must be rejected for {label}"
        );

        let proof = prove_ownership(&stmt, &witness, profile, &[0x22; 32]).expect(label);
        let wire = proof.to_bytes();
        let decoded = OwnershipProof::from_bytes(&wire, &stmt).expect("canonical v2 wire proof");
        assert!(
            verify_ownership(&stmt, profile, &decoded),
            "zk-Hem v2 ownership verification failed for {label}"
        );

        // Mutate proof wire & destination PQ commitment -> must reject
        let mut tampered = wire.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0x01;
        assert!(
            OwnershipProof::from_bytes(&tampered, &stmt)
                .is_none_or(|p| !verify_ownership(&stmt, profile, &p))
        );

        let mut forged_stmt = stmt.clone();
        forged_stmt.pq_commitment[0] ^= 0x80;
        assert!(!verify_ownership(&forged_stmt, profile, &decoded));
    }

    // 4. Subgroup safety: point `(0, 2)` is on `y^2 = x^3 + 4` over `FpBls381` (`2^2 = 0^3 + 4`),
    //    NOT in prime-order `G_1`! Verify both `blstrs` and `qsag_migrate::BlsG1Point` reject it!
    let torsion_pt = BlsG1Point {
        x: FpBls381::ZERO,
        y: FpBls381([2, 0, 0, 0, 0, 0]),
        z: FpBls381::ONE,
    };
    assert!(!torsion_pt.is_in_g1_subgroup(), "(0, 2) must fail G_1 subgroup check");
    let torsion_comp48 = torsion_pt.to_compressed_48();
    assert!(
        BlsG1Point::from_compressed_48(&torsion_comp48).is_none(),
        "qsag_migrate must reject out-of-subgroup point (0, 2)"
    );
    assert!(
        bool::from(BlsRefG1Affine::from_compressed(&torsion_comp48).is_none()),
        "upstream blstrs also rejects out-of-subgroup point (0, 2)"
    );
}
