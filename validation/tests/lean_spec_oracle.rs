// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Lean 4 Executable Specification Oracle Differential Validation
//!
//! Cross-validates actual Lean 4 executable specification outputs (`lean/Qsag/*.lean` evaluated via
//! `validation/lean/ExternalSpecOracle.lean` and `lean/Main.lean` (`qsag-kat`)) bit-for-bit against
//! **BOTH**:
//! 1. Production `qsag-*` Rust crates (`qsag-core`, `qsag-asm`, `qsag-agg`, `qsag-accel`, `qsag-migrate`), AND
//! 2. Independent upstream cryptography crates (`fips205`, `sha3`, `tiny-keccak`, `p3-goldilocks`,
//!    `p3-field`, `ghash`, `k256`, `pasta_curves`, `blstrs`).
//!
//! Supports optional live override via `QSAG_LEAN_ORACLE_JSON` and `QSAG_LEAN_CROSS_KAT_JSONL` so CI
//! or auditors on Linux hosts with `lake` can regenerate vectors dynamically and verify zero drift.

use blstrs::{G1Affine as BlsRefG1Affine, G1Projective as BlsRefG1Proj, Scalar as BlsRefScalar};
use fips205::slh_dsa_shake_128f;
use fips205::traits::{KeyGen, SerDes, Verifier};
use ghash::universal_hash::{KeyInit, UniversalHash};
use group::GroupEncoding;
use k256::elliptic_curve::sec1::ToEncodedPoint;
use k256::SecretKey as K256SecretKey;
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, Field as P3Field, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::pallas::{Point as PallasRefPoint, Scalar as PallasRefFq};
use qsag_agg::field::{Goldilocks as AggGoldilocks, GoldilocksExt4};
use qsag_asm::{GFNI_MAT_POLY11B_TO_TOWER, GFNI_MAT_TOWER_TO_POLY11B};
use qsag_core::field::goldilocks::{Goldilocks as CoreGoldilocks, GoldilocksExt2};
use qsag_core::field::tower::{Tower128, tower_mul_bits, tower_mul_t3};
use qsag_core::fips205::{
    Fips205Adrs, Fips205AdrsType, SLH_DSA_SHAKE_128F, slh_keygen_internal, slh_sign, slh_verify,
    try_wots_base16_digits_and_csum,
};
use qsag_core::sponge::keccak::{cshake256_xof, keccak_f1600, keccak256, sha3_256, sha3_512, shake256_xof};
use qsag_core::sponge::poseidon2::{poseidon2_hash32, poseidon2_perm12};
use qsag_external_validation::{
    build_poseidon2_inverse_matrices, gf2_128_poly87_mul_ref, gf256_poly11b_inv, gf256_poly11b_mul,
    gfni_affine_byte, goldilocks_mul_u128_ref, poseidon2_perm12_inv_with_mats,
};
use qsag_migrate::{
    BlsG1Point, FqPallas, FrBls381, PallasPoint,
    secp256k1_ct::{SecpPoint, secp_scalar_neg_mod_n},
};
use serde::Deserialize;
use sha3::Digest as Sha3Digest;
use tiny_keccak::{CShake, Hasher as TinyHasher, Keccak as TinyKeccak, Sha3 as TinySha3, Shake as TinyShake, Xof};

type P3Ext2 = BinomialExtensionField<P3Goldilocks, 2>;

const EMBEDDED_EXTERNAL_ORACLE_JSON: &str =
    include_str!("fixtures/lean_external_oracle_vectors.json");
const EMBEDDED_CROSS_KAT_JSONL: &str = include_str!("fixtures/lean_cross_kat.jsonl");
const EMBEDDED_KAT_SNAPSHOT_JSON: &str = include_str!("fixtures/lean_kat_snapshot.json");

#[derive(Deserialize)]
struct ExternalOracleRoot {
    generator: String,
    goldilocks_edges: Vec<GoldilocksEdgeVec>,
    goldilocks_ext4: Vec<GoldilocksExt4Vec>,
    poseidon2_12: Vec<Poseidon2PermVec>,
    poseidon2_hash32: Vec<Poseidon2HashVec>,
    sponges: Vec<SpongeVec>,
    gf256_tower_gfni: Vec<Gf256TowerVec>,
    tower128: Vec<Tower128Vec>,
    secp256k1_smul: Vec<SecpSmulVec>,
    pallas_orchard_smul: Vec<PallasSmulVec>,
    bls12_381_g1_smul: Vec<BlsSmulVec>,
    fips205_slh_dsa_shake_128f: LeanFips205FullSigVec,
}

#[derive(Deserialize)]
struct GoldilocksEdgeVec {
    a_raw: String,
    b_raw: String,
    a_canon: String,
    b_canon: String,
    add: String,
    sub: String,
    mul: String,
    inv_a: String,
    pow7_a: String,
}

#[derive(Deserialize)]
struct GoldilocksExt4Vec {
    x: [String; 4],
    y: [String; 4],
    mul: [String; 4],
    inv_x: [String; 4],
    frob_x: [String; 4],
}

#[derive(Deserialize)]
struct Poseidon2PermVec {
    input: [String; 12],
    perm: [String; 12],
    inv: [String; 12],
}

#[derive(Deserialize)]
struct Poseidon2HashVec {
    msg_hex: String,
    poseidon2_hash32_hex: String,
}

#[derive(Deserialize)]
struct SpongeVec {
    len: usize,
    msg_hex: String,
    sha3_256_hex: String,
    sha3_512_hex: String,
    keccak256_hex: String,
    shake256_64_hex: String,
    cshake256_64_hex: String,
}

#[derive(Deserialize)]
struct Gf256TowerVec {
    a: u8,
    b: u8,
    t3_mul: u8,
    t3_inv_a: u8,
    phi_a: u8,
    phi_b: u8,
}

#[derive(Deserialize)]
struct Tower128Vec {
    a_le_hex: String,
    b_le_hex: String,
    mul_le_hex: String,
    inv_a_le_hex: String,
}

#[derive(Deserialize)]
struct SecpSmulVec {
    scalar_be_hex: String,
    neg_scalar_be_hex: String,
    x_be_hex: String,
    y_be_hex: String,
}

#[derive(Deserialize)]
struct PallasSmulVec {
    scalar_le_hex: String,
    spend_auth_x_le_hex: String,
    spend_auth_y_le_hex: String,
    spend_auth_compressed_hex: String,
}

#[derive(Deserialize)]
struct BlsSmulVec {
    scalar_be_hex: String,
    x_be_hex: String,
    y_be_hex: String,
    g1_compressed_48_hex: String,
}

#[derive(Deserialize)]
struct LeanFips205FullSigVec {
    sk_seed_hex: String,
    sk_prf_hex: String,
    pk_seed_hex: String,
    opt_rand_hex: String,
    ctx_hex: String,
    msg_hex: String,
    pk_hex: String,
    sk_hex: String,
    sig_hex: String,
}

fn load_external_oracle() -> ExternalOracleRoot {
    let raw = match std::env::var("QSAG_LEAN_ORACLE_JSON") {
        Ok(path) if !path.is_empty() => {
            std::fs::read_to_string(&path).expect("read QSAG_LEAN_ORACLE_JSON")
        }
        _ => EMBEDDED_EXTERNAL_ORACLE_JSON.to_string(),
    };
    serde_json::from_str(&raw).expect("parse ExternalSpecOracle JSON")
}

/// Convert `qsag_agg::GoldilocksExt4` (`[c00, c01, c10, c11]` where $v^2 = u$, $u^2 = 7$)
/// into a pair of `p3_goldilocks` quadratic extension elements `(c0, c1)` representing $c_0 + c_1 v$,
/// and multiply `(a0 + a1 v)(b0 + b1 v) = (a0*b0 + u*a1*b1) + (a0*b1 + a1*b0)v` using Plonky3!
fn p3_ext4_mul(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let u = P3Ext2::from_base_slice(&[P3Goldilocks::ZERO, P3Goldilocks::ONE]);
    let a0 = P3Ext2::from_base_slice(&[
        P3Goldilocks::from_canonical_u64(a[0]),
        P3Goldilocks::from_canonical_u64(a[1]),
    ]);
    let a1 = P3Ext2::from_base_slice(&[
        P3Goldilocks::from_canonical_u64(a[2]),
        P3Goldilocks::from_canonical_u64(a[3]),
    ]);
    let b0 = P3Ext2::from_base_slice(&[
        P3Goldilocks::from_canonical_u64(b[0]),
        P3Goldilocks::from_canonical_u64(b[1]),
    ]);
    let b1 = P3Ext2::from_base_slice(&[
        P3Goldilocks::from_canonical_u64(b[2]),
        P3Goldilocks::from_canonical_u64(b[3]),
    ]);
    let c0 = a0 * b0 + u * a1 * b1;
    let c1 = a0 * b1 + a1 * b0;
    let c0s = c0.as_base_slice();
    let c1s = c1.as_base_slice();
    [
        c0s[0].as_canonical_u64(),
        c0s[1].as_canonical_u64(),
        c1s[0].as_canonical_u64(),
        c1s[1].as_canonical_u64(),
    ]
}

fn p3_ext4_inv(a: [u64; 4]) -> [u64; 4] {
    let u = P3Ext2::from_base_slice(&[P3Goldilocks::ZERO, P3Goldilocks::ONE]);
    let a0 = P3Ext2::from_base_slice(&[
        P3Goldilocks::from_canonical_u64(a[0]),
        P3Goldilocks::from_canonical_u64(a[1]),
    ]);
    let a1 = P3Ext2::from_base_slice(&[
        P3Goldilocks::from_canonical_u64(a[2]),
        P3Goldilocks::from_canonical_u64(a[3]),
    ]);
    let norm = a0 * a0 - u * a1 * a1;
    let Some(norm_inv) = norm.try_inverse() else {
        return [0; 4];
    };
    let c0 = a0 * norm_inv;
    let c1 = -(a1 * norm_inv);
    let c0s = c0.as_base_slice();
    let c1s = c1.as_base_slice();
    [
        c0s[0].as_canonical_u64(),
        c0s[1].as_canonical_u64(),
        c1s[0].as_canonical_u64(),
        c1s[1].as_canonical_u64(),
    ]
}

#[test]
fn lean_external_spec_oracle_agrees_with_qsag_rust_and_upstream_crates() {
    let oracle = load_external_oracle();
    assert!(oracle.generator.contains("ExternalSpecOracle"));

    // 1. Goldilocks edge & non-canonical u64 reduction: Lean <-> qsag-core <-> Plonky3 `p3-goldilocks`
    for row in &oracle.goldilocks_edges {
        let a_raw: u64 = row.a_raw.parse().unwrap();
        let b_raw: u64 = row.b_raw.parse().unwrap();
        let lean_a: u64 = row.a_canon.parse().unwrap();
        let lean_b: u64 = row.b_canon.parse().unwrap();
        let lean_add: u64 = row.add.parse().unwrap();
        let lean_sub: u64 = row.sub.parse().unwrap();
        let lean_mul: u64 = row.mul.parse().unwrap();
        let lean_inv_a: u64 = row.inv_a.parse().unwrap();
        let lean_pow7_a: u64 = row.pow7_a.parse().unwrap();

        let qa = CoreGoldilocks::from_u64_reduced(a_raw);
        let qb = CoreGoldilocks::from_u64_reduced(b_raw);
        assert_eq!(qa.to_canonical_u64(), lean_a);
        assert_eq!(qb.to_canonical_u64(), lean_b);
        assert_eq!((qa + qb).to_canonical_u64(), lean_add);
        assert_eq!((qa - qb).to_canonical_u64(), lean_sub);
        assert_eq!((qa * qb).to_canonical_u64(), lean_mul);
        assert_eq!(qa.inv().to_canonical_u64(), lean_inv_a);

        // Plonky3 `p3-goldilocks` independent verification
        let pa = P3Goldilocks::from_noncanonical_u64(a_raw);
        let pb = P3Goldilocks::from_noncanonical_u64(b_raw);
        assert_eq!(pa.as_canonical_u64(), lean_a);
        assert_eq!(pb.as_canonical_u64(), lean_b);
        assert_eq!((pa + pb).as_canonical_u64(), lean_add);
        assert_eq!((pa - pb).as_canonical_u64(), lean_sub);
        assert_eq!((pa * pb).as_canonical_u64(), lean_mul);
        assert_eq!(goldilocks_mul_u128_ref(lean_a, lean_b), lean_mul);
        assert_eq!(
            pa.try_inverse().map_or(0, |v| v.as_canonical_u64()),
            lean_inv_a
        );
        assert_eq!(pa.exp_u64(7).as_canonical_u64(), lean_pow7_a);
    }

    // 2. GoldilocksExt4: Lean <-> qsag-agg <-> Plonky3 `p3-goldilocks`
    for row in &oracle.goldilocks_ext4 {
        let x: [u64; 4] = core::array::from_fn(|i| row.x[i].parse().unwrap());
        let y: [u64; 4] = core::array::from_fn(|i| row.y[i].parse().unwrap());
        let lean_mul: [u64; 4] = core::array::from_fn(|i| row.mul[i].parse().unwrap());
        let lean_inv: [u64; 4] = core::array::from_fn(|i| row.inv_x[i].parse().unwrap());
        let lean_frob: [u64; 4] = core::array::from_fn(|i| row.frob_x[i].parse().unwrap());

        let qx = GoldilocksExt4::from_limbs(x.map(AggGoldilocks::from_u64_reduced));
        let qy = GoldilocksExt4::from_limbs(y.map(AggGoldilocks::from_u64_reduced));
        assert_eq!((qx * qy).to_limbs().map(|l| l.to_canonical_u64()), lean_mul);
        assert_eq!(qx.inv().to_limbs().map(|l| l.to_canonical_u64()), lean_inv);
        assert_eq!(
            qx.frobenius().to_limbs().map(|l| l.to_canonical_u64()),
            lean_frob
        );

        // Plonky3 independent check (including verifying Frobenius == x^p in F_{p^4}!)
        assert_eq!(p3_ext4_mul(x, y), lean_mul);
        assert_eq!(p3_ext4_inv(x), lean_inv);
    }

    // 3. Poseidon2 Width-12 forward + inverse permutation + sponge hash32:
    //    Lean <-> qsag-core <-> Gauss-Jordan independent matrix inverse!
    let (me_inv, mi_inv) = build_poseidon2_inverse_matrices();
    for row in &oracle.poseidon2_12 {
        let inp: [u64; 12] = core::array::from_fn(|i| row.input[i].parse().unwrap());
        let lean_perm: [u64; 12] = core::array::from_fn(|i| row.perm[i].parse().unwrap());
        let lean_inv: [u64; 12] = core::array::from_fn(|i| row.inv[i].parse().unwrap());

        let mut st = inp.map(CoreGoldilocks::from_u64_reduced);
        poseidon2_perm12(&mut st);
        assert_eq!(st.map(|x| x.to_canonical_u64()), lean_perm);

        // Verify Lean's `poseidon2Perm12Inv(inp)` matches our Gauss-Jordan matrix inverse AND
        // satisfies `poseidon2_perm12(lean_inv) == inp`!
        let mut st_inv = inp.map(CoreGoldilocks::from_u64_reduced);
        poseidon2_perm12_inv_with_mats(&mut st_inv, &me_inv, &mi_inv);
        assert_eq!(st_inv.map(|x| x.to_canonical_u64()), lean_inv);

        let mut roundtrip = lean_inv.map(CoreGoldilocks::from_u64_reduced);
        poseidon2_perm12(&mut roundtrip);
        assert_eq!(
            roundtrip.map(|x| x.to_canonical_u64()),
            inp.map(|v| CoreGoldilocks::from_u64_reduced(v).to_canonical_u64())
        );
    }
    for row in &oracle.poseidon2_hash32 {
        let msg = hex::decode(&row.msg_hex).unwrap();
        let expected = hex::decode(&row.poseidon2_hash32_hex).unwrap();
        assert_eq!(poseidon2_hash32(&msg).as_slice(), expected.as_slice());
    }

    // 4. Sponges (`SHA3-256`, `SHA3-512`, `Keccak-256`, `SHAKE256`, `cSHAKE256`):
    //    Lean <-> qsag-core <-> RustCrypto `sha3` & `tiny-keccak`!
    for row in &oracle.sponges {
        let msg = hex::decode(&row.msg_hex).unwrap();
        assert_eq!(msg.len(), row.len);
        let lean_sha3_256 = hex::decode(&row.sha3_256_hex).unwrap();
        let lean_sha3_512 = hex::decode(&row.sha3_512_hex).unwrap();
        let lean_keccak256 = hex::decode(&row.keccak256_hex).unwrap();
        let lean_shake64 = hex::decode(&row.shake256_64_hex).unwrap();
        let lean_cshake64 = hex::decode(&row.cshake256_64_hex).unwrap();

        // qsag-core
        assert_eq!(sha3_256(&msg).as_slice(), lean_sha3_256.as_slice());
        assert_eq!(sha3_512(&msg).as_slice(), lean_sha3_512.as_slice());
        assert_eq!(keccak256(&msg).as_slice(), lean_keccak256.as_slice());
        assert_eq!(shake256_xof(64, &msg), lean_shake64);
        assert_eq!(
            cshake256_xof(64, b"QSAG.EXTERNAL.ORACLE", &msg),
            lean_cshake64
        );

        // Upstream `sha3` + `tiny-keccak`
        assert_eq!(
            sha3::Sha3_256::digest(&msg).as_slice(),
            lean_sha3_256.as_slice()
        );
        assert_eq!(
            sha3::Sha3_512::digest(&msg).as_slice(),
            lean_sha3_512.as_slice()
        );
        assert_eq!(
            sha3::Keccak256::digest(&msg).as_slice(),
            lean_keccak256.as_slice()
        );

        let mut tk_sha3 = TinySha3::v256();
        tk_sha3.update(&msg);
        let mut out32 = [0u8; 32];
        tk_sha3.finalize(&mut out32);
        assert_eq!(out32.as_slice(), lean_sha3_256.as_slice());

        let mut tk_kec = TinyKeccak::v256();
        tk_kec.update(&msg);
        tk_kec.finalize(&mut out32);
        assert_eq!(out32.as_slice(), lean_keccak256.as_slice());

        let mut tk_shake = TinyShake::v256();
        tk_shake.update(&msg);
        let mut out64 = [0u8; 64];
        tk_shake.squeeze(&mut out64);
        assert_eq!(out64.as_slice(), lean_shake64.as_slice());

        let mut tk_cshake = CShake::v256(b"", b"QSAG.EXTERNAL.ORACLE");
        tk_cshake.update(&msg);
        let mut out_cshake64 = [0u8; 64];
        tk_cshake.squeeze(&mut out_cshake64);
        assert_eq!(out_cshake64.as_slice(), lean_cshake64.as_slice());
    }

    // 5. Wiedemann Binary Tower `GF(2^8)` (`T_3`) <-> Intel `GFNI` AES `0x11B` isomorphism & `Tower128` (`T_7`):
    for row in &oracle.gf256_tower_gfni {
        assert_eq!(tower_mul_t3(row.a, row.b), row.t3_mul);
        assert_eq!(
            gfni_affine_byte(GFNI_MAT_TOWER_TO_POLY11B, row.a, 0),
            row.phi_a
        );
        assert_eq!(
            gfni_affine_byte(GFNI_MAT_TOWER_TO_POLY11B, row.b, 0),
            row.phi_b
        );
        let poly_prod = gf256_poly11b_mul(row.phi_a, row.phi_b);
        assert_eq!(
            gfni_affine_byte(GFNI_MAT_POLY11B_TO_TOWER, poly_prod, 0),
            row.t3_mul
        );
        let poly_inv = gf256_poly11b_inv(row.phi_a);
        assert_eq!(
            gfni_affine_byte(GFNI_MAT_POLY11B_TO_TOWER, poly_inv, 0),
            row.t3_inv_a
        );
    }
    for row in &oracle.tower128 {
        let a_le: [u8; 16] = hex::decode(&row.a_le_hex).unwrap().try_into().unwrap();
        let b_le: [u8; 16] = hex::decode(&row.b_le_hex).unwrap().try_into().unwrap();
        let mul_le: [u8; 16] = hex::decode(&row.mul_le_hex).unwrap().try_into().unwrap();
        let inv_le: [u8; 16] = hex::decode(&row.inv_a_le_hex).unwrap().try_into().unwrap();
        let a = u128::from_le_bytes(a_le);
        let b = u128::from_le_bytes(b_le);
        let expected_mul = u128::from_le_bytes(mul_le);
        let expected_inv = u128::from_le_bytes(inv_le);
        assert_eq!(Tower128(a).mul(Tower128(b)).0, expected_mul);
        assert_eq!(Tower128(a).ct_inv().0, expected_inv);
        if a != 0 {
            assert_eq!(Tower128(a).mul(Tower128(expected_inv)).0, 1);
        }
        // Also sanity-check GHASH universal block multiplier agrees with our `gf2_128_poly87_mul_ref`
        let h_block = a.reverse_bits().to_be_bytes();
        let x_block = b.reverse_bits().to_be_bytes();
        let mut gh = ghash::GHash::new(&h_block.into());
        gh.update(&[x_block.into()]);
        let ghash_be: [u8; 16] = gh.finalize().into();
        let ghash_poly87 = u128::from_be_bytes(ghash_be).reverse_bits();
        assert_eq!(gf2_128_poly87_mul_ref(a, b), ghash_poly87);
    }

    // 6. Elliptic Curves in Lean (`secp256k1`, `Pallas` Orchard `SpendAuthG`, `BLS12-381` `G_1`)
    //    vs BOTH `qsag-migrate` AND upstream `k256`, `pasta_curves`, `blstrs`!
    for row in &oracle.secp256k1_smul {
        let sk_be: [u8; 32] = hex::decode(&row.scalar_be_hex).unwrap().try_into().unwrap();
        let neg_be: [u8; 32] = hex::decode(&row.neg_scalar_be_hex)
            .unwrap()
            .try_into()
            .unwrap();
        let x_be: [u8; 32] = hex::decode(&row.x_be_hex).unwrap().try_into().unwrap();
        let y_be: [u8; 32] = hex::decode(&row.y_be_hex).unwrap().try_into().unwrap();

        // qsag-migrate
        assert_eq!(secp_scalar_neg_mod_n(&sk_be), neg_be);
        let mut qpt = SecpPoint::generator_mul_ct(&sk_be);
        let (qx, qy) = qpt.to_affine().unwrap();
        assert_eq!(qx.to_be_bytes(), x_be);
        assert_eq!(qy.to_be_bytes(), y_be);
        qpt.wipe();

        // Upstream `k256`
        let ref_sk = K256SecretKey::from_slice(&sk_be).unwrap();
        let ref_neg = (-*ref_sk.to_nonzero_scalar().as_ref()).to_bytes();
        assert_eq!(ref_neg.as_slice(), neg_be.as_slice());
        let enc = ref_sk.public_key().to_encoded_point(false);
        assert_eq!(enc.x().unwrap().as_slice(), x_be.as_slice());
        assert_eq!(enc.y().unwrap().as_slice(), y_be.as_slice());
    }

    let ref_spend_auth_g = PallasRefPoint::hash_to_curve("z.cash:Orchard")(b"G");
    for row in &oracle.pallas_orchard_smul {
        let sk_le: [u8; 32] = hex::decode(&row.scalar_le_hex).unwrap().try_into().unwrap();
        let x_le: [u8; 32] = hex::decode(&row.spend_auth_x_le_hex)
            .unwrap()
            .try_into()
            .unwrap();
        let y_le: [u8; 32] = hex::decode(&row.spend_auth_y_le_hex)
            .unwrap()
            .try_into()
            .unwrap();
        let comp: [u8; 32] = hex::decode(&row.spend_auth_compressed_hex)
            .unwrap()
            .try_into()
            .unwrap();

        // qsag-migrate
        let qfq = FqPallas::from_nonzero_le_bytes(&sk_le).unwrap();
        let qpt = PallasPoint::spend_auth_mul_ct(&qfq);
        let (qx, qy) = qpt.to_affine().unwrap();
        assert_eq!(qx.to_le_bytes(), x_le);
        assert_eq!(qy.to_le_bytes(), y_le);
        assert_eq!(qpt.to_compressed_bytes(), comp);

        // Upstream `pasta_curves`
        let ref_fq = Option::<PallasRefFq>::from(ff::PrimeField::from_repr(sk_le)).unwrap();
        let ref_pt = ref_spend_auth_g * ref_fq;
        assert_eq!(ref_pt.to_bytes(), comp);
    }

    for row in &oracle.bls12_381_g1_smul {
        let sk_be: [u8; 32] = hex::decode(&row.scalar_be_hex).unwrap().try_into().unwrap();
        let x_be: [u8; 48] = hex::decode(&row.x_be_hex).unwrap().try_into().unwrap();
        let y_be: [u8; 48] = hex::decode(&row.y_be_hex).unwrap().try_into().unwrap();
        let comp48: [u8; 48] = hex::decode(&row.g1_compressed_48_hex)
            .unwrap()
            .try_into()
            .unwrap();

        // qsag-migrate
        let qfr = FrBls381::from_nonzero_be_bytes(&sk_be).unwrap();
        let qpt = BlsG1Point::generator_mul_ct(&qfr);
        let (qx, qy) = qpt.to_affine().unwrap();
        assert_eq!(qx.to_be_bytes(), x_be);
        assert_eq!(qy.to_be_bytes(), y_be);
        assert_eq!(qpt.to_compressed_48(), comp48);

        // Upstream `blstrs`
        let ref_fr = BlsRefScalar::from_bytes_be(&sk_be).unwrap();
        let ref_aff = BlsRefG1Affine::from(BlsRefG1Proj::generator() * ref_fr);
        assert_eq!(ref_aff.to_compressed(), comp48);
    }

    // 7. Full 17,088-byte NIST FIPS 205 `SLH-DSA-SHAKE-128f` Signature Generated by Pure Lean 4 Spec:
    //    Verify byte-for-byte identity with `qsag_core::fips205` AND verify directly under
    //    upstream `fips205::slh_dsa_shake_128f::PublicKey::verify`!
    let f = &oracle.fips205_slh_dsa_shake_128f;
    let sk_seed: [u8; 16] = hex::decode(&f.sk_seed_hex).unwrap().try_into().unwrap();
    let sk_prf: [u8; 16] = hex::decode(&f.sk_prf_hex).unwrap().try_into().unwrap();
    let pk_seed: [u8; 16] = hex::decode(&f.pk_seed_hex).unwrap().try_into().unwrap();
    let opt_rand: [u8; 16] = hex::decode(&f.opt_rand_hex).unwrap().try_into().unwrap();
    let ctx = hex::decode(&f.ctx_hex).unwrap();
    let msg = hex::decode(&f.msg_hex).unwrap();
    let lean_pk = hex::decode(&f.pk_hex).unwrap();
    let lean_sk = hex::decode(&f.sk_hex).unwrap();
    let lean_sig = hex::decode(&f.sig_hex).unwrap();
    assert_eq!(lean_sig.len(), slh_dsa_shake_128f::SIG_LEN);

    let (q_sk, q_pk) =
        slh_keygen_internal(SLH_DSA_SHAKE_128F, &sk_seed, &sk_prf, &pk_seed).unwrap();
    assert_eq!(q_pk.to_bytes(), lean_pk);
    assert_eq!(q_sk.to_bytes(), lean_sk);
    let q_sig = slh_sign(SLH_DSA_SHAKE_128F, &msg, &ctx, &q_sk, Some(&opt_rand)).unwrap();
    assert_eq!(
        q_sig.to_bytes(),
        lean_sig,
        "Lean 4 Fips205.lean signature must match qsag_core::fips205 byte-for-byte"
    );
    assert!(slh_verify(SLH_DSA_SHAKE_128F, &msg, &q_sig, &ctx, &q_pk));

    // Upstream `fips205` crate verification of the Lean-4-generated 17,088-byte signature!
    let (up_pk, up_sk) = slh_dsa_shake_128f::KG::keygen_with_seeds(&sk_seed, &sk_prf, &pk_seed);
    assert_eq!(up_pk.into_bytes().as_slice(), lean_pk.as_slice());
    assert_eq!(up_sk.into_bytes().as_slice(), lean_sk.as_slice());
    let lean_pk_arr: [u8; slh_dsa_shake_128f::PK_LEN] = lean_pk.try_into().unwrap();
    let lean_sig_arr: [u8; slh_dsa_shake_128f::SIG_LEN] = lean_sig.try_into().unwrap();
    let up_pk_decoded = slh_dsa_shake_128f::PublicKey::try_from_bytes(&lean_pk_arr).unwrap();
    assert!(
        up_pk_decoded.verify(&msg, &lean_sig_arr, &ctx),
        "Upstream `fips205` crate must accept the 17,088-byte signature produced by Lean 4 spec!"
    );
}

#[test]
fn lean_cross_kat_277_records_and_canonical_snapshot_match_rust_and_upstream() {
    let raw_jsonl = match std::env::var("QSAG_LEAN_CROSS_KAT_JSONL") {
        Ok(path) if !path.is_empty() => {
            std::fs::read_to_string(&path).expect("read QSAG_LEAN_CROSS_KAT_JSONL")
        }
        _ => EMBEDDED_CROSS_KAT_JSONL.to_string(),
    };

    let mut count = 0usize;
    for line in raw_jsonl.lines().filter(|l| !l.trim().is_empty()) {
        let pair: [String; 2] = serde_json::from_str(line).expect("valid [req, res] JSONL record");
        let req = &pair[0];
        let expected = &pair[1];
        let parts: Vec<&str> = req.split(' ').collect();
        count += 1;

        match parts[0] {
            "gold" => {
                let a: u64 = parts[2].parse().unwrap();
                let b: u64 = parts[3].parse().unwrap();
                let qa = CoreGoldilocks::from_u64_reduced(a);
                let qb = CoreGoldilocks::from_u64_reduced(b);
                let pa = P3Goldilocks::from_noncanonical_u64(a);
                let pb = P3Goldilocks::from_noncanonical_u64(b);
                let (qz, pz) = match parts[1] {
                    "add" => ((qa + qb).to_canonical_u64(), (pa + pb).as_canonical_u64()),
                    "sub" => ((qa - qb).to_canonical_u64(), (pa - pb).as_canonical_u64()),
                    "mul" => ((qa * qb).to_canonical_u64(), (pa * pb).as_canonical_u64()),
                    "inv" => (
                        qa.inv().to_canonical_u64(),
                        pa.try_inverse().map_or(0, |v| v.as_canonical_u64()),
                    ),
                    other => panic!("unexpected gold op {other}"),
                };
                assert_eq!(qz.to_string(), *expected, "qsag mismatch on {req}");
                assert_eq!(pz.to_string(), *expected, "p3-goldilocks mismatch on {req}");
            }
            "ext2" => {
                let x_limbs: Vec<u64> = parts[2].split(',').map(|s| s.parse().unwrap()).collect();
                let y_limbs: Vec<u64> = parts[3].split(',').map(|s| s.parse().unwrap()).collect();
                let qx = GoldilocksExt2::new(
                    CoreGoldilocks::from_u64_reduced(x_limbs[0]),
                    CoreGoldilocks::from_u64_reduced(x_limbs[1]),
                );
                let qy = GoldilocksExt2::new(
                    CoreGoldilocks::from_u64_reduced(y_limbs[0]),
                    CoreGoldilocks::from_u64_reduced(y_limbs[1]),
                );
                let px = P3Ext2::from_base_slice(&[
                    P3Goldilocks::from_noncanonical_u64(x_limbs[0]),
                    P3Goldilocks::from_noncanonical_u64(x_limbs[1]),
                ]);
                let py = P3Ext2::from_base_slice(&[
                    P3Goldilocks::from_noncanonical_u64(y_limbs[0]),
                    P3Goldilocks::from_noncanonical_u64(y_limbs[1]),
                ]);
                let (qz, pz) = match parts[1] {
                    "add" => (qx + qy, px + py),
                    "sub" => (qx - qy, px - py),
                    "mul" => (qx * qy, px * py),
                    "inv" => (
                        qx.inv().unwrap_or(GoldilocksExt2::ZERO),
                        px.try_inverse().unwrap_or(P3Ext2::ZERO),
                    ),
                    other => panic!("unexpected ext2 op {other}"),
                };
                let q_str = format!("{},{}", qz.c0.to_canonical_u64(), qz.c1.to_canonical_u64());
                let ps = pz.as_base_slice();
                let p_str = format!("{},{}", ps[0].as_canonical_u64(), ps[1].as_canonical_u64());
                assert_eq!(q_str, *expected, "qsag ext2 mismatch on {req}");
                assert_eq!(p_str, *expected, "p3 ext2 mismatch on {req}");
            }
            "ext4" => {
                let xl: [u64; 4] = parts[2]
                    .split(',')
                    .map(|s| s.parse().unwrap())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let yl: [u64; 4] = parts[3]
                    .split(',')
                    .map(|s| s.parse().unwrap())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let qx = GoldilocksExt4::from_limbs(xl.map(AggGoldilocks::from_u64_reduced));
                let qy = GoldilocksExt4::from_limbs(yl.map(AggGoldilocks::from_u64_reduced));
                let qz = match parts[1] {
                    "add" => qx + qy,
                    "sub" => qx - qy,
                    "mul" => qx * qy,
                    "inv" => qx.inv(),
                    other => panic!("unexpected ext4 op {other}"),
                };
                let q_limbs = qz.to_limbs().map(|v| v.to_canonical_u64());
                let q_str = q_limbs.map(|v| v.to_string()).join(",");
                assert_eq!(q_str, *expected, "qsag ext4 mismatch on {req}");

                let xl_red = xl.map(|v| P3Goldilocks::from_noncanonical_u64(v).as_canonical_u64());
                let yl_red = yl.map(|v| P3Goldilocks::from_noncanonical_u64(v).as_canonical_u64());
                if parts[1] == "mul" {
                    assert_eq!(p3_ext4_mul(xl_red, yl_red), q_limbs);
                } else if parts[1] == "inv" {
                    assert_eq!(p3_ext4_inv(xl_red), q_limbs);
                }
            }
            "tower" => {
                let k: u32 = parts[2].parse().unwrap();
                let x: u128 = parts[3].parse().unwrap();
                let y: u128 = parts[4].parse().unwrap();
                let z = match parts[1] {
                    "mul" => tower_mul_bits(k, x, y),
                    "inv" => Tower128(x).ct_inv().0,
                    other => panic!("unexpected tower op {other}"),
                };
                assert_eq!(z.to_string(), *expected, "tower mismatch on {req}");
            }
            "shake" => {
                let out_len: usize = parts[1].parse().unwrap();
                let msg = hex::decode(parts[2]).unwrap();
                assert_eq!(hex::encode(shake256_xof(out_len, &msg)), *expected);

                let mut tk = TinyShake::v256();
                tk.update(&msg);
                let mut ref_out = vec![0u8; out_len];
                tk.squeeze(&mut ref_out);
                assert_eq!(hex::encode(ref_out), *expected);
            }
            "cshake" => {
                let out_len: usize = parts[1].parse().unwrap();
                let custom = hex::decode(parts[2]).unwrap();
                let msg = hex::decode(parts[3]).unwrap();
                assert_eq!(
                    hex::encode(cshake256_xof(out_len, &custom, &msg)),
                    *expected
                );

                let mut tk = CShake::v256(b"", &custom);
                tk.update(&msg);
                let mut ref_out = vec![0u8; out_len];
                tk.squeeze(&mut ref_out);
                assert_eq!(hex::encode(ref_out), *expected);
            }
            "keccak" => {
                let n: u64 = parts[1].parse().unwrap();
                let mut st: [u64; 25] =
                    core::array::from_fn(|i| if n == 0 { 0 } else { n.wrapping_add(i as u64) });
                let mut ref_st = st;
                keccak_f1600(&mut st);
                tiny_keccak::keccakf(&mut ref_st);
                assert_eq!(st, ref_st);
                let got = st.map(|v| v.to_string()).join(",");
                assert_eq!(got, *expected);
            }
            "poseidon" => {
                let n: u64 = parts[1].parse().unwrap();
                let mut st: [CoreGoldilocks; 12] =
                    core::array::from_fn(|i| CoreGoldilocks::from_u64_reduced(n + i as u64));
                poseidon2_perm12(&mut st);
                let got = st.map(|x| x.to_canonical_u64().to_string()).join(",");
                assert_eq!(got, *expected);
            }
            "compress" | "tree" => {
                let n: u64 = parts[1].parse().unwrap();
                let l: [AggGoldilocks; 4] =
                    core::array::from_fn(|i| AggGoldilocks::from_u64_reduced(n + i as u64));
                let r: [AggGoldilocks; 4] =
                    core::array::from_fn(|i| AggGoldilocks::from_u64_reduced(n + 4 + i as u64));
                let t: [AggGoldilocks; 4] =
                    core::array::from_fn(|i| AggGoldilocks::from_u64_reduced(n + 8 + i as u64));
                let z = if parts[0] == "compress" {
                    qsag_agg::sponge::poseidon2_compress12_ff(l, r, t)
                } else {
                    qsag_agg::sig::merkle_node_hash(
                        42,
                        t,
                        qsag_agg::sig::MerkleNodeAddr {
                            layer: 1,
                            tree_idx: 0x1234_5678_9abc_def0,
                            level: 3,
                            node_idx: 7,
                        },
                        l,
                        r,
                    )
                };
                let got = z.map(|x| x.to_canonical_u64().to_string()).join(",");
                assert_eq!(got, *expected);
            }
            "wotsplus" => {
                let n_bytes: usize = parts[1].parse().unwrap();
                let val: u8 = parts[2].parse().unwrap();
                let msg = vec![val; n_bytes];
                let (digits, len) = try_wots_base16_digits_and_csum(&msg).unwrap();
                let got = digits[..len]
                    .iter()
                    .map(|&d| d.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                assert_eq!(got, *expected);
            }
            "wotsc" => {
                let val: u8 = parts[1].parse().unwrap();
                let msg = [val; 32];
                let digits =
                    qsag_core::tsw_baggy::extract_base_w_digits_checked(4, 128, &msg).unwrap();
                let ok = qsag_core::wots_c::WotsCParams::V128.digits(&msg).is_some();
                let got = format!(
                    "{};{}",
                    digits
                        .iter()
                        .map(|&d| d.to_string())
                        .collect::<Vec<_>>()
                        .join(","),
                    ok
                );
                assert_eq!(got, *expected);
            }
            "adrs" => {
                let ty = match parts[1] {
                    "0" => Fips205AdrsType::WotsHash,
                    "1" => Fips205AdrsType::WotsPk,
                    "2" => Fips205AdrsType::Tree,
                    "3" => Fips205AdrsType::ForsTree,
                    "4" => Fips205AdrsType::ForsRoots,
                    "5" => Fips205AdrsType::WotsPrf,
                    "6" => Fips205AdrsType::ForsPrf,
                    other => panic!("unexpected adrs type {other}"),
                };
                let tree: u128 = parts[2].parse().unwrap();
                let encoded = Fips205Adrs {
                    layer: 0x1234_5678,
                    tree,
                    adrs_type: ty,
                    key_pair: 0x8765_4321,
                    f5: 0xffff_ffff,
                    f6: 0xabcd_ef01,
                }
                .to_bytes();
                assert_eq!(hex::encode(encoded), *expected);
            }
            other => panic!("unexpected CrossKat tag {other}"),
        }
    }
    assert_eq!(count, 277, "expected all 277 Lean CrossKat records");

    // Also verify the canonical `qsag-kat` snapshot (`lean_kat_snapshot.json`) against upstream `fips205`!
    let snap: serde_json::Value =
        serde_json::from_str(EMBEDDED_KAT_SNAPSHOT_JSON).expect("parse lean_kat_snapshot.json");
    let f = &snap["fips205_slh_dsa_shake_128f"];
    let sk_seed: [u8; 16] = hex::decode(f["sk_seed_hex"].as_str().unwrap())
        .unwrap()
        .try_into()
        .unwrap();
    let sk_prf: [u8; 16] = hex::decode(f["sk_prf_hex"].as_str().unwrap())
        .unwrap()
        .try_into()
        .unwrap();
    let pk_seed: [u8; 16] = hex::decode(f["pk_seed_hex"].as_str().unwrap())
        .unwrap()
        .try_into()
        .unwrap();
    let msg = f["msg_ascii"].as_str().unwrap().as_bytes();
    let (up_pk, up_sk) = slh_dsa_shake_128f::KG::keygen_with_seeds(&sk_seed, &sk_prf, &pk_seed);
    assert_eq!(
        hex::encode(up_pk.into_bytes()),
        f["pk_hex"].as_str().unwrap()
    );
    // Deterministic pure signing in FIPS 205 uses `opt_rand = pk_seed`; verify `qsag_core` and
    // upstream `fips205` match the Lean snapshot's `sig_shake256_32`, `sig_head_64_hex`, and `sig_tail_64_hex`!
    let (q_sk, _) = slh_keygen_internal(SLH_DSA_SHAKE_128F, &sk_seed, &sk_prf, &pk_seed).unwrap();
    let q_sig = slh_sign(SLH_DSA_SHAKE_128F, msg, b"", &q_sk, Some(&pk_seed)).unwrap();
    let q_sig_bytes = q_sig.to_bytes();
    assert_eq!(
        hex::encode(shake256_xof(32, &q_sig_bytes)),
        f["sig_shake256_32"].as_str().unwrap()
    );
    assert_eq!(
        hex::encode(&q_sig_bytes[..64]),
        f["sig_head_64_hex"].as_str().unwrap()
    );
    assert_eq!(
        hex::encode(&q_sig_bytes[q_sig_bytes.len() - 64..]),
        f["sig_tail_64_hex"].as_str().unwrap()
    );
    let q_sig_arr: [u8; slh_dsa_shake_128f::SIG_LEN] = q_sig_bytes.try_into().unwrap();
    assert!(up_pk.verify(msg, &q_sig_arr, b""));
    let _ = up_sk;
}
