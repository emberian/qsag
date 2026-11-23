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
use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar as DalekScalar;
use fips205::traits::{KeyGen, SerDes, Verifier};
use fips205::{slh_dsa_shake_128f, slh_dsa_shake_128s};
use ghash::universal_hash::{KeyInit, UniversalHash};
use group::{Group, GroupEncoding};
use k256::SecretKey as K256SecretKey;
use k256::elliptic_curve::sec1::ToEncodedPoint;
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, Field as P3Field, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::pallas::{Point as PallasRefPoint, Scalar as PallasRefFq};
use qsag_accel::keccak::{KeccakSponge, keccak256, sha3_256};
use qsag_agg::field::Goldilocks as AggGoldilocks;
use qsag_asm::{GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY};
use qsag_core::field::goldilocks::{Goldilocks as CoreGoldilocks, GoldilocksExt2};
use qsag_core::field::tower::{Tower128, TowerGf256, tower_mul_bits};
use qsag_core::fips205::{
    Fips205Adrs, Fips205AdrsType, Fips205Params, fips205_f, fips205_h_msg, fips205_prf,
    fips205_prf_msg, format_pure_m_prime, slh_keygen_internal, slh_sign, slh_verify,
    split_digest_indices, try_wots_base16_digits_and_csum,
};
use qsag_core::poseidon2_mpc::hem_poseidon2_compress12_ff;
use qsag_core::sponge::keccak::{cshake256_xof, keccak_f1600, shake256_xof};
use qsag_core::sponge::poseidon2::{poseidon2_hash32, poseidon2_perm12};
use qsag_external_validation::{
    GOLDILOCKS_P, gf2_128_poly87_mul_ref, gf256_poly11b_inv, gf256_poly11b_mul, gfni_affine_byte,
    goldilocks_mul_u128_ref, p3_fp5_inv, p3_fp5_mul, p3_fp5_pow, p3_gl, poseidon2_ref,
};
use qsag_migrate::{
    BlsG1Point, FqPallas, FrBls381, PallasPoint, ScalarGroup, SpendingScalar,
    ed25519_ct::public_key_from_clamped_scalar,
    secp256k1_ct::{SecpPoint, secp_scalar_neg_mod_n},
};
use serde::Deserialize;
use sha3::Digest as Sha3Digest;
use tiny_keccak::{
    CShake, Hasher as TinyHasher, Keccak as TinyKeccak, Sha3 as TinySha3, Shake as TinyShake, Xof,
};

type P3Ext2 = BinomialExtensionField<P3Goldilocks, 2>;

const EMBEDDED_EXTERNAL_ORACLE_JSON: &str =
    include_str!("fixtures/lean_external_oracle_vectors.json");
const EMBEDDED_CROSS_KAT_JSONL: &str = include_str!("fixtures/lean_cross_kat.jsonl");
const EMBEDDED_KAT_SNAPSHOT_JSON: &str = include_str!("fixtures/lean_kat_snapshot.json");
const WORKSPACE_KAT_VECTORS_JSON: &str = include_str!("../../tests/kat_vectors.json");

#[derive(Deserialize)]
struct ExternalOracleRoot {
    generator: String,
    goldilocks_edges: Vec<GoldilocksEdgeVec>,
    #[serde(default)]
    goldilocks_ext4: Vec<serde_json::Value>,
    poseidon2_12: Vec<Poseidon2PermVec>,
    poseidon2_hash32: Vec<Poseidon2HashVec>,
    sponges: Vec<SpongeVec>,
    gf256_tower_gfni: Vec<Gf256TowerVec>,
    tower128: Vec<Tower128Vec>,
    secp256k1_smul: Vec<SecpSmulVec>,
    pallas_orchard_smul: Vec<PallasSmulVec>,
    bls12_381_g1_smul: Vec<BlsSmulVec>,
    ed25519_clamp_slip0010: Vec<Ed25519ClampVec>,
    fips205_slh_dsa_shake_128s_hmsg: LeanFips205HMsg128sVec,
    fips205_slh_dsa_shake_128f: LeanFips205FullSigVec,
    pors_fp_and_baggy: LeanPorsFpAndBaggyVec,
    frontier_sum_fts: Vec<LeanFrontierFtsVec>,
    whir_high_cap_and_regimes: LeanWhirHighCapVec,
    agg_sig_profiles: LeanAggSigProfilesVec,
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
struct Ed25519ClampVec {
    raw_le_hex: String,
    clamped_le_hex: String,
    normalized_mod_l_le_hex: String,
}

#[derive(Deserialize)]
struct LeanFips205HMsg128sVec {
    m_bytes: usize,
    md_bytes: usize,
    tree_bytes: usize,
    leaf_bytes: usize,
    sk_seed_hex: String,
    sk_prf_hex: String,
    pk_seed_hex: String,
    pk_root_hex: String,
    opt_rand_hex: String,
    ctx_hex: String,
    msg_hex: String,
    r_rand_hex: String,
    h_msg_30_hex: String,
    md_21_hex: String,
    idx_tree: String,
    idx_leaf: u32,
    fors_indices: Vec<String>,
    fors_leaf0_hex: String,
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

#[derive(Deserialize)]
struct LeanPorsFpAndBaggyVec {
    tree_height: usize,
    reveal: usize,
    max_auth_nodes: usize,
    draw_budget: usize,
    opening_bytes_max: usize,
    baggy_sig_bytes_max: usize,
    forgery_bits_milli: [u32; 4],
    adrs_vectors: Vec<LeanPorsAdrsVec>,
    octopus_vectors: Vec<LeanOctopusVec>,
    select_vectors: Vec<LeanPorsSelectVec>,
}

#[derive(Deserialize)]
struct LeanPorsAdrsVec {
    kind_name: String,
    kind_code: u32,
    layer: u32,
    tree: String,
    key_pair: u32,
    chain_idx: u32,
    hash_step: u32,
    adrs_32_hex: String,
}

#[derive(Deserialize)]
struct LeanOctopusVec {
    tree_height: usize,
    indices: Vec<u32>,
    positions: Vec<[u32; 2]>,
}

#[derive(Deserialize)]
struct LeanPorsSelectVec {
    custom_ascii: String,
    seed_hex: String,
    selected_indices: Option<Vec<u32>>,
    auth_len: Option<usize>,
}

#[derive(Deserialize)]
struct LeanFrontierFtsVec {
    profile: String,
    node_bytes: usize,
    tree_height: usize,
    winternitz_w: usize,
    frontier_len: usize,
    target_sum: usize,
    index_bits: usize,
    counter_bits: usize,
    signature_bytes: usize,
    rotated_epoch_vote_bytes: usize,
    frontier_cardinality_dec: String,
    decoration_cardinality_dec: String,
    total_cardinality_dec: String,
    pid_56_hex: String,
    pk_seed_hex: String,
    pk_root_hex: String,
    sk_seed_hex: String,
    sk_prf_hex: String,
    hedge_hex: String,
    msg_hex: String,
    grind_counter: u16,
    prehash_msg_hex: String,
    prf_rand_hex: String,
    squeeze_rank_hex: String,
    leaf0_start_hex: String,
    leaf0_step1_hex: String,
    merge_root_hex: String,
}

#[derive(Deserialize)]
struct LeanWhirHighCapVec {
    max_pcs_num_vars: usize,
    max_batch_polys: usize,
    ood_samples: usize,
    retired_wire_tags: Vec<u8>,
    stage_geometries: Vec<LeanWhirGeomVec>,
    regimes: Vec<LeanWhirRegimeVec>,
}

#[derive(Deserialize)]
struct LeanWhirGeomVec {
    nv: usize,
    stages: Vec<[usize; 2]>,
    folding_sum: usize,
}

#[derive(Deserialize)]
struct LeanWhirRegimeVec {
    wire_tag: u8,
    pow_bits: u8,
    query_counts: [usize; 4],
}

#[derive(Deserialize)]
struct LeanAggSigProfilesVec {
    jorts_poseidon2: LeanAggSigProfileRow,
    corduroy_poseidon2: LeanAggSigProfileRow,
}

#[derive(Deserialize)]
struct LeanAggSigProfileRow {
    wire_tag: u8,
    wots_chains: usize,
    target_sum: usize,
    num_layers: usize,
    subtree_height: usize,
    fors_trees: usize,
    fors_height: usize,
    max_sigs_log2: usize,
    raw_signature_bytes: usize,
    domain_prf_msg_u64: String,
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

fn qsag_sha3_512(input: &[u8]) -> [u8; 64] {
    let mut sp = KeccakSponge::<72>::new();
    sp.absorb(input);
    sp.finalize(0x06);
    let mut out = [0u8; 64];
    sp.squeeze(&mut out);
    out
}

#[test]
fn lean_external_spec_oracle_agrees_with_qsag_rust_and_upstream_crates() {
    let oracle = load_external_oracle();
    assert!(oracle.generator.contains("ExternalSpecOracle"));
    let _ = &oracle.goldilocks_ext4;
    for (name, len) in [
        ("goldilocks_edges", oracle.goldilocks_edges.len()),
        ("poseidon2_12", oracle.poseidon2_12.len()),
        ("poseidon2_hash32", oracle.poseidon2_hash32.len()),
        ("sponges", oracle.sponges.len()),
        ("gf256_tower_gfni", oracle.gf256_tower_gfni.len()),
        ("tower128", oracle.tower128.len()),
        ("secp256k1_smul", oracle.secp256k1_smul.len()),
        ("pallas_orchard_smul", oracle.pallas_orchard_smul.len()),
        ("bls12_381_g1_smul", oracle.bls12_381_g1_smul.len()),
        (
            "ed25519_clamp_slip0010",
            oracle.ed25519_clamp_slip0010.len(),
        ),
    ] {
        assert!(len > 0, "oracle section {name} must not become vacuous");
    }

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
        let pa = p3_gl(a_raw);
        let pb = p3_gl(b_raw);
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

    // 2. Quintic Fp5 (`F_p[X]/(X^5 - 3)`): qsag-agg <-> Plonky3 `p3_fp5_*`
    {
        use qsag_agg::QuinticFp5;
        let x = [17u64, GOLDILOCKS_P - 3, 0x1_0000_0001, 42, 999_999];
        let y = [GOLDILOCKS_P - 1, 7, 13, 0xFFFF_FFFF, 3];
        let qx = QuinticFp5::from_limbs(x.map(AggGoldilocks::from_u64_reduced));
        let qy = QuinticFp5::from_limbs(y.map(AggGoldilocks::from_u64_reduced));
        assert_eq!((qx * qy).to_limbs().map(|l| l.to_canonical_u64()), p3_fp5_mul(x, y));
        assert_eq!(qx.inv_or_zero().to_limbs().map(|l| l.to_canonical_u64()), p3_fp5_inv(x));
        assert_eq!(qx.frobenius().to_limbs().map(|l| l.to_canonical_u64()), p3_fp5_pow(x, GOLDILOCKS_P));
    }

    // 3. Canonical Poseidon2 width-12 permutation, its inverse, and the `hash32` sponge:
    //    Lean <-> qsag-core <-> the dense-matrix reference.
    assert!(!oracle.poseidon2_12.is_empty() && !oracle.poseidon2_hash32.is_empty());
    for row in &oracle.poseidon2_12 {
        let inp: [u64; 12] = core::array::from_fn(|i| row.input[i].parse().unwrap());
        let lean_perm: [u64; 12] = core::array::from_fn(|i| row.perm[i].parse().unwrap());
        let lean_inv: [u64; 12] = core::array::from_fn(|i| row.inv[i].parse().unwrap());
        let canon_in = inp.map(|v| v % GOLDILOCKS_P);

        assert_eq!(poseidon2_ref::perm12(&inp), lean_perm);
        assert_eq!(poseidon2_ref::perm12_inv(&inp), lean_inv);

        let mut st = inp.map(CoreGoldilocks::from_u64_reduced);
        poseidon2_perm12(&mut st);
        assert_eq!(st.map(|x| x.to_canonical_u64()), lean_perm);

        let mut roundtrip = lean_inv.map(CoreGoldilocks::from_u64_reduced);
        poseidon2_perm12(&mut roundtrip);
        assert_eq!(roundtrip.map(|x| x.to_canonical_u64()), canon_in);
    }
    for row in &oracle.poseidon2_hash32 {
        let msg = hex::decode(&row.msg_hex).unwrap();
        assert_eq!(
            hex::encode(poseidon2_ref::hash32(&msg)),
            row.poseidon2_hash32_hex
        );
        assert_eq!(
            hex::encode(poseidon2_hash32(&msg)),
            row.poseidon2_hash32_hex
        );
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

        // qsag-core / qsag-accel
        assert_eq!(sha3_256(&msg).as_slice(), lean_sha3_256.as_slice());
        assert_eq!(qsag_sha3_512(&msg).as_slice(), lean_sha3_512.as_slice());
        assert_eq!(keccak256(&msg).as_slice(), lean_keccak256.as_slice());
        assert_eq!(shake256_xof(64, &msg), lean_shake64);
        assert_eq!(
            cshake256_xof(64, b"QSAG.EXTERNAL.SPEC", &msg),
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

        let mut tk_cshake = CShake::v256(b"", b"QSAG.EXTERNAL.SPEC");
        tk_cshake.update(&msg);
        let mut out_cshake64 = [0u8; 64];
        tk_cshake.squeeze(&mut out_cshake64);
        assert_eq!(out_cshake64.as_slice(), lean_cshake64.as_slice());
    }

    // 5. Wiedemann Binary Tower `GF(2^8)` (`T_3`) <-> Intel `GFNI` AES `0x11B` isomorphism & `Tower128` (`T_7`):
    for row in &oracle.gf256_tower_gfni {
        assert_eq!(TowerGf256(row.a).mul(TowerGf256(row.b)).0, row.t3_mul);
        assert_eq!(gfni_affine_byte(GFNI_MAT_T3_TO_POLY, row.a, 0), row.phi_a);
        assert_eq!(gfni_affine_byte(GFNI_MAT_T3_TO_POLY, row.b, 0), row.phi_b);
        let poly_prod = gf256_poly11b_mul(row.phi_a, row.phi_b);
        assert_eq!(
            gfni_affine_byte(GFNI_MAT_POLY_TO_T3, poly_prod, 0),
            row.t3_mul
        );
        let poly_inv = gf256_poly11b_inv(row.phi_a);
        assert_eq!(
            gfni_affine_byte(GFNI_MAT_POLY_TO_T3, poly_inv, 0),
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

        // Reduce 256-bit integer scalar modulo prime curve order `PALLAS_Q` when `sk_le >= PALLAS_Q`
        // (row 4 in `ExternalSpecOracle.lean` intentionally tests `[k] SpendAuthG` for a scalar `k`
        // in `(q_pallas, r_bls381)`, exercising prime-order subgroup wrap `[q_pallas] G = O`!).
        let mut limbs = [
            u64::from_le_bytes(sk_le[0..8].try_into().unwrap()),
            u64::from_le_bytes(sk_le[8..16].try_into().unwrap()),
            u64::from_le_bytes(sk_le[16..24].try_into().unwrap()),
            u64::from_le_bytes(sk_le[24..32].try_into().unwrap()),
        ];
        let q_mod = qsag_migrate::pallas::PALLAS_Q;
        let ge_q = |a: &[u64; 4]| -> bool {
            for i in (0..4).rev() {
                if a[i] != q_mod[i] {
                    return a[i] > q_mod[i];
                }
            }
            true
        };
        if ge_q(&limbs) {
            // Both `qsag-migrate` and upstream `pasta_curves` must reject non-canonical `sk_le >= q`.
            assert!(FqPallas::from_nonzero_le_bytes(&sk_le).is_none());
            assert!(Option::<PallasRefFq>::from(ff::PrimeField::from_repr(sk_le)).is_none());
            while ge_q(&limbs) {
                let mut borrow = 0u128;
                for i in 0..4 {
                    let diff = (limbs[i] as u128)
                        .wrapping_sub(q_mod[i] as u128)
                        .wrapping_sub(borrow);
                    limbs[i] = diff as u64;
                    borrow = (diff >> 127) & 1;
                }
            }
        }
        let mut sk_canon_le = [0u8; 32];
        for (i, &w) in limbs.iter().enumerate() {
            sk_canon_le[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
        }

        // qsag-migrate
        let qfq = FqPallas::from_nonzero_le_bytes(&sk_canon_le).unwrap();
        let qpt = PallasPoint::spend_auth_mul_ct(&qfq);
        let (qx, qy) = qpt.to_affine().unwrap();
        assert_eq!(qx.to_le_bytes(), x_le);
        assert_eq!(qy.to_le_bytes(), y_le);
        assert_eq!(qpt.to_compressed_bytes(), comp);

        // Upstream `pasta_curves`
        let ref_fq = Option::<PallasRefFq>::from(ff::PrimeField::from_repr(sk_canon_le)).unwrap();
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
    let oracle_pk = hex::decode(&f.pk_hex).unwrap();
    let oracle_sk = hex::decode(&f.sk_hex).unwrap();
    let oracle_sig = hex::decode(&f.sig_hex).unwrap();
    assert_eq!(oracle_sig.len(), slh_dsa_shake_128f::SIG_LEN);

    let params_128f = &Fips205Params::SLH_DSA_SHAKE_128F;
    let (q_sk, q_pk) = slh_keygen_internal(params_128f, &sk_seed, &sk_prf, &pk_seed).unwrap();
    assert_eq!(q_pk.to_bytes(), oracle_pk);
    assert_eq!(q_sk.to_bytes(), oracle_sk);
    let q_sig = slh_sign(params_128f, &msg, &ctx, &q_sk, Some(&opt_rand)).unwrap();
    assert_eq!(
        q_sig, oracle_sig,
        "Lean 4 Fips205.lean signature must match qsag_core::fips205 byte-for-byte"
    );
    assert!(slh_verify(params_128f, &msg, &q_sig, &ctx, &q_pk));

    // Upstream `fips205` crate verification of the Lean-4-generated 17,088-byte signature!
    let (up_pk, up_sk) = slh_dsa_shake_128f::KG::keygen_with_seeds(&sk_seed, &sk_prf, &pk_seed);
    assert_eq!(up_pk.into_bytes().as_slice(), oracle_pk.as_slice());
    assert_eq!(up_sk.into_bytes().as_slice(), oracle_sk.as_slice());
    let oracle_pk_arr: [u8; slh_dsa_shake_128f::PK_LEN] = oracle_pk.try_into().unwrap();
    let oracle_sig_arr: [u8; slh_dsa_shake_128f::SIG_LEN] = oracle_sig.try_into().unwrap();
    let up_pk_decoded = slh_dsa_shake_128f::PublicKey::try_from_bytes(&oracle_pk_arr).unwrap();
    assert!(
        up_pk_decoded.verify(&msg, &oracle_sig_arr, &ctx),
        "Upstream `fips205` crate must accept the 17,088-byte signature produced by Lean 4 spec!"
    );

    // 8. NIST FIPS 205 `SLH-DSA-SHAKE-128s` (`m = 30 = 21 + 7 + 2`) `H_msg`, digest splitting,
    //    and FORS leaf 0 (`Fips205.lean` `slhDsaShake128s` vs `qsag_core::fips205` vs upstream `fips205`):
    let s128 = &oracle.fips205_slh_dsa_shake_128s_hmsg;
    let params_128s = &Fips205Params::SLH_DSA_SHAKE_128S;
    assert_eq!(s128.m_bytes, 30, "FIPS 205 Table 2 mandates m=30 for 128s");
    assert_eq!(s128.md_bytes, 21);
    assert_eq!(s128.tree_bytes, 7);
    assert_eq!(s128.leaf_bytes, 2);
    assert_eq!(params_128s.m, s128.m_bytes);

    let s_sk_seed: [u8; 16] = hex::decode(&s128.sk_seed_hex).unwrap().try_into().unwrap();
    let s_sk_prf: [u8; 16] = hex::decode(&s128.sk_prf_hex).unwrap().try_into().unwrap();
    let s_pk_seed: [u8; 16] = hex::decode(&s128.pk_seed_hex).unwrap().try_into().unwrap();
    let s_pk_root: [u8; 16] = hex::decode(&s128.pk_root_hex).unwrap().try_into().unwrap();
    let s_opt_rand: [u8; 16] = hex::decode(&s128.opt_rand_hex).unwrap().try_into().unwrap();
    let s_ctx = hex::decode(&s128.ctx_hex).unwrap();
    let s_msg = hex::decode(&s128.msg_hex).unwrap();
    let expected_r_rand = hex::decode(&s128.r_rand_hex).unwrap();
    let expected_h_msg = hex::decode(&s128.h_msg_30_hex).unwrap();
    let expected_md = hex::decode(&s128.md_21_hex).unwrap();
    let expected_idx_tree: u128 = s128.idx_tree.parse().unwrap();
    let expected_fors_indices: Vec<u32> = s128
        .fors_indices
        .iter()
        .map(|s| s.parse().unwrap())
        .collect();
    let expected_fors_leaf0 = hex::decode(&s128.fors_leaf0_hex).unwrap();

    assert_eq!(expected_h_msg.len(), 30);
    let m_prime_128s = format_pure_m_prime(&s_msg, &s_ctx).unwrap();
    let got_r_rand = fips205_prf_msg(16, &s_sk_prf, &s_opt_rand, &m_prime_128s);
    assert_eq!(got_r_rand.as_slice(), expected_r_rand.as_slice());
    let got_h_msg = fips205_h_msg(
        params_128s.m,
        got_r_rand.as_slice(),
        &s_pk_seed,
        &s_pk_root,
        &m_prime_128s,
    );
    assert_eq!(got_h_msg, expected_h_msg);
    assert_eq!(&got_h_msg[..21], expected_md.as_slice());

    let (got_fors_indices, got_idx_tree, got_idx_leaf) =
        split_digest_indices(params_128s, &got_h_msg);
    assert_eq!(got_idx_tree, expected_idx_tree);
    assert_eq!(got_idx_leaf, s128.idx_leaf);
    assert_eq!(got_fors_indices, expected_fors_indices);

    let fors_sk_adrs = Fips205Adrs {
        layer: 0,
        tree: got_idx_tree,
        adrs_type: Fips205AdrsType::ForsPrf,
        key_pair: got_idx_leaf,
        f5: 0,
        f6: got_fors_indices[0],
    };
    let fors_leaf_adrs = Fips205Adrs {
        layer: 0,
        tree: got_idx_tree,
        adrs_type: Fips205AdrsType::ForsTree,
        key_pair: got_idx_leaf,
        f5: 0,
        f6: got_fors_indices[0],
    };
    let fors_sk0 = fips205_prf(16, &s_pk_seed, &s_sk_seed, &fors_sk_adrs);
    let fors_leaf0 = fips205_f(16, &s_pk_seed, &fors_leaf_adrs, &fors_sk0);
    assert_eq!(fors_leaf0.as_slice(), expected_fors_leaf0.as_slice());

    // Cross-check full 7,856-byte `SLH-DSA-SHAKE-128s` signing & verification against upstream `fips205`!
    let (q_sk_128s, q_pk_128s) =
        slh_keygen_internal(params_128s, &s_sk_seed, &s_sk_prf, &s_pk_seed).unwrap();
    let (up_pk_128s, up_sk_128s) =
        slh_dsa_shake_128s::KG::keygen_with_seeds(&s_sk_seed, &s_sk_prf, &s_pk_seed);
    assert_eq!(
        q_pk_128s.to_bytes().as_slice(),
        up_pk_128s.clone().into_bytes().as_slice()
    );
    let q_sig_128s = slh_sign(params_128s, &s_msg, &s_ctx, &q_sk_128s, Some(&s_opt_rand)).unwrap();
    assert_eq!(q_sig_128s.len(), slh_dsa_shake_128s::SIG_LEN);
    let q_sig_128s_arr: [u8; slh_dsa_shake_128s::SIG_LEN] = q_sig_128s.clone().try_into().unwrap();
    assert!(up_pk_128s.verify(&s_msg, &q_sig_128s_arr, &s_ctx));
    assert!(slh_verify(
        params_128s,
        &s_msg,
        &q_sig_128s,
        &s_ctx,
        &q_pk_128s
    ));
    let _ = up_sk_128s;

    // 9. Ed25519 RFC 8032 clamping & SLIP-0010 scalar normalization (`ActiveMigrationZeroTest.lean`
    //    vs `qsag_migrate::ed25519_ct`, `SpendingScalar`, and `curve25519-dalek`!):
    for row in &oracle.ed25519_clamp_slip0010 {
        let raw_le: [u8; 32] = hex::decode(&row.raw_le_hex).unwrap().try_into().unwrap();
        let lean_clamped: [u8; 32] = hex::decode(&row.clamped_le_hex)
            .unwrap()
            .try_into()
            .unwrap();
        let lean_norm: [u8; 32] = hex::decode(&row.normalized_mod_l_le_hex)
            .unwrap()
            .try_into()
            .unwrap();

        let mut rust_clamped = raw_le;
        rust_clamped[0] &= 248;
        rust_clamped[31] = (rust_clamped[31] & 127) | 64;
        assert_eq!(rust_clamped, lean_clamped);

        let dalek_scalar = DalekScalar::from_bytes_mod_order(rust_clamped);
        assert_eq!(dalek_scalar.to_bytes(), lean_norm);

        let spend_scalar = SpendingScalar::from_le_bytes(lean_norm, ScalarGroup::Ed25519)
            .expect("normalized SLIP-0010 scalar must be canonical nonzero mod L");
        assert_eq!(*spend_scalar.as_le_bytes(), lean_norm);

        let dalek_pk = (ED25519_BASEPOINT_POINT * dalek_scalar)
            .compress()
            .to_bytes();
        assert_eq!(public_key_from_clamped_scalar(&rust_clamped), dalek_pk);
        assert_eq!(public_key_from_clamped_scalar(&lean_norm), dalek_pk);
    }
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
                let pa = p3_gl(a);
                let pb = p3_gl(b);
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
                let px = P3Ext2::from_base_slice(&[p3_gl(x_limbs[0]), p3_gl(x_limbs[1])]);
                let py = P3Ext2::from_base_slice(&[p3_gl(y_limbs[0]), p3_gl(y_limbs[1])]);
                let (qz, pz) = match parts[1] {
                    "add" => (qx + qy, px + py),
                    "sub" => (qx - qy, px - py),
                    "mul" => (qx * qy, px * py),
                    "inv" => (
                        qx.inv().unwrap_or(GoldilocksExt2::ZERO),
                        px.try_inverse().unwrap_or_else(P3Ext2::zero),
                    ),
                    other => panic!("unexpected ext2 op {other}"),
                };
                let q_str = format!("{},{}", qz.c0.to_canonical_u64(), qz.c1.to_canonical_u64());
                let ps: &[P3Goldilocks] = pz.as_base_slice();
                let p_str = format!("{},{}", ps[0].as_canonical_u64(), ps[1].as_canonical_u64());
                assert_eq!(q_str, *expected, "qsag ext2 mismatch on {req}");
                assert_eq!(p_str, *expected, "p3 ext2 mismatch on {req}");
            }
            "ext4" => {
                // Retired quartic extension lines in static JSONL fixture are ignored in Stage 2.
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
                let seq: [u64; 12] = core::array::from_fn(|i| n + i as u64);
                let reference = poseidon2_ref::perm12(&seq).map(|x| x.to_string()).join(",");
                assert_eq!(reference, *expected);
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
                    let [rl, rr, rt]: [[u64; 4]; 3] =
                        core::array::from_fn(|b| core::array::from_fn(|i| n + (4 * b + i) as u64));
                    let reference = poseidon2_ref::compress(rl, rr, rt);
                    assert_eq!(reference.map(|x| x.to_string()).join(","), *expected);
                    let core_z = hem_poseidon2_compress12_ff(
                        rl.map(CoreGoldilocks::from_u64_reduced),
                        rr.map(CoreGoldilocks::from_u64_reduced),
                        rt.map(CoreGoldilocks::from_u64_reduced),
                    );
                    assert_eq!(core_z.map(|x| x.to_canonical_u64()), reference);
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
            "fp5" => {
                use qsag_agg::zk_hem::v2::field5::Fp5;
                let xl: [u64; 5] = parts[2]
                    .split(',')
                    .map(|s| s.parse().unwrap())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let yl: [u64; 5] = parts[3]
                    .split(',')
                    .map(|s| s.parse().unwrap())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let qx = Fp5::from_limbs(xl.map(AggGoldilocks::from_u64_reduced));
                let qy = Fp5::from_limbs(yl.map(AggGoldilocks::from_u64_reduced));
                // Independent schoolbook F_p[X]/(X^5 - 3) multiplication over Plonky3 Goldilocks.
                let p3_fp5_mul = |a: [u64; 5], b: [u64; 5]| -> [u64; 5] {
                    let mut out = [P3Goldilocks::zero(); 5];
                    let w = p3_gl(3);
                    for i in 0..5 {
                        for j in 0..5 {
                            let prod = p3_gl(a[i]) * p3_gl(b[j]);
                            if i + j < 5 {
                                out[i + j] += prod;
                            } else {
                                out[i + j - 5] += prod * w;
                            }
                        }
                    }
                    out.map(|v| v.as_canonical_u64())
                };
                if parts[1] == "norm" {
                    let got = qx.norm().to_canonical_u64().to_string();
                    assert_eq!(got, *expected, "fp5 norm mismatch on {req}");
                } else {
                    let qz = match parts[1] {
                        "add" => qx + qy,
                        "sub" => qx - qy,
                        "mul" => qx * qy,
                        "frob" => qx.frobenius(),
                        "inv" => qx.inverse(),
                        other => panic!("unexpected fp5 op {other}"),
                    };
                    let q_limbs = qz.to_limbs().map(|v| v.to_canonical_u64());
                    let q_str = q_limbs.map(|v| v.to_string()).join(",");
                    assert_eq!(q_str, *expected, "qsag fp5 mismatch on {req}");
                    if parts[1] == "mul" {
                        assert_eq!(p3_fp5_mul(xl, yl), q_limbs, "p3 fp5 mul mismatch on {req}");
                    } else if parts[1] == "inv" && !qx.is_zero() {
                        assert_eq!(
                            p3_fp5_mul(xl, q_limbs),
                            [1, 0, 0, 0, 0],
                            "p3 fp5 inv mismatch on {req}"
                        );
                    }
                }
            }
            "p2gl24" => match parts[1] {
                "perm" => {
                    let n: u64 = parts[2].parse().unwrap();
                    let mut s_acc: [u64; 24] = core::array::from_fn(|i| {
                        CoreGoldilocks::from_u64_reduced(n + i as u64).to_canonical_u64()
                    });
                    let mut s_agg: [AggGoldilocks; 24] =
                        core::array::from_fn(|i| AggGoldilocks::from_u64_reduced(n + i as u64));
                    qsag_accel::poseidon2::poseidon2_gl24_perm(&mut s_acc);
                    qsag_agg::sponge::poseidon2_gl24_perm(&mut s_agg);
                    assert_eq!(s_acc, s_agg.map(|x| x.to_canonical_u64()));
                    assert_eq!(s_acc.map(|x| x.to_string()).join(","), *expected);
                }
                "jive" => {
                    let n: u64 = parts[2].parse().unwrap();
                    let l_acc: [u64; 7] = core::array::from_fn(|i| {
                        CoreGoldilocks::from_u64_reduced(n + i as u64).to_canonical_u64()
                    });
                    let r_acc: [u64; 7] = core::array::from_fn(|i| {
                        CoreGoldilocks::from_u64_reduced(n + 7 + i as u64).to_canonical_u64()
                    });
                    let t_acc = [
                        CoreGoldilocks::from_u64_reduced(n + 14).to_canonical_u64(),
                        CoreGoldilocks::from_u64_reduced(n + 15).to_canonical_u64(),
                    ];
                    let z_acc =
                        qsag_accel::poseidon2::poseidon2_gl24_compress_merkle(&l_acc, &r_acc, &t_acc);
                    let z_agg = qsag_agg::sponge::poseidon2_gl24_compress_merkle(
                        &l_acc.map(AggGoldilocks::from_u64_reduced),
                        &r_acc.map(AggGoldilocks::from_u64_reduced),
                        &t_acc.map(AggGoldilocks::from_u64_reduced),
                    )
                    .map(|x| x.to_canonical_u64());
                    assert_eq!(z_acc, z_agg);
                    assert_eq!(z_acc.map(|x| x.to_string()).join(","), *expected);
                }
                "hash56" => {
                    let dom: u64 = parts[2].parse().unwrap();
                    let msg = hex::decode(parts[3]).unwrap();
                    let h_acc = qsag_accel::poseidon2::poseidon2_gl24_hash56(dom, &msg);
                    let h_agg = qsag_agg::sponge::poseidon2_gl24_hash56(dom, &msg);
                    assert_eq!(h_acc, h_agg);
                    assert_eq!(hex::encode(h_acc), *expected);
                }
                other => panic!("unexpected p2gl24 op {other}"),
            },
            "turbo400" => {
                use qsag_agg::HemQuinticProfile;
                use qsag_agg::zk_hem::v2::field5::Fp5;
                use qsag_agg::zk_hem::v2::hash::Hasher as V2Hasher;
                use qsag_agg::zk_hem::v2::params::Profile as V2Profile;
                let h = V2Hasher::new(V2Profile::TurboShakeJohnson400);
                match parts[1] {
                    "perm12" => {
                        let n: u64 = parts[2].parse().unwrap();
                        let mut s1: [u64; 25] = core::array::from_fn(|i| {
                            if n == 0 { 0 } else { n.wrapping_add(i as u64) }
                        });
                        let mut s2 = s1;
                        qsag_agg::sponge::keccak_p1600_12(&mut s1);
                        qsag_ass2::wire::keccak_p1600_12(&mut s2);
                        assert_eq!(s1, s2);
                        assert_eq!(s1.map(|x| x.to_string()).join(","), *expected);
                    }
                    "zkh2_salt" => {
                        let seed: [u8; 32] = core::array::from_fn(|i| i as u8);
                        assert_eq!(hex::encode(h.salt(&seed, parts[2].parse().unwrap())), *expected);
                    }
                    "zkh2_leaf_ext" => {
                        let got = h.leaf_ext(
                            parts[2].parse().unwrap(),
                            parts[3].parse().unwrap(),
                            &[Fp5::ONE, Fp5::X],
                        );
                        assert_eq!(hex::encode(got), *expected);
                    }
                    "zkh2_node" => {
                        let l: [u8; 50] = core::array::from_fn(|i| i as u8);
                        let r: [u8; 50] = core::array::from_fn(|i| (100 + i) as u8);
                        assert_eq!(
                            hex::encode(h.node(parts[2].parse().unwrap(), &l, &r)),
                            *expected
                        );
                    }
                    "zkh2_root" => {
                        let top: [u8; 50] = core::array::from_fn(|i| i as u8);
                        assert_eq!(
                            hex::encode(h.root(
                                parts[2].parse().unwrap(),
                                parts[3].parse().unwrap(),
                                &top
                            )),
                            *expected
                        );
                    }
                    "hqm2_leaf" => {
                        let sym: [u8; 40] = core::array::from_fn(|i| i as u8);
                        assert_eq!(
                            hex::encode(HemQuinticProfile::turbo_canopy_leaf(
                                parts[2].parse().unwrap(),
                                parts[3].parse().unwrap(),
                                &sym
                            )),
                            *expected
                        );
                    }
                    "hqm2_node" => {
                        let l: [u8; 50] = core::array::from_fn(|i| i as u8);
                        let r: [u8; 50] = core::array::from_fn(|i| (50 + i) as u8);
                        assert_eq!(
                            hex::encode(HemQuinticProfile::turbo_canopy_node(
                                parts[2].parse().unwrap(),
                                &l,
                                &r
                            )),
                            *expected
                        );
                    }
                    "hqm2_root" => {
                        let top: [u8; 50] = core::array::from_fn(|i| i as u8);
                        assert_eq!(
                            hex::encode(HemQuinticProfile::turbo_canopy_root(
                                parts[2].parse().unwrap(),
                                parts[3].parse().unwrap(),
                                &top
                            )),
                            *expected
                        );
                    }
                    "hqm2_gl24_leaf" => {
                        let sym: [u8; 40] = core::array::from_fn(|i| i as u8);
                        assert_eq!(
                            hex::encode(HemQuinticProfile::gl24_canopy_leaf(
                                parts[2].parse().unwrap(),
                                parts[3].parse().unwrap(),
                                &sym
                            )),
                            *expected
                        );
                    }
                    "hqm2_gl24_node" => {
                        let pack = |base: u64| -> [u8; 56] {
                            let mut b = [0u8; 56];
                            for i in 0..7 {
                                b[8 * i..8 * (i + 1)]
                                    .copy_from_slice(&(base + i as u64).to_le_bytes());
                            }
                            b
                        };
                        assert_eq!(
                            hex::encode(HemQuinticProfile::gl24_canopy_node(
                                parts[2].parse().unwrap(),
                                &pack(1),
                                &pack(8)
                            )),
                            *expected
                        );
                    }
                    other => panic!("unexpected turbo400 op {other}"),
                }
            }
            "hqm2fs" => {
                use qsag_agg::{
                    AggSigProfile, HemQuinticProfile, SignerBitmap, SigningMode, ValidatorPublicKey,
                };
                let prof = match parts[2] {
                    "1" => HemQuinticProfile::TurboShake400,
                    "2" => HemQuinticProfile::Poseidon2Gl24,
                    other => panic!("unexpected hqm2fs profile {other}"),
                };
                let mk_pk = |base: u64| ValidatorPublicKey {
                    profile: AggSigProfile::JortsPoseidon2,
                    pk_seed: core::array::from_fn(|i| AggGoldilocks::from_u64_reduced(base + i as u64)),
                    pk_root: core::array::from_fn(|i| {
                        AggGoldilocks::from_u64_reduced(base + 4 + i as u64)
                    }),
                };
                let pks = [mk_pk(1), mk_pk(9)];
                match parts[1] {
                    "shared_chain" | "shared_fp5" => {
                        let bm = SignerBitmap::from_active_indices(2, &[0]).unwrap();
                        let mut tr = prof
                            .open_transcript(&pks, &bm, &SigningMode::SharedMessage(b"hqm2-shared"))
                            .unwrap();
                        let got = if parts[1] == "shared_chain" {
                            hex::encode(tr.digest())
                        } else {
                            tr.squeeze_fp5(b"OOD")
                                .to_limbs()
                                .map(|l| l.to_canonical_u64().to_string())
                                .join(",")
                        };
                        assert_eq!(got, *expected, "hqm2fs mismatch on {req}");
                    }
                    "persig_chain" | "persig_idx" => {
                        let bm = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
                        let msgs: [&[u8]; 2] = [b"sig-a", b"sig-bb"];
                        let mut tr = prof
                            .open_transcript(&pks, &bm, &SigningMode::PerSignerMessages(&msgs))
                            .unwrap();
                        let got = if parts[1] == "persig_chain" {
                            hex::encode(tr.digest())
                        } else {
                            tr.squeeze_distinct_indices(b"QUERY", 64, 6)
                                .into_iter()
                                .map(|i| i.to_string())
                                .collect::<Vec<_>>()
                                .join(",")
                        };
                        assert_eq!(got, *expected, "hqm2fs mismatch on {req}");
                    }
                    other => panic!("unexpected hqm2fs op {other}"),
                }
            }
            "ass2wotsc" => match parts[1] {
                "ts256" => {
                    let mut out = vec![0u8; parts[2].parse().unwrap()];
                    let msg = hex::decode(parts[3]).unwrap();
                    qsag_ass2::wire::turboshake256(&msg, &mut out);
                    assert_eq!(hex::encode(out), *expected);
                }
                "step" => {
                    let node: [u8; 16] = hex::decode(parts[4]).unwrap().try_into().unwrap();
                    let got = qsag_ass2::wire::wotsc_step(
                        &node,
                        parts[2].parse().unwrap(),
                        parts[3].parse().unwrap(),
                    );
                    assert_eq!(hex::encode(got), *expected);
                }
                "pubkey" => {
                    let sk: [u8; 32] = hex::decode(parts[2]).unwrap().try_into().unwrap();
                    assert_eq!(hex::encode(qsag_ass2::wire::owner_wotsc_pubkey(&sk)), *expected);
                }
                "cap_code" => {
                    let img: [u8; 16] = hex::decode(parts[2]).unwrap().try_into().unwrap();
                    let sib: [u8; 16] = hex::decode(parts[3]).unwrap().try_into().unwrap();
                    assert_eq!(
                        hex::encode(qsag_ass2::wire::capability_commit_code(&img, &sib)),
                        *expected
                    );
                }
                "cap_cth" => {
                    let sib: [u8; 16] = hex::decode(parts[2]).unwrap().try_into().unwrap();
                    let req: [u8; 16] = hex::decode(parts[3]).unwrap().try_into().unwrap();
                    assert_eq!(
                        hex::encode(qsag_ass2::wire::capability_commit_cth(&sib, &req)),
                        *expected
                    );
                }
                "img_id" => {
                    let enc: [u8; 32] = hex::decode(parts[2]).unwrap().try_into().unwrap();
                    let ws: Vec<u32> = parts[3]
                        .split(',')
                        .map(|s| s.parse().unwrap())
                        .collect();
                    assert_eq!(
                        hex::encode(qsag_ass2::wire::compute_image_id(&enc, &ws)),
                        *expected
                    );
                }
                "chal" => {
                    let salt: u64 = parts[2].parse().unwrap();
                    let enc = [0xa5u8; 32];
                    let nonce: [u8; 16] = core::array::from_fn(|i| (i + 1) as u8);
                    let cap = [0x33u8; 16];
                    let next = [0x77u8; 32];
                    let d = qsag_ass2::wire::wotsc_challenge_digest(
                        &enc, 0x12, 0, &nonce, 0, &cap, &next, salt,
                    );
                    let ok =
                        d.iter().map(|&b| u32::from(b)).sum::<u32>() == qsag_ass2::wire::WOTSC_TARGET_SUM;
                    assert_eq!(format!("{};{ok}", hex::encode(d)), *expected);
                }
                other => panic!("unexpected ass2wotsc op {other}"),
            },
            other => panic!("unexpected CrossKat tag {other}"),
        }
    }
    assert_eq!(count, 342, "expected all 342 Lean CrossKat records");

    // The `qsag-kat` snapshot is the same artifact as the workspace `tests/kat_vectors.json`.
    assert_eq!(
        EMBEDDED_KAT_SNAPSHOT_JSON, WORKSPACE_KAT_VECTORS_JSON,
        "tests/kat_vectors.json drifted from validation/tests/fixtures/lean_kat_snapshot.json"
    );
    let snap: serde_json::Value =
        serde_json::from_str(EMBEDDED_KAT_SNAPSHOT_JSON).expect("parse lean_kat_snapshot.json");

    // Its Poseidon2 section, against the dense-matrix reference and `qsag-core`.
    let p2 = &snap["poseidon2_goldilocks_12"];
    let lanes = |key: &str| -> [u64; 12] {
        let arr = p2[key].as_array().unwrap();
        core::array::from_fn(|i| arr[i].as_str().unwrap().parse().unwrap())
    };
    let seq: [u64; 12] = core::array::from_fn(|i| i as u64);
    for (key, input) in [("perm_zero", [0u64; 12]), ("perm_seq_0_11", seq)] {
        assert_eq!(poseidon2_ref::perm12(&input), lanes(key), "{key}");
        let mut st = input.map(CoreGoldilocks::from_u64_reduced);
        poseidon2_perm12(&mut st);
        assert_eq!(st.map(|x| x.to_canonical_u64()), lanes(key), "{key}");
    }
    for (key, msg) in [
        ("hash32_empty", &b""[..]),
        ("hash32_00", &[0x00]),
        ("hash32_010203", &[0x01, 0x02, 0x03]),
        ("hash32_label", b"qsag-poseidon2-kat"),
    ] {
        let expected = p2[key].as_str().unwrap();
        assert_eq!(hex::encode(poseidon2_ref::hash32(msg)), expected, "{key}");
        assert_eq!(hex::encode(poseidon2_hash32(msg)), expected, "{key}");
    }

    // And its FIPS 205 section, against upstream `fips205`.
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
        hex::encode(up_pk.clone().into_bytes()),
        f["pk_hex"].as_str().unwrap()
    );
    // Deterministic pure signing in FIPS 205 uses `opt_rand = pk_seed`; verify `qsag_core` and
    // upstream `fips205` match the Lean snapshot's `sig_shake256_32`, `sig_head_64_hex`, and `sig_tail_64_hex`!
    let params_128f = &Fips205Params::SLH_DSA_SHAKE_128F;
    let (q_sk, _) = slh_keygen_internal(params_128f, &sk_seed, &sk_prf, &pk_seed).unwrap();
    let q_sig_bytes = slh_sign(params_128f, msg, b"", &q_sk, Some(&pk_seed)).unwrap();
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

#[test]
fn lean_external_oracle_pors_fts_whir_and_corduroy_vectors() {
    use qsag_accel::keccak::cshake256_framed_32;
    use qsag_agg::pcs::MAX_PCS_NUM_VARS;
    use qsag_agg::zk_hem::v2::params::{Profile as ZkHemV2Profile, schedule as zkhem_v2_schedule};
    use qsag_agg::sig::{
        AggSigProfile, CORDUROY_MAX_STATELESS_SIGS_PER_KEY, CORDUROY_NUM_LAYERS,
        CORDUROY_SUBTREE_HEIGHT, DOMAIN_PRF_MSG, FORS_HEIGHT, FORS_TREES, JORTS_XMSS_HEIGHT,
        WOTS_CHAINS, WOTS_TARGET_SUM,
    };
    use qsag_core::baggy::BaggyParams;
    use qsag_core::pors_fp::{PorsFpParams, octopus_positions, pors_fp_select};
    use qsag_core::sponge::keccak::Cshake256Xof;
    use qsag_core::tsw_baggy::{AdrsKind, HashAdrs};
    use qsag_external_validation::spec_ref::{
        ExactNat, cshake256_framed_32_nist_ref, frontier_fts_cardinalities_ref, octopus_cover_ref,
        pors_selection_nist_ref,
    };
    use qsag_fts::{FrontierDpTable, FrontierFtsProfile};

    let oracle = load_external_oracle();

    // 1. PORS+FP & Baggy SHA3_128F Lean <-> Rust parity
    {
        let pors = &oracle.pors_fp_and_baggy;
        let p = PorsFpParams::SHA3_128F;
        assert_eq!(pors.tree_height, p.tree_height);
        assert_eq!(pors.reveal, p.reveal);
        assert_eq!(pors.max_auth_nodes, p.max_auth_nodes);
        assert_eq!(pors.draw_budget, p.draw_budget());
        assert_eq!(pors.opening_bytes_max, p.opening_bytes_max());
        assert_eq!(
            Some(pors.baggy_sig_bytes_max),
            BaggyParams::SHA3_128F.sig_bytes_checked()
        );
        for r in 1..=4usize {
            assert_eq!(
                p.forgery_bits_milli(r as u32),
                Some(pors.forgery_bits_milli[r - 1])
            );
        }
        assert!(!pors.adrs_vectors.is_empty());
        for av in &pors.adrs_vectors {
            let kind = match (av.kind_name.as_str(), av.kind_code) {
                ("pors_prf", 7) => AdrsKind::PorsPrf,
                ("pors_tree", 8) => AdrsKind::PorsTree,
                other => panic!("unexpected PORS ADRS kind {other:?}"),
            };
            let tree: u64 = av.tree.parse().unwrap();
            let adrs = HashAdrs {
                layer: av.layer,
                tree,
                kind,
                key_pair: av.key_pair,
                chain_idx: av.chain_idx,
                hash_step: av.hash_step,
            };
            assert_eq!(hex::encode(adrs.to_bytes()), av.adrs_32_hex);
        }
        assert!(!pors.octopus_vectors.is_empty());
        for ov in &pors.octopus_vectors {
            let got = octopus_positions(ov.tree_height, &ov.indices).expect("octopus_positions");
            assert_eq!(
                Some(got.clone()),
                octopus_cover_ref(ov.tree_height, &ov.indices)
            );
            let got_arr: Vec<[u32; 2]> = got.into_iter().map(|(h, idx)| [h, idx]).collect();
            assert_eq!(got_arr, ov.positions);
        }
        assert!(!pors.select_vectors.is_empty());
        for sv in &pors.select_vectors {
            let seed = hex::decode(&sv.seed_hex).unwrap();
            let mut xof = Cshake256Xof::new(sv.custom_ascii.as_bytes());
            xof.absorb(&seed);
            let got = pors_fp_select(&p, &mut xof);
            assert_eq!(
                got,
                pors_selection_nist_ref(
                    p.tree_height,
                    p.reveal,
                    p.draw_budget(),
                    p.max_auth_nodes,
                    sv.custom_ascii.as_bytes(),
                    &seed,
                )
            );
            assert_eq!(got, sv.selected_indices);
            let got_auth_len = got
                .as_ref()
                .map(|idx| octopus_positions(p.tree_height, idx).unwrap().len());
            assert_eq!(got_auth_len, sv.auth_len);
        }
    }

    // 2. FrontierSumFts (`Compact1122` & `Full256Bit`) Lean <-> Rust <-> NIST SP 800-185 parity
    {
        assert_eq!(oracle.frontier_sum_fts.len(), 2);
        let mut profile_names: Vec<_> = oracle
            .frontier_sum_fts
            .iter()
            .map(|r| r.profile.as_str())
            .collect();
        profile_names.sort_unstable();
        assert_eq!(profile_names, ["Compact1122", "Full256Bit"]);
        for row in &oracle.frontier_sum_fts {
            let profile = match row.profile.as_str() {
                "Compact1122" => FrontierFtsProfile::Compact1122,
                "Full256Bit" => FrontierFtsProfile::Full256Bit,
                other => panic!("unexpected FrontierFtsProfile {other}"),
            };
            let p = profile.params();
            assert_eq!(row.node_bytes, p.node_bytes);
            assert_eq!(row.tree_height, p.tree_height);
            assert_eq!(row.winternitz_w, p.winternitz_w);
            assert_eq!(row.frontier_len, p.frontier_len);
            assert_eq!(row.target_sum, p.target_sum);
            assert_eq!(row.index_bits, p.index_bits);
            assert_eq!(row.counter_bits, p.counter_bits);
            assert_eq!(row.signature_bytes, profile.signature_bytes());
            assert_eq!(row.rotated_epoch_vote_bytes, 72 + profile.signature_bytes());

            let pid = profile.pid_bytes();
            assert_eq!(hex::encode(pid), row.pid_56_hex);

            let dp = FrontierDpTable::build(profile);
            let (n, d, total) = frontier_fts_cardinalities_ref(
                p.tree_height,
                p.winternitz_w,
                p.frontier_len,
                p.target_sum,
            );
            assert_eq!(n.to_decimal_string(), row.frontier_cardinality_dec);
            assert_eq!(d.to_decimal_string(), row.decoration_cardinality_dec);
            assert_eq!(total.to_decimal_string(), row.total_cardinality_dec);
            assert_eq!(
                ExactNat::from_u64_limbs_le(&dp.frontier_cardinality.0).to_decimal_string(),
                row.frontier_cardinality_dec
            );
            assert_eq!(
                ExactNat::from_u64_limbs_le(&dp.decoration_cardinality.0).to_decimal_string(),
                row.decoration_cardinality_dec
            );
            assert_eq!(
                ExactNat::from_u64_limbs_le(&dp.total_cardinality.0).to_decimal_string(),
                row.total_cardinality_dec
            );

            let pk_seed = hex::decode(&row.pk_seed_hex).unwrap();
            let pk_root = hex::decode(&row.pk_root_hex).unwrap();
            let sk_seed = hex::decode(&row.sk_seed_hex).unwrap();
            let sk_prf = hex::decode(&row.sk_prf_hex).unwrap();
            let hedge = hex::decode(&row.hedge_hex).unwrap();
            let msg = hex::decode(&row.msg_hex).unwrap();

            let checked_hash = |custom: &[u8], fields: &[&[u8]]| {
                let actual = cshake256_framed_32(custom, fields);
                assert_eq!(actual, cshake256_framed_32_nist_ref(custom, fields));
                actual
            };

            let d_rust = checked_hash(b"QSAG.FTS.MSG256.V1", &[&pid, &pk_seed, &pk_root, &msg]);
            assert_eq!(hex::encode(d_rust), row.prehash_msg_hex);

            let r_rust = checked_hash(
                b"QSAG.FTS.RAND.V1",
                &[&pid, &sk_prf, &pk_seed, &pk_root, &hedge, &[0u8], &d_rust],
            );
            assert_eq!(hex::encode(r_rust), row.prf_rand_hex);

            let ctr_be = row.grind_counter.to_be_bytes();
            let hmsg_rust = checked_hash(
                b"QSAG.FTS.HMSG.V1",
                &[&pid, &ctr_be, &pk_seed, &pk_root, &r_rust, &d_rust],
            );
            assert_eq!(hex::encode(hmsg_rust), row.squeeze_rank_hex);

            let v256_be = 256u64.to_be_bytes();
            let leaf0 = checked_hash(b"QSAG.FTS.LEAF.V1", &[&pid, &pk_seed, &v256_be, &sk_seed]);
            assert_eq!(hex::encode(leaf0), row.leaf0_start_hex);

            let step0_be = 0u64.to_be_bytes();
            let leaf0_s1 = checked_hash(
                b"QSAG.FTS.CHAIN.V1",
                &[&pid, &pk_seed, &v256_be, &step0_be, &leaf0],
            );
            assert_eq!(hex::encode(leaf0_s1), row.leaf0_step1_hex);

            let v1_be = 1u64.to_be_bytes();
            let merged = checked_hash(
                b"QSAG.FTS.MERGE.V1",
                &[&pid, &pk_seed, &v1_be, &pk_seed, &pk_root],
            );
            assert_eq!(hex::encode(merged), row.merge_root_hex);
        }
    }

    // 3. Quintic `[DKT26]` WHIR high-capacity geometries (`nv = 16..=28`) & retired tag burial (`0..=15`)
    {
        let whir = &oracle.whir_high_cap_and_regimes;
        assert_eq!(whir.max_pcs_num_vars, MAX_PCS_NUM_VARS);
        let _ = (whir.max_batch_polys, whir.ood_samples, &whir.retired_wire_tags, &whir.regimes);
        for reg in &whir.regimes {
            let _ = (reg.wire_tag, reg.pow_bits, reg.query_counts);
        }
        for retired_tag in 0u8..=15 {
            assert_eq!(ZkHemV2Profile::from_wire_tag(retired_tag), None);
        }
        for geom in whir.stage_geometries.iter().filter(|g| g.nv >= 16) {
            let sched = zkhem_v2_schedule(geom.nv).expect("certified DKT26 schedule");
            let rust_stages: Vec<[usize; 2]> = sched
                .stages
                .iter()
                .map(|s| [s.blowup.trailing_zeros() as usize, s.step_vars])
                .collect();
            assert_eq!(
                rust_stages, geom.stages,
                "nv={} Lean <-> Rust stage geometry",
                geom.nv
            );
            let sum: usize = sched.stages.iter().map(|s| s.step_vars).sum();
            assert_eq!(sum, geom.folding_sum);
            assert_eq!(sum + sched.early_stop_vars, geom.nv);
        }
    }

    // 4. Aggregation signature profiles (`JortsPoseidon2` & `CorduroyPoseidon2`)
    {
        let agg = &oracle.agg_sig_profiles;
        let jp = &agg.jorts_poseidon2;
        assert_eq!(jp.wire_tag, AggSigProfile::JortsPoseidon2 as u8);
        assert_eq!(jp.wots_chains, WOTS_CHAINS);
        assert_eq!(jp.target_sum, WOTS_TARGET_SUM);
        assert_eq!(jp.num_layers, 1);
        assert_eq!(jp.subtree_height, JORTS_XMSS_HEIGHT);
        assert_eq!(jp.fors_trees, 0);
        assert_eq!(jp.fors_height, 0);
        assert_eq!(jp.max_sigs_log2, JORTS_XMSS_HEIGHT);
        assert_eq!(
            jp.raw_signature_bytes,
            AggSigProfile::JortsPoseidon2.raw_signature_bytes()
        );
        assert_eq!(
            jp.domain_prf_msg_u64.parse::<u64>().unwrap(),
            DOMAIN_PRF_MSG
        );

        let cp = &agg.corduroy_poseidon2;
        assert_eq!(cp.wire_tag, AggSigProfile::CorduroyPoseidon2 as u8);
        assert_eq!(cp.wots_chains, WOTS_CHAINS);
        assert_eq!(cp.target_sum, WOTS_TARGET_SUM);
        assert_eq!(cp.num_layers, CORDUROY_NUM_LAYERS);
        assert_eq!(cp.subtree_height, CORDUROY_SUBTREE_HEIGHT);
        assert_eq!(cp.fors_trees, FORS_TREES);
        assert_eq!(cp.fors_height, FORS_HEIGHT);
        assert_eq!(
            1u64 << cp.max_sigs_log2,
            CORDUROY_MAX_STATELESS_SIGS_PER_KEY
        );
        assert_eq!(
            cp.raw_signature_bytes,
            AggSigProfile::CorduroyPoseidon2.raw_signature_bytes()
        );
        assert_eq!(
            cp.domain_prf_msg_u64.parse::<u64>().unwrap(),
            DOMAIN_PRF_MSG
        );
    }
}
