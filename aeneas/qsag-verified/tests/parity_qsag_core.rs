//! Live differential parity suite verifying bit-for-bit agreement between the
//! Aeneas-extracted `#![no_std]` crate `qsag-verified` and the production
//! `crates/qsag-core` implementation across all shared cryptographic primitives.

#![cfg_attr(qsag_nightly_const_option, feature(const_trait_impl, const_option_ops))]
#![cfg_attr(qsag_nightly_const_option, allow(unused_features))]
#![allow(unused)]
extern crate alloc;

include!(concat!(env!("OUT_DIR"), "/qsag_core_mods.rs"));

use field::goldilocks::{
    Goldilocks as CoreGoldilocks, GoldilocksExt2 as CoreExt2, eval_poly_goldilocks,
    lagrange_weights_zero_goldilocks,
};
use field::tower::{
    Tower128 as CoreTower128, TowerGf256 as CoreGf256, eval_poly_gf256,
    lagrange_weights_zero_gf256, tower_mul_bits,
};
use fips205::{
    Fips205Adrs as CoreAdrs, Fips205AdrsType as CoreAdrsType, SlhBlock,
    fips205_chain as core_fips205_chain, fips205_f as core_fips205_f,
    wots_base16_digits_and_csum,
};
use qsag_verified::{Gf16, Gf256, Goldilocks, GoldilocksExt2, Tower128};
use sponge::keccak::{
    cshake256_32 as core_cshake256_32, keccak_f1600 as core_keccak_f1600,
    shake256_32 as core_shake256_32,
};
use tsw_baggy::{canonical_target_sum, check_target_sum};

struct DetCshake256Stream {
    sponge: qsag_verified::Shake256Sponge,
}

impl DetCshake256Stream {
    fn new(domain_seed: u64) -> Self {
        let mut sponge =
            qsag_verified::Shake256Sponge::new_cshake256(b"QSAG.PARITY.DET.XOF/v1");
        sponge.absorb(&domain_seed.to_le_bytes());
        let mut stream = Self { sponge };
        let mut prefix = [0u8; 32];
        stream.fill_bytes(&mut prefix);
        assert_eq!(
            prefix,
            core_cshake256_32(b"QSAG.PARITY.DET.XOF/v1", &domain_seed.to_le_bytes()),
            "sample generator must match qsag-core before generating samples",
        );
        stream
    }

    fn fill_bytes(&mut self, buf: &mut [u8]) {
        self.sponge.squeeze(buf);
    }

    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0u8; 8];
        self.fill_bytes(&mut bytes);
        u64::from_le_bytes(bytes)
    }

    fn next_u128(&mut self) -> u128 {
        let mut bytes = [0u8; 16];
        self.fill_bytes(&mut bytes);
        u128::from_le_bytes(bytes)
    }
}

fn parity_goldilocks_and_ext2_against_qsag_core() {
    let mut rng = DetCshake256Stream::new(0x51A6_4701_D110_C455);
    let mut samples = Vec::with_capacity(256);
    samples.extend_from_slice(&[
        0u64,
        1,
        2,
        7,
        (1u64 << 32) - 1,
        1u64 << 32,
        (1u64 << 32) + 1,
        qsag_verified::GOLDILOCKS_PRIME - 2,
        qsag_verified::GOLDILOCKS_PRIME - 1,
        qsag_verified::GOLDILOCKS_PRIME,
        qsag_verified::GOLDILOCKS_PRIME + 1,
        u64::MAX - 1,
        u64::MAX,
    ]);
    for _ in 0..180 {
        samples.push(rng.next_u64());
    }

    for &raw in &samples {
        let ver_lift = qsag_verified::goldilocks_from_canonical(raw);
        let core_lift = CoreGoldilocks::from_canonical(raw);
        assert_eq!(ver_lift.is_ok(), core_lift.is_ok());
        if let (Ok(v), Ok(c)) = (ver_lift, core_lift) {
            assert_eq!(v.0, c.to_canonical_u64());
        }

        let ver_canon = qsag_verified::goldilocks_canon(raw);
        let core_canon = CoreGoldilocks::from_u64_reduced(raw);
        assert_eq!(ver_canon.0, core_canon.to_canonical_u64());

        assert_eq!(
            qsag_verified::goldilocks_neg(ver_canon).0,
            core_canon.const_neg().to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::goldilocks_square(ver_canon).0,
            core_canon.square().to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::goldilocks_pow7(ver_canon).0,
            core_canon.pow(7).to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::goldilocks_inv_or_zero(ver_canon).0,
            core_canon.inv_or_zero().to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::goldilocks_inv(ver_canon).map(|x| x.0),
            core_canon.checked_inv().map(|x| x.to_canonical_u64())
        );
    }

    for i in 0..80 {
        let a_ver = qsag_verified::goldilocks_canon(samples[i]);
        let b_ver = qsag_verified::goldilocks_canon(samples[samples.len() - 1 - i]);
        let ca = CoreGoldilocks::from_canonical(a_ver.0).unwrap();
        let cb = CoreGoldilocks::from_canonical(b_ver.0).unwrap();

        assert_eq!(
            qsag_verified::goldilocks_add(a_ver, b_ver).0,
            ca.const_add(cb).to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::goldilocks_sub(a_ver, b_ver).0,
            ca.const_sub(cb).to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::goldilocks_mul(a_ver, b_ver).0,
            ca.const_mul(cb).to_canonical_u64()
        );

        let wide = rng.next_u128();
        assert_eq!(
            qsag_verified::goldilocks_reduce128(wide).0,
            CoreGoldilocks::reduce128(wide).to_canonical_u64()
        );

        let a1_ver = qsag_verified::goldilocks_canon(samples[(i + 17) % samples.len()]);
        let b1_ver = qsag_verified::goldilocks_canon(samples[(i + 53) % samples.len()]);
        let ver_x = GoldilocksExt2 {
            c0: a_ver,
            c1: a1_ver,
        };
        let ver_y = GoldilocksExt2 {
            c0: b_ver,
            c1: b1_ver,
        };
        let core_x = CoreExt2::from_canonical_u64_pair(a_ver.0, a1_ver.0).unwrap();
        let core_y = CoreExt2::from_canonical_u64_pair(b_ver.0, b1_ver.0).unwrap();

        let add_v = qsag_verified::goldilocks_ext2_add(ver_x, ver_y);
        let add_c = core_x.const_add(core_y);
        assert_eq!(
            (add_v.c0.0, add_v.c1.0),
            (add_c.c0.to_canonical_u64(), add_c.c1.to_canonical_u64())
        );

        let sub_v = qsag_verified::goldilocks_ext2_sub(ver_x, ver_y);
        let sub_c = core_x.const_sub(core_y);
        assert_eq!(
            (sub_v.c0.0, sub_v.c1.0),
            (sub_c.c0.to_canonical_u64(), sub_c.c1.to_canonical_u64())
        );

        let neg_v = qsag_verified::goldilocks_ext2_neg(ver_x);
        let neg_c = core_x.const_neg();
        assert_eq!(
            (neg_v.c0.0, neg_v.c1.0),
            (neg_c.c0.to_canonical_u64(), neg_c.c1.to_canonical_u64())
        );

        let mul_v = qsag_verified::goldilocks_ext2_mul(ver_x, ver_y);
        let mul_c = core_x.const_mul(core_y);
        assert_eq!(
            (mul_v.c0.0, mul_v.c1.0),
            (mul_c.c0.to_canonical_u64(), mul_c.c1.to_canonical_u64())
        );
    }
}

fn parity_wiedemann_tower_and_shamir_against_qsag_core() {
    let mut rng = DetCshake256Stream::new(0x70E2_1280_00FF_AA55);

    // Exhaustive Gf16 (16 x 16) and Gf256 (256 x 256) parity against qsag-core!
    for a in 0u8..16 {
        for b in 0u8..16 {
            assert_eq!(
                qsag_verified::gf16_mul(Gf16(a), Gf16(b)).0 as u128,
                tower_mul_bits(2, a as u128, b as u128)
            );
        }
    }

    for a in 0u16..256 {
        let au = a as u8;
        assert_eq!(
            qsag_verified::gf256_inv(Gf256(au)).map(|v| v.0),
            CoreGf256(au).inv().map(|v| v.0)
        );
        assert_eq!(
            qsag_verified::embed_gf256_to_tower128(Gf256(au)).0,
            CoreTower128::embed_gf256(CoreGf256(au)).0
        );
        for b in 0u16..256 {
            let bu = b as u8;
            assert_eq!(
                qsag_verified::gf256_add(Gf256(au), Gf256(bu)).0,
                CoreGf256(au).add(CoreGf256(bu)).0
            );
            assert_eq!(
                qsag_verified::gf256_mul(Gf256(au), Gf256(bu)).0,
                CoreGf256(au).mul(CoreGf256(bu)).0
            );
        }
    }

    for _ in 0..256 {
        let a = rng.next_u128();
        let b = rng.next_u128();
        assert_eq!(
            qsag_verified::tower128_add(Tower128(a), Tower128(b)).0,
            CoreTower128(a).add(CoreTower128(b)).0
        );
        assert_eq!(
            qsag_verified::tower128_mul(Tower128(a), Tower128(b)).0,
            CoreTower128(a).mul(CoreTower128(b)).0
        );
    }

    // Shamir polynomial evaluation & Lagrange weights over Gf256 and Goldilocks
    let coeffs_u8 = [0x53u8, 0xCA, 0x19, 0xE7, 0x04];
    let coeffs_ver: Vec<Gf256> = coeffs_u8.iter().copied().map(Gf256).collect();
    let coeffs_core: Vec<CoreGf256> = coeffs_u8.iter().copied().map(CoreGf256).collect();
    for x in 1u8..=40 {
        assert_eq!(
            qsag_verified::shamir_eval_poly_gf256(&coeffs_ver, Gf256(x)).0,
            eval_poly_gf256(&coeffs_core, CoreGf256(x)).0
        );
    }

    let pts_u8 = [1u8, 2, 5, 9, 17];
    let pts_ver: Vec<Gf256> = pts_u8.iter().copied().map(Gf256).collect();
    let pts_core: Vec<CoreGf256> = pts_u8.iter().copied().map(CoreGf256).collect();
    let core_weights = lagrange_weights_zero_gf256(&pts_core).unwrap();
    let mut shares_ver = [Gf256(0); 5];
    for i in 0..pts_u8.len() {
        assert_eq!(
            qsag_verified::shamir_lagrange_weight_zero_gf256(&pts_ver, i).map(|v| v.0),
            Some(core_weights[i].0)
        );
        shares_ver[i] = qsag_verified::shamir_eval_poly_gf256(&coeffs_ver, pts_ver[i]);
    }
    assert_eq!(
        qsag_verified::shamir_lagrange_at_zero_gf256(&pts_ver, &shares_ver),
        Some(Gf256(coeffs_u8[0]))
    );

    let coeffs_gl_raw = [
        qsag_verified::GOLDILOCKS_PRIME - 42,
        123_456_789u64,
        9_876_543_210u64,
        777u64,
    ];
    let coeffs_gl_ver: Vec<Goldilocks> = coeffs_gl_raw.iter().copied().map(Goldilocks).collect();
    let coeffs_gl_core: Vec<CoreGoldilocks> = coeffs_gl_raw
        .iter()
        .map(|&v| CoreGoldilocks::from_canonical(v).unwrap())
        .collect();
    let pts_gl_raw = [1u64, 2, 3, 4];
    let pts_gl_ver: Vec<Goldilocks> = pts_gl_raw.iter().copied().map(Goldilocks).collect();
    let pts_gl_core: Vec<CoreGoldilocks> = pts_gl_raw
        .iter()
        .map(|&v| CoreGoldilocks::from_canonical(v).unwrap())
        .collect();
    let core_gl_weights = lagrange_weights_zero_goldilocks(&pts_gl_core).unwrap();
    let mut shares_gl_ver = [Goldilocks(0); 4];
    for i in 0..pts_gl_raw.len() {
        assert_eq!(
            qsag_verified::shamir_eval_poly_goldilocks(&coeffs_gl_ver, pts_gl_ver[i]).0,
            eval_poly_goldilocks(&coeffs_gl_core, pts_gl_core[i]).to_canonical_u64()
        );
        assert_eq!(
            qsag_verified::shamir_lagrange_weight_zero_goldilocks(&pts_gl_ver, i).map(|v| v.0),
            Some(core_gl_weights[i].to_canonical_u64())
        );
        shares_gl_ver[i] =
            qsag_verified::shamir_eval_poly_goldilocks(&coeffs_gl_ver, pts_gl_ver[i]);
    }
    assert_eq!(
        qsag_verified::shamir_lagrange_at_zero_goldilocks(&pts_gl_ver, &shares_gl_ver),
        Some(Goldilocks(coeffs_gl_raw[0]))
    );
}

fn parity_keccak_shake256_and_cshake256_against_qsag_core() {
    let mut rng = DetCshake256Stream::new(0x4ECC_AC25_6000_0001);

    for _ in 0..32 {
        let mut st_ver = [0u64; 25];
        for lane in &mut st_ver {
            *lane = rng.next_u64();
        }
        let mut st_core = st_ver;
        qsag_verified::keccak_f1600(&mut st_ver);
        core_keccak_f1600(&mut st_core);
        assert_eq!(st_ver, st_core);
    }

    for len in [0usize, 1, 3, 31, 32, 64, 135, 136, 137, 200, 271, 272, 273, 409] {
        let mut msg = vec![0u8; len];
        rng.fill_bytes(&mut msg);
        assert_eq!(qsag_verified::shake256_32(&msg), core_shake256_32(&msg));

        for custom in [
            &b""[..],
            &b"QSAG.PQ.SUITE.CSHAKE256/v1"[..],
            &b"QSAG.CRYPTO.FS.ABSORB/v1"[..],
            &[0xAAu8; 160][..],
        ] {
            assert_eq!(
                qsag_verified::cshake256_32(custom, &msg),
                core_cshake256_32(custom, &msg)
            );
        }
    }
}

fn parity_fips205_and_tsw_against_qsag_core() {
    let mut rng = DetCshake256Stream::new(0xF195_2050_AD25_0001);

    let types = [
        (qsag_verified::Fips205AdrsType::WotsHash, CoreAdrsType::WotsHash),
        (qsag_verified::Fips205AdrsType::WotsPk, CoreAdrsType::WotsPk),
        (qsag_verified::Fips205AdrsType::Tree, CoreAdrsType::Tree),
        (qsag_verified::Fips205AdrsType::ForsTree, CoreAdrsType::ForsTree),
        (qsag_verified::Fips205AdrsType::ForsRoots, CoreAdrsType::ForsRoots),
        (qsag_verified::Fips205AdrsType::WotsPrf, CoreAdrsType::WotsPrf),
        (qsag_verified::Fips205AdrsType::ForsPrf, CoreAdrsType::ForsPrf),
    ];

    for (ver_ty, core_ty) in types {
        for _ in 0..24 {
            let layer = rng.next_u64() as u32;
            let tree_hi = rng.next_u64() as u32;
            let tree_lo = rng.next_u64();
            let tree_u96 = ((tree_hi as u128) << 64) | (tree_lo as u128);
            let kp = rng.next_u64() as u32;
            let chain = rng.next_u64() as u32;
            let hash = rng.next_u64() as u32;

            let ver_adrs =
                qsag_verified::Fips205Adrs::from_tree_u96(layer, tree_u96, ver_ty, kp, chain, hash);
            let core_adrs = CoreAdrs {
                layer,
                tree: tree_u96,
                adrs_type: core_ty,
                key_pair: kp,
                f5: chain,
                f6: hash,
            };

            let ver_bytes = qsag_verified::encode_fips205_adrs(ver_adrs);
            let core_bytes = core_adrs.to_bytes();
            assert_eq!(ver_bytes, core_bytes);
            assert_eq!(qsag_verified::decode_fips205_adrs(&core_bytes), Some(ver_adrs));
            assert_eq!(CoreAdrs::from_bytes(&ver_bytes), Some(core_adrs));
        }
    }

    for _ in 0..64 {
        let mut msg16 = [0u8; 16];
        let mut pk_seed = [0u8; 16];
        let mut m1 = [0u8; 16];
        rng.fill_bytes(&mut msg16);
        rng.fill_bytes(&mut pk_seed);
        rng.fill_bytes(&mut m1);

        let ver_digits = qsag_verified::fips205_wots_checksum(&msg16);
        let (core_digits, core_len) = wots_base16_digits_and_csum(&msg16);
        assert_eq!(core_len, 35);
        assert_eq!(&ver_digits[..], &core_digits[..35]);

        let ver_adrs = qsag_verified::Fips205Adrs {
            layer: 3,
            tree_hi: 0x0102_0304,
            tree_lo: 0x0506_0708_090A_0B0C,
            adrs_type: qsag_verified::Fips205AdrsType::WotsHash,
            kp: 7,
            chain: 11,
            hash: 0,
        };
        let core_adrs = CoreAdrs {
            layer: 3,
            tree: ((0x0102_0304u128) << 64) | 0x0506_0708_090A_0B0Cu128,
            adrs_type: CoreAdrsType::WotsHash,
            key_pair: kp_val(),
            f5: 11,
            f6: 0,
        };
        let m1_blk = SlhBlock::from_slice_checked(16, &m1).unwrap();
        let ver_f = qsag_verified::fips205_f(&pk_seed, &ver_adrs, &m1);
        let core_f = core_fips205_f(16, &pk_seed, &core_adrs, &m1_blk);
        assert_eq!(&ver_f[..], core_f.as_slice());

        let start = (rng.next_u64() % 16) as u32;
        let steps = (rng.next_u64() % (16 - start as u64)) as u32;
        let ver_ch =
            qsag_verified::fips205_wots_chain(m1, start, steps, &pk_seed, ver_adrs).unwrap();
        let core_ch = core_fips205_chain(m1_blk, start, steps, &pk_seed, core_adrs);
        assert_eq!(&ver_ch[..], core_ch.as_slice());
    }

    for (w, ell1) in [(4usize, 64usize), (16, 32), (4, 8), (16, 64)] {
        let ver_t = qsag_verified::tsw_canonical_target_sum(w as u32, ell1 as u32).unwrap();
        let core_t = canonical_target_sum(w, ell1);
        assert_eq!(ver_t as usize, core_t);

        let mut digits_u32 = vec![0u32; ell1];
        let mut rem = core_t;
        for d in &mut digits_u32 {
            let take = rem.min(w - 1);
            *d = take as u32;
            rem -= take;
        }
        let digits_usize: Vec<usize> = digits_u32.iter().map(|&x| x as usize).collect();
        assert_eq!(
            qsag_verified::tsw_check_target_sum(w as u32, ell1, ver_t, &digits_u32),
            check_target_sum(w, ell1, core_t, &digits_usize)
        );
        digits_u32[0] = digits_u32[0].wrapping_add(1);
        let bad_usize: Vec<usize> = digits_u32.iter().map(|&x| x as usize).collect();
        assert_eq!(
            qsag_verified::tsw_check_target_sum(w as u32, ell1, ver_t, &digits_u32),
            check_target_sum(w, ell1, core_t, &bad_usize)
        );
    }
}

#[inline]
const fn kp_val() -> u32 {
    7
}

fn main() {
    let cases: [(&str, fn()); 4] = [
        (
            "parity_goldilocks_and_ext2_against_qsag_core",
            parity_goldilocks_and_ext2_against_qsag_core,
        ),
        (
            "parity_wiedemann_tower_and_shamir_against_qsag_core",
            parity_wiedemann_tower_and_shamir_against_qsag_core,
        ),
        (
            "parity_keccak_shake256_and_cshake256_against_qsag_core",
            parity_keccak_shake256_and_cshake256_against_qsag_core,
        ),
        (
            "parity_fips205_and_tsw_against_qsag_core",
            parity_fips205_and_tsw_against_qsag_core,
        ),
    ];
    println!("\nrunning {} differential parity tests", cases.len());
    for (name, f) in cases {
        f();
        println!("test {} ... ok", name);
    }
    println!("[parity_qsag_core] PASS: 4/4 differential parity suites matched qsag-core");
}
