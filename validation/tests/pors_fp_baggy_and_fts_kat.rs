// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Differential & Structural Validation for Canonical `Baggy` (`PORS+FP` `SHA3_128F`)
//! and `FrontierSumFts` (`Compact1122` + `RotatedEpochVote` + `Full256Bit`).
//!
//! Covers every `Lean ↔ Rust` differential & structural blind spot in Domain 1:
//! 1. `PORS+FP` (`PorsFpParams::SHA3_128F`: `h=11, k=28, max_auth=128, <= 4,994 B`):
//!    - `AdrsKind::PorsPrf = 7` and `AdrsKind::PorsTree = 8` 32-byte big-endian `HashAdrs` codecs,
//!    - Set-theoretic Octopus multiproof cover equivalence (`octopus_positions` == `octopus_cover_ref`),
//!      canonical bottom-up left-to-right ordering, sibling-pair pruning, and strict rejection of
//!      empty, duplicate, unsorted, out-of-range, non-canonical, or unpruned (`> 128`) openings,
//!    - Zero-float exact rational subset-cover security verification over `ExactNat`:
//!      `floor(-log2(C(28*r, 28) / C(2048, 28))) == [209, 157, 136, 122]` bits and exact millibit
//!      floors `[209_788, 157_024, 136_093, 122_451]` (`PorsFpSecurity.lean:sha3_128f_binomial_bits`,
//!      `sha3_128f_millibits`) vs `forgery_bits_milli` `[209_767, 156_999, 136_068, 122_425]`, plus
//!      witness that dropping index distinctness (`28^28 / 2048^28`) collapses below 209 bits.
//! 2. `Baggy` (`BaggyParams::SHA3_128F`: `d=16, h'=2, <= 71,654 B`):
//!    - Exact wire upper bound (`71,654 B`), parameter domain digest (`QSAG.BAGGY.PARAMS/v1`),
//!      single-party `baggy_reference_keygen`/`baggy_reference_sign` AND 2-of-3 dealerless
//!      `Rss256Engine` `baggy_keygen_mpc`/`baggy_sign_mpc` + `WaistbandCache` + `FirstSignedLedger`,
//!      plus wire/tamper/conflict rejection.
//! 3. `FrontierSumFts` (`Compact1122`: `w=96, h=8, L=34, S=1615, 1,122 B` + `RotatedEpochVote`
//!    `1,194 B`; `Full256Bit`: `w=5, h=8, L=72, S=144, 2,338 B`):
//!    - Exact `U384` DP cardinalities (`N_root(h, L)`, `D(L, S)`, `M(h, w, L, S)`) cross-checked
//!      against `frontier_fts_cardinalities_ref`,
//!    - Bijective `U384` `unrank <-> rank` across boundary and `proptest` ranks,
//!    - Prefix-free binary-tree antichain partition check (`[256, 512)` covered with zero overlaps,
//!      no root singleton `v=1`, ancestor+descendant pairs rejected),
//!    - Independent NIST SP 800-185 `cshake256_framed_32_nist_ref` domain verification (`56 B` PID
//!      and `QSAG.FTS.*.V1`),
//!    - Cached vs uncached signer byte-identity, `1`-time `UseBudgetExhausted` latch, and
//!      8-lane SIMD batch (`verify_frontier_fts_batch`, `verify_rotated_epoch_votes_batch`) vs
//!      scalar (`verify_frontier_fts`, `RotatedEpochVote::verify`) equivalence across partial/multi
//!      batches and adversarial faulted lanes.

use proptest::prelude::*;
use qsag_accel::CpuReferenceBackend;
use qsag_core::baggy::{
    BaggyError, BaggyParams, BaggySig, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc,
    baggy_reference_keygen, baggy_reference_sign, baggy_sign_mpc, baggy_verify,
};
use qsag_core::keccak_mpc::{RssKeyShare256, run_dealerless_rss_dkg_2of3};
use qsag_core::pors_fp::{
    PorsFpOpening, PorsFpParams, octopus_positions, pors_fp_auth, pors_fp_root, pors_fp_select,
    pors_leaf_adrs, pors_prf_adrs, pors_reference_tree,
};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_core::rss256::Rss256Engine;
use qsag_core::sponge::keccak::Cshake256Xof;
use qsag_core::tsw_baggy::{AdrsKind, PqSecretKey};
use qsag_external_validation::spec_ref::{
    ExactNat, cshake256_framed_32_nist_ref, exact_neg_log2_floor_bits,
    exact_neg_log2_floor_millibits, ff_top_exact, frontier_fts_cardinalities_ref,
    octopus_cover_ref, pors_selection_nist_ref, rational_at_least_bits,
};
use qsag_fts::{
    EpochKeyLink, FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsSignature,
    FrontierFtsSigningKey, FrontierVerifyInput, FtsEpochWal, RotatedEpochVerifyInput,
    RotatedEpochVote, U384, verify_frontier_fts, verify_frontier_fts_batch,
    verify_rotated_epoch_votes_batch,
};

struct OneShotMemWal {
    expected_key: [u8; 32],
    uses: u8,
    cap: u8,
}

impl OneShotMemWal {
    fn new(expected_key: [u8; 32], cap: u8) -> Self {
        Self {
            expected_key,
            uses: 0,
            cap,
        }
    }
}

impl FtsEpochWal for OneShotMemWal {
    fn uses_completed(&self, key: &[u8; 32]) -> Result<u8, FrontierFtsError> {
        if key != &self.expected_key {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        Ok(self.uses)
    }

    fn reserve_use(&mut self, key: &[u8; 32], next: u8) -> Result<(), FrontierFtsError> {
        if key != &self.expected_key || next != self.uses + 1 || next > self.cap {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        self.uses = next;
        Ok(())
    }
}

fn u384_to_exact_nat(v: U384) -> ExactNat {
    ExactNat::from_u64_limbs_le(&v.0)
}

fn leaf_interval(node: u32, tree_height: usize) -> Option<(u32, u32)> {
    if node <= 1 {
        return None;
    }
    let depth = 31usize.saturating_sub(node.leading_zeros() as usize);
    if depth > tree_height {
        return None;
    }
    let shift = tree_height - depth;
    Some((node << shift, (node + 1) << shift))
}

#[test]
fn pors_fp_sha3_128f_geometry_adrs_and_exact_rational_subset_cover_bounds() {
    let p = PorsFpParams::SHA3_128F;
    assert_eq!(p.tree_height, 11);
    assert_eq!(p.leaves(), 2048);
    assert_eq!(p.reveal, 28);
    assert_eq!(p.max_auth_nodes, 128);
    assert_eq!(p.draw_budget(), 88);
    assert_eq!(p.opening_bytes_max(), 4994);
    assert!(p.is_well_formed());

    // `AdrsKind::PorsPrf = 7` and `AdrsKind::PorsTree = 8` 32-byte big-endian layout:
    // `[0..4]=layer, [4..16]=tree (u96 BE -> 0..4 zero, 8..16 u64 BE), [16..20]=kind,
    //  [20..24]=key_pair, [24..28]=chain_idx(height), [28..32]=hash_step(index)`.
    assert_eq!(AdrsKind::PorsPrf as u32, 7);
    assert_eq!(AdrsKind::PorsTree as u32, 8);

    let tree_idx: u64 = 0x0123_4567_89AB_CDEF;
    let kp_idx: u32 = 3;
    let leaf_idx: u32 = 1777;

    let prf_bytes = pors_prf_adrs(tree_idx, kp_idx, leaf_idx).to_bytes();
    assert_eq!(&prf_bytes[0..8], &[0u8; 8]);
    assert_eq!(&prf_bytes[8..16], &tree_idx.to_be_bytes());
    assert_eq!(&prf_bytes[16..20], &7u32.to_be_bytes());
    assert_eq!(&prf_bytes[20..24], &kp_idx.to_be_bytes());
    assert_eq!(&prf_bytes[24..28], &0u32.to_be_bytes());
    assert_eq!(&prf_bytes[28..32], &leaf_idx.to_be_bytes());

    let leaf_bytes = pors_leaf_adrs(tree_idx, kp_idx, leaf_idx).to_bytes();
    assert_eq!(&leaf_bytes[8..16], &tree_idx.to_be_bytes());
    assert_eq!(&leaf_bytes[16..20], &8u32.to_be_bytes());
    assert_eq!(&leaf_bytes[20..24], &kp_idx.to_be_bytes());
    assert_eq!(&leaf_bytes[24..28], &0u32.to_be_bytes());
    assert_eq!(&leaf_bytes[28..32], &leaf_idx.to_be_bytes());
    assert_ne!(prf_bytes, leaf_bytes);

    // Exact zero-float rational subset-cover bounds (`PorsFpSecurity.lean:sha3_128f_binomial_bits`,
    // `sha3_128f_millibits`, `sha3_128f_rust_estimate`, `sha3_128f_rust_estimate_sound`):
    // Ratio `C(28*r, 28) / C(2048, 28) == ffTop(28*r, 28) / ffTop(2048, 28)`.
    let den = ff_top_exact(2048, 28);
    let expected_exact_bits = [209usize, 157, 136, 122];
    let expected_exact_millibits = [209_788usize, 157_024, 136_093, 122_451];
    let expected_rust_millibits = [209_767u32, 156_999, 136_068, 122_425];

    for r in 1..=4usize {
        let num = ff_top_exact(28 * r as u64, 28);
        let exact_bits = exact_neg_log2_floor_bits(&num, &den).unwrap();
        let exact_milli = exact_neg_log2_floor_millibits(&num, &den).unwrap();
        let rust_milli = p.forgery_bits_milli(r as u32).expect("forgery_bits_milli");

        assert_eq!(
            exact_bits,
            expected_exact_bits[r - 1],
            "r={r} exact integer bit floor mismatch"
        );
        assert_eq!(
            exact_milli,
            expected_exact_millibits[r - 1],
            "r={r} exact millibit floor mismatch"
        );
        assert_eq!(
            rust_milli,
            expected_rust_millibits[r - 1],
            "r={r} Rust forgery_bits_milli mismatch"
        );
        // Rust's fixed-point bound must be a sound lower bound within 26 millibits of exact.
        assert!(
            (rust_milli as usize) <= exact_milli && exact_milli - (rust_milli as usize) <= 26,
            "r={r}: rust_milli={rust_milli} vs exact_milli={exact_milli}"
        );
    }

    // Distinctness witness (`sha3_128f_bound_fails_without_distinctness`):
    // Without distinct index selection, `(28 / 2048)^28 = 2^(-173.38...) > 2^(-209)`.
    let non_distinct_num = ExactNat::from_u64(28).pow_u32(28);
    let non_distinct_den = ExactNat::from_u64(2048).pow_u32(28);
    assert!(!rational_at_least_bits(
        209,
        &non_distinct_num,
        &non_distinct_den
    ));
    assert_eq!(
        exact_neg_log2_floor_bits(&non_distinct_num, &non_distinct_den),
        Some(173)
    );
}

#[test]
fn pors_fp_octopus_sorting_uniqueness_pruning_and_tamper_rejection() {
    // 1. Exhaustive verification over all 255 non-empty subsets of height 3 against `octopus_cover_ref`.
    for mask in 1u32..(1 << 8) {
        let subset: Vec<u32> = (0..8).filter(|&i| (mask >> i) & 1 == 1).collect();
        assert_eq!(
            octopus_positions(3, &subset),
            octopus_cover_ref(3, &subset),
            "mask={mask:#010b}"
        );
    }
    for bad in [&[][..], &[3, 3], &[5, 2], &[0, 8], &[7, 7]] {
        assert_eq!(octopus_positions(3, bad), None);
        assert_eq!(octopus_cover_ref(3, bad), None);
    }

    // 2. Real `SHA3_128F` (`h = 11, k = 28, max_auth = 128`) XOF selection, pruning, and opening checks.
    let params = PorsFpParams::SHA3_128F;
    let loose_params = PorsFpParams {
        max_auth_nodes: params.reveal * params.tree_height,
        ..params
    };
    let make_xof = |ctr: u32| {
        let mut xof = Cshake256Xof::new(b"QSAG.VALIDATION.PORS_FP/v1");
        xof.absorb(&ctr.to_be_bytes());
        xof
    };

    let mut accepted_indices = None;
    let mut unpruned_indices = None;
    for ctr in 0u32..50_000 {
        let reference = |max_auth| {
            pors_selection_nist_ref(
                params.tree_height,
                params.reveal,
                params.draw_budget(),
                max_auth,
                b"QSAG.VALIDATION.PORS_FP/v1",
                &ctr.to_be_bytes(),
            )
        };
        let selected = pors_fp_select(&params, &mut make_xof(ctr));
        assert_eq!(selected, reference(params.max_auth_nodes), "counter={ctr}");
        if let Some(idx) = selected {
            if accepted_indices.is_none() {
                accepted_indices = Some(idx);
            }
        } else if unpruned_indices.is_none()
            && let Some(idx) = pors_fp_select(&loose_params, &mut make_xof(ctr))
        {
            assert_eq!(Some(idx.clone()), reference(loose_params.max_auth_nodes));
            let cover = octopus_cover_ref(params.tree_height, &idx).unwrap();
            assert!(cover.len() > params.max_auth_nodes);
            unpruned_indices = Some(idx);
        }
        if accepted_indices.is_some() && unpruned_indices.is_some() {
            break;
        }
    }

    let indices = accepted_indices.expect("must find pruned SHA3_128F subset");
    let wide_indices = unpruned_indices.expect("must find unpruned SHA3_128F subset");

    // Verify canonical sorting, distinctness, cover equivalence, and node-level ascending invariant.
    assert_eq!(indices.len(), 28);
    assert!(indices.windows(2).all(|w| w[0] < w[1]));
    let cover = octopus_positions(11, &indices).unwrap();
    assert!(cover.len() <= 128);
    assert_eq!(Some(cover.clone()), octopus_cover_ref(11, &indices));
    assert!(
        cover
            .windows(2)
            .all(|w| (w[0].0, w[0].1) < (w[1].0, w[1].1)),
        "Octopus positions must be strictly lexicographically ordered by (level, index)"
    );

    let sk = PqSecretKey {
        sk_seed: [0x31; 32],
        sk_prf: [0x42; 32],
        pk_seed: [0x53; 32],
    };
    let (secrets, levels) = pors_reference_tree(&params, &sk, 9, 2);
    let root = levels[params.tree_height][0];
    // Independent leaf-hash oracle: four LEB128-framed fields, all lengths < 128.
    // This is the legacy PQ framing, not the u64 framing used by FrontierSumFts.
    let mut adrs = [0u8; 32];
    adrs[8..16].copy_from_slice(&9u64.to_be_bytes());
    adrs[16..20].copy_from_slice(&8u32.to_be_bytes());
    adrs[20..24].copy_from_slice(&2u32.to_be_bytes());
    adrs[28..].copy_from_slice(&indices[0].to_be_bytes());
    let mut leaf_preimage = vec![4];
    for field in [
        &b"QSAG.PQ.TH_F/v1"[..],
        &sk.pk_seed,
        &adrs,
        &secrets[indices[0] as usize],
    ] {
        leaf_preimage.push(field.len() as u8);
        leaf_preimage.extend_from_slice(field);
    }
    let expected_leaf = qsag_external_validation::cshake256_nist_sp800_185_ref(
        b"",
        b"QSAG.PQ.SUITE.CSHAKE256/v1",
        &leaf_preimage,
        32,
    );
    assert_eq!(levels[0][indices[0] as usize].as_slice(), expected_leaf);

    let opening = PorsFpOpening {
        secrets: indices.iter().map(|&i| secrets[i as usize]).collect(),
        auth: pors_fp_auth(&params, &levels, &indices).unwrap(),
    };
    assert_eq!(opening.auth.len(), cover.len());
    let wire = opening.to_wire_bytes();
    assert!(wire.len() <= params.opening_bytes_max());
    let (decoded, used) = PorsFpOpening::from_wire_bytes(&params, &wire).unwrap();
    assert_eq!((decoded, used), (opening.clone(), wire.len()));
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &indices, &opening),
        Some(root)
    );

    // Unsorted, duplicate, wrong-length, out-of-range index rejections (`demo_unsorted_rejected`,
    // `demo_duplicate_rejected`).
    let mut unsorted = indices.clone();
    unsorted.swap(3, 4);
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &unsorted, &opening),
        None
    );
    let mut dup = indices.clone();
    dup[7] = dup[6];
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &dup, &opening),
        None
    );
    let mut oor = indices.clone();
    oor[27] = 2048;
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &oor, &opening),
        None
    );

    // Extra auth node, missing auth node, swapped auth nodes, and bit-flipped secret/auth.
    let mut extra = opening.clone();
    extra.auth.push([0xAA; 32]);
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &indices, &extra),
        None
    );
    let mut missing = opening.clone();
    missing.auth.pop();
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &indices, &missing),
        None
    );
    let mut flipped_sec = opening.clone();
    flipped_sec.secrets[13][0] ^= 0x01;
    assert_ne!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &indices, &flipped_sec)
            .expect("secret tamper preserves opening structure"),
        root
    );
    let mut flipped_auth = opening.clone();
    flipped_auth.auth[0][0] ^= 1;
    let mut swapped_auth = opening.clone();
    assert_ne!(swapped_auth.auth[0], swapped_auth.auth[1]);
    swapped_auth.auth.swap(0, 1);
    for bad in [flipped_auth, swapped_auth] {
        let (parsed, consumed) = PorsFpOpening::from_wire_bytes(&params, &bad.to_wire_bytes())
            .expect("auth tamper preserves canonical wire format");
        assert_eq!(consumed, wire.len());
        assert_ne!(
            pors_fp_root(&params, &sk.pk_seed, 9, 2, &indices, &parsed)
                .expect("auth tamper preserves opening structure"),
            root
        );
    }

    // Honest opening of `wide_indices` (> 128 auth nodes) succeeds under `loose_params` but
    // MUST fail closed under `SHA3_128F` in `pors_fp_auth`, `pors_fp_root`, AND `from_wire_bytes`!
    let wide_opening = PorsFpOpening {
        secrets: wide_indices.iter().map(|&i| secrets[i as usize]).collect(),
        auth: pors_fp_auth(&loose_params, &levels, &wide_indices).unwrap(),
    };
    assert_eq!(
        pors_fp_root(
            &loose_params,
            &sk.pk_seed,
            9,
            2,
            &wide_indices,
            &wide_opening
        ),
        Some(root)
    );
    assert_eq!(pors_fp_auth(&params, &levels, &wide_indices), None);
    assert_eq!(
        pors_fp_root(&params, &sk.pk_seed, 9, 2, &wide_indices, &wide_opening),
        None
    );
    assert!(PorsFpOpening::from_wire_bytes(&params, &wide_opening.to_wire_bytes()).is_none());
}

#[test]
fn baggy_sha3_128f_wire_budget_reference_and_rss256_mpc_parity() {
    // 1. Canonical `BaggyParams::SHA3_128F` (`d = 16, h' = 2, <= 71,654 B`) full sign + verify + wire check.
    let prod = BaggyParams::SHA3_128F;
    assert!(prod.is_well_formed());
    assert_eq!(prod.num_layers, 16);
    assert_eq!(prod.subtree_height, 2);
    assert_eq!(prod.total_height_checked(), Some(32));
    assert_eq!(prod.wots.chains, 128);
    assert_eq!(prod.wots.target_sum, 192);
    assert_eq!(prod.sig_bytes_checked(), Some(71_654));

    let sk_prod = PqSecretKey {
        sk_seed: [0x14; 32],
        sk_prf: [0x25; 32],
        pk_seed: [0x36; 32],
    };
    let pk_prod = baggy_reference_keygen(&prod, &sk_prod).expect("baggy_reference_keygen");
    let msg_prod = b"qsag-validation: canonical Baggy SHA3_128F <= 71,654 B hypertree over PORS+FP";
    let sig_prod = baggy_reference_sign(&prod, &sk_prod, &pk_prod, msg_prod)
        .expect("baggy_reference_sign SHA3_128F");
    assert_eq!(sig_prod.layers.len(), 16);
    assert_eq!(sig_prod.pors.secrets.len(), 28);
    assert!(sig_prod.pors.auth.len() <= 128);

    let wire_prod = sig_prod.to_wire_bytes();
    assert!(
        wire_prod.len() <= 71_654,
        "Baggy SHA3_128F signature wire bytes {} exceeded 71,654 B",
        wire_prod.len()
    );
    assert_eq!(
        wire_prod.len(),
        36 + (32 * 28 + 2 + 32 * sig_prod.pors.auth.len()) + 16 * (4 + 128 * 32 + 2 * 32)
    );
    let parsed_prod =
        BaggySig::from_wire_bytes(&prod, &wire_prod).expect("BaggySig::from_wire_bytes");
    assert_eq!(parsed_prod, sig_prod);
    assert!(baggy_verify(&prod, &pk_prod, msg_prod, &parsed_prod));
    assert!(!baggy_verify(
        &prod,
        &pk_prod,
        b"tampered-message",
        &parsed_prod
    ));

    // Bit-flips in randomizer, PORS opening, and hypertree WOTS+C / Merkle path must all fail closed.
    let mut bad_r = sig_prod.clone();
    bad_r.r[0] ^= 0x80;
    assert!(!baggy_verify(&prod, &pk_prod, msg_prod, &bad_r));

    let mut bad_pors = sig_prod.clone();
    bad_pors.pors.secrets[0][15] ^= 0x01;
    assert!(!baggy_verify(&prod, &pk_prod, msg_prod, &bad_pors));

    let mut bad_layer = sig_prod.clone();
    bad_layer.layers[9].chains[42][7] ^= 0x04;
    assert!(!baggy_verify(&prod, &pk_prod, msg_prod, &bad_layer));

    let mut trailing = wire_prod.clone();
    trailing.push(0);
    assert!(BaggySig::from_wire_bytes(&prod, &trailing).is_none());
    assert!(BaggySig::from_wire_bytes(&prod, &wire_prod[..wire_prod.len() - 1]).is_none());

    // 2. 2-of-3 Dealerless `Rss256Engine` MPC vs `baggy_reference_sign` byte-for-byte parity
    //    + `WaistbandCache` & `FirstSignedLedger` anti-equivocation checks (`TEST_SMALL` for fast MPC sweep).
    let small = BaggyParams::TEST_SMALL;
    let sid = [0x77; 32];
    let mut dkg_rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
        PartyPrivateRng::from_seed([0x90 + p as u8; 32], b"VALIDATION.BAGGY.DKG/v1")
    });
    let (rss_keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut dkg_rngs).unwrap();
    let serialized_shares: [_; 3] = core::array::from_fn(|p| rss_keys[p].to_secret_bytes());
    drop(rss_keys);

    let mk_engine = |sess_byte: u8| {
        let restored: [RssKeyShare256; 3] = core::array::from_fn(|p| {
            RssKeyShare256::from_secret_bytes(&serialized_shares[p]).expect("QSRSSK01 decode")
        });
        let sess_rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
            PartyPrivateRng::from_seed(
                [sess_byte.wrapping_add((p as u8) * 17); 32],
                b"VALIDATION.BAGGY.SESS/v1",
            )
        });
        Rss256Engine::new([sess_byte; 32], restored, sess_rngs).unwrap()
    };

    let mut kg_engine = mk_engine(0xA1);
    let mut waistband = WaistbandCache::new(2, 16);
    let (mpc_pk, binding) = baggy_keygen_mpc(&mut kg_engine, &small, &mut waistband).unwrap();
    assert!(binding.matches(&small, &mpc_pk));

    // Reconstruct the underlying secret from canonical `QSRSSK01` primary slots (`[44..76]` =
    // `sk_seed_primary`, `[108..140]` = `sk_prf_primary`) solely to check byte-exact MPC parity.
    let mut sk_seed = [0u8; 32];
    let mut sk_prf = [0u8; 32];
    for share_bytes in &serialized_shares {
        for i in 0..32 {
            sk_seed[i] ^= share_bytes[44 + i];
            sk_prf[i] ^= share_bytes[108 + i];
        }
    }
    let reconstructed_sk = PqSecretKey {
        sk_seed,
        sk_prf,
        pk_seed: mpc_pk.pk_seed,
    };
    assert_eq!(
        baggy_reference_keygen(&small, &reconstructed_sk),
        Some(mpc_pk)
    );

    let mut ledger = MemoryFirstSigned::new();
    for (idx, m) in [&b"baggy-mpc-msg-alpha"[..], &b"baggy-mpc-msg-beta"[..]]
        .into_iter()
        .enumerate()
    {
        let mut sign_eng = mk_engine(0xB0 + idx as u8);
        sign_eng.bind_key_identity(&binding.identity()).unwrap();
        let mpc_sig = baggy_sign_mpc(
            &mut sign_eng,
            &small,
            &mpc_pk,
            &binding,
            &mut waistband,
            &mut ledger,
            m,
        )
        .unwrap();
        let ref_sig = baggy_reference_sign(&small, &reconstructed_sk, &mpc_pk, m).unwrap();
        assert_eq!(
            mpc_sig.to_wire_bytes(),
            ref_sig.to_wire_bytes(),
            "Rss256Engine MPC Baggy signature must equal reference signature byte-for-byte"
        );
        assert!(baggy_verify(&small, &mpc_pk, m, &mpc_sig));
    }

    // Wrong key binding (`SHA3_128F` digest on `TEST_SMALL`) must fail closed before MPC work!
    let wrong_binding = qsag_core::baggy::BaggyKeyBinding::new(&prod, &mpc_pk);
    let mut bad_eng = mk_engine(0xC9);
    bad_eng.bind_key_identity(&binding.identity()).unwrap();
    assert_eq!(
        baggy_sign_mpc(
            &mut bad_eng,
            &small,
            &mpc_pk,
            &wrong_binding,
            &mut WaistbandCache::disabled(),
            &mut ledger,
            b"binding-mismatch",
        ),
        Err(BaggyError::KeyBindingMismatch)
    );
}

#[test]
fn frontier_sum_fts_compact1122_and_full256bit_dp_bijection_antichain_and_batch_equivalence() {
    for (profile, expected_w, expected_l, expected_s, expected_sig_bytes, expected_vote_bytes) in [
        (
            FrontierFtsProfile::Compact1122,
            96usize,
            34usize,
            1615usize,
            1122usize,
            1194usize,
        ),
        (
            FrontierFtsProfile::Full256Bit,
            5usize,
            72usize,
            144usize,
            2338usize,
            2410usize,
        ),
    ] {
        let p = profile.params();
        assert_eq!(p.node_bytes, 32);
        assert_eq!(p.tree_height, 8);
        assert_eq!(p.winternitz_w, expected_w);
        assert_eq!(p.frontier_len, expected_l);
        assert_eq!(p.target_sum, expected_s);
        assert_eq!(p.index_bits, 256);
        assert_eq!(p.counter_bits, 16);
        assert_eq!(p.max_safe_uses, 1);
        assert_eq!(profile.signature_bytes(), expected_sig_bytes);
        assert_eq!(72 + profile.signature_bytes(), expected_vote_bytes);

        // 1. Exact `U384` DP cardinalities vs independent `ExactNat` recurrence (`FrontierCompact1122AndCorduroySecurity.lean`).
        let dp = FrontierDpTable::build(profile);
        let (n_ref, d_ref, m_ref) = frontier_fts_cardinalities_ref(
            p.tree_height,
            p.winternitz_w,
            p.frontier_len,
            p.target_sum,
        );
        assert_eq!(u384_to_exact_nat(dp.frontier_cardinality), n_ref);
        assert_eq!(u384_to_exact_nat(dp.decoration_cardinality), d_ref);
        assert_eq!(u384_to_exact_nat(dp.total_cardinality), m_ref);
        assert!(
            m_ref.bit_len() >= 257,
            "{profile:?} M must strictly exceed 2^256"
        );
        if profile == FrontierFtsProfile::Compact1122 {
            assert_eq!(dp.total_cardinality.public_bit_len(), 264);
        }

        // 2. Boundary ranks + prefix-free antichain partition check (`[256, 512)` exact cover).
        let max_minus_1 = dp.total_cardinality.overflowing_sub(U384::ONE).0;
        let max_minus_2 = max_minus_1.overflowing_sub(U384::ONE).0;
        let max_256 = U384([u64::MAX, u64::MAX, u64::MAX, u64::MAX, 0, 0]);
        let third = dp.total_cardinality.ct_divmod(U384::from_u64(3)).0;

        for r in [
            U384::ZERO,
            U384::ONE,
            U384::from_u64(1_000_003),
            third,
            max_256,
            max_minus_2,
            max_minus_1,
        ] {
            let (frontier, offsets) = dp.unrank(r).expect("unrank boundary");
            assert_eq!(frontier.len(), expected_l);
            assert_eq!(offsets.len(), expected_l);
            assert_eq!(
                offsets.iter().map(|&x| x as usize).sum::<usize>(),
                expected_s
            );
            assert!(offsets.iter().all(|&x| (x as usize) < expected_w));

            // Prefix-free binary-tree antichain check: leaf intervals `[lo_i, hi_i)` must
            // partition `[256, 512)` left-to-right with zero gaps and zero overlaps!
            let mut cursor = 1u32 << p.tree_height;
            for &node in &frontier {
                assert!(node > 1, "root singleton v=1 forbidden");
                let (lo, hi) = leaf_interval(node, p.tree_height).expect("valid heap node");
                assert_eq!(lo, cursor, "antichain leaf partition gap/overlap");
                cursor = hi;
            }
            assert_eq!(cursor, 1u32 << (p.tree_height + 1));
            assert_eq!(dp.rank(&frontier, &offsets), Ok(r));
        }

        // Out-of-range & non-antichain / bad-sum rejections.
        assert_eq!(
            dp.unrank(dp.total_cardinality),
            Err(FrontierFtsError::RankOutOfRange)
        );
        let (valid_front, valid_offs) = dp.unrank(third).unwrap();
        let mut bad_front = valid_front.clone();
        // Replace `bad_front[0]` with its parent (`v >> 1`), creating an overlapping/incomplete cover.
        bad_front[0] >>= 1;
        assert_eq!(
            dp.rank_frontier(&bad_front),
            Err(FrontierFtsError::InvalidAntichainFrontier)
        );
        let mut bad_offs = valid_offs;
        if bad_offs[0] + 1 < expected_w as u8 {
            bad_offs[0] += 1;
        } else {
            bad_offs[0] -= 1;
        }
        assert_eq!(
            dp.rank_decorations(&bad_offs),
            Err(FrontierFtsError::InvalidDecorationSum)
        );
    }

    // 3. Literal 56-byte `PID` layout: seven `u64` big-endian parameters.
    let pid_1122 = FrontierFtsProfile::Compact1122.pid_bytes();
    let mut expected_pid = [0u8; 56];
    for (slot, val) in [32u64, 8, 96, 34, 1615, 256, 16].into_iter().enumerate() {
        expected_pid[slot * 8..(slot + 1) * 8].copy_from_slice(&val.to_be_bytes());
    }
    assert_eq!(pid_1122, expected_pid);

    // 4. Cached vs uncached signer byte-exactness + 11-signature SIMD batch vs scalar verifier equivalence
    //    (9 `Compact1122` + 2 `Full256Bit` items straddling an 8-lane AVX-512 Keccak batch + 3-lane remainder!).
    let cpu_accel = CpuReferenceBackend::new();
    let dp_1122 = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
    let dp_full = FrontierDpTable::build(FrontierFtsProfile::Full256Bit);

    let mut pks_1122 = Vec::new();
    let mut msgs_1122 = Vec::new();
    let mut sigs_1122 = Vec::new();

    for idx in 0..9u8 {
        let sk_seed = [0x10 + idx; 32];
        let sk_prf = [0x30 + idx; 32];
        let pk_seed = [0x50 + idx; 32];
        let hedge = [0x70 + idx; 32];
        let msg = format!("frontier-compact1122-batch-lane-{idx}").into_bytes();

        let sk_cached = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact1122,
            sk_seed,
            sk_prf,
            pk_seed,
            true,
            &cpu_accel,
        );
        let wal_c = OneShotMemWal::new(sk_cached.wal_key(), 1);
        let mut sk_cached = sk_cached.attach_wal(Box::new(wal_c)).unwrap();

        let sk_uncached = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact1122,
            sk_seed,
            sk_prf,
            pk_seed,
            false,
            &cpu_accel,
        );
        let wal_u = OneShotMemWal::new(sk_uncached.wal_key(), 1);
        let mut sk_uncached = sk_uncached.attach_wal(Box::new(wal_u)).unwrap();

        assert_eq!(sk_cached.pk, sk_uncached.pk);

        // Verify `wal_key` matches independent NIST SP 800-185 framed cSHAKE256!
        let ref_wal_key = cshake256_framed_32_nist_ref(
            b"QSAG.FRONTIER.WAL.V1",
            &[&pid_1122, &sk_cached.pk.pk_seed, &sk_cached.pk.root],
        );
        assert_eq!(sk_cached.wal_key(), ref_wal_key);

        let sig_c = sk_cached.sign(&dp_1122, &msg, &hedge).unwrap();
        let sig_u = sk_uncached.sign(&dp_1122, &msg, &hedge).unwrap();
        assert_eq!(sig_c, sig_u);
        assert_eq!(sig_c.to_bytes(FrontierFtsProfile::Compact1122).len(), 1122);
        assert_eq!(
            sk_cached.sign(&dp_1122, b"second-use-must-fail", &hedge),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
        assert_eq!(
            FrontierFtsSignature::from_bytes(
                FrontierFtsProfile::Compact1122,
                &sig_c.to_bytes(FrontierFtsProfile::Compact1122),
            )
            .unwrap(),
            sig_c
        );
        verify_frontier_fts(&sk_cached.pk, &dp_1122, &msg, &sig_c).unwrap();

        pks_1122.push(sk_cached.pk.clone());
        msgs_1122.push(msg);
        sigs_1122.push(sig_c);
    }

    // Also include 2 `Full256Bit` (`2,338 B`) items in a heterogeneous 11-signature batch!
    let mut pks_full = Vec::new();
    let mut msgs_full = Vec::new();
    let mut sigs_full = Vec::new();
    for idx in 0..2u8 {
        let sk = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Full256Bit,
            [0x91 + idx; 32],
            [0xA1 + idx; 32],
            [0xB1 + idx; 32],
            true,
            &cpu_accel,
        );
        let wal = OneShotMemWal::new(sk.wal_key(), 1);
        let mut sk = sk.attach_wal(Box::new(wal)).unwrap();
        let msg = format!("frontier-full256bit-batch-lane-{idx}").into_bytes();
        let sig = sk.sign(&dp_full, &msg, &[0xC1 + idx; 32]).unwrap();
        assert_eq!(sig.to_bytes(FrontierFtsProfile::Full256Bit).len(), 2338);
        verify_frontier_fts(&sk.pk, &dp_full, &msg, &sig).unwrap();
        pks_full.push(sk.pk.clone());
        msgs_full.push(msg);
        sigs_full.push(sig);
    }

    #[allow(clippy::too_many_arguments)]
    fn assemble_batch<'a>(
        pks_1122: &'a [qsag_fts::FrontierFtsPublicKey],
        dp_1122: &'a FrontierDpTable,
        msgs_1122: &'a [Vec<u8>],
        sigs_a: &'a [FrontierFtsSignature],
        pks_full: &'a [qsag_fts::FrontierFtsPublicKey],
        dp_full: &'a FrontierDpTable,
        msgs_full: &'a [Vec<u8>],
        sigs_b: &'a [FrontierFtsSignature],
    ) -> Vec<FrontierVerifyInput<'a>> {
        let mut inputs = Vec::with_capacity(11);
        for i in 0..9 {
            inputs.push(FrontierVerifyInput {
                pk: &pks_1122[i],
                dp: dp_1122,
                message: &msgs_1122[i],
                signature: &sigs_a[i],
            });
        }
        for i in 0..2 {
            inputs.push(FrontierVerifyInput {
                pk: &pks_full[i],
                dp: dp_full,
                message: &msgs_full[i],
                signature: &sigs_b[i],
            });
        }
        inputs
    }

    let valid_inputs = assemble_batch(
        &pks_1122, &dp_1122, &msgs_1122, &sigs_1122, &pks_full, &dp_full, &msgs_full, &sigs_full,
    );
    let batch_ok = verify_frontier_fts_batch(&valid_inputs);
    assert_eq!(batch_ok.len(), 11);
    assert!(batch_ok.iter().all(Result::is_ok));

    // Corrupt exactly one lane at index 0, index 7 (end of first 8-lane SIMD block),
    // index 8 (remainder block), and index 10 (`Full256Bit`): ONLY the corrupted lane
    // must fail, matching scalar `verify_frontier_fts` lane-by-lane!
    for bad_lane in [0usize, 7, 8] {
        let mut mutated = sigs_1122.clone();
        mutated[bad_lane].chain_values[19] ^= 0x01;
        let scalar_res = verify_frontier_fts(
            &pks_1122[bad_lane],
            &dp_1122,
            &msgs_1122[bad_lane],
            &mutated[bad_lane],
        );
        assert_eq!(
            scalar_res,
            Err(FrontierFtsError::SignatureVerificationFailed)
        );
        let batch_inputs = assemble_batch(
            &pks_1122, &dp_1122, &msgs_1122, &mutated, &pks_full, &dp_full, &msgs_full, &sigs_full,
        );
        let batch_res = verify_frontier_fts_batch(&batch_inputs);
        for (lane, res) in batch_res.into_iter().enumerate() {
            if lane == bad_lane {
                assert_eq!(res, scalar_res);
            } else {
                assert_eq!(res, Ok(()), "honest lane {lane} must stay valid");
            }
        }
    }
    let mut mutated_full = sigs_full.clone();
    mutated_full[1].randomizer[0] ^= 0x40;
    let batch_inputs = assemble_batch(
        &pks_1122,
        &dp_1122,
        &msgs_1122,
        &sigs_1122,
        &pks_full,
        &dp_full,
        &msgs_full,
        &mutated_full,
    );
    let batch_res = verify_frontier_fts_batch(&batch_inputs);
    assert!(batch_res[..10].iter().all(Result::is_ok));
    assert!(batch_res[10].is_err());

    // 5. `RotatedEpochVote` (`1,194 B`) forward-secure chain + `verify_rotated_epoch_votes_batch`.
    let chain_id = [0xE1; 32];
    let mut epoch_keys: Vec<FrontierFtsSigningKey> = (0..4u8)
        .map(|ep| {
            let sk = FrontierFtsSigningKey::keygen(
                FrontierFtsProfile::Compact1122,
                [0xD0 + ep; 32],
                [0xE0 + ep; 32],
                [0xF5; 32], // shared public `pk_seed` across rotated epochs
                true,
                &cpu_accel,
            );
            let wal = OneShotMemWal::new(sk.wal_key(), 1);
            sk.attach_wal(Box::new(wal)).unwrap()
        })
        .collect();
    let epoch_pks: Vec<_> = epoch_keys.iter().map(|k| k.pk.clone()).collect();
    let mut votes = Vec::new();
    let mut vote_digests = Vec::new();
    for ep in 0..3usize {
        let vd = [0x40 + ep as u8; 32];
        let next_root: [u8; 32] = epoch_pks[ep + 1].root.as_slice().try_into().unwrap();
        let vote = epoch_keys[ep]
            .sign_rotated_epoch_vote(
                &dp_1122,
                &chain_id,
                EpochKeyLink {
                    epoch: 100 + ep as u64,
                    next_epoch_pk_root: next_root,
                },
                vd,
                &[0x80 + ep as u8; 32],
            )
            .unwrap();
        let raw_vote = vote.to_bytes(FrontierFtsProfile::Compact1122);
        assert_eq!(raw_vote.len(), 1194);
        assert_eq!(
            RotatedEpochVote::from_bytes(FrontierFtsProfile::Compact1122, &raw_vote).unwrap(),
            vote
        );
        let next_pk = vote
            .verify(&epoch_pks[ep], &dp_1122, &chain_id, 100 + ep as u64, &vd)
            .unwrap();
        assert_eq!(next_pk, epoch_pks[ep + 1]);
        votes.push(vote);
        vote_digests.push(vd);
    }

    let vote_inputs: Vec<RotatedEpochVerifyInput<'_>> = (0..3)
        .map(|ep| RotatedEpochVerifyInput {
            current: &epoch_pks[ep],
            dp: &dp_1122,
            chain_id: &chain_id,
            expected_epoch: 100 + ep as u64,
            expected_vote_digest: &vote_digests[ep],
            vote: &votes[ep],
        })
        .collect();
    let next_pks: Vec<_> = verify_rotated_epoch_votes_batch(&vote_inputs)
        .into_iter()
        .map(Result::unwrap)
        .collect();
    assert_eq!(next_pks, epoch_pks[1..4]);
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        rng_seed: proptest::test_runner::RngSeed::Fixed(0x5153_4147_5735),
        ..ProptestConfig::default()
    })]

    /// Every 256-bit digest rank embeds injectively into both `Compact1122` and `Full256Bit`
    /// with exact `rank(unrank(r)) == r`, prefix-free antichain partition, and constant sum `S`.
    #[test]
    fn proptest_frontier_u384_bijection_and_octopus_cover(
        limbs in any::<[u64; 4]>(),
        leaf_draws in prop::collection::vec(0u32..2048u32, 1..=28),
    ) {
        let rank = U384([limbs[0], limbs[1], limbs[2], limbs[3], 0, 0]);
        let dp_1122 = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let dp_full = FrontierDpTable::build(FrontierFtsProfile::Full256Bit);

        for (dp, l, s) in [(&dp_1122, 34usize, 1615usize), (&dp_full, 72usize, 144usize)] {
            prop_assert!(rank.ct_lt(dp.total_cardinality));
            let (front, offs) = dp.unrank(rank).unwrap();
            prop_assert_eq!(front.len(), l);
            prop_assert_eq!(offs.iter().map(|&x| x as usize).sum::<usize>(), s);
            prop_assert_eq!(dp.rank(&front, &offs).unwrap(), rank);
        }

        let mut sorted_unique = leaf_draws;
        sorted_unique.sort_unstable();
        sorted_unique.dedup();
        prop_assert_eq!(
            octopus_positions(11, &sorted_unique),
            octopus_cover_ref(11, &sorted_unique)
        );
    }
}
