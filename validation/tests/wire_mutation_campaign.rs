// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Deterministic `120,000+` Adversarial Wire-Mutation & Boundary Campaign
//!
//! Exercises structured boundary corruptions (magic tags, length prefixes, trailing bytes,
//! `GOLDILOCKS_PRIME` non-canonical limbs, bitmap active-set mismatches, 64-bit alignment pad
//! bytes, `u32::MAX` generation wraparound, ISA reserved-bit encodings, `.org` OOM guards, and
//! VM trap latches) plus deterministic SplitMix64 byte/bit-flip fuzzing across:
//! 1. `HemQuinticProof::from_bytes` (`QSAGHQM2`) + `verify_hem_quintic_128` (`30,000+` mutations)
//! 2. `FixedPathWhirW24::from_bytes_canonical` (`QSAGIW24`) & `SuccinctIvcProof::from_bytes_canonical`
//!    (`QSAGIVC1`) + `verify_ivc_tree` (`30,000+` mutations)
//! 3. `ZkHemV2Proof::from_bytes` (`QSAGZKH2`) & `ZkHemV2SplitProof::from_bytes` (`QSAGZKS2`)
//!    with and without LogUp lookup tables (`30,000+` mutations)
//! 4. `qsag-ass2` Owner `WOTS+C` frames, fast capability `CMD_LOAD_CODE`, 32-bit ISA codec,
//!    two-pass assembler, and `Ass2Vm` (`30,000+` mutations)

use qsag_agg::field::{GOLDILOCKS_PRIME, Goldilocks};
use qsag_agg::sig::{EpochWalSink, SigError, WalEpochState};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, sponge12};
use qsag_agg::zk_hem::v2::field5::Fp5;
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{
    self as v2, MAGIC_SPLIT as ZKS2_MAGIC, ZkHemV2Proof, ZkHemV2SplitProof,
};
use qsag_agg::{
    AggSigProfile, FixedPathWhirW24, HemQuinticProfile, HemQuinticProof, IvcStepConfig,
    IvcSubtreeStatement, IvcTableCommitment, SignerBitmap, SigningMode, SuccinctIvcProof,
    ValidatorKeypair, prove_hem_quintic_128, verify_hem_quintic_128, verify_ivc_tree,
};
use qsag_ass2::wire::{
    Ass2WireError, OwnerOp, capability_commit_code, compute_image_id, encode_owner_lifecycle_frame,
    load_code_frame, load_code_wotsc_frame, owner_wotsc_pubkey,
    parse_and_verify_load_code_wotsc_frame, parse_and_verify_owner_lifecycle_frame,
    parse_load_code_frame,
};
use qsag_ass2::{
    Ass2Vm, DitMode, RunExit, StepOutcome, assemble, decode_insn_le, disassemble_insn,
    encode_insn_le,
};

struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn next_usize(&mut self, bound: usize) -> usize {
        (self.next_u64() as usize) % bound
    }

    fn next_nonzero_u8(&mut self) -> u8 {
        ((self.next_u64() as u8) % 255) + 1
    }
}

#[derive(Default)]
struct MemWal(Option<WalEpochState>);

impl EpochWalSink for MemWal {
    fn recovered_state(&self, _pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        Ok(self.0)
    }
    fn persist_latched_epoch(
        &mut self,
        _pk_root: &[u8; 32],
        next: u32,
        epoch: u32,
        mu: &[u8; 32],
    ) -> Result<(), SigError> {
        self.0 = Some((next, epoch, *mu));
        Ok(())
    }
}

#[test]
fn adversarial_wire_mutation_campaign_120k_zero_panics_zero_forgeries() {
    let mut total_mutations = 0usize;
    let mut rng = SplitMix64(0x5835_4943_445F_2026);
    let f = Goldilocks::from_u64_reduced;

    // =========================================================================
    // Campaign 1: HemQuinticProof (`QSAGHQM2`) — 30,500+ mutations
    // =========================================================================
    {
        let mut w0 = MemWal::default();
        let mut w1 = MemWal::default();
        let mut kp0 = ValidatorKeypair::from_master_seed_with_wal(
            AggSigProfile::JortsPoseidon2,
            &[0x11; 32],
            0,
            &w0,
        )
        .unwrap();
        let mut kp1 = ValidatorKeypair::from_master_seed_with_wal(
            AggSigProfile::JortsPoseidon2,
            &[0x22; 32],
            1,
            &w1,
        )
        .unwrap();
        let pks = [kp0.pk, kp1.pk];
        let bm1 = SignerBitmap::from_active_indices(2, &[0]).unwrap();
        let bm2 = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let shared_msg = b"qsag-hqm2-shared";
        let sig0_shared = kp0.sign_stateful(shared_msg, 0, &mut w0).unwrap();
        let sig0_per = kp0.sign_stateful(b"per-0", 1, &mut w0).unwrap();
        let sig1_per = kp1.sign_stateful(b"per-1", 0, &mut w1).unwrap();

        let shared_mode = SigningMode::SharedMessage(shared_msg);
        let per_msgs: [&[u8]; 2] = [b"per-0", b"per-1"];
        let per_mode = SigningMode::PerSignerMessages(&per_msgs);

        let turbo_proof = prove_hem_quintic_128(
            HemQuinticProfile::TurboShake400,
            &pks,
            &bm1,
            &shared_mode,
            std::slice::from_ref(&sig0_shared),
        )
        .unwrap();
        let gl24_proof = prove_hem_quintic_128(
            HemQuinticProfile::Poseidon2Gl24,
            &pks,
            &bm2,
            &per_mode,
            &[sig0_per, sig1_per],
        )
        .unwrap();
        let turbo_wire = turbo_proof.to_bytes();
        let gl24_wire = gl24_proof.to_bytes();

        assert_eq!(HemQuinticProof::from_bytes(&turbo_wire).as_ref(), Some(&turbo_proof));
        assert_eq!(HemQuinticProof::from_bytes(&gl24_wire).as_ref(), Some(&gl24_proof));
        assert!(verify_hem_quintic_128(&pks, &shared_mode, &turbo_proof));
        assert!(verify_hem_quintic_128(&pks, &per_mode, &gl24_proof));

        // Structured boundary checks: trailing byte, truncated prefix, zero bitmap, bad profile tag,
        // and PerSignerMessages boundary shifting `[b"per-0", b"per-1"]` -> `[b"per-", b"0per-1"]`!
        let shifted_msgs: [&[u8]; 2] = [b"per-", b"0per-1"];
        assert!(!verify_hem_quintic_128(
            &pks,
            &SigningMode::PerSignerMessages(&shifted_msgs),
            &gl24_proof
        ));
        for base in [&turbo_wire, &gl24_wire] {
            let mut trailing = base.clone();
            trailing.push(0);
            assert!(HemQuinticProof::from_bytes(&trailing).is_none());
            total_mutations += 1;

            for cut in 0..64.min(base.len()) {
                assert!(HemQuinticProof::from_bytes(&base[..cut]).is_none());
                total_mutations += 1;
            }
            for bad_prof in [0u8, 3, 255] {
                let mut m = base.clone();
                m[8] = bad_prof;
                assert!(HemQuinticProof::from_bytes(&m).is_none());
                total_mutations += 1;
            }
            // Zero active bits in bitmap must be rejected by `from_bytes`
            let mut zero_bm = base.clone();
            zero_bm[13..21].copy_from_slice(&0u64.to_le_bytes());
            assert!(HemQuinticProof::from_bytes(&zero_bm).is_none());
            total_mutations += 1;
        }

        // 30,000 randomized single/multi-byte & non-canonical-limb injections
        for step in 0..30_000usize {
            let (base, mode) = if step & 1 == 0 {
                (&turbo_wire, &shared_mode)
            } else {
                (&gl24_wire, &per_mode)
            };
            let mut cand = base.clone();
            match step % 6 {
                0 => {
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                }
                1 => {
                    for _ in 0..3 {
                        let idx = rng.next_usize(cand.len());
                        cand[idx] ^= rng.next_nonzero_u8();
                    }
                }
                2 => {
                    // Inject non-canonical Goldilocks limb >= p into payload
                    let off = 29 + rng.next_usize(cand.len() - 37);
                    let bad_limb = if step & 2 == 0 { GOLDILOCKS_PRIME } else { u64::MAX };
                    cand[off..off + 8].copy_from_slice(&bad_limb.to_le_bytes());
                }
                3 => {
                    cand.truncate(rng.next_usize(cand.len()));
                }
                4 => {
                    cand.push(rng.next_nonzero_u8());
                }
                _ => {
                    // Corrupt u64 payload length header at bytes 21..29
                    let fake_len = rng.next_u64();
                    cand[21..29].copy_from_slice(&fake_len.to_le_bytes());
                }
            }
            if cand != *base
                && let Some(decoded) = HemQuinticProof::from_bytes(&cand)
            {
                assert_eq!(decoded.to_bytes(), cand);
                // Only decode-checked envelope passed; cryptographic verification must reject!
                assert!(
                    !verify_hem_quintic_128(&pks, mode, &decoded),
                    "forged HemQuinticProof accepted at step {step}"
                );
            }
            total_mutations += 1;
        }
    }

    // =========================================================================
    // Campaign 2: FixedPathWhirW24 (`QSAGIW24`) & SuccinctIvcProof (`QSAGIVC1`) — 30,500+ mutations
    // =========================================================================
    {
        let cfg16 = IvcStepConfig::dkt26(16).unwrap();
        let _census16 = cfg16.opening_row_census(4);
        let table16: Vec<Goldilocks> = (0..(1usize << 16))
            .map(|i| f((i as u64).wrapping_mul(29).wrapping_add(7)))
            .collect();
        let com16 = IvcTableCommitment::commit(&cfg16, &table16, &[0x44; 32]).unwrap();
        let ctx = [f(3), f(5), f(7)];
        let pt16: Vec<Fp5> = (0..16).map(|i| Fp5::from_u64((i + 2) as u64)).collect();
        let (val16, op16) = com16.open(&ctx, &pt16).unwrap();
        let op16_wire = op16.to_bytes();
        assert!(op16.verify(&cfg16, &ctx, com16.nonce(), com16.root(), &pt16, val16));

        // Sampled 8-byte word slots across `op16_wire[8..]` set to `GOLDILOCKS_PRIME` MUST be rejected!
        let total_words = (op16_wire.len() - 8) / 8;
        let stride = (total_words / 512).max(1);
        for w in (0..total_words).step_by(stride) {
            let slot = 8 + 8 * w;
            let mut noncanon = op16_wire.clone();
            noncanon[slot..slot + 8].copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
            assert!(
                FixedPathWhirW24::from_bytes_canonical(&cfg16, &noncanon).is_none(),
                "slot {slot} accepted non-canonical GOLDILOCKS_PRIME limb"
            );
            total_mutations += 1;
        }
        // Also test the exact last word slot explicitly!
        {
            let last_slot = op16_wire.len() - 8;
            let mut noncanon = op16_wire.clone();
            noncanon[last_slot..last_slot + 8].copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
            assert!(FixedPathWhirW24::from_bytes_canonical(&cfg16, &noncanon).is_none());
            total_mutations += 1;
        }

        // Construct valid-length canonical zero-word `[DKT26]` `SuccinctIvcProof` (`QSAGIVC1\x00`,
        // `639,673` bytes) wire image and verify canonical `< p` roundtrip, tag-`!= 0` rejection,
        // and `verify_ivc_tree` rejection!
        let prod_len = SuccinctIvcProof::encoded_len();
        assert_eq!(prod_len, 639_673);
        let mut zero_ivc = vec![0u8; prod_len];
        zero_ivc[..8].copy_from_slice(b"QSAGIVC1");
        zero_ivc[8] = 0;
        let open_len23 = IvcStepConfig::dkt26(23).unwrap().opening_bytes();
        let split23 = prod_len - open_len23;
        zero_ivc[split23..split23 + 8].copy_from_slice(b"QSAGIW24");
        let parsed_zero_ivc = SuccinctIvcProof::from_bytes_canonical(&zero_ivc)
            .expect("canonical zero-limb SuccinctIvcProof must decode");
        assert_eq!(parsed_zero_ivc.to_bytes(), zero_ivc);
        // Any non-zero profile tag at byte 8 (including retired diagnostic tag `1`) MUST be rejected!
        for bad_tag in [1u8, 2, 0xFF] {
            let mut tagged = zero_ivc.clone();
            tagged[8] = bad_tag;
            assert!(SuccinctIvcProof::from_bytes_canonical(&tagged).is_none());
            total_mutations += 1;
        }
        let ivc_stmt = IvcSubtreeStatement {
            policy_registry_root: [0x12; 32],
            shard_lo: 0,
            shard_hi: 2,
            total_quorums: 2,
            message_digest: [0x34; 32],
        };
        assert!(!verify_ivc_tree(&ivc_stmt, &parsed_zero_ivc));

        for step in 0..30_000usize {
            if step % 3 != 0 {
                let mut cand = op16_wire.clone();
                match step % 5 {
                    0 => {
                        let idx = rng.next_usize(cand.len());
                        cand[idx] ^= rng.next_nonzero_u8();
                    }
                    1 => {
                        let word_idx = 8 + 8 * rng.next_usize((cand.len() - 8) / 8);
                        cand[word_idx..word_idx + 8]
                            .copy_from_slice(&(GOLDILOCKS_PRIME + (step as u64 % 99)).to_le_bytes());
                    }
                    2 => {
                        cand.pop();
                    }
                    3 => {
                        cand.push(0);
                    }
                    _ => {
                        for _ in 0..2 {
                            let idx = 8 + rng.next_usize(cand.len() - 8);
                            cand[idx] ^= rng.next_nonzero_u8();
                        }
                    }
                }
                if cand != op16_wire
                    && let Some(dec) = FixedPathWhirW24::from_bytes_canonical(&cfg16, &cand)
                {
                    assert_eq!(dec.to_bytes(), cand);
                    assert!(
                        !dec.verify(&cfg16, &ctx, com16.nonce(), com16.root(), &pt16, val16),
                        "mutated FixedPathWhirW24 forged verification at step {step}"
                    );
                }
            } else {
                let mut cand = zero_ivc.clone();
                match step % 4 {
                    0 => {
                        let word_idx = 9 + 8 * rng.next_usize((split23 - 9) / 8);
                        cand[word_idx..word_idx + 8]
                            .copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
                        assert!(SuccinctIvcProof::from_bytes_canonical(&cand).is_none());
                    }
                    1 => {
                        cand[8] = rng.next_nonzero_u8();
                        assert!(SuccinctIvcProof::from_bytes_canonical(&cand).is_none());
                    }
                    2 => {
                        cand.pop();
                        assert!(SuccinctIvcProof::from_bytes_canonical(&cand).is_none());
                    }
                    _ => {
                        let idx = 9 + rng.next_usize(split23 - 9);
                        cand[idx] ^= rng.next_nonzero_u8() & 0x7F;
                        if let Some(dec) = SuccinctIvcProof::from_bytes_canonical(&cand) {
                            assert_eq!(dec.to_bytes(), cand);
                        }
                    }
                }
            }
            total_mutations += 1;
        }
    }

    // =========================================================================
    // Campaign 3: ZkHemV2Proof (`QSAGZKH2`) & ZkHemV2SplitProof (`QSAGZKS2`) — 30,000+ mutations
    // =========================================================================
    {
        let mut cs_plain = ConstraintSystem::new();
        let p0: Lc = cs_plain.public_input(f(77)).into();
        let w0: Lc = cs_plain.alloc(f(1)).into();
        cs_plain.enforce_boolean(&w0);
        let st0 = sponge12(&mut cs_plain, &[p0, w0]);
        let _ = cs_plain.mul(&st0[0], &st0[1]);
        let (plain_shape, plain_z) = cs_plain.finish_v2();
        let plain_proof = v2::prove(
            &plain_shape,
            plain_z,
            b"x5-v2-plain",
            Profile::TurboShakeJohnson400,
            &[0x51; 32],
        )
        .unwrap();
        let plain_wire = plain_proof.to_bytes();

        let mut cs_lk = ConstraintSystem::new();
        let p_lk: Lc = cs_lk.public_input(f(88)).into();
        for i in 0..8u64 {
            let v: Lc = cs_lk.alloc(f(20 + i)).into();
            cs_lk.enforce_byte(&v);
        }
        let st_lk = sponge12(&mut cs_lk, &[p_lk]);
        let _ = cs_lk.mul(&st_lk[0], &st_lk[1]);
        let (lk_shape, lk_z) = cs_lk.finish_v2();
        let lk_proof = v2::prove(
            &lk_shape,
            lk_z,
            b"x5-v2-lk",
            Profile::TurboShakeJohnson400,
            &[0x62; 32],
        )
        .unwrap();
        let lk_wire = lk_proof.to_bytes();

        // Lift `plain_wire` into a 1-committer `QSAGZKS2` wire frame to hammer `ZkHemV2SplitProof::from_bytes`!
        let mut split1_wire = Vec::with_capacity(plain_wire.len() + 1);
        split1_wire.extend_from_slice(&ZKS2_MAGIC);
        split1_wire.push(plain_wire[8]);
        split1_wire.push(plain_wire[9]);
        split1_wire.push(1u8);
        split1_wire.extend_from_slice(&plain_wire[10..]);
        let split1_parsed = ZkHemV2SplitProof::from_bytes(&split1_wire, &plain_shape)
            .expect("1-committer ZkHemV2SplitProof canonical wire must decode");
        assert_eq!(split1_parsed.to_bytes(), split1_wire);

        // `committers == 0` and `committers == 9` (`> MAX_STAGE0_SHARES`) MUST be rejected!
        for bad_c in [0u8, 9, 255] {
            let mut bad = split1_wire.clone();
            bad[10] = bad_c;
            assert!(ZkHemV2SplitProof::from_bytes(&bad, &plain_shape).is_none());
            total_mutations += 1;
        }

        for step in 0..30_000usize {
            match step % 3 {
                0 => {
                    let mut cand = plain_wire.clone();
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                    if step % 9 == 0 {
                        cand.push(0);
                    }
                    if let Some(dec) = ZkHemV2Proof::from_bytes(&cand, &plain_shape) {
                        assert_eq!(dec.to_bytes(), cand);
                        assert!(!v2::verify(
                            &plain_shape,
                            &[f(77)],
                            b"x5-v2-plain",
                            Profile::TurboShakeJohnson400,
                            &dec
                        ));
                    }
                }
                1 => {
                    let mut cand = lk_wire.clone();
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                    if let Some(dec) = ZkHemV2Proof::from_bytes(&cand, &lk_shape) {
                        assert_eq!(dec.to_bytes(), cand);
                        assert!(!v2::verify(
                            &lk_shape,
                            &[f(88)],
                            b"x5-v2-lk",
                            Profile::TurboShakeJohnson400,
                            &dec
                        ));
                    }
                }
                _ => {
                    let mut cand = split1_wire.clone();
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                    if let Some(dec) = ZkHemV2SplitProof::from_bytes(&cand, &plain_shape) {
                        assert_eq!(dec.to_bytes(), cand);
                        assert!(!v2::verify_split(
                            &plain_shape,
                            &[f(77)],
                            b"x5-v2-plain",
                            Profile::TurboShakeJohnson400,
                            &dec
                        ));
                    }
                }
            }
            total_mutations += 1;
        }
    }

    // =========================================================================
    // Campaign 4: `qsag-ass2` Wire Frames, WOTS+C, ISA Codec & VM — 30,000+ mutations
    // =========================================================================
    {
        let sk0 = [0x42u8; 32];
        let sk1 = [0x99u8; 32];
        let owner_pk = owner_wotsc_pubkey(&sk0);
        let next_pk = owner_wotsc_pubkey(&sk1);
        let enclave_id = [0xA5u8; 32];
        let nonce: [u8; 16] = core::array::from_fn(|i| (i + 1) as u8);
        let record = (7u64 << 32) | 2;
        let words = [0x0006_0000u32, 0x0005_0000u32]; // even word count -> 4 pad bytes!
        let sib = [0x5Cu8; 16];
        let cap = capability_commit_code(&compute_image_id(&enclave_id, &words), &sib);

        let gate_frame = encode_owner_lifecycle_frame(
            0x80,
            &sk0,
            &enclave_id,
            OwnerOp::Gate { from: 2, to: 3 },
            &nonce,
            record,
            &cap,
            &next_pk,
        )
        .unwrap();
        let fast_load = load_code_frame(0x40, &sib, &words).unwrap();
        let wotsc_load =
            load_code_wotsc_frame(0x80, &sk0, &enclave_id, &nonce, record, &next_pk, &words)
                .unwrap();

        // Explicit boundary checks: `u32::MAX` generation wraparound and non-zero pad bytes!
        let max_gen_record = (u64::from(u32::MAX) << 32) | 2;
        assert_eq!(
            encode_owner_lifecycle_frame(
                0x80,
                &sk0,
                &enclave_id,
                OwnerOp::Commit,
                &nonce,
                max_gen_record,
                &cap,
                &next_pk
            ),
            Err(Ass2WireError::GenerationOverflow)
        );
        assert!(
            load_code_wotsc_frame(
                0x80,
                &sk0,
                &enclave_id,
                &nonce,
                max_gen_record,
                &next_pk,
                &words
            )
            .is_none()
        );
        for pad_pos in 1..=4 {
            let mut dirty_fast = fast_load.clone();
            let n = dirty_fast.len();
            dirty_fast[n - pad_pos] = 1;
            assert_eq!(
                parse_load_code_frame(&dirty_fast),
                Err(Ass2WireError::NonZeroPadding)
            );
            let mut dirty_wotsc = wotsc_load.clone();
            let m = dirty_wotsc.len();
            dirty_wotsc[m - pad_pos] = 0x80;
            assert_eq!(
                parse_and_verify_load_code_wotsc_frame(
                    &dirty_wotsc,
                    &owner_pk,
                    &enclave_id,
                    &nonce,
                    record
                ),
                Err(Ass2WireError::NonZeroPadding)
            );
            total_mutations += 2;
        }

        // Explicit boundary checks: `.org 0xffffffff` rejected in pass 1, VM trap stays latched!
        assert!(assemble(".org 0xffffffff\nhalt").is_err());
        let mut trap_vm = Ass2Vm::new(4096);
        trap_vm.dit_mode = DitMode::Trap;
        trap_vm.load_image(0, &[0xFF, 0xFF, 0xFF, 0xFF]).unwrap();
        let RunExit::Trap(cause) = trap_vm.run(4) else {
            panic!("illegal instruction must trap");
        };
        assert_eq!(trap_vm.step(), StepOutcome::Trap(cause));
        assert_eq!(trap_vm.run(4), RunExit::Trap(cause));

        for step in 0..30_000usize {
            match step % 4 {
                0 => {
                    let mut cand = gate_frame.to_vec();
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                    // Byte 0 is serial width prefix (`0`, `0x40`, `0x80`); any mutation elsewhere must fail!
                    if idx > 0 {
                        assert!(
                            parse_and_verify_owner_lifecycle_frame(
                                &cand,
                                &owner_pk,
                                &enclave_id,
                                &nonce,
                                record
                            )
                            .is_err(),
                            "mutated gate_frame forged verification at byte {idx}"
                        );
                    }
                }
                1 => {
                    let mut cand = wotsc_load.clone();
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                    if idx > 0 {
                        assert!(
                            parse_and_verify_load_code_wotsc_frame(
                                &cand,
                                &owner_pk,
                                &enclave_id,
                                &nonce,
                                record
                            )
                            .is_err(),
                            "mutated wotsc_load forged verification at byte {idx}"
                        );
                    }
                }
                2 => {
                    let mut cand = fast_load.clone();
                    let idx = rng.next_usize(cand.len());
                    cand[idx] ^= rng.next_nonzero_u8();
                    if let Ok((p, ws, tok)) = parse_load_code_frame(&cand) {
                        assert_eq!(load_code_frame(p, &tok, &ws).unwrap(), cand);
                    }
                }
                _ => {
                    let raw_word = (rng.next_u64() as u32).to_le_bytes();
                    if let Some(insn) = decode_insn_le(raw_word) {
                        assert_eq!(encode_insn_le(&insn).unwrap(), raw_word);
                        let text = disassemble_insn(&insn);
                        assert_eq!(assemble(&text).unwrap(), raw_word);
                    }
                }
            }
            total_mutations += 1;
        }
    }

    assert!(
        total_mutations >= 120_000,
        "expected >= 120,000 mutations, ran {total_mutations}"
    );
}
