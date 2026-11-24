#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
#![no_std]
#![forbid(unsafe_code)]
//! Compact Few-Time Signatures with FrontierSumFts.

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod frontier;
pub mod u384;

pub use frontier::{
    EpochKeyLink, FrontierDpTable, FrontierFtsError, FrontierFtsParams, FrontierFtsProfile,
    FrontierFtsPublicKey, FrontierFtsSignature, FrontierFtsSigningKey, FrontierVerifyInput,
    FtsEpochWal, RotatedEpochVerifyInput, RotatedEpochVote, verify_frontier_fts,
    verify_frontier_fts_batch, verify_rotated_epoch_votes_batch,
};
pub use u384::U384;

#[cfg(feature = "std")]
pub mod wal;
#[cfg(feature = "std")]
pub use wal::FsWalFtsEpochLatch;

#[cfg(test)]
mod tests {
    use alloc::format;
    use qsag_accel::CpuReferenceBackend;

    use super::*;

    #[test]
    fn compact1122_domain_wire_and_epoch_rotation() {
        let profile = FrontierFtsProfile::Compact1122;
        assert_eq!(profile.signature_bytes(), 1122);
        assert!(profile.signature_bytes() + 96 <= 1232);
        let dp = FrontierDpTable::build(profile);
        assert_eq!(dp.total_cardinality.public_bit_len(), 264);
        let rank_limit = U384([0, 0, 0, 0, 1, 0]);
        assert!(rank_limit.ct_lt(dp.total_cardinality));
        for rank in [
            U384::ZERO,
            U384::ONE,
            U384([u64::MAX, u64::MAX, u64::MAX, u64::MAX, 0, 0]),
            dp.total_cardinality.overflowing_sub(U384::ONE).0,
        ] {
            let (frontier, offsets) = dp.unrank(rank).unwrap();
            assert_eq!(dp.rank(&frontier, &offsets).unwrap(), rank);
        }
        let accel = CpuReferenceBackend::new();
        let mut current =
            FrontierFtsSigningKey::keygen(profile, [1; 32], [2; 32], [3; 32], true, &accel);
        let mut next =
            FrontierFtsSigningKey::keygen(profile, [4; 32], [5; 32], [3; 32], true, &accel);
        let chain = [6; 32];
        let vote_digest = [7; 32];
        let link = EpochKeyLink {
            epoch: 42,
            next_epoch_pk_root: next.pk.root.as_slice().try_into().unwrap(),
        };
        let vote = current
            .sign_rotated_epoch_vote(&dp, &chain, link.clone(), vote_digest, &[8; 32])
            .unwrap();
        let bytes = vote.to_bytes(profile);
        assert_eq!(bytes.len(), 1194);
        let decoded = RotatedEpochVote::from_bytes(profile, &bytes).unwrap();
        assert_eq!(vote, decoded);
        assert_eq!(
            decoded
                .verify(&current.pk, &dp, &chain, 42, &vote_digest)
                .unwrap(),
            next.pk
        );
        assert_eq!(
            current.sign_rotated_epoch_vote(&dp, &chain, link, vote_digest, &[8; 32]),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
        // Every envelope region is bound: epoch, message, root, randomizer, counter and chains.
        for position in [0, 8, 40, 72, 104, bytes.len() - 1] {
            let mut changed = bytes.clone();
            changed[position] ^= 1;
            let forged = RotatedEpochVote::from_bytes(profile, &changed).unwrap();
            assert!(
                forged
                    .verify(&current.pk, &dp, &chain, 42, &vote_digest)
                    .is_err()
            );
            // Matching the forged header in application expectations must still fail
            // the cryptographic binding, rather than only the epoch/digest precheck.
            assert!(
                forged
                    .verify(
                        &current.pk,
                        &dp,
                        &chain,
                        forged.link.epoch,
                        &forged.vote_digest
                    )
                    .is_err()
            );
        }
        assert!(
            decoded
                .verify(&current.pk, &dp, &[9; 32], 42, &vote_digest)
                .is_err()
        );
        assert!(
            decoded
                .verify(&current.pk, &dp, &chain, 43, &vote_digest)
                .is_err()
        );
        assert!(
            decoded
                .verify(&next.pk, &dp, &chain, 42, &vote_digest)
                .is_err()
        );
        assert!(RotatedEpochVote::from_bytes(profile, &bytes[..bytes.len() - 1]).is_err());
        let mut extended = bytes.clone();
        extended.push(0);
        assert!(RotatedEpochVote::from_bytes(profile, &extended).is_err());
        let verified_next = decoded
            .verify(&current.pk, &dp, &chain, 42, &vote_digest)
            .unwrap();
        assert_eq!(
            next.sign_rotated_epoch_vote(
                &dp,
                &chain,
                EpochKeyLink {
                    epoch: u64::MAX,
                    next_epoch_pk_root: [10; 32]
                },
                [11; 32],
                &[12; 32]
            ),
            Err(FrontierFtsError::ProfileMismatch)
        );
        let next_vote = next
            .sign_rotated_epoch_vote(
                &dp,
                &chain,
                EpochKeyLink {
                    epoch: 43,
                    next_epoch_pk_root: [10; 32],
                },
                [11; 32],
                &[12; 32],
            )
            .unwrap();
        assert!(
            next_vote
                .verify(&verified_next, &dp, &chain, 43, &[11; 32])
                .is_ok()
        );
    }

    #[test]
    fn test_compact_profile_exact_signature_sizes_and_dp_bijection() {
        assert_eq!(FrontierFtsProfile::Compact1122.signature_bytes(), 1122);
        assert_eq!(FrontierFtsProfile::Full256Bit.signature_bytes(), 2338);
        let compact = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let full = FrontierDpTable::build(FrontierFtsProfile::Full256Bit);
        for dp in [&compact, &full] {
            assert!(dp.total_cardinality.public_bit_len() >= 256);
            assert_eq!(dp.params.node_bytes, 32);
            let max_minus_1 = dp.total_cardinality.overflowing_sub(U384::ONE).0;
            let mid = dp.total_cardinality.ct_divmod(U384::from_u64(3)).0;
            for sample in [
                U384::ZERO,
                U384::ONE,
                U384::from_u64(987_654_321),
                mid,
                max_minus_1,
            ] {
                let (front, offs) = dp.unrank(sample).unwrap();
                assert_eq!(front.len(), dp.params.frontier_len);
                let sum: usize = offs.iter().map(|&x| x as usize).sum();
                assert_eq!(sum, dp.params.target_sum);
                let r_back = dp.rank(&front, &offs).unwrap();
                assert_eq!(r_back, sample);
            }
            assert_eq!(
                dp.unrank(dp.total_cardinality),
                Err(FrontierFtsError::RankOutOfRange)
            );
        }
    }

    #[test]
    fn test_frontier_sum_fts_sign_verify_cached_uncached_and_single_use_latch() {
        let accel = CpuReferenceBackend::new();
        assert_eq!(FrontierFtsProfile::Full256Bit.params().max_safe_uses, 1);
        assert_eq!(FrontierFtsProfile::Fast256Test.params().max_safe_uses, 1);

        let dp = FrontierDpTable::build(FrontierFtsProfile::Full256Bit);
        let sk_seed = [0x11u8; 32];
        let sk_prf = [0x22u8; 32];
        let pk_seed = [0x33u8; 32];

        let mut sk_cached = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Full256Bit,
            sk_seed,
            sk_prf,
            pk_seed,
            true,
            &accel,
        );
        let mut sk_uncached = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Full256Bit,
            sk_seed,
            sk_prf,
            pk_seed,
            false,
            &accel,
        );
        assert_eq!(sk_cached.pk, sk_uncached.pk);

        // Debug output must redact secrets!
        let dbg_str = format!("{:?}", sk_cached);
        assert!(dbg_str.contains("<REDACTED>"));
        assert!(!dbg_str.contains("11"));

        let msg1 = b"transfer 1000 units to pq vault alpha";
        let msg2 = b"transfer 2000 units to pq vault beta";
        let hedge = [0x55u8; 32];

        let sig1 = sk_cached.sign(&dp, msg1, &hedge).unwrap();
        let sig1_uncached = sk_uncached.sign(&dp, msg1, &hedge).unwrap();
        assert_eq!(sig1, sig1_uncached);
        assert_eq!(
            sig1.to_bytes(FrontierFtsProfile::Full256Bit).len(),
            FrontierFtsProfile::Full256Bit.signature_bytes()
        );
        verify_frontier_fts(&sk_cached.pk, &dp, msg1, &sig1).unwrap();

        // Full256Bit (`h=8, L=72`) is strictly 1-use: a second signature attempt MUST fail with
        // `Err(FrontierFtsError::UseBudgetExhausted)` on both cached and uncached keys!
        assert_eq!(
            sk_cached.sign(&dp, msg2, &hedge),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
        assert_eq!(
            sk_uncached.sign(&dp, msg2, &hedge),
            Err(FrontierFtsError::UseBudgetExhausted)
        );

        // Tampering any byte of sig1 or message must fail verification!
        assert!(verify_frontier_fts(&sk_cached.pk, &dp, msg2, &sig1).is_err());
        let mut tampered = sig1.clone();
        tampered.chain_values[0] ^= 0x01;
        assert!(verify_frontier_fts(&sk_cached.pk, &dp, msg1, &tampered).is_err());

        // Fast256Test (`h=5, L=8`) is also strictly 1-use: 2nd sign returns `Err`.
        let dp_fast = FrontierDpTable::build(FrontierFtsProfile::Fast256Test);
        let mut sk_fast = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Fast256Test,
            sk_seed,
            sk_prf,
            pk_seed,
            true,
            &accel,
        );
        let sig_fast = sk_fast.sign(&dp_fast, msg1, &hedge).unwrap();
        verify_frontier_fts(&sk_fast.pk, &dp_fast, msg1, &sig_fast).unwrap();
        assert_eq!(
            sk_fast.sign(&dp_fast, msg2, &hedge),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
    }

    #[test]
    fn test_compact_1122_byte_profile_end_to_end_sign_and_verify() {
        let accel = CpuReferenceBackend::new();
        let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let mut sk = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact1122,
            [0xA1; 32],
            [0xB2; 32],
            [0xC3; 32],
            true,
            &accel,
        );
        let sig = sk
            .sign(&dp, b"compact 1122-byte post-quantum fts", &[0xD4; 32])
            .unwrap();
        let raw = sig.to_bytes(FrontierFtsProfile::Compact1122);
        assert_eq!(raw.len(), 1122);
        let parsed =
            FrontierFtsSignature::from_bytes(FrontierFtsProfile::Compact1122, &raw).unwrap();
        verify_frontier_fts(&sk.pk, &dp, b"compact 1122-byte post-quantum fts", &parsed).unwrap();

        // Compact1122 is strictly 1-use: a second signature attempt MUST return `Err`!
        assert_eq!(
            sk.sign(&dp, b"second attempt on compact1122", &[0xE5; 32]),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
    }
}
