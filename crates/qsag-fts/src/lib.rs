#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
#![no_std]
#![forbid(unsafe_code)]
//! Compact Few-Time Signatures (`FrontierSumFts` + Height-Independent MPC `ParallelSeededFts`).

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod frontier;
pub mod ot;
pub mod parallel_mpc;
mod release_gate;
pub mod u384;

pub use frontier::{
    EpochKeyLink, FrontierDpTable, FrontierFtsError, FrontierFtsParams, FrontierFtsProfile,
    FrontierFtsPublicKey, FrontierFtsSignature, FrontierFtsSigningKey, FtsEpochWal,
    RotatedEpochVote, verify_frontier_fts, FrontierVerifyInput, verify_frontier_fts_batch, RotatedEpochVerifyInput, verify_rotated_epoch_votes_batch,
};
#[cfg(any(test, feature = "testing-ephemeral"))]
pub use parallel_mpc::InMemoryBurnLog;
pub use parallel_mpc::{
    CommittedMacBarrierShare, LeafBurnPersistence, ParallelSeededDkgBeaverShare,
    ParallelSeededDkgCheckCoin, ParallelSeededDkgCheckCommit, ParallelSeededDkgCheckShares,
    ParallelSeededDkgCheckTagCommit, ParallelSeededDkgCheckTagOpen, ParallelSeededDkgConfig,
    ParallelSeededDkgOt, ParallelSeededDkgOutput, ParallelSeededDkgProducts,
    ParallelSeededDkgRound1Commit, ParallelSeededDkgRound1State, ParallelSeededDkgRound2Open,
    ParallelSeededDkgSharePackage, ParallelSeededDkgUnverifiedOutput, ParallelSeededError,
    ParallelSeededGilboaProducts, ParallelSeededMerkleLayers, ParallelSeededParams,
    ParallelSeededPartyShare, ParallelSeededPublicKey, ParallelSeededSignMessage,
    ParallelSeededSignRequest, ParallelSeededSignResult, ParallelSeededSignSession,
    ParallelSeededSignature, ParallelSeededThresholdSetup, assemble_parallel_seeded_public_key,
    finalize_parallel_seeded_dkg_party, verify_parallel_seeded_fts,
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
        assert_eq!(FrontierFtsProfile::Compact514.signature_bytes(), 514);
        assert_eq!(FrontierFtsProfile::Compact770.signature_bytes(), 770);
        assert_eq!(FrontierFtsProfile::Compact1314.signature_bytes(), 1314);
        assert_eq!(FrontierFtsProfile::Full256Bit.signature_bytes(), 2338);

        // Compact514 DP fits inside u128 (< 2^128), while Compact770 and Compact1314 fit in U384!
        let dp514 = FrontierDpTable::build(FrontierFtsProfile::Compact514);
        assert!(dp514.total_cardinality_u128().is_some());
        assert!(dp514.total_cardinality.public_bit_len() >= 118);
        assert!(dp514.total_cardinality.public_bit_len() <= 128);

        let dp770 = FrontierDpTable::build(FrontierFtsProfile::Compact770);
        assert!(dp770.total_cardinality.public_bit_len() >= 175);
        assert!(dp770.total_cardinality.public_bit_len() <= 190);

        let dp1314 = FrontierDpTable::build(FrontierFtsProfile::Compact1314);
        assert!(dp1314.total_cardinality.public_bit_len() >= 315);
        assert!(dp1314.total_cardinality.public_bit_len() <= 335);

        // Verify rank(unrank(r)) == r across sample points of Compact514, Compact770, and Compact1314!
        for dp in [&dp514, &dp770, &dp1314] {
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
    fn test_frontier_sum_fts_sign_verify_cached_uncached_and_2use_latch() {
        let accel = CpuReferenceBackend::new();
        assert_eq!(FrontierFtsProfile::Full256Bit.params().max_safe_uses, 1);
        assert_eq!(FrontierFtsProfile::Compact514.params().max_safe_uses, 1);
        assert_eq!(FrontierFtsProfile::Fast256Test.params().max_safe_uses, 1);
        assert_eq!(FrontierFtsProfile::Compact770.params().max_safe_uses, 2);
        assert_eq!(FrontierFtsProfile::Compact1314.params().max_safe_uses, 2);

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

        // Compact770 (`h=15, L=47, S=118`) supports 2 uses (>80-bit 2-use security) and latches on the 3rd!
        let dp770 = FrontierDpTable::build(FrontierFtsProfile::Compact770);
        let mut sk770 = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact770,
            sk_seed,
            sk_prf,
            pk_seed,
            true,
            &accel,
        );
        let sig770_1 = sk770.sign(&dp770, msg1, &hedge).unwrap();
        let sig770_2 = sk770.sign(&dp770, msg2, &hedge).unwrap();
        verify_frontier_fts(&sk770.pk, &dp770, msg1, &sig770_1).unwrap();
        verify_frontier_fts(&sk770.pk, &dp770, msg2, &sig770_2).unwrap();
        assert_ne!(sig770_1.randomizer, sig770_2.randomizer);
        assert_eq!(
            sk770.sign(&dp770, b"third message", &hedge),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
    }

    #[test]
    fn test_compact_514_byte_profile_end_to_end_sign_and_verify() {
        let accel = CpuReferenceBackend::new();
        let dp = FrontierDpTable::build(FrontierFtsProfile::Compact514);
        let mut sk = FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact514,
            [0xA1; 32],
            [0xB2; 32],
            [0xC3; 32],
            true,
            &accel,
        );
        let sig = sk
            .sign(&dp, b"compact 514-byte post-quantum fts", &[0xD4; 32])
            .unwrap();
        let raw = sig.to_bytes(FrontierFtsProfile::Compact514);
        assert_eq!(raw.len(), 514);
        let parsed =
            FrontierFtsSignature::from_bytes(FrontierFtsProfile::Compact514, &raw).unwrap();
        verify_frontier_fts(&sk.pk, &dp, b"compact 514-byte post-quantum fts", &parsed).unwrap();

        // Compact514 is strictly 1-use: a second signature attempt MUST return `Err`!
        assert_eq!(
            sk.sign(&dp, b"second attempt on compact514", &[0xE5; 32]),
            Err(FrontierFtsError::UseBudgetExhausted)
        );
    }

    #[test]
    fn test_parallel_seeded_fts_mpc_depth_and_threshold_sign() {
        let accel = CpuReferenceBackend::new();
        // Verify the height-independent batched depth formula.
        let h15_params = ParallelSeededParams {
            tree_height: 15,
            winternitz_w: 5,
            num_chains: 64,
            target_sum: 128,
        };
        assert_eq!(h15_params.secret_mpc_depth(), 296);
        let (ours_rounds, internal_rounds) = h15_params.secret_keccak_and_rounds_vs_internal_tree();
        assert_eq!(internal_rounds, 1824);
        assert!(ours_rounds < internal_rounds);

        // End-to-end 4-party threshold signing with committed BDOZ MAC barrier + plaintext Merkle path!
        let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams::FAST_H4_W5,
            4,
            [0x77; 32],
            [0x88; 32],
            &accel,
        )
        .unwrap();

        let dbg_share = format!("{:?}", setup.shares[0]);
        assert!(dbg_share.contains("<REDACTED>"));

        let mut burn_log = InMemoryBurnLog::default();
        let msg = b"threshold mpc parallel-seeded few-time signature";
        let sig = setup
            .threshold_sign(5, msg, [0x99; 32], &mut burn_log, &accel)
            .unwrap();
        verify_parallel_seeded_fts(&setup.pk, msg, &sig, &accel).unwrap();

        assert_eq!(
            setup.threshold_sign(5, b"second message", [0x9B; 32], &mut burn_log, &accel),
            Err(ParallelSeededError::EpochUseBudgetExhausted)
        );

        // Negative BDOZ Soundness Test: a 1-bit wire fault (`delta = 1`) in party 0's candidate
        // chain opening on epoch 6 MUST be caught by the non-tautological BDOZ MAC barrier!
        assert_eq!(
            setup.threshold_sign_with_fault(
                6,
                b"faulted mpc opening attempt",
                [0x9C; 32],
                Some((0, 0, 1u128)),
                &accel,
            ),
            Err(ParallelSeededError::BdozMacCheckFailed)
        );

        assert!(setup.shares.iter().all(|sh| sh.is_poisoned()));
        assert_eq!(
            setup.threshold_sign(7, msg, [0; 32], &mut burn_log, &accel),
            Err(ParallelSeededError::Poisoned)
        );
        // Tampered chain value or wrong message fails verification.
        let mut bad_sig = sig.clone();
        bad_sig.chain_nodes[3][0] ^= 0x80;
        assert!(verify_parallel_seeded_fts(&setup.pk, msg, &bad_sig, &accel).is_err());
    }
}

#[cfg(test)]
mod distributed_tests {
    extern crate std;
    use super::*;
    use alloc::{vec, vec::Vec};
    use qsag_accel::ct::{ct_zeroize_bytes, ct_zeroize_u128s};
    use qsag_accel::keccak::cshake256_framed_xof;
    use qsag_accel::{CpuReferenceBackend, gf2_128::gf2_128_mul};
    use std::sync::mpsc::{self, Receiver, Sender};
    use std::thread;

    struct Packet {
        context: [u8; 32],
        values: Vec<u128>,
    }
    impl Drop for Packet {
        fn drop(&mut self) {
            ct_zeroize_u128s(&mut self.values);
        }
    }
    // Three-party assisted oblivious products over separate private mailboxes.
    // The third participant supplies independent masks a,b,r and sees neither
    // endpoint's masked operand. Privacy assumes at most one passive corruption.
    // This is a real distributed algebra test, not validation of an OT provider
    // or of malicious preprocessing. Production uses a reviewed backend.
    struct AssistedProducts {
        id: u16,
        tx: Vec<Option<Sender<Packet>>>,
        rx: Vec<Option<Receiver<Packet>>>,
        entropy: [u8; 32],
    }
    impl AssistedProducts {
        fn send(&self, peer: u16, context: [u8; 32], values: Vec<u128>) {
            self.tx[peer as usize]
                .as_ref()
                .unwrap()
                .send(Packet { context, values })
                .unwrap();
        }
        fn receive(&self, peer: u16, context: [u8; 32]) -> Packet {
            let packet = self.rx[peer as usize].as_ref().unwrap().recv().unwrap();
            assert_eq!(packet.context, context);
            packet
        }
    }
    impl Drop for AssistedProducts {
        fn drop(&mut self) {
            ct_zeroize_bytes(&mut self.entropy);
        }
    }
    impl ParallelSeededDkgProducts for AssistedProducts {
        fn party_id(&self) -> u16 {
            self.id
        }
        fn product_shares(
            &mut self,
            context: [u8; 32],
            sender: u16,
            receiver: u16,
            operand: &[u128],
        ) -> Result<Vec<u128>, ParallelSeededError> {
            let helper = 3 - sender - receiver;
            if self.id == helper {
                // Length is public and explicitly sent by the sender.
                let size = self.receive(sender, context);
                let count = size.values[0] as usize;
                let mut raw = vec![0; count * 48];
                cshake256_framed_xof(
                    b"QSAG.TEST.ASSISTED.PRODUCT",
                    &[&self.entropy, &context],
                    &mut raw,
                );
                let mut left = Vec::with_capacity(count * 2);
                let mut right = Vec::with_capacity(count * 2);
                for chunk in raw.as_chunks::<48>().0.iter() {
                    let a = u128::from_le_bytes(chunk[..16].try_into().unwrap());
                    let b = u128::from_le_bytes(chunk[16..32].try_into().unwrap());
                    let r = u128::from_le_bytes(chunk[32..].try_into().unwrap());
                    left.extend_from_slice(&[a, r]);
                    right.extend_from_slice(&[b, gf2_128_mul(a, b) ^ r]);
                }
                ct_zeroize_bytes(&mut raw);
                self.send(sender, context, left);
                self.send(receiver, context, right);
                Ok(Vec::new())
            } else {
                if self.id == sender {
                    self.send(helper, context, vec![operand.len() as u128]);
                }
                let pads = self.receive(helper, context);
                assert_eq!(pads.values.len(), operand.len() * 2);
                let peer = if self.id == sender { receiver } else { sender };
                let masked = operand
                    .iter()
                    .zip(pads.values.as_chunks::<2>().0.iter())
                    .map(|(&x, pad)| x ^ pad[0])
                    .collect();
                self.send(peer, context, masked);
                let remote = self.receive(peer, context);
                assert_eq!(remote.values.len(), operand.len());
                Ok(operand
                    .iter()
                    .zip(pads.values.as_chunks::<2>().0.iter())
                    .zip(&remote.values)
                    .map(|((&x, pad), &other)| {
                        pad[1] ^ gf2_128_mul(if self.id == sender { x } else { pad[0] }, other)
                    })
                    .collect())
            }
        }
    }
    fn networks() -> Vec<AssistedProducts> {
        let mut outgoing: Vec<Vec<Option<Sender<Packet>>>> =
            (0..3).map(|_| (0..3).map(|_| None).collect()).collect();
        let mut incoming: Vec<Vec<Option<Receiver<Packet>>>> =
            (0..3).map(|_| (0..3).map(|_| None).collect()).collect();
        for (sender, row) in outgoing.iter_mut().enumerate() {
            for (receiver, column) in incoming.iter_mut().enumerate() {
                if sender == receiver {
                    continue;
                }
                let (tx, rx) = mpsc::channel();
                row[receiver] = Some(tx);
                column[sender] = Some(rx);
            }
        }
        outgoing
            .into_iter()
            .zip(incoming)
            .enumerate()
            .map(|(id, (tx, rx))| AssistedProducts {
                id: id as u16,
                tx,
                rx,
                entropy: [id as u8 + 91; 32],
            })
            .collect()
    }
    fn config(power_count: usize) -> ParallelSeededDkgConfig {
        ParallelSeededDkgConfig {
            params: ParallelSeededParams {
                tree_height: 2,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            roster: vec![0, 1, 2],
            session: [51; 32],
            power_count,
            beaver_count: 2,
        }
    }
    /// Run rounds 1-3 with one product backend per party; nothing is activated yet.
    fn unverified_setup<B: ParallelSeededDkgProducts + Send>(
        power_count: usize,
        wrap: impl Fn(AssistedProducts) -> B,
    ) -> Vec<ParallelSeededDkgUnverifiedOutput> {
        let mut states: Vec<_> = (0..3)
            .map(|id| {
                ParallelSeededDkgRound1State::begin(config(power_count), id, [id as u8 + 13; 32])
                    .unwrap()
            })
            .collect();
        let commits: Vec<_> = states
            .iter()
            .map(ParallelSeededDkgRound1State::commitment)
            .collect();
        let openings: Vec<_> = states
            .iter_mut()
            .map(|s| s.open(&commits).unwrap())
            .collect();
        let mut inboxes: Vec<Vec<ParallelSeededDkgSharePackage>> =
            (0..3).map(|_| Vec::new()).collect();
        for state in &mut states {
            for package in state.private_packages().unwrap() {
                inboxes[package.recipient as usize].push(package);
            }
        }
        let backends: Vec<B> = networks().into_iter().map(wrap).collect();
        thread::scope(|scope| {
            let handles: Vec<_> = states
                .into_iter()
                .zip(inboxes)
                .zip(backends)
                .map(|((state, packages), mut network)| {
                    let openings = &openings;
                    scope.spawn(move || {
                        finalize_parallel_seeded_dkg_party(state, openings, packages, &mut network)
                            .unwrap()
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }
    /// Run the five-message consistency check with every party following the protocol.
    fn consistency_check(
        mut pending: Vec<ParallelSeededDkgUnverifiedOutput>,
    ) -> Vec<Result<ParallelSeededDkgOutput, ParallelSeededError>> {
        let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let coins: Vec<_> = pending
            .iter_mut()
            .map(|p| p.reveal_check_coin(&commits).unwrap())
            .collect();
        let shares: Vec<_> = pending
            .iter_mut()
            .map(|p| p.masked_shares(&coins).unwrap())
            .collect();
        let tag_commits: Vec<_> = pending
            .iter_mut()
            .map(|p| p.tag_commitment(&shares).unwrap())
            .collect();
        let tags: Vec<_> = pending
            .iter_mut()
            .map(|p| p.open_tags(&tag_commits).unwrap())
            .collect();
        pending.into_iter().map(|p| p.activate(&tags)).collect()
    }
    fn distributed_setup(power_count: usize) -> Vec<ParallelSeededDkgOutput> {
        consistency_check(unverified_setup(power_count, |network| network))
            .into_iter()
            .map(Result::unwrap)
            .collect()
    }
    #[derive(Clone, Copy, Debug)]
    enum Cheat {
        /// Feed a different operand into one pairwise product than into the others.
        Operand,
        /// Report a different additive share than the product returned.
        OutputShare,
    }
    /// Malicious participant: follows the protocol except for one pairwise product,
    /// counted over the products in which it is an endpoint.
    struct CheatingProducts {
        inner: AssistedProducts,
        endpoint_calls: usize,
        cheat: Option<(usize, Cheat)>,
    }
    impl ParallelSeededDkgProducts for CheatingProducts {
        fn party_id(&self) -> u16 {
            self.inner.party_id()
        }
        fn product_shares(
            &mut self,
            context: [u8; 32],
            sender: u16,
            receiver: u16,
            operand: &[u128],
        ) -> Result<Vec<u128>, ParallelSeededError> {
            if operand.is_empty() {
                return self
                    .inner
                    .product_shares(context, sender, receiver, operand);
            }
            let call = self.endpoint_calls;
            self.endpoint_calls += 1;
            match self.cheat {
                Some((at, Cheat::Operand)) if at == call => {
                    let mut altered = operand.to_vec();
                    altered[0] ^= 1;
                    self.inner
                        .product_shares(context, sender, receiver, &altered)
                }
                Some((at, Cheat::OutputShare)) if at == call => {
                    let mut share = self
                        .inner
                        .product_shares(context, sender, receiver, operand)?;
                    share[0] ^= 1;
                    Ok(share)
                }
                _ => self
                    .inner
                    .product_shares(context, sender, receiver, operand),
            }
        }
    }
    fn setup_with_cheater(cheat: Option<(usize, Cheat)>) -> Vec<ParallelSeededDkgUnverifiedOutput> {
        unverified_setup(2, |inner| {
            let cheat = if inner.id == 2 { cheat } else { None };
            CheatingProducts {
                inner,
                endpoint_calls: 0,
                cheat,
            }
        })
    }
    // Each party is an endpoint of four pairwise products per multiplication, in this order:
    // a^3 (calls 0..4), a^5 (4..8), a^7 (8..12), Beaver u*v (12..16), MAC lane 0 (16..20),
    // MAC lane 1 (20..24).
    #[test]
    fn dkg_consistency_check_catches_every_inconsistent_share_injection() {
        assert!(
            consistency_check(setup_with_cheater(None))
                .iter()
                .all(Result::is_ok)
        );
        for call in [0, 3, 5, 10, 12, 15, 16, 19, 21, 23] {
            for cheat in [Cheat::Operand, Cheat::OutputShare] {
                let results = consistency_check(setup_with_cheater(Some((call, cheat))));
                assert!(
                    results
                        .iter()
                        .all(|r| matches!(r, Err(ParallelSeededError::BdozMacCheckFailed))),
                    "{cheat:?} in endpoint product {call} must abort every party before activation"
                );
            }
        }
    }
    #[test]
    fn dkg_consistency_check_rejects_altered_and_replayed_check_messages() {
        // An altered coin opening is attributed to its sender.
        let mut pending = setup_with_cheater(None);
        let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let mut coins: Vec<_> = pending
            .iter_mut()
            .map(|p| p.reveal_check_coin(&commits).unwrap())
            .collect();
        assert!(
            pending[0].reveal_check_coin(&commits).is_err(),
            "a step can not be replayed"
        );
        coins[1].coin[0] ^= 1;
        assert!(matches!(
            pending[1].masked_shares(&coins),
            Err(ParallelSeededError::CommitmentMismatch { party_id: 1 })
        ));
        assert!(
            pending[1].masked_shares(&coins).is_err(),
            "a failed check stays failed"
        );

        // A share shifted after the honest shares are known: the sender's own view refuses the
        // altered broadcast, and the others' MAC tags no longer cancel.
        let mut pending = setup_with_cheater(None);
        let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let coins: Vec<_> = pending
            .iter_mut()
            .map(|p| p.reveal_check_coin(&commits).unwrap())
            .collect();
        let shares: Vec<_> = pending
            .iter_mut()
            .map(|p| p.masked_shares(&coins).unwrap())
            .collect();
        let mut shifted = shares.clone();
        shifted[2].rho[0] ^= 1;
        let mut truncated = shares.clone();
        truncated[2].sigma.pop();
        let mut probe = setup_with_cheater(None);
        let probe_commits: Vec<_> = probe.iter().map(|p| p.check_commitment()).collect();
        let probe_coins: Vec<_> = probe
            .iter_mut()
            .map(|p| p.reveal_check_coin(&probe_commits).unwrap())
            .collect();
        for p in probe.iter_mut() {
            p.masked_shares(&probe_coins).unwrap();
        }
        assert!(
            probe[2].tag_commitment(&shifted).is_err(),
            "own share was altered in transit"
        );
        assert!(
            probe[0].tag_commitment(&truncated).is_err(),
            "malformed share vector"
        );
        let tag_commits: Vec<_> = pending
            .iter_mut()
            .enumerate()
            .map(|(i, p)| {
                p.tag_commitment(if i == 2 { &shares } else { &shifted })
                    .unwrap()
            })
            .collect();
        let mut tags: Vec<_> = pending
            .iter_mut()
            .map(|p| p.open_tags(&tag_commits).unwrap())
            .collect();
        let mut pending = pending.into_iter();
        assert!(matches!(
            pending.next().unwrap().activate(&tags),
            Err(ParallelSeededError::BdozMacCheckFailed)
        ));
        // A tag changed after its commitment is attributed to its sender.
        tags[2].tags[1] ^= 1;
        assert!(matches!(
            pending.next().unwrap().activate(&tags),
            Err(ParallelSeededError::CommitmentMismatch { party_id: 2 })
        ));
    }
    #[test]
    fn dkg_output_is_not_released_before_the_check_completes() {
        let mut pending = setup_with_cheater(None);
        let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let party = pending.remove(0);
        assert!(matches!(
            party.activate(&[]),
            Err(ParallelSeededError::InvalidThresholdParameters)
        ));
        let mut party = pending.remove(0);
        assert!(
            party.masked_shares(&[]).is_err(),
            "coins before commitments are frozen"
        );
        assert!(party.reveal_check_coin(&commits).is_err());
    }
    fn drive(sessions: &mut [ParallelSeededSignSession<'_>]) -> ParallelSeededSignResult {
        for _ in 0..1024 {
            if let Some(result) = sessions[0].result() {
                assert!(sessions.iter().all(|s| s.result() == Some(result)));
                return result.clone();
            }
            let messages: Vec<_> = sessions.iter().map(|s| s.outbound().unwrap()).collect();
            for session in sessions.iter_mut() {
                session.advance(&messages).unwrap();
            }
        }
        panic!("signing phase bound exceeded");
    }
    #[test]
    fn dkg_rejects_unfrozen_repeated_and_altered_transcripts() {
        let mut states: Vec<_> = (0..3)
            .map(|id| {
                ParallelSeededDkgRound1State::begin(config(1), id, [id as u8 + 8; 32]).unwrap()
            })
            .collect();
        assert!(states[0].private_packages().is_err());
        let commits: Vec<_> = states
            .iter()
            .map(ParallelSeededDkgRound1State::commitment)
            .collect();
        let mut duplicate = commits.clone();
        duplicate[1] = duplicate[0].clone();
        assert!(states[0].open(&duplicate).is_err());
        let mut openings: Vec<_> = states
            .iter_mut()
            .map(|s| s.open(&commits).unwrap())
            .collect();
        assert!(states[0].open(&commits).is_err());
        let packages = states[0].private_packages().unwrap();
        assert_eq!(packages.len(), 2);
        assert!(packages.iter().all(|p| p.sender == 0 && p.recipient != 0));
        assert!(states[0].private_packages().is_err());
        openings[1].coin[0] ^= 1;
        let mut backend = networks().remove(0);
        assert!(matches!(
            finalize_parallel_seeded_dkg_party(
                states.remove(0),
                &openings,
                Vec::new(),
                &mut backend
            )
            .map(|_| ()),
            Err(ParallelSeededError::CommitmentMismatch { party_id: 1 })
        ));
    }
    #[test]
    fn dealerless_dkg_all_epochs_and_distributed_signature() {
        // Four leaves need 4*384 tuples; a signature needs another 384.
        let mut outputs = distributed_setup(1920);
        let seed = outputs[0].pk_seed_bytes;
        assert!(
            outputs
                .iter()
                .all(|o| o.pk_seed_bytes == seed && o.beaver_triples.len() == 2)
        );
        let mut leaves = Vec::new();
        for epoch in 0..4 {
            let mut sessions: Vec<_> = outputs
                .iter_mut()
                .map(|o| {
                    ParallelSeededSignSession::begin_leaf_preparation(
                        &mut o.share,
                        epoch,
                        [epoch as u8 + 1; 32],
                        &[0, 1, 2],
                    )
                    .unwrap()
                })
                .collect();
            match drive(&mut sessions) {
                ParallelSeededSignResult::Leaf {
                    epoch: actual,
                    digest,
                } => {
                    assert_eq!(actual, epoch);
                    leaves.push(digest);
                }
                _ => panic!("expected a leaf"),
            }
        }
        let (pk, layers) =
            assemble_parallel_seeded_public_key(config(1920).params, seed, &leaves).unwrap();
        let epoch = 2;
        let siblings = [layers[0][3], layers[1][0]];
        let message = b"distributed signing after dealerless setup";
        let mut burns = InMemoryBurnLog::default();
        let mut sessions: Vec<_> = outputs
            .iter_mut()
            .map(|o| {
                ParallelSeededSignSession::begin(
                    &mut o.share,
                    &ParallelSeededSignRequest {
                        pk: &pk,
                        epoch,
                        msg: message,
                        session_id: [72; 32],
                        roster: &[0, 1, 2],
                        siblings: &siblings,
                    },
                    &mut burns,
                )
                .unwrap()
            })
            .collect();
        let signature = match drive(&mut sessions) {
            ParallelSeededSignResult::Signature(sig) => sig,
            _ => panic!("expected a signature"),
        };
        verify_parallel_seeded_fts(&pk, message, &signature, &CpuReferenceBackend).unwrap();
        drop(sessions);
        assert!(outputs.iter().all(|o| !o.share.is_poisoned()));
    }
    #[test]
    fn custody_shape_chain_endpoints_pass_through_the_verified_release_gate() {
        let params = ParallelSeededParams {
            tree_height: 1,
            ..ParallelSeededParams::CUSTODY_H10_W5
        };
        for fault in [false, true] {
            let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
                params,
                2,
                [41; 32],
                [42; 32],
                &CpuReferenceBackend,
            )
            .unwrap();
            let pk = setup.pk.clone();
            let siblings = [setup.public_tree_layers[0][1]];
            let msg = b"custody shape";
            let mut burns = InMemoryBurnLog::default();
            let mut sessions: Vec<_> = setup
                .shares
                .iter_mut()
                .map(|share| {
                    ParallelSeededSignSession::begin(
                        share,
                        &ParallelSeededSignRequest {
                            pk: &pk,
                            epoch: 0,
                            msg,
                            session_id: [75; 32],
                            roster: &[0, 1],
                            siblings: &siblings,
                        },
                        &mut burns,
                    )
                    .unwrap()
                })
                .collect();
            // Kinds of custody the opened candidates passed through, in order.
            let mut custody = Vec::new();
            let mut altered = false;
            let mut rejected = 0;
            let mut signature = None;
            for _ in 0..1024 {
                if let Some(ParallelSeededSignResult::Signature(sig)) = sessions[0].result() {
                    signature = Some(sig.clone());
                    break;
                }
                if fault && !altered {
                    altered = sessions[0].alter_chain_value_share_for_test();
                }
                let messages: Vec<_> = sessions.iter().map(|s| s.outbound().unwrap()).collect();
                for session in &mut sessions {
                    if let Err(error) = session.advance(&messages) {
                        assert!(altered);
                        assert_eq!(error, ParallelSeededError::BdozMacCheckFailed);
                        assert!(session.result().is_none());
                        rejected += 1;
                    }
                    if let Some(verified) = session.held_in_verified_sessions()
                        && custody.last() != Some(&verified)
                    {
                        custody.push(verified);
                    }
                }
                if rejected != 0 {
                    break;
                }
            }
            drop(sessions);
            // The randomizer has no codeword yet; the 68 chain endpoints do.
            assert_eq!(custody, [false, true]);
            if fault {
                assert_eq!(rejected, 2);
                assert!(signature.is_none());
                assert!(setup.shares.iter().all(|s| s.is_poisoned()));
            } else {
                let sig = signature.unwrap();
                assert_eq!(sig.chain_nodes.len(), 68);
                verify_parallel_seeded_fts(&pk, msg, &sig, &CpuReferenceBackend).unwrap();
            }
        }
    }
    #[test]
    fn value_open_bit_error_fails_mac_open_and_poisons_honest_party() {
        let mut outputs = distributed_setup(384);
        let (pk, layers) = assemble_parallel_seeded_public_key(
            config(384).params,
            outputs[0].pk_seed_bytes,
            &[[0; 4]; 4],
        )
        .unwrap();
        let siblings = [layers[0][1], layers[1][1]];
        let mut burns = InMemoryBurnLog::default();
        let mut sessions: Vec<_> = outputs
            .iter_mut()
            .map(|o| {
                ParallelSeededSignSession::begin(
                    &mut o.share,
                    &ParallelSeededSignRequest {
                        pk: &pk,
                        epoch: 0,
                        msg: b"MAC barrier",
                        session_id: [73; 32],
                        roster: &[0, 1, 2],
                        siblings: &siblings,
                    },
                    &mut burns,
                )
                .unwrap()
            })
            .collect();
        let mut altered_round = None;
        let mut rejected = false;
        for _ in 0..1024 {
            // A malicious party commits to the changed value. Its MAC remains
            // unchanged, so the test reaches MacOpen rather than failing the
            // earlier commitment barrier.
            if altered_round.is_none() && sessions[0].alter_value_share_for_test() {
                match sessions[0].outbound().unwrap() {
                    ParallelSeededSignMessage::Commitment { round, .. } => {
                        altered_round = Some(round)
                    }
                    _ => panic!("expected value commitment"),
                }
            }
            let messages: Vec<_> = sessions.iter().map(|s| s.outbound().unwrap()).collect();
            for session in &mut sessions {
                if let Err(error) = session.advance(&messages) {
                    assert_eq!(error, ParallelSeededError::BdozMacCheckFailed);
                    assert!(
                        matches!(&messages[0], ParallelSeededSignMessage::Opening {round, ..}
                        if Some(*round) == altered_round.map(|r| r + 1))
                    );
                    assert!(session.result().is_none());
                    assert_eq!(session.outbound(), Err(ParallelSeededError::Poisoned));
                    rejected = true;
                }
            }
            if rejected {
                break;
            }
        }
        assert!(altered_round.is_some() && rejected);
        drop(sessions);
        assert!(outputs.iter().all(|o| o.share.is_poisoned()));
        assert!(matches!(
            ParallelSeededSignSession::begin_leaf_preparation(
                &mut outputs[1].share,
                1,
                [74; 32],
                &[0, 1, 2]
            ),
            Err(ParallelSeededError::Poisoned)
        ));
    }
}
