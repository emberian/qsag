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
    FrontierFtsPublicKey, FrontierFtsSignature, FrontierFtsSigningKey, FrontierVerifyInput,
    FtsEpochWal, RotatedEpochVerifyInput, RotatedEpochVote, verify_frontier_fts,
    verify_frontier_fts_batch, verify_rotated_epoch_votes_batch,
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
pub use parallel_mpc::{
    ParallelSeededDkgOtPads, ParallelSeededDkgOtPeer, ParallelSeededDkgRefillState,
    ParallelSeededDkgRefillUnverified, ParallelSeededDkgReservoir,
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
    use qsag_accel::ct::ct_zeroize_bytes;
    use qsag_accel::keccak::cshake256_framed_xof;
    use qsag_accel::{CpuReferenceBackend, gf2_128::gf2_128_mul};
    use qsag_asm::wipe::{SecretBuffer, SecretVec};
    use std::sync::mpsc::{self, Receiver, Sender};
    use std::thread;

    struct Packet {
        context: [u8; 32],
        values: SecretVec<u128>,
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
                .send(Packet {
                    context,
                    values: SecretBuffer(values),
                })
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
                    .zip(remote.values.iter())
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
        setup_with_backends(
            power_count,
            networks().into_iter().map(wrap).collect(),
            &[],
            &[],
        )
    }
    /// As [`unverified_setup`] over any backends. Party 2 authenticates `value[index] + delta`
    /// for every `(index, delta)` in `faults`, consistently toward every peer, and shifts its
    /// shares of the first products by `product_faults` before deriving `a^6` and `a^7`.
    fn setup_with_backends<B: ParallelSeededDkgProducts + Send>(
        power_count: usize,
        backends: Vec<B>,
        faults: &[(usize, u128)],
        product_faults: &[(usize, u128)],
    ) -> Vec<ParallelSeededDkgUnverifiedOutput> {
        let mut states: Vec<_> = (0..3)
            .map(|id| {
                ParallelSeededDkgRound1State::begin(config(power_count), id, [id as u8 + 13; 32])
                    .unwrap()
            })
            .collect();
        states[2].value_faults = faults.to_vec();
        states[2].product_faults = product_faults.to_vec();
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
    /// Malicious participant: follows the protocol except for one element of one pairwise
    /// product, counted over the products in which it is an endpoint.
    struct CheatingProducts {
        inner: AssistedProducts,
        endpoint_calls: usize,
        /// `(endpoint call, element, kind)`; the element index wraps at the operand length.
        cheat: Option<(usize, usize, Cheat)>,
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
                Some((at, element, Cheat::Operand)) if at == call => {
                    let mut altered = operand.to_vec();
                    altered[element % operand.len()] ^= 1;
                    self.inner
                        .product_shares(context, sender, receiver, &altered)
                }
                Some((at, element, Cheat::OutputShare)) if at == call => {
                    let mut share = self
                        .inner
                        .product_shares(context, sender, receiver, operand)?;
                    share[element % operand.len()] ^= 1;
                    Ok(share)
                }
                _ => self
                    .inner
                    .product_shares(context, sender, receiver, operand),
            }
        }
    }
    fn setup_with_cheater(
        cheat: Option<(usize, usize, Cheat)>,
    ) -> Vec<ParallelSeededDkgUnverifiedOutput> {
        unverified_setup(2, |inner| {
            let cheat = if inner.id == 2 { cheat } else { None };
            CheatingProducts {
                inner,
                endpoint_calls: 0,
                cheat,
            }
        })
    }
    // Each party is an endpoint of four pairwise products per multiplication, the first two
    // as receiver and the last two as sender, in this order: `(a^2, a^4, u) * a` (calls 0..4,
    // three sender operands per tuple), `a^6 * a` (4..8), Beaver `u*v` (8..12, absent without
    // output triples), MAC lane 0 and MAC lane 1 (four calls each).
    fn refill_reservoirs(
        reservoirs: Vec<ParallelSeededDkgReservoir>,
        count: usize,
        cheat: Option<(usize, usize, Cheat)>,
    ) -> Vec<Result<ParallelSeededDkgReservoir, ParallelSeededError>> {
        let mut states: Vec<_> = reservoirs
            .into_iter()
            .enumerate()
            .map(|(id, r)| {
                r.into_refill([71; 32], count, 0, [id as u8 + 17; 32])
                    .unwrap()
            })
            .collect();
        let commits: Vec<_> = states.iter().map(|s| s.commitment()).collect();
        let opens: Vec<_> = states
            .iter_mut()
            .map(|s| s.open(&commits).unwrap())
            .collect();
        let mut inboxes: Vec<Vec<_>> = (0..3).map(|_| Vec::new()).collect();
        for state in &mut states {
            for package in state.private_packages().unwrap() {
                inboxes[package.recipient as usize].push(package);
            }
        }
        let mut pending: Vec<_> = thread::scope(|scope| {
            let handles: Vec<_> = states
                .into_iter()
                .zip(inboxes)
                .zip(networks())
                .map(|((state, packages), inner)| {
                    let opens = &opens;
                    scope.spawn(move || {
                        let local_cheat = if inner.id == 2 { cheat } else { None };
                        let mut backend = CheatingProducts {
                            inner,
                            endpoint_calls: 0,
                            cheat: local_cheat,
                        };
                        state.finalize(opens, packages, &mut backend).unwrap()
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
        let coins: Vec<_> = pending
            .iter_mut()
            .map(|p| p.reveal_check_coin(&commits).unwrap())
            .collect();
        let masked: Vec<_> = pending
            .iter_mut()
            .map(|p| p.masked_shares(&coins).unwrap())
            .collect();
        let commits: Vec<_> = pending
            .iter_mut()
            .map(|p| p.tag_commitment(&masked).unwrap())
            .collect();
        let tags: Vec<_> = pending
            .iter_mut()
            .map(|p| p.open_tags(&commits).unwrap())
            .collect();
        pending.into_iter().map(|p| p.activate(&tags)).collect()
    }

    #[test]
    fn dkg_reservoir_streams_leaves_and_preserves_burns() {
        let mut reservoirs: Vec<_> = distributed_setup(384)
            .into_iter()
            .map(|o| ParallelSeededDkgReservoir::new(o).unwrap())
            .collect();
        let seed = reservoirs[0].pk_seed_bytes();
        let mut previous_masks: Vec<_> =
            reservoirs.iter().map(|r| r.first_mask_for_test()).collect();
        let mut leaves = Vec::new();
        for epoch in 0..4 {
            if epoch != 0 {
                reservoirs = refill_reservoirs(reservoirs, 384, None)
                    .into_iter()
                    .map(Result::unwrap)
                    .collect();
            }
            let masks: Vec<_> = reservoirs.iter().map(|r| r.first_mask_for_test()).collect();
            if epoch != 0 {
                // The helper intentionally repeats session and entropy. The
                // reservoir generation must still produce fresh masks.
                assert_ne!(masks, previous_masks);
            }
            previous_masks = masks;
            assert!(
                reservoirs
                    .iter()
                    .all(|r| r.pk_seed_bytes() == seed && r.remaining_powers() == 384)
            );
            let mut sessions: Vec<_> = reservoirs
                .iter_mut()
                .map(|r| {
                    ParallelSeededSignSession::begin_leaf_preparation(
                        r.share_mut(),
                        epoch,
                        [epoch as u8 + 1; 32],
                        &[0, 1, 2],
                    )
                    .unwrap()
                })
                .collect();
            match drive(&mut sessions) {
                ParallelSeededSignResult::Leaf { digest, .. } => leaves.push(digest),
                _ => panic!("expected leaf"),
            }
            drop(sessions);
            assert!(reservoirs.iter().all(|r| r.remaining_powers() == 0));
        }
        let (pk, layers) =
            assemble_parallel_seeded_public_key(config(384).params, seed, &leaves).unwrap();
        reservoirs = refill_reservoirs(reservoirs, 384, None)
            .into_iter()
            .map(Result::unwrap)
            .collect();
        let siblings = [layers[0][1], layers[1][1]];
        let mut burns = InMemoryBurnLog::default();
        let request = ParallelSeededSignRequest {
            pk: &pk,
            epoch: 0,
            msg: b"streamed key",
            session_id: [44; 32],
            roster: &[0, 1, 2],
            siblings: &siblings,
        };
        let mut sessions: Vec<_> = reservoirs
            .iter_mut()
            .map(|r| ParallelSeededSignSession::begin(r.share_mut(), &request, &mut burns).unwrap())
            .collect();
        let ParallelSeededSignResult::Signature(sig) = drive(&mut sessions) else {
            panic!("expected signature")
        };
        verify_parallel_seeded_fts(&pk, request.msg, &sig, &CpuReferenceBackend).unwrap();
        drop(sessions);
        reservoirs = refill_reservoirs(reservoirs, 384, None)
            .into_iter()
            .map(Result::unwrap)
            .collect();
        for r in &mut reservoirs {
            assert!(matches!(
                ParallelSeededSignSession::begin(r.share_mut(), &request, &mut burns),
                Err(ParallelSeededError::EpochUseBudgetExhausted)
            ));
        }
    }

    #[test]
    fn dkg_reservoir_rejects_key_substitution_and_oversized_batches() {
        let mut reservoirs: Vec<_> = distributed_setup(2)
            .into_iter()
            .map(|o| ParallelSeededDkgReservoir::new(o).unwrap())
            .collect();
        reservoirs[2].corrupt_seed_for_test();
        assert!(
            refill_reservoirs(reservoirs, 2, None)
                .iter()
                .all(|r| matches!(r, Err(ParallelSeededError::BdozMacCheckFailed)))
        );
        for count in [0, parallel_mpc::DEFAULT_BEAVER_TRIPLE_POOL + 1, usize::MAX] {
            let output = distributed_setup(2).remove(0);
            assert!(
                ParallelSeededDkgReservoir::new(output)
                    .unwrap()
                    .into_refill([1; 32], count, 0, [2; 32])
                    .is_err()
            );
        }
        for height in [3, 5, 8, 10] {
            let params = ParallelSeededParams {
                tree_height: height,
                ..ParallelSeededParams::CUSTODY_H10_W5
            };
            assert_eq!(params.leaf_preparation_power_count(), 32_640);
            assert_eq!(params.signing_power_count(), 19_680);
            let config = ParallelSeededDkgConfig {
                params,
                roster: vec![0, 1, 2],
                session: [1; 32],
                power_count: params.leaf_preparation_power_count(),
                beaver_count: 0,
            };
            assert!(ParallelSeededDkgRound1State::begin(config, 0, [2; 32]).is_ok());
        }
    }

    #[test]
    fn dkg_reservoir_refill_detects_products_and_both_mac_lane_cheating() {
        // A refill carries no output triples: two product calls, then the two MAC lanes.
        for call in 0..16 {
            for cheat in [Cheat::Operand, Cheat::OutputShare] {
                let reservoirs = distributed_setup(2)
                    .into_iter()
                    .map(|o| ParallelSeededDkgReservoir::new(o).unwrap())
                    .collect();
                assert!(
                    refill_reservoirs(reservoirs, 2, Some((call, call, cheat)))
                        .iter()
                        .all(|r| matches!(r, Err(ParallelSeededError::BdozMacCheckFailed))),
                    "{cheat:?} in refill endpoint product {call}"
                );
            }
        }
    }

    fn all_abort(results: &[Result<ParallelSeededDkgOutput, ParallelSeededError>]) -> bool {
        results
            .iter()
            .all(|r| matches!(r, Err(ParallelSeededError::BdozMacCheckFailed)))
    }
    #[test]
    fn dkg_consistency_check_catches_every_inconsistent_share_injection() {
        assert!(
            consistency_check(setup_with_cheater(None))
                .iter()
                .all(Result::is_ok)
        );
        // Twenty endpoint products with two power tuples and two output triples. Elements 0..3
        // reach each of the three products that share a tuple's OTs; 5 and 20 land in the
        // second tuple, the triples and, in the MAC lanes, the sacrificial values.
        for call in 0..20 {
            for element in [0, 1, 2, 5, 20] {
                for cheat in [Cheat::Operand, Cheat::OutputShare] {
                    let results =
                        consistency_check(setup_with_cheater(Some((call, element, cheat))));
                    assert!(
                        all_abort(&results),
                        "{cheat:?} at element {element} of endpoint product {call} must abort \
                         every party before activation"
                    );
                }
            }
        }
    }
    /// A party that authenticates one wrong value, consistently toward every peer, breaks a
    /// relation rather than a MAC. Every value except its own key shares and the fold mask
    /// is pinned by a relation, so every such deviation must abort.
    #[test]
    fn dkg_consistency_check_pins_every_authenticated_value_to_its_relation() {
        // Four key lanes, 2 x 7 powers, 4 x 3 triple values, 2 x 2 sacrificial values, the
        // square-mask pair, the fold mask.
        let fold_mask = 4 + 14 + 12 + 4 + 2;
        let run = |faults: &[(usize, u128)]| {
            consistency_check(setup_with_backends(2, networks(), faults, &[]))
        };
        assert!(
            run(&[(fold_mask, 1)]).iter().all(Result::is_ok),
            "a mask is any value"
        );
        assert!(
            run(&[(0, 1), (3, 1 << 90)]).iter().all(Result::is_ok),
            "so is a key share"
        );
        // (r + 1)^2 = r^2 + 1 is another valid square-mask pair.
        assert!(
            run(&[(fold_mask - 2, 1), (fold_mask - 1, 1)])
                .iter()
                .all(Result::is_ok)
        );
        for index in 4..fold_mask {
            for delta in [1, 1 << 127] {
                assert!(
                    all_abort(&run(&[(index, delta)])),
                    "value {index} is not pinned"
                );
            }
        }
        // Deviations that keep one relation true and break the next one.
        let (a, a2, a3, a4, a6) = (4, 5, 6, 7, 9);
        let (sacrifice, product) = (4 + 14 + 12, 4 + 14 + 12 + 1);
        for faults in [
            // (a + 1)^2 = a^2 + 1: the square holds, the products with `a` do not.
            vec![(a, 1), (a2, 1)],
            // (a^2 + 1)^2 = a^4 + 1: the second square holds, the first does not.
            vec![(a2, 1), (a4, 1)],
            vec![(a3, 1), (a6, 1)],
            // An error in a product together with one in the sacrificial product.
            vec![(a3, 1), (product, 1)],
            vec![(a3, 1), (sacrifice, 1)],
            vec![(sacrifice, 1), (product, 1)],
            // An error in a square together with one in the square mask's image.
            vec![(a2, 1), (fold_mask - 1, 1)],
            vec![(fold_mask - 2, 1), (fold_mask - 1, 2)],
        ] {
            assert!(all_abort(&run(&faults)), "{faults:?} survives the check");
        }
    }
    /// A wrong product carried forward consistently: the party shifts its share of `a^3`
    /// (or `a^5`) and of the sacrificial product `u*a` by the same amount, then derives `a^6`
    /// and `a^7` from the shifted cube. The squares and the last product then hold, and the
    /// two errors cancel in the checked sum unless every product has a challenge weight.
    #[test]
    fn dkg_consistency_check_weights_every_product_against_the_sacrificial_one() {
        let run = |product_faults: &[(usize, u128)]| {
            consistency_check(setup_with_backends(2, networks(), &[], product_faults))
        };
        assert!(run(&[]).iter().all(Result::is_ok));
        // Shares 0..3 of tuple 0 are `a^3`, `a^5`, `u*a`; tuple 1 follows.
        for delta in [1, 1 << 64, u128::MAX] {
            for faults in [
                vec![(0, delta), (2, delta)],
                vec![(1, delta), (2, delta)],
                // Equal errors in two products cancel under equal weights.
                vec![(0, delta), (1, delta)],
                vec![(0, delta), (1, delta), (2, delta)],
                vec![(3, delta), (4, delta), (5, delta)],
                vec![(0, delta)],
                vec![(5, delta)],
            ] {
                assert!(all_abort(&run(&faults)), "{faults:?} survives the check");
            }
        }
    }
    /// The Gilboa adapter's random-OT and fixed-key paths under the full ceremony, and a
    /// sender that puts a different operand into its correction words than into its shares.
    #[test]
    fn dkg_over_gilboa_products_passes_and_catches_altered_correction_words() {
        use parallel_mpc::ideal_ot::{IdealOt, Mailbox, Tamper};
        // Party 2 sends to its two peers in turn: the first tuple flight (sends 0 and 1), the
        // seventh-power flight (2, 3), the triples (4, 5), then one block per MAC lane.
        fn shift_first_factor(words: &mut [u128]) {
            // `a^2 + 1` for tuple 0: bit `i` carries the operand times `z^i`.
            for (bit, word) in words.iter_mut().step_by(3).take(128).enumerate() {
                *word ^= 1 << bit;
            }
        }
        fn shift_sacrificial_factor(words: &mut [u128]) {
            for (bit, word) in words.iter_mut().skip(2).step_by(3).take(128).enumerate() {
                *word ^= 1 << bit;
            }
        }
        fn shift_first_value(words: &mut [u128]) {
            // Row `i` of a block holds stream `i` for every value; shift value 0 in all rows.
            let count = words.len() / 128;
            for word in words.iter_mut().step_by(count) {
                *word ^= 1;
            }
        }
        fn shift_last_value(words: &mut [u128]) {
            let count = words.len() / 128;
            for word in words.iter_mut().skip(count - 1).step_by(count) {
                *word ^= 1 << 77;
            }
        }
        let run = |tamper: Option<Tamper>| {
            let mailbox = Mailbox::default();
            let backends = (0..3u16)
                .map(|id| {
                    let mut ot = IdealOt::new(id, &mailbox);
                    ot.tamper = tamper.filter(|_| id == 2);
                    ParallelSeededGilboaProducts::new(id, [id as u8 + 60; 32], ot)
                })
                .collect();
            let results = consistency_check(setup_with_backends(3, backends, &[], &[]));
            assert!(mailbox.is_empty());
            results
        };
        let honest = run(None);
        let seed = honest[0].as_ref().unwrap().pk_seed_bytes;
        assert!(honest.iter().all(|o| {
            let o = o.as_ref().unwrap();
            o.pk_seed_bytes == seed && o.beaver_triples.len() == 2 && !o.share.is_poisoned()
        }));
        let tampers: [Tamper; 8] = [
            (0, shift_first_factor),
            (1, shift_sacrificial_factor),
            (2, shift_first_factor),
            (5, shift_first_factor),
            (6, shift_first_value),
            (7, shift_last_value),
            (8, shift_last_value),
            (9, shift_first_value),
        ];
        for (send, alter) in tampers {
            assert!(
                all_abort(&run(Some((send, alter)))),
                "altered send {send} survives"
            );
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
    /// Every opening is bound to authenticated values before the challenges exist: a party
    /// that moves one of its broadcast shares afterwards leaves MAC tags that do not cancel.
    #[test]
    fn dkg_consistency_check_binds_every_opened_value_to_its_mac() {
        let alterations: [fn(&mut ParallelSeededDkgCheckShares); 6] = [
            // Two output triples come first in `rho`, then the two power tuples.
            |s| s.rho[1] ^= 1,
            |s| s.rho[2] ^= 1,
            |s| s.rho[3] ^= 1 << 100,
            |s| s.sigma[0] ^= 1,
            |s| s.square ^= 1,
            |s| s.masked ^= 1,
        ];
        for (index, alter) in alterations.into_iter().enumerate() {
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
            alter(&mut shifted[2]);
            // Party 2 computes its tag from what it really holds; the others see its shift.
            let tag_commits: Vec<_> = pending
                .iter_mut()
                .enumerate()
                .map(|(i, p)| {
                    p.tag_commitment(if i == 2 { &shares } else { &shifted })
                        .unwrap()
                })
                .collect();
            let tags: Vec<_> = pending
                .iter_mut()
                .map(|p| p.open_tags(&tag_commits).unwrap())
                .collect();
            let results: Vec<_> = pending.into_iter().map(|p| p.activate(&tags)).collect();
            assert!(all_abort(&results), "alteration {index} survives");
        }
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
