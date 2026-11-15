//! Bounded, independent verification lanes. No equations or acceptance decisions are combined.
use super::*;

/// One independently authenticated Frontier signature and its exact verification context.
pub struct FrontierVerifyInput<'a> {
    pub pk: &'a FrontierFtsPublicKey,
    pub dp: &'a FrontierDpTable,
    pub message: &'a [u8],
    pub signature: &'a FrontierFtsSignature,
}

struct HashJob {
    state: [u64; 25],
    bytes: [u8; 272],
    needs_prefix: bool,
    chain_node: Option<u32>,
}

struct Lane<'a> {
    input: &'a FrontierVerifyInput<'a>,
    pid: [u8; 56],
    frontier: Vec<u32>,
    offsets: Vec<u8>,
    index: usize,
    stack: Vec<(u32, [u8; 32])>,
    current: Option<(u32, usize, [u8; 32])>,
    // This lane owns one immutable profile/key context. The cached state is after
    // absorbing the first rate block of TAG_CHAIN for exactly this node. The step
    // and chain value start in block two, so neither is part of this cache key.
    chain_prefix: Option<(u32, [u64; 25])>,
}

impl<'a> Lane<'a> {
    fn new(input: &'a FrontierVerifyInput<'a>) -> Result<Self, FrontierFtsError> {
        let FrontierVerifyInput {
            pk,
            dp,
            message,
            signature: sig,
        } = input;
        let p = pk.profile.params();
        if dp.params != p {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        if sig.randomizer.len() != p.node_bytes
            || sig.chain_values.len() != p.frontier_len * p.node_bytes
        {
            return Err(FrontierFtsError::MalformedSignatureLength);
        }
        if (sig.grind_counter as u32) >= (1u32 << p.counter_bits) {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        let pid = pk.profile.pid_bytes();
        let digest = prehash_message_256(&pid, &pk.pk_seed, &pk.root, message);
        let rank = squeeze_target_index(
            &pid,
            &pk.pk_seed,
            &pk.root,
            &sig.randomizer,
            &digest,
            sig.grind_counter,
            p.index_bits,
        );
        if !rank.ct_lt(dp.total_cardinality) {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        let (frontier, offsets) = dp.unrank(rank)?;
        Ok(Self {
            input,
            pid,
            frontier,
            offsets,
            index: 0,
            stack: Vec::with_capacity(p.frontier_len),
            current: None,
            chain_prefix: None,
        })
    }

    // Same left-to-right stack reduction as the scalar verifier; yields at every hash.
    fn next(&mut self) -> Option<HashJob> {
        let p = self.input.pk.profile.params();
        loop {
            if let Some((v, step, value)) = self.current.take() {
                if step < p.winternitz_w - 1 {
                    self.current = Some((v, step + 1, value));
                    let (mut state, bytes) = frame(
                        false,
                        &self.pid,
                        &self.input.pk.pk_seed,
                        v,
                        &(step as u64).to_be_bytes(),
                        &value[..p.node_bytes],
                    );
                    let needs_prefix = match self.chain_prefix {
                        Some((node, prefix)) if node == v => {
                            state = prefix;
                            false
                        }
                        _ => true,
                    };
                    return Some(HashJob {
                        state,
                        bytes,
                        needs_prefix,
                        chain_node: Some(v),
                    });
                }
                self.stack.push((v, value));
            }
            let len = self.stack.len();
            if len >= 2
                && self.stack[len - 2].0 & 1 == 0
                && self.stack[len - 1].0 == self.stack[len - 2].0 + 1
            {
                let (right_v, right) = self.stack[len - 1];
                let (_, left) = self.stack[len - 2];
                self.stack.truncate(len - 2);
                let parent = right_v >> 1;
                self.current = Some((
                    parent,
                    if parent > 1 { 0 } else { p.winternitz_w - 1 },
                    [0; 32],
                ));
                let (state, bytes) = frame(
                    true,
                    &self.pid,
                    &self.input.pk.pk_seed,
                    parent,
                    &left[..p.node_bytes],
                    &right[..p.node_bytes],
                );
                return Some(HashJob {
                    state,
                    bytes,
                    needs_prefix: true,
                    chain_node: None,
                });
            }
            if self.index == self.frontier.len() {
                return None;
            }
            let i = self.index;
            self.index += 1;
            let mut value = [0; 32];
            value[..p.node_bytes].copy_from_slice(
                &self.input.signature.chain_values[i * p.node_bytes..(i + 1) * p.node_bytes],
            );
            self.current = Some((self.frontier[i], self.offsets[i] as usize, value));
        }
    }
}

// Both five-field transcripts occupy strictly between one and two 136-byte rate blocks.
fn frame(
    merge: bool,
    pid: &[u8; 56],
    seed: &[u8; 32],
    node: u32,
    fourth: &[u8],
    fifth: &[u8],
) -> ([u64; 25], [u8; 272]) {
    const CHAIN: [u64; 25] = qsag_core::sponge::keccak::cshake256_static_midstate(TAG_CHAIN);
    const MERGE: [u64; 25] = qsag_core::sponge::keccak::cshake256_static_midstate(TAG_MERGE);
    let mut bytes = [0; 272];
    bytes[..8].copy_from_slice(&5u64.to_le_bytes());
    let mut pos = 8;
    for field in [
        pid.as_slice(),
        seed.as_slice(),
        &(node as u64).to_be_bytes(),
        fourth,
        fifth,
    ] {
        bytes[pos..pos + 8].copy_from_slice(&(field.len() as u64).to_le_bytes());
        pos += 8;
        bytes[pos..pos + field.len()].copy_from_slice(field);
        pos += field.len();
    }
    debug_assert!(pos > 136 && pos < 272);
    bytes[pos] ^= 0x04;
    bytes[271] ^= 0x80;
    (if merge { MERGE } else { CHAIN }, bytes)
}

fn absorb_rate(state: &mut [u64; 25], bytes: &[u8]) {
    for (word, src) in state[..17].iter_mut().zip(bytes.as_chunks::<8>().0.iter()) {
        *word ^= u64::from_le_bytes(*src);
    }
}

/// Verify up to eight independent hash streams at once using the existing Keccak batch backend.
/// Reuses each node's invariant first chain block within its own key/profile lane.
/// Returns one scalar-equivalent verdict per input in input order, with bounded workspace and
/// no internal worker threads. Profiles, keys, messages, and DP tables may differ between lanes.
pub fn verify_frontier_fts_batch(
    inputs: &[FrontierVerifyInput<'_>],
) -> Vec<Result<(), FrontierFtsError>> {
    verify_batch_with_permutation(inputs, qsag_core::sponge::keccak::keccak_f1600_batch)
}

fn verify_batch_with_permutation(
    inputs: &[FrontierVerifyInput<'_>],
    mut permute: impl FnMut(&mut [[u64; 25]]),
) -> Vec<Result<(), FrontierFtsError>> {
    let mut results = Vec::with_capacity(inputs.len());
    for chunk in inputs.chunks(8) {
        let mut lanes: Vec<_> = chunk.iter().map(Lane::new).collect();
        let mut states = Vec::with_capacity(8);
        let mut jobs = Vec::with_capacity(8);
        let mut indices = Vec::with_capacity(8);
        let mut prefix_states = Vec::with_capacity(8);
        let mut prefix_indices = Vec::with_capacity(8);
        loop {
            states.clear();
            jobs.clear();
            indices.clear();
            prefix_states.clear();
            prefix_indices.clear();
            for (i, lane) in lanes.iter_mut().enumerate() {
                if let Ok(lane) = lane
                    && let Some(job) = lane.next()
                {
                    states.push(job.state);
                    jobs.push(job);
                    indices.push(i);
                }
            }
            if states.is_empty() {
                break;
            }
            for (j, job) in jobs.iter().enumerate() {
                if job.needs_prefix {
                    let mut state = job.state;
                    absorb_rate(&mut state, &job.bytes[..136]);
                    prefix_states.push(state);
                    prefix_indices.push(j);
                }
            }
            if !prefix_states.is_empty() {
                permute(&mut prefix_states);
            }
            for (&state, &j) in prefix_states.iter().zip(&prefix_indices) {
                states[j] = state;
                if let Some(node) = jobs[j].chain_node {
                    let Ok(lane) = &mut lanes[indices[j]] else {
                        unreachable!()
                    };
                    lane.chain_prefix = Some((node, state));
                }
            }
            for (state, job) in states.iter_mut().zip(&jobs) {
                absorb_rate(state, &job.bytes[136..]);
            }
            permute(&mut states);
            for (state, i) in states.iter().zip(indices.iter().copied()) {
                let Ok(lane) = &mut lanes[i] else {
                    unreachable!()
                };
                let Some((_, _, value)) = &mut lane.current else {
                    unreachable!()
                };
                for (dst, word) in value.as_chunks_mut::<8>().0.iter_mut().zip(state) {
                    dst.copy_from_slice(&word.to_le_bytes());
                }
            }
        }
        results.extend(lanes.into_iter().map(|lane| {
            lane.and_then(|lane| {
                let n = lane.input.pk.profile.params().node_bytes;
                if lane.stack.len() == 1
                    && lane.stack[0].0 == 1
                    && ct_eq_bytes(&lane.stack[0].1[..n], &lane.input.pk.root)
                {
                    Ok(())
                } else {
                    Err(FrontierFtsError::SignatureVerificationFailed)
                }
            })
        }));
    }
    results
}

/// Exact context for one epoch-rotated vote.
pub struct RotatedEpochVerifyInput<'a> {
    pub current: &'a FrontierFtsPublicKey,
    pub dp: &'a FrontierDpTable,
    pub vote: &'a RotatedEpochVote,
    pub chain_id: &'a [u8; 32],
    pub expected_epoch: u64,
    pub expected_vote_digest: &'a [u8; 32],
}

/// Authenticate independent epoch transitions, preserving the scalar wrapper's checks.
pub fn verify_rotated_epoch_votes_batch(
    inputs: &[RotatedEpochVerifyInput<'_>],
) -> Vec<Result<FrontierFtsPublicKey, FrontierFtsError>> {
    let mut result = Vec::with_capacity(inputs.len());
    for chunk in inputs.chunks(8) {
        let messages: Vec<_> = chunk
            .iter()
            .map(|i| i.vote.link.message(i.chain_id, &i.vote.vote_digest))
            .collect();
        let valid: Vec<_> = chunk
            .iter()
            .enumerate()
            .filter(|(_, i)| {
                i.current.profile.params().node_bytes == 32
                    && i.current.profile.params().max_safe_uses == 1
                    && i.current.root.len() == 32
                    && i.vote.link.epoch == i.expected_epoch
                    && i.expected_epoch.checked_add(1).is_some()
                    && &i.vote.vote_digest == i.expected_vote_digest
            })
            .map(|(index, i)| {
                (
                    index,
                    FrontierVerifyInput {
                        pk: i.current,
                        dp: i.dp,
                        message: &messages[index],
                        signature: &i.vote.signature,
                    },
                )
            })
            .collect();
        let verification = verify_frontier_fts_batch(
            &valid
                .iter()
                .map(|(_, i)| FrontierVerifyInput {
                    pk: i.pk,
                    dp: i.dp,
                    message: i.message,
                    signature: i.signature,
                })
                .collect::<Vec<_>>(),
        );
        let mut verdicts = verification.into_iter();
        let mut valid_indices = valid.iter().map(|(index, _)| *index).peekable();
        for (index, input) in chunk.iter().enumerate() {
            if valid_indices.peek() == Some(&index) {
                valid_indices.next();
                let Some(verdict) = verdicts.next() else {
                    unreachable!()
                };
                result.push(verdict.map(|()| FrontierFtsPublicKey {
                    profile: input.current.profile,
                    pk_seed: input.current.pk_seed,
                    root: input.vote.link.next_epoch_pk_root.to_vec(),
                }));
            } else {
                result.push(Err(FrontierFtsError::SignatureVerificationFailed));
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_accel::CpuReferenceBackend;

    #[test]
    fn batch_transcripts_match_scalar_hashes() {
        for n in [16, 32] {
            for merge in [false, true] {
                let pid = [17; 56];
                let seed = [29; 32];
                let value = [43; 32];
                let step = 95u64.to_be_bytes();
                let fourth = if merge { &value[..n] } else { &step };
                let (mut state, bytes) = frame(merge, &pid, &seed, 511, fourth, &value[..n]);
                for block in bytes.as_chunks::<136>().0 {
                    for (word, src) in state[..17].iter_mut().zip(block.as_chunks::<8>().0.iter()) {
                        *word ^= u64::from_le_bytes(*src);
                    }
                    qsag_core::sponge::keccak::keccak_f1600_batch(core::slice::from_mut(
                        &mut state,
                    ));
                }
                let mut expected = [0; 32];
                cshake256_framed_xof(
                    if merge { TAG_MERGE } else { TAG_CHAIN },
                    &[&pid, &seed, &511u64.to_be_bytes(), fourth, &value[..n]],
                    &mut expected[..n],
                );
                let actual: Vec<_> = state[..4].iter().flat_map(|w| w.to_le_bytes()).collect();
                assert_eq!(&actual[..n], &expected[..n]);
            }
        }
    }

    #[test]
    fn batch_verdicts_match_scalar_mixed_inputs() {
        let profile = FrontierFtsProfile::Fast256Test;
        let dp = FrontierDpTable::build(profile);
        let wrong_dp = FrontierDpTable::build(FrontierFtsProfile::Full256Bit);
        let mut keys = Vec::new();
        let mut sigs = Vec::new();
        for i in 0..9 {
            let mut key = FrontierFtsSigningKey::keygen(
                profile,
                [i; 32],
                [i + 10; 32],
                [i + 20; 32],
                true,
                &CpuReferenceBackend::new(),
            );
            sigs.push(key.sign(&dp, b"batch vote", &[i + 30; 32]).unwrap());
            keys.push(key);
        }
        let good = sigs[0].clone();
        sigs[1].chain_values[3] ^= 1;
        sigs[2].randomizer.clear();
        sigs[3].chain_values.pop();
        sigs[4].grind_counter ^= 1;
        for count in [0, 1, 7, 8, 9, 17, 32] {
            let inputs: Vec<_> = (0..count)
                .map(|j| {
                    let i = (j * 7) % 9;
                    FrontierVerifyInput {
                        pk: &keys[i].pk,
                        dp: if i == 6 { &wrong_dp } else { &dp },
                        message: if i == 5 { b"wrong" } else { b"batch vote" },
                        signature: if i == 7 { &good } else { &sigs[i] },
                    }
                })
                .collect();
            let expected: Vec<_> = inputs
                .iter()
                .map(|i| verify_frontier_fts(i.pk, i.dp, i.message, i.signature))
                .collect();
            assert_eq!(verify_frontier_fts_batch(&inputs), expected);
            assert_eq!(
                verify_batch_with_permutation(&inputs, |states| {
                    for state in states {
                        qsag_core::sponge::keccak::keccak_f1600(state);
                    }
                }),
                expected
            );
        }
    }

    #[test]
    fn batch_heterogeneous_production_profiles() {
        let profiles = [
            FrontierFtsProfile::Compact514,
            FrontierFtsProfile::Full256Bit,
            FrontierFtsProfile::Compact1122,
        ];
        let tables: Vec<_> = profiles
            .iter()
            .map(|&p| FrontierDpTable::build(p))
            .collect();
        let mut keys = Vec::new();
        let mut sigs = Vec::new();
        for (i, &profile) in profiles.iter().enumerate() {
            let mut key = FrontierFtsSigningKey::keygen(
                profile,
                [i as u8; 32],
                [41; 32],
                [42; 32],
                true,
                &CpuReferenceBackend::new(),
            );
            sigs.push(key.sign(&tables[i], b"profile test", &[43; 32]).unwrap());
            keys.push(key);
        }
        let mut wrong_profile = keys[0].pk.clone();
        wrong_profile.profile = FrontierFtsProfile::Compact1122;
        let inputs: Vec<_> = (0..17)
            .map(|j| {
                let i = j % 3;
                FrontierVerifyInput {
                    pk: if j == 4 { &wrong_profile } else { &keys[i].pk },
                    dp: &tables[i],
                    message: b"profile test",
                    signature: &sigs[i],
                }
            })
            .collect();
        let scalar: Vec<_> = inputs
            .iter()
            .map(|i| verify_frontier_fts(i.pk, i.dp, i.message, i.signature))
            .collect();
        assert!(scalar[0].is_ok());
        assert!(scalar[1].is_ok());
        assert!(scalar[2].is_ok());
        assert!(scalar[4].is_err());
        assert_eq!(verify_frontier_fts_batch(&inputs), scalar);
    }

    #[test]
    fn rotated_batch_matches_all_scalar_context_checks() {
        let profile = FrontierFtsProfile::Fast256Test;
        let dp = FrontierDpTable::build(profile);
        let mut key = FrontierFtsSigningKey::keygen(
            profile,
            [1; 32],
            [2; 32],
            [3; 32],
            true,
            &CpuReferenceBackend::new(),
        );
        let chain = [4; 32];
        let digest = [5; 32];
        let vote = key
            .sign_rotated_epoch_vote(
                &dp,
                &chain,
                EpochKeyLink {
                    epoch: 17,
                    next_epoch_pk_root: [6; 32],
                },
                digest,
                &[7; 32],
            )
            .unwrap();
        let mut bad = vote.clone();
        bad.signature.chain_values[0] ^= 1;
        let mut short_pk = key.pk.clone();
        short_pk.root.pop();
        let wrong = [9; 32];
        let inputs: Vec<_> = (0..17)
            .map(|i| RotatedEpochVerifyInput {
                current: if i == 7 { &short_pk } else { &key.pk },
                dp: &dp,
                vote: if i == 3 { &bad } else { &vote },
                chain_id: if i == 4 { &wrong } else { &chain },
                expected_epoch: if i == 5 {
                    18
                } else if i == 6 {
                    u64::MAX
                } else {
                    17
                },
                expected_vote_digest: if i == 2 { &wrong } else { &digest },
            })
            .collect();
        let scalar: Vec<_> = inputs
            .iter()
            .map(|i| {
                i.vote.verify(
                    i.current,
                    i.dp,
                    i.chain_id,
                    i.expected_epoch,
                    i.expected_vote_digest,
                )
            })
            .collect();
        assert!(scalar[0].is_ok());
        for result in scalar.iter().take(8).skip(2) {
            assert!(result.is_err());
        }
        assert_eq!(verify_rotated_epoch_votes_batch(&inputs), scalar);
    }

    #[cfg(feature = "std")]
    #[test]
    #[ignore = "focused release timing"]
    fn benchmark_compact1122_batch() {
        let profile = FrontierFtsProfile::Compact1122;
        let dp = FrontierDpTable::build(profile);
        let mut keys = Vec::new();
        let mut sigs = Vec::new();
        for i in 0..8 {
            let mut key = FrontierFtsSigningKey::keygen(
                profile,
                [i; 32],
                [i + 10; 32],
                [i + 20; 32],
                true,
                &CpuReferenceBackend::new(),
            );
            sigs.push(key.sign(&dp, b"batch vote", &[i + 30; 32]).unwrap());
            keys.push(key);
        }
        for count in [1, 8, 32, 128, 900, 1200] {
            let inputs: Vec<_> = (0..count)
                .map(|i| FrontierVerifyInput {
                    pk: &keys[i % 8].pk,
                    dp: &dp,
                    message: b"batch vote",
                    signature: &sigs[i % 8],
                })
                .collect();
            let start = std::time::Instant::now();
            for input in &inputs {
                assert!(
                    verify_frontier_fts(input.pk, input.dp, input.message, input.signature).is_ok()
                );
            }
            let scalar = start.elapsed();
            let start = std::time::Instant::now();
            assert!(verify_frontier_fts_batch(&inputs).iter().all(Result::is_ok));
            std::eprintln!(
                "votes={count} scalar_us={} batch_us={}",
                scalar.as_micros(),
                start.elapsed().as_micros()
            );
            if count == 1200 {
                for workers in [2, 8] {
                    let start = std::time::Instant::now();
                    std::thread::scope(|scope| {
                        for chunk in inputs.chunks(count.div_ceil(workers)) {
                            scope.spawn(move || {
                                for input in chunk {
                                    assert!(
                                        verify_frontier_fts(
                                            input.pk,
                                            input.dp,
                                            input.message,
                                            input.signature
                                        )
                                        .is_ok()
                                    );
                                }
                            });
                        }
                    });
                    let scalar = start.elapsed();
                    let start = std::time::Instant::now();
                    std::thread::scope(|scope| {
                        for chunk in inputs.chunks(count.div_ceil(workers)) {
                            scope.spawn(move || {
                                assert!(verify_frontier_fts_batch(chunk).iter().all(Result::is_ok))
                            });
                        }
                    });
                    std::eprintln!(
                        "votes={count} workers={workers} scalar_us={} batch_us={}",
                        scalar.as_micros(),
                        start.elapsed().as_micros()
                    );
                }
            }
        }
    }
}
