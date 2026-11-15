//! Distributed 3-custodian prover emulation with active 1-of-3 malicious
//! multiplication verification over authenticated confidential pairwise channels.
//!
//! Privacy and integrity threshold: at most one corrupted custodian (`1`-of-`3`
//! honest majority), assuming confidential authenticated pairwise channels and
//! independently sampled private custodian entropy. Every Boolean `AND` gate and
//! prime-field multiplication is batch-verified with coin-flipped challenges
//! (per flush: `< 2^-127.99` Boolean soundness over `GF(2^128)`, `< 2^-249`
//! over the curve fields `GF(p)` and `< 2^-186` over Goldilocks `GF(p^3)`)
//! before any wire opening, masked A2B/B2A conversion difference, view
//! commitment, public output, or challenged ZKBoo party view is reconstructed.
//! Two colluding custodians can reconstruct replicated secrets, and abort
//! remains non-identifiable / unfair (`1` corrupt custodian can force an
//! abort). See `SECURITY.md` for exact scope.
pub use crate::outer_mpc::{Envelope, Error, Transport};
use crate::secret::SecretVec;
use crate::{
    circuit::{Circuit, Domain, Op},
    outer_mpc::{self, Bit, Engine, FieldWord, Sponge, Word},
    zk_engine::{
        self, MIT_REPETITIONS, MigrationStatement, MigrationZkProof, OpenedRepetitionView,
        PartyView,
    },
};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::{ct_zeroize_bytes, ct_zeroize_u64s},
    keccak::cshake256_framed_32,
};

/// One-shot local custody material. Supply the XOR share of the *normalized
/// spending scalar*, encoded little endian, not a derivation seed. Each channel
/// key is shared only with its peer, ordered `[previous, next]`. Session identifiers
/// must be unique; entropy must be fresh and independent at every custodian.
/// No dealer, combined witness, or other custodian's entropy enters this API.
pub struct CoZkCustodianShare {
    party: usize,
    session: [u8; 32],
    witness: [u8; 32],
    entropy: [u8; 32],
    channel_keys: [[u8; 32]; 2],
}
impl Drop for CoZkCustodianShare {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.witness);
        ct_zeroize_bytes(&mut self.entropy);
        for k in &mut self.channel_keys {
            ct_zeroize_bytes(k);
        }
    }
}
impl CoZkCustodianShare {
    pub fn new(
        party: usize,
        session: [u8; 32],
        witness: [u8; 32],
        entropy: [u8; 32],
        channel_keys: [[u8; 32]; 2],
    ) -> Result<Self, Error> {
        if party >= 3 {
            return Err(Error::InvalidConfiguration);
        }
        Ok(Self {
            party,
            session,
            witness,
            entropy,
            channel_keys,
        })
    }

    /// Consumes the ceremony. A transport or verification error consumes all state as well.
    /// The returned proof has passed the unchanged single-prover verifier.
    ///
    /// Ceremony state cannot be reused, including after a failed call:
    /// ```compile_fail
    /// use qsag_migrate::{CoZkCustodianShare, MigrationStatement};
    /// use qsag_migrate::co_zk_mpc::Transport;
    /// fn reuse<T: Transport>(state: CoZkCustodianShare, statement: &MigrationStatement, a: T, b: T) {
    ///     let _ = state.prove(statement, a);
    ///     let _ = state.prove(statement, b);
    /// }
    /// ```
    pub fn prove<T: Transport>(
        self,
        statement: &MigrationStatement,
        transport: T,
    ) -> Result<MigrationZkProof, Error> {
        self.prove_with_backend(statement, transport, &qsag_accel::CpuReferenceBackend)
    }

    /// Use the backend to hash the challenged views during final verification.
    /// Unopened commitments remain interactive shared sponges: applying an
    /// ordinary Keccak kernel to individual shares would not compute their hash.
    pub fn prove_with_backend<T: Transport, B: qsag_accel::AcceleratorBackend>(
        self,
        statement: &MigrationStatement,
        transport: T,
        accel: &B,
    ) -> Result<MigrationZkProof, Error> {
        #[cfg(test)]
        transport.audit_private_state(
            self.party,
            &self.session,
            &self.witness,
            &self.entropy,
            &self.channel_keys,
            statement,
        );
        let children = {
            #[cfg(any(feature = "std", test))]
            {
                let mut transport = transport;
                let mut children = Vec::new();
                for batch in 0..MIT_REPETITIONS.div_ceil(64) {
                    if let Some(child) = transport.fork(batch) {
                        children.push(child);
                    }
                }
                if !children.is_empty() && children.len() != MIT_REPETITIONS.div_ceil(64) {
                    return Err(Error::InvalidConfiguration);
                }
                (transport, children)
            }
            #[cfg(not(any(feature = "std", test)))]
            {
                (transport, Vec::new())
            }
        };
        let (transport, children) = children;
        let mut e = Engine::new(self.party, self.session, self.channel_keys, transport)?;
        e.mix_entropy(&self.entropy);

        let statement_bytes = statement.to_transcript_bytes();
        e.agree(cshake256_framed_32(
            b"QSAG.OUTER.STATEMENT.V1",
            &[&statement_bytes, &(children.len() as u64).to_le_bytes()],
        ))?;

        let mut own: Vec<_> = self
            .witness
            .iter()
            .flat_map(|b| (0..8).map(move |i| if (b >> i) & 1 != 0 { u64::MAX } else { 0 }))
            .collect();
        let shared = e.share_uniform_lanes(&own);
        ct_zeroize_u64s(&mut own);
        // Both replicated witness components this custodian holds are wiped on
        // every exit path, as are its shares of all virtual-head tape seeds.
        let witness = shared?;
        let witness: &[Bit] = &witness;
        let circuit = crate::ownership::build(statement, &[0; 32]);

        let num_batches = MIT_REPETITIONS.div_ceil(64);
        let mut seeds = Vec::with_capacity(num_batches);
        for batch in 0..num_batches {
            let mut heads = Vec::with_capacity(3);
            for head in 0..3 {
                let mut lane_seeds: Vec<_> = (0..64)
                    .map(|lane| {
                        cshake256_framed_32(
                            b"QSAG.OUTER.SEED.V1",
                            &[
                                &self.entropy,
                                &self.session,
                                &statement_bytes,
                                &((batch * 64 + lane) as u64).to_le_bytes(),
                                &[head],
                            ],
                        )
                    })
                    .collect();
                let mut own_seed: Vec<_> = (0..256)
                    .map(|i| {
                        lane_seeds.iter().enumerate().fold(0, |v, (lane, s)| {
                            v | (((s[i / 8] >> (i % 8)) & 1) as u64) << lane
                        })
                    })
                    .collect();
                for seed in &mut lane_seeds {
                    ct_zeroize_bytes(seed);
                }
                let shared = e.share(&own_seed);
                ct_zeroize_u64s(&mut own_seed);
                heads.push(shared?);
            }
            seeds.push(heads);
        }

        // Phase 1: Evaluate all batches, compute shared view commitments, and run
        // mandatory active multiplication checks on EVERY batch BEFORE opening any
        // commitment, public circuit output, or ZKBoo view.
        let mut computed_batches = compute_batches(
            &mut e,
            &circuit,
            witness,
            &seeds,
            children,
            BatchContext {
                session: self.session,
                entropy: self.entropy,
                keys: self.channel_keys,
            },
        )?;

        // Cross-batch barrier: all custodians confirm every batch passed active
        // multiplication verification before ANY view commitment or output opens.
        e.agree(cshake256_framed_32(
            b"QSAG.OUTER.PRECOMMIT.V1",
            &[&statement_bytes],
        ))?;

        // Phase 2: Open view commitments and public outputs for each batch.
        let mut public = Vec::with_capacity(MIT_REPETITIONS);
        for (batch, item) in computed_batches.iter_mut().enumerate() {
            let opening_engine = item.engine.as_mut().unwrap_or(&mut e);
            let rounds =
                open_batch_public_rounds(opening_engine, batch, &item.commit_bits, &item.views)?;
            public.extend(rounds);
        }

        let roots: Vec<_> = public
            .iter()
            .enumerate()
            .flat_map(|(rep, r)| {
                zk_engine::rep_root(rep, &r.commits, r.outputs.each_ref().map(Vec::as_slice))
            })
            .collect();
        let root = cshake256_framed_32(b"QSAG.MIGRATE.ROOT.V3", &[&roots]);

        // Ceremony-wide Fiat-Shamir freeze precedes every challenged ZKBoo view opening.
        e.agree(cshake256_framed_32(
            b"QSAG.OUTER.FREEZE.V1",
            &[&statement_bytes, &root],
        ))?;

        let mut t = zk_engine::transcript(statement, &root);
        let challenges = zk_engine::challenges(&mut t);
        let mut repetitions = Vec::with_capacity(MIT_REPETITIONS);

        #[cfg(test)]
        let audit_inputs: Vec<[Word; 3]> = computed_batches
            .iter()
            .map(|batch| core::array::from_fn(|head| batch.views[head].inputs.clone()))
            .collect();

        for (batch, mut result) in computed_batches.into_iter().enumerate() {
            let opening_engine = result.engine.as_mut().unwrap_or(&mut e);
            let views = &result.views;
            let count = core::cmp::min(64, MIT_REPETITIONS - batch * 64);
            let mut opened: Vec<Vec<PartyView>> = Vec::with_capacity(3);
            for (head, view) in views.iter().enumerate() {
                let mask = (0..count).fold(0, |mask, lane| {
                    if (challenges[batch * 64 + lane] as usize + 2) % 3 != head {
                        mask | (1u64 << lane)
                    } else {
                        mask
                    }
                });
                let total_bits =
                    view.seed.len() + view.inputs.len() + view.products.len() + view.outputs.len();
                let mut masked = Word::with_capacity(total_bits);
                for part in [&view.seed, &view.inputs, &view.products, &view.outputs] {
                    masked.extend(part.iter().map(|b| Bit([b.0[0] & mask, b.0[1] & mask])));
                }
                #[cfg(test)]
                opening_engine.transport.on_public_or_view_open();
                let clear = opening_engine.open(&masked)?;
                let head_views = (0..count)
                    .map(|lane| {
                        let bytes = outer_mpc::lane_bytes(&clear, lane);
                        let inputs_end = 32 + view.inputs.len() / 8;
                        let products_end = inputs_end + view.products.len() / 8;
                        PartyView {
                            seed: bytes[..32].try_into().unwrap(),
                            inputs: bytes[32..inputs_end].to_vec(),
                            products: bytes[inputs_end..products_end].to_vec(),
                            outputs: bytes[products_end..].to_vec(),
                        }
                    })
                    .collect();
                opened.push(head_views);
            }
            for (lane, &ch_byte) in challenges[batch * 64..batch * 64 + count]
                .iter()
                .enumerate()
            {
                let rep = batch * 64 + lane;
                let challenge = ch_byte as usize;
                let hidden = (challenge + 2) % 3;
                repetitions.push(OpenedRepetitionView {
                    opened_e: ch_byte,
                    pair: [
                        opened[challenge][lane].clone(),
                        opened[(challenge + 1) % 3][lane].clone(),
                    ],
                    hidden_party_commit: public[rep].commits[hidden],
                    hidden_outputs: public[rep].outputs[hidden].clone(),
                });
            }
        }

        let proof = MigrationZkProof {
            views_merkle_root: root,
            repetitions,
        };
        zk_engine::verify_migration_proof_with_backend(
            statement,
            &proof,
            &statement.migration_domain,
            statement.epoch_anchor,
            accel,
        )
        .map_err(|_| Error::InvalidProof)?;
        e.agree(cshake256_framed_32(b"QSAG.OUTER.COMPLETE.V1", &[&root]))?;
        #[cfg(test)]
        tests::audit_old_attack(&self, &e, witness, &audit_inputs, &proof);
        Ok(proof)
    }
}

struct BatchComputed<T: Transport> {
    views: Vec<SharedView>,
    commit_bits: [Word; 3],
    engine: Option<Engine<T>>,
}

fn compute_batch<T: Transport>(
    e: &mut Engine<T>,
    c: &Circuit,
    witness: &[Bit],
    seeds: &[Word],
    batch: usize,
) -> Result<BatchComputed<T>, Error> {
    let views = evaluate_inner(e, c, witness, seeds, true)?;
    let commit_bits = compute_view_commit_bits(e, batch, &views)?;
    // Verify all pending Boolean and prime-field multiplications in this batch
    // BEFORE returning or opening any view commitment or output wire.
    e.verify_all_pending()?;
    Ok(BatchComputed {
        views,
        commit_bits,
        engine: None,
    })
}

fn open_batch_public_rounds<T: Transport>(
    e: &mut Engine<T>,
    batch: usize,
    commit_bits: &[Word; 3],
    views: &[SharedView],
) -> Result<Vec<PublicRound>, Error> {
    #[cfg(test)]
    e.transport.on_public_or_view_open();
    let out_len = views[0].outputs.len();
    let mut flat = Word::with_capacity(3 * 256 + 3 * out_len);
    for cb in commit_bits {
        flat.extend_from_slice(cb);
    }
    for v in views {
        flat.extend_from_slice(&v.outputs);
    }
    let opened = e.open(&flat)?;
    let count = core::cmp::min(64, MIT_REPETITIONS - batch * 64);
    let commits_clear: [&[u64]; 3] = [&opened[0..256], &opened[256..512], &opened[512..768]];
    let outputs_clear: [&[u64]; 3] = [
        &opened[768..768 + out_len],
        &opened[768 + out_len..768 + 2 * out_len],
        &opened[768 + 2 * out_len..768 + 3 * out_len],
    ];
    Ok((0..count)
        .map(|lane| PublicRound {
            commits: core::array::from_fn(|h| {
                outer_mpc::lane_bytes(commits_clear[h], lane)
                    .try_into()
                    .unwrap()
            }),
            outputs: core::array::from_fn(|h| outer_mpc::lane_bytes(outputs_clear[h], lane)),
        })
        .collect())
}

struct BatchContext {
    session: [u8; 32],
    entropy: [u8; 32],
    keys: [[u8; 32]; 2],
}
impl Drop for BatchContext {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.entropy);
        for k in &mut self.keys {
            ct_zeroize_bytes(k);
        }
    }
}

fn compute_batches<T: Transport>(
    e: &mut Engine<T>,
    c: &Circuit,
    witness: &[Bit],
    seeds: &[Vec<Word>],
    children: Vec<T>,
    ctx: BatchContext,
) -> Result<Vec<BatchComputed<T>>, Error> {
    #[cfg(any(feature = "std", test))]
    if !children.is_empty() {
        let party = e.party;
        let session = ctx.session;
        let entropy = ctx.entropy;
        let keys = ctx.keys;
        let cancelled = alloc::sync::Arc::new(core::sync::atomic::AtomicBool::new(false));
        let width = e
            .transport
            .max_parallel_batches()
            .max(1)
            .min(children.len())
            .min(
                std::thread::available_parallelism()
                    .map_or(1, |n| n.get())
                    .min(16),
            );
        let mut jobs = children.into_iter().enumerate();
        let mut completed = Vec::with_capacity(seeds.len());
        while jobs.len() != 0 {
            let wave: Result<Vec<_>, Error> = std::thread::scope(|scope| {
                let handles: Vec<_> = jobs
                    .by_ref()
                    .take(width)
                    .map(|(batch, transport)| {
                        let cancelled = cancelled.clone();
                        scope.spawn(move || {
                            let result = (|| {
                                let batch_session = cshake256_framed_32(
                                    b"QSAG.OUTER.BATCH.V1",
                                    &[&session, &(batch as u64).to_le_bytes()],
                                );
                                let mut batch_entropy = cshake256_framed_32(
                                    b"QSAG.OUTER.BATCH.ENTROPY.V1",
                                    &[&entropy, &session, &(batch as u64).to_le_bytes()],
                                );
                                let mut engine =
                                    Engine::new(party, batch_session, keys, transport)?;
                                engine.batch_cancelled = Some(cancelled.clone());
                                engine.mix_entropy(&batch_entropy);
                                ct_zeroize_bytes(&mut batch_entropy);
                                let mut result =
                                    compute_batch(&mut engine, c, witness, &seeds[batch], batch)?;
                                engine.release_verified_scratch();
                                engine.batch_cancelled = None;
                                result.engine = Some(engine);
                                Ok(result)
                            })();
                            if result.is_err() {
                                // Cancellation can only abort. Every successful batch still
                                // passes its multiplication checks and the global barrier.
                                cancelled.store(true, core::sync::atomic::Ordering::Relaxed);
                            }
                            result
                        })
                    })
                    .collect();
                let results: Vec<Result<_, Error>> = handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or(Err(Error::Transport)))
                    .collect();
                // A sibling cancelled at an exchange reports Transport. Preserve the
                // actual rejection (especially InvalidTape, which callers may retry).
                if let Some(error) = results
                    .iter()
                    .filter_map(|r| r.as_ref().err())
                    .find(|&&error| error != Error::Transport)
                {
                    return Err(*error);
                }
                results.into_iter().collect()
            });
            completed.extend(wave?);
        }
        return Ok(completed);
    }
    #[cfg(not(any(feature = "std", test)))]
    let _ = (children, ctx.session, ctx.entropy, ctx.keys);
    seeds
        .iter()
        .enumerate()
        .map(|(batch, seed)| compute_batch(e, c, witness, seed, batch))
        .collect()
}

#[derive(Clone)]
struct PublicRound {
    commits: [[u8; 32]; 3],
    outputs: [Vec<u8>; 3],
}

struct SharedView {
    seed: Word,
    inputs: Word,
    products: Word,
    outputs: Word,
}
impl SharedView {
    #[cfg(test)]
    fn bytes(&self) -> Word {
        let mut out = Word::with_capacity(
            self.seed.len() + self.inputs.len() + self.products.len() + self.outputs.len(),
        );
        out.extend_from_slice(&self.seed);
        out.extend_from_slice(&self.inputs);
        out.extend_from_slice(&self.products);
        out.extend_from_slice(&self.outputs);
        out
    }
}

enum SharedValue {
    Bit(Bit),
    Field(FieldWord),
}
impl SharedValue {
    fn zero(d: Domain) -> Self {
        if d == Domain::Bit {
            Self::Bit(Bit::default())
        } else {
            Self::Field(vec![[[0; 4]; 2]; 64].into())
        }
    }
    fn bit(&self) -> Bit {
        match self {
            Self::Bit(b) => *b,
            _ => unreachable!("public circuit domain"),
        }
    }
    fn field(&self) -> &FieldWord {
        match self {
            Self::Field(f) => f,
            _ => unreachable!("public circuit domain"),
        }
    }
}
impl Drop for SharedValue {
    fn drop(&mut self) {
        match self {
            Self::Bit(b) => ct_zeroize_u64s(&mut b.0),
            Self::Field(_) => {} // FieldWord owns its wipe-on-drop storage.
        }
    }
}

#[derive(Default)]
struct TapeCursor {
    sponge_bits: usize,
    bit_chunk_start: usize,
    bit_rem: usize,
}
impl TapeCursor {
    fn next_bit(&mut self) -> usize {
        if self.bit_rem == 0 {
            self.bit_chunk_start = self.sponge_bits;
            self.sponge_bits += 64;
            self.bit_rem = 64;
        }
        let pos = self.bit_chunk_start + (64 - self.bit_rem);
        self.bit_rem -= 1;
        pos
    }
    fn next_field(&mut self, d: Domain) -> usize {
        let start = self.sponge_bits;
        self.sponge_bits += d.width().div_ceil(8) * 8;
        start
    }
}

#[derive(Clone, Copy)]
enum NodeTape {
    None,
    InputBit { witness_idx: usize, pos: [usize; 2] },
    InputField { target: usize, draws: [usize; 2] },
    MulBit { pos: [usize; 3] },
    MulField { draws: [usize; 3] },
}

struct FieldTapeDraw {
    head: usize,
    start: usize,
    domain: Domain,
}

// Replay a finite tape with a public per-draw attempt budget. Rejection masks
// remain shared: each lane conditionally removes a rejected word from the entire
// unread suffix, including future Boolean refill words. Previously cached bits
// precede `start` and are never moved. A failed budget is retried from the original
// stream, so an unresolved draw cannot discard a later draw's valid candidate.
fn canonical_tape_attempt<T: Transport>(
    e: &mut Engine<T>,
    streams: &[Word],
    draws: &[FieldTapeDraw],
    counts: [usize; 3],
    attempts: usize,
) -> Result<Option<Vec<Word>>, Error> {
    let required = tape_counts(draws, counts, attempts)?;
    if streams.len() != 3 || streams.iter().zip(required).any(|(s, n)| s.len() < n) {
        return Err(Error::InvalidTape);
    }
    let mut out: Vec<Word> = streams
        .iter()
        .zip(required)
        .map(|(s, n)| s[..n].iter().copied().collect())
        .collect();
    let mut valid: [Word; 3] = core::array::from_fn(|_| Word::new());
    for draw in draws {
        let stream = &mut out[draw.head];
        let width = draw.domain.width();
        let consumed = width.div_ceil(8) * 8;
        for attempt in 0..attempts {
            let word = stream[draw.start..draw.start + width]
                .iter()
                .copied()
                .collect();
            let accepted = e.less_than_modulus_many(&[word], draw.domain)?[0];
            if attempt + 1 == attempts {
                valid[draw.head].push(accepted);
            } else {
                let end = stream.len() - consumed;
                let reject = accepted ^ e.constant(u64::MAX);
                let pairs: SecretVec<_> = (draw.start..end)
                    .map(|i| (reject, stream[i] ^ stream[i + consumed]))
                    .collect();
                let changes = e.and(&pairs)?;
                for (slot, change) in stream[draw.start..end].iter_mut().zip(changes.iter()) {
                    *slot = *slot ^ *change;
                }
                stream.truncate(end);
            }
        }
    }
    let valid = fold_valid_bits(e, valid)?;
    Ok(if e.open(&valid)?.iter().all(|&v| v == u64::MAX) {
        Some(out)
    } else {
        None
    })
}

fn tape_counts(
    draws: &[FieldTapeDraw],
    counts: [usize; 3],
    attempts: usize,
) -> Result<[usize; 3], Error> {
    let extra = attempts.checked_sub(1).ok_or(Error::InvalidTape)?;
    let mut required = counts;
    let mut ends = [0; 3];
    for draw in draws {
        let width = draw.domain.width().div_ceil(8) * 8;
        if draw.head >= 3 || draw.domain == Domain::Bit {
            return Err(Error::InvalidTape);
        }
        let end = draw.start.checked_add(width).ok_or(Error::InvalidTape)?;
        if draw.start < ends[draw.head] || end > counts[draw.head] {
            return Err(Error::InvalidTape);
        }
        ends[draw.head] = end;
        required[draw.head] = required[draw.head]
            .checked_add(width.checked_mul(extra).ok_or(Error::InvalidTape)?)
            .ok_or(Error::InvalidTape)?;
    }
    Ok(required)
}

fn fold_valid_bits<T: Transport>(
    e: &mut Engine<T>,
    mut groups: [Word; 3],
) -> Result<[Bit; 3], Error> {
    for g in &mut groups {
        if g.is_empty() {
            g.push(e.constant(u64::MAX));
        }
    }
    while groups.iter().any(|g| g.len() > 1) {
        let mut pairs = SecretVec::new();
        for g in &groups {
            for pair in g.chunks_exact(2) {
                pairs.push((pair[0], pair[1]));
            }
        }
        let prods = e.and(&pairs)?;
        let mut cur = 0usize;
        for g in &mut groups {
            let num_pairs = g.len() / 2;
            let mut next = Word::with_capacity(num_pairs + (g.len() % 2));
            next.extend_from_slice(&prods[cur..cur + num_pairs]);
            cur += num_pairs;
            if g.len() % 2 == 1 {
                next.push(*g.last().unwrap());
            }
            *g = next;
        }
    }
    Ok([groups[0][0], groups[1][0], groups[2][0]])
}

fn fold_all_true_bits<T: Transport>(e: &mut Engine<T>, mut bits: Word) -> Result<Bit, Error> {
    if bits.is_empty() {
        return Ok(e.constant(u64::MAX));
    }
    while bits.len() > 1 {
        let mut pairs = SecretVec::with_capacity(bits.len() / 2);
        for pair in bits.chunks_exact(2) {
            pairs.push((pair[0], pair[1]));
        }
        let mut next = e.and(&pairs)?;
        if bits.len() % 2 == 1 {
            next.push(*bits.last().unwrap());
        }
        bits = next;
    }
    Ok(bits[0])
}

#[cfg(test)]
fn evaluate<T: Transport>(
    e: &mut Engine<T>,
    c: &Circuit,
    witness: &[Bit],
    seeds: &[Word],
) -> Result<Vec<SharedView>, Error> {
    evaluate_inner(e, c, witness, seeds, false)
}

fn evaluate_inner<T: Transport>(
    e: &mut Engine<T>,
    c: &Circuit,
    witness: &[Bit],
    seeds: &[Word],
    verify_zero_outputs: bool,
) -> Result<Vec<SharedView>, Error> {
    // Keep field-fault regressions aimed at circuit evaluation, even when tape
    // conversion itself uses arithmetic multiplications for carry correction.
    #[cfg(test)]
    let circuit_field_fault = if matches!(e.fault, Some(outer_mpc::FaultInjection::FieldMul { .. }))
    {
        e.fault.take()
    } else {
        None
    };

    // 1. Pre-schedule exact `Tape` bit/field draws and topological DAG waves.
    let mut cursors: [TapeCursor; 3] = core::array::from_fn(|_| TapeCursor::default());
    let mut field_draws: Vec<FieldTapeDraw> = Vec::new();
    let mut node_tapes = Vec::with_capacity(c.nodes.len());
    let mut waves = vec![0usize; c.nodes.len()];
    let mut max_wave = 0usize;
    let mut witness_cursor = 0usize;

    for (index, node) in c.nodes.iter().enumerate() {
        let d = node.domain;
        let (nt, w) = match node.op {
            Op::Constant(_) => (NodeTape::None, 0),
            Op::Input => {
                if d == Domain::Bit {
                    if witness_cursor >= witness.len() {
                        return Err(Error::InvalidConfiguration);
                    }
                    let witness_idx = witness_cursor;
                    witness_cursor += 1;
                    let pos = [cursors[0].next_bit(), cursors[1].next_bit()];
                    (NodeTape::InputBit { witness_idx, pos }, 0)
                } else {
                    let target = match c.nodes.get(index + 1).map(|n| n.op) {
                        Some(Op::Mul(a, b)) if a == index => b,
                        Some(Op::Mul(a, b)) if b == index => a,
                        _ => return Err(Error::InvalidConfiguration),
                    };
                    if target >= index {
                        return Err(Error::InvalidConfiguration);
                    }
                    let d0 = field_draws.len();
                    field_draws.push(FieldTapeDraw {
                        head: 0,
                        start: cursors[0].next_field(d),
                        domain: d,
                    });
                    let d1 = field_draws.len();
                    field_draws.push(FieldTapeDraw {
                        head: 1,
                        start: cursors[1].next_field(d),
                        domain: d,
                    });
                    (
                        NodeTape::InputField {
                            target,
                            draws: [d0, d1],
                        },
                        waves[target] + 1,
                    )
                }
            }
            Op::Lift(a, _) | Op::Digit(a, _, _) => (NodeTape::None, waves[a] + 1),
            Op::Add(a, b) | Op::Sub(a, b) => (NodeTape::None, waves[a].max(waves[b])),
            Op::Scale(a, _) => (NodeTape::None, waves[a]),
            Op::Mul(a, b) => {
                let w = waves[a].max(waves[b]) + 1;
                if d == Domain::Bit {
                    let pos = [
                        cursors[0].next_bit(),
                        cursors[1].next_bit(),
                        cursors[2].next_bit(),
                    ];
                    (NodeTape::MulBit { pos }, w)
                } else {
                    let mut draws = [0usize; 3];
                    for h in 0..3 {
                        draws[h] = field_draws.len();
                        field_draws.push(FieldTapeDraw {
                            head: h,
                            start: cursors[h].next_field(d),
                            domain: d,
                        });
                    }
                    (NodeTape::MulField { draws }, w)
                }
            }
        };
        waves[index] = w;
        if w > max_wave {
            max_wave = w;
        }
        node_tapes.push(nt);
    }

    // 2. Initialize all 3 `Tape` sponges and squeeze their exact streams in lockstep.
    let mut tape_sponges = Vec::with_capacity(3);
    for seed in seeds {
        let mut sp = Sponge::new(e);
        sp.public(e, b"QSAG.MIGRATE.TAPE.V3")?;
        sp.absorb(e, seed)?;
        sp.pad_only(e, 0x1f);
        tape_sponges.push(sp);
    }
    {
        let (s0, rest) = tape_sponges.split_first_mut().unwrap();
        let (s1, rest2) = rest.split_first_mut().unwrap();
        let s2 = &mut rest2[0];
        e.permutations(&mut [&mut s0.state, &mut s1.state, &mut s2.state])?;
    }
    let mut squeezed = outer_mpc::squeeze_sponges_lockstep(
        e,
        &mut tape_sponges,
        &[
            cursors[0].sponge_bits,
            cursors[1].sponge_bits,
            cursors[2].sponge_bits,
        ],
    )?;

    // 3. Batch-check `< modulus` across all field draws per domain and open `valid` upfront.
    let mut valid_groups: [Word; 3] = core::array::from_fn(|_| Word::new());
    let mut raw_draw_words: Vec<Word> = field_draws
        .iter()
        .map(|fd| {
            squeezed[fd.head][fd.start..fd.start + fd.domain.width()]
                .iter()
                .copied()
                .collect()
        })
        .collect();

    for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
        let mut dom_words = Vec::new();
        let mut dom_heads = Vec::new();
        for (idx, fd) in field_draws.iter().enumerate() {
            if fd.domain == dom {
                dom_words.push(raw_draw_words[idx].clone());
                dom_heads.push(fd.head);
            }
        }
        if !dom_words.is_empty() {
            let lt_bits = e.less_than_modulus_many(&dom_words, dom)?;
            for (h, lt) in dom_heads.into_iter().zip(lt_bits) {
                valid_groups[h].push(lt);
            }
        }
    }
    let valid = fold_valid_bits(e, valid_groups)?;
    if e.open(&valid)?.iter().any(|&v| v != u64::MAX) {
        let counts = core::array::from_fn(|h| cursors[h].sponge_bits);
        let mut attempts = 2usize;
        loop {
            let required = tape_counts(&field_draws, counts, attempts)?;
            let additional: Vec<_> = required
                .iter()
                .zip(&squeezed)
                .map(|(&n, s)| n - s.len())
                .collect();
            let more = outer_mpc::squeeze_sponges_lockstep(e, &mut tape_sponges, &additional)?;
            for (stream, tail) in squeezed.iter_mut().zip(&more) {
                stream.extend_from_slice(tail);
            }
            if let Some(repaired) =
                canonical_tape_attempt(e, &squeezed, &field_draws, counts, attempts)?
            {
                squeezed = repaired;
                break;
            }
            attempts = attempts.checked_mul(2).ok_or(Error::InvalidTape)?;
        }
        for (word, draw) in raw_draw_words.iter_mut().zip(&field_draws) {
            word.copy_from_slice(
                &squeezed[draw.head][draw.start..draw.start + draw.domain.width()],
            );
        }
    }

    // Only `NodeTape::InputField` draws are read again in Step 7; move all `MulField`
    // draws directly into `bits_to_field_many` so their `Word` buffers free early.
    let mut keep_raw_draw = vec![false; field_draws.len()];
    for nt in &node_tapes {
        if let NodeTape::InputField { draws, .. } = *nt {
            keep_raw_draw[draws[0]] = true;
            keep_raw_draw[draws[1]] = true;
        }
    }

    // 4. Batch-convert all validated field tape draws (`bits_to_field_many` per domain).
    let mut draw_fields: Vec<Option<FieldWord>> = (0..field_draws.len()).map(|_| None).collect();
    for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
        let mut idxs = Vec::new();
        let mut dom_words = Vec::new();
        for (idx, fd) in field_draws.iter().enumerate() {
            if fd.domain == dom {
                idxs.push(idx);
                if keep_raw_draw[idx] {
                    dom_words.push(raw_draw_words[idx].clone());
                } else {
                    dom_words.push(core::mem::take(&mut raw_draw_words[idx]));
                }
            }
        }
        if !dom_words.is_empty() {
            let converted = e.bits_to_field_many(&dom_words, dom)?;
            for (idx, fw) in idxs.into_iter().zip(converted) {
                draw_fields[idx] = Some(fw);
            }
        }
    }

    #[cfg(test)]
    if circuit_field_fault.is_some() {
        e.fault = circuit_field_fault;
    }

    // 5. Execute the circuit wave by wave, batching all parallel communication gates.
    let mut wave_comm: Vec<Vec<usize>> = (0..=max_wave).map(|_| Vec::new()).collect();
    let mut wave_local: Vec<Vec<usize>> = (0..=max_wave).map(|_| Vec::new()).collect();
    let mut keep_wire = vec![false; c.nodes.len()];
    let mut last_use_wave = waves.clone();
    for &out in &c.outputs {
        keep_wire[out] = true;
    }
    for (index, node) in c.nodes.iter().enumerate() {
        let w = waves[index];
        match node.op {
            Op::Input => {
                keep_wire[index] = true;
                if let NodeTape::InputField { target, .. } = node_tapes[index] {
                    last_use_wave[target] = last_use_wave[target].max(w);
                }
            }
            Op::Mul(a, b) => {
                keep_wire[index] = true;
                last_use_wave[a] = last_use_wave[a].max(w);
                last_use_wave[b] = last_use_wave[b].max(w);
            }
            Op::Add(a, b) | Op::Sub(a, b) => {
                last_use_wave[a] = last_use_wave[a].max(w);
                last_use_wave[b] = last_use_wave[b].max(w);
            }
            Op::Scale(a, _) | Op::Lift(a, _) | Op::Digit(a, _, _) => {
                last_use_wave[a] = last_use_wave[a].max(w);
            }
            Op::Constant(_) => {}
        }
        let is_comm = match node.op {
            Op::Input => node.domain != Domain::Bit,
            Op::Lift(_, _) | Op::Digit(_, _, _) | Op::Mul(_, _) => true,
            Op::Constant(_) | Op::Add(_, _) | Op::Sub(_, _) | Op::Scale(_, _) => false,
        };
        if is_comm {
            wave_comm[w].push(index);
        } else {
            wave_local[w].push(index);
        }
    }
    let mut retire_at_wave: Vec<Vec<usize>> = (0..=max_wave).map(|_| Vec::new()).collect();
    for (index, &keep) in keep_wire.iter().enumerate() {
        if !keep {
            retire_at_wave[last_use_wave[index]].push(index);
        }
    }

    let mut wires: Vec<Option<[SharedValue; 3]>> = (0..c.nodes.len()).map(|_| None).collect();
    let mut encodings: Vec<[Option<Word>; 3]> =
        (0..c.nodes.len()).map(|_| [None, None, None]).collect();

    for w in 0..=max_wave {
        let comm_nodes = &wave_comm[w];
        if !comm_nodes.is_empty() {
            // 5a. Prime-field `Op::Input` (`finverse`).
            for &idx in comm_nodes {
                if let NodeTape::InputField { target, draws } = node_tapes[idx] {
                    let d = c.nodes[idx].domain;
                    let tw = wires[target].as_ref().unwrap();
                    let sum01 = e.fadd(tw[0].field(), tw[1].field(), d);
                    let sum = e.fadd(&sum01, tw[2].field(), d);
                    let inv = e.finverse(&sum, d)?;
                    let aa = draw_fields[draws[0]].take().unwrap();
                    let bb = draw_fields[draws[1]].take().unwrap();
                    let ab = e.fadd(&aa, &bb, d);
                    let cc = e.fsub(&inv, &ab, d);
                    wires[idx] = Some([
                        SharedValue::Field(aa),
                        SharedValue::Field(bb),
                        SharedValue::Field(cc),
                    ]);
                }
            }

            // 5b. `Op::Lift` batched per domain (`lift_bits_many`).
            for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let mut lift_idxs = Vec::new();
                let mut lift_owners = Vec::new();
                let mut lift_bits = Word::new();
                for &idx in comm_nodes {
                    if c.nodes[idx].domain == dom
                        && let Op::Lift(a, owner) = c.nodes[idx].op
                    {
                        lift_idxs.push(idx);
                        lift_owners.push(owner);
                        lift_bits.push(wires[a].as_ref().unwrap()[owner].bit());
                    }
                }
                if !lift_bits.is_empty() {
                    let lifted = e.lift_bits_many(&lift_bits, dom)?;
                    for ((idx, owner), fw) in lift_idxs.into_iter().zip(lift_owners).zip(lifted) {
                        let mut parts = core::array::from_fn(|_| SharedValue::zero(dom));
                        parts[owner] = SharedValue::Field(fw);
                        wires[idx] = Some(parts);
                    }
                }
            }

            // 5c. `Op::Digit` batched per source domain (`field_to_bits_many`).
            let mut digit_nodes = Vec::new();
            let mut unique_sources: Vec<(usize, usize)> = Vec::new();
            for &idx in comm_nodes {
                if let Op::Digit(a, owner, bit) = c.nodes[idx].op {
                    digit_nodes.push((idx, a, owner, bit));
                    if encodings[a][owner].is_none() && !unique_sources.contains(&(a, owner)) {
                        unique_sources.push((a, owner));
                    }
                }
            }
            for &(a, owner) in &unique_sources {
                if c.nodes[a].domain == Domain::Bit {
                    encodings[a][owner] =
                        Some(vec![wires[a].as_ref().unwrap()[owner].bit()].into());
                }
            }
            for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let mut src_pairs = Vec::new();
                let mut src_refs = Vec::new();
                for &(a, owner) in &unique_sources {
                    if c.nodes[a].domain == dom && encodings[a][owner].is_none() {
                        src_pairs.push((a, owner));
                        src_refs.push(wires[a].as_ref().unwrap()[owner].field());
                    }
                }
                if !src_refs.is_empty() {
                    let converted = e.field_to_bits_many(&src_refs, dom)?;
                    for ((a, owner), bits_w) in src_pairs.into_iter().zip(converted) {
                        encodings[a][owner] = Some(bits_w);
                    }
                }
            }
            for (idx, a, owner, bit) in digit_nodes {
                let mut parts = core::array::from_fn(|_| SharedValue::zero(Domain::Bit));
                parts[owner] = SharedValue::Bit(encodings[a][owner].as_ref().unwrap()[bit]);
                wires[idx] = Some(parts);
            }

            // 5d. Boolean `Op::Mul` batched into a single `e.and`.
            let mut bit_mul_idxs = Vec::new();
            let mut bit_mul_pairs = SecretVec::new();
            for &idx in comm_nodes {
                if c.nodes[idx].domain == Domain::Bit
                    && let Op::Mul(a, b) = c.nodes[idx].op
                {
                    let wa = wires[a].as_ref().unwrap();
                    let wb = wires[b].as_ref().unwrap();
                    bit_mul_idxs.push(idx);
                    for head in 0..3 {
                        let next = (head + 1) % 3;
                        bit_mul_pairs.push((wa[head].bit(), wb[head].bit() ^ wb[next].bit()));
                        bit_mul_pairs.push((wa[next].bit(), wb[head].bit()));
                    }
                }
            }
            if !bit_mul_pairs.is_empty() {
                let prods = e.and(&bit_mul_pairs)?;
                for (idx, chunk) in bit_mul_idxs.into_iter().zip(prods.chunks_exact(6)) {
                    let NodeTape::MulBit { pos } = node_tapes[idx] else {
                        unreachable!()
                    };
                    let m = [
                        squeezed[0][pos[0]],
                        squeezed[1][pos[1]],
                        squeezed[2][pos[2]],
                    ];
                    let parts = core::array::from_fn(|head| {
                        SharedValue::Bit(
                            chunk[2 * head] ^ chunk[2 * head + 1] ^ m[head] ^ m[(head + 1) % 3],
                        )
                    });
                    wires[idx] = Some(parts);
                }
            }

            // 5e. Prime-field `Op::Mul` batched per domain into a single `e.fmul_many`.
            for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let mut fmul_idxs = Vec::new();
                let mut bb_sums: Vec<[FieldWord; 3]> = Vec::new();
                for &idx in comm_nodes {
                    if c.nodes[idx].domain == dom
                        && let Op::Mul(_, b) = c.nodes[idx].op
                    {
                        let wb = wires[b].as_ref().unwrap();
                        fmul_idxs.push(idx);
                        bb_sums.push(core::array::from_fn(|head| {
                            e.fadd(wb[head].field(), wb[(head + 1) % 3].field(), dom)
                        }));
                    }
                }
                if !fmul_idxs.is_empty() {
                    let mut pairs = Vec::with_capacity(fmul_idxs.len() * 6);
                    for (k, &idx) in fmul_idxs.iter().enumerate() {
                        let Op::Mul(a, b) = c.nodes[idx].op else {
                            unreachable!()
                        };
                        let wa = wires[a].as_ref().unwrap();
                        let wb = wires[b].as_ref().unwrap();
                        for head in 0..3 {
                            let next = (head + 1) % 3;
                            pairs.push((wa[head].field(), &bb_sums[k][head]));
                            pairs.push((wa[next].field(), wb[head].field()));
                        }
                    }
                    let prods = e.fmul_many(&pairs, dom)?;
                    for (idx, chunk) in fmul_idxs.into_iter().zip(prods.chunks_exact(6)) {
                        let NodeTape::MulField { draws } = node_tapes[idx] else {
                            unreachable!()
                        };
                        let masks: [FieldWord; 3] = [
                            draw_fields[draws[0]].take().unwrap(),
                            draw_fields[draws[1]].take().unwrap(),
                            draw_fields[draws[2]].take().unwrap(),
                        ];
                        let parts = core::array::from_fn(|head| {
                            let next = (head + 1) % 3;
                            let sum = e.fadd(&chunk[2 * head], &chunk[2 * head + 1], dom);
                            let r = e.fsub(&masks[head], &masks[next], dom);
                            SharedValue::Field(e.fadd(&sum, &r, dom))
                        });
                        wires[idx] = Some(parts);
                    }
                }
            }
        }

        // 5f. Local gates in increasing `index` order.
        for &idx in &wave_local[w] {
            let node = &c.nodes[idx];
            let d = node.domain;
            let val = match node.op {
                Op::Constant(value) => [
                    if d == Domain::Bit {
                        SharedValue::Bit(e.constant(if value[0] == 0 { 0 } else { u64::MAX }))
                    } else {
                        SharedValue::Field(e.fconstant(value))
                    },
                    SharedValue::zero(d),
                    SharedValue::zero(d),
                ],
                Op::Input => {
                    let NodeTape::InputBit { witness_idx, pos } = node_tapes[idx] else {
                        unreachable!()
                    };
                    let a = squeezed[0][pos[0]];
                    let b = squeezed[1][pos[1]];
                    let secret = witness[witness_idx];
                    [
                        SharedValue::Bit(a),
                        SharedValue::Bit(b),
                        SharedValue::Bit(secret ^ a ^ b),
                    ]
                }
                Op::Add(a, b) | Op::Sub(a, b) => {
                    let wa = wires[a].as_ref().unwrap();
                    let wb = wires[b].as_ref().unwrap();
                    core::array::from_fn(|head| {
                        if d == Domain::Bit {
                            SharedValue::Bit(wa[head].bit() ^ wb[head].bit())
                        } else if matches!(node.op, Op::Add(..)) {
                            SharedValue::Field(e.fadd(wa[head].field(), wb[head].field(), d))
                        } else {
                            SharedValue::Field(e.fsub(wa[head].field(), wb[head].field(), d))
                        }
                    })
                }
                Op::Scale(a, value) => {
                    let wa = wires[a].as_ref().unwrap();
                    core::array::from_fn(|head| {
                        if d == Domain::Bit {
                            SharedValue::Bit(if value[0] == 0 {
                                Bit::default()
                            } else {
                                wa[head].bit()
                            })
                        } else {
                            SharedValue::Field(e.fscale(wa[head].field(), value, d))
                        }
                    })
                }
                Op::Lift(_, _) | Op::Digit(_, _, _) | Op::Mul(_, _) => unreachable!(),
            };
            wires[idx] = Some(val);
        }
        for &dead in &retire_at_wave[w] {
            wires[dead] = None;
        }
    }
    drop(squeezed);
    drop(draw_fields);

    // 5g. Mandatory in-MPC output-residual zero check (`P0-1`): verify that every
    // Boolean and prime-field output residual reconstructs to `0` across all 3 ZKBoo
    // heads BEFORE converting views or opening any output shares / view commitments.
    if verify_zero_outputs {
        let mut residual_bits: Word = Word::new();
        for &out in &c.outputs {
            if c.nodes[out].domain == Domain::Bit {
                let w = wires[out].as_ref().unwrap();
                residual_bits.push(w[0].bit() ^ w[1].bit() ^ w[2].bit());
            }
        }
        for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
            let mut sums: Vec<FieldWord> = Vec::new();
            for &out in &c.outputs {
                if c.nodes[out].domain == dom {
                    let w = wires[out].as_ref().unwrap();
                    let s01 = e.fadd(w[0].field(), w[1].field(), dom);
                    sums.push(e.fadd(&s01, w[2].field(), dom));
                }
            }
            if !sums.is_empty() {
                let refs: Vec<&FieldWord> = sums.iter().collect();
                let converted = e.field_to_bits_many(&refs, dom)?;
                for fw in &mut sums {
                    for pair in fw {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
                for word in converted {
                    residual_bits.extend(word);
                }
            }
        }
        let ones = e.constant(u64::MAX);
        let zero_flags: Word = residual_bits.into_iter().map(|b| b ^ ones).collect();
        let all_outputs_zero = fold_all_true_bits(e, zero_flags)?;
        // Explicitly verify all circuit, conversion, and tree-AND multiplications
        // BEFORE opening the single 1-bit `all_outputs_zero` predicate.
        e.verify_all_pending()?;
        let opened_ok = e.open(&[all_outputs_zero])?;
        if opened_ok[0] != u64::MAX {
            return Err(Error::InvalidProof);
        }
    }

    // 6. Batch-convert all remaining `FieldWord`s needed for `views[0..3]` per domain.
    for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
        let mut to_convert_pairs: Vec<(usize, usize)> = Vec::new();
        for (idx, node) in c.nodes.iter().enumerate() {
            if node.domain != dom {
                continue;
            }
            match node.op {
                Op::Input => {
                    if encodings[idx][2].is_none() {
                        to_convert_pairs.push((idx, 2));
                    }
                }
                Op::Mul(_, _) => {
                    for (head, slot) in encodings[idx].iter().enumerate() {
                        if slot.is_none() {
                            to_convert_pairs.push((idx, head));
                        }
                    }
                }
                _ => {}
            }
        }
        for &out in &c.outputs {
            if c.nodes[out].domain == dom {
                for (head, slot) in encodings[out].iter().enumerate() {
                    if slot.is_none() && !to_convert_pairs.contains(&(out, head)) {
                        to_convert_pairs.push((out, head));
                    }
                }
            }
        }
        if !to_convert_pairs.is_empty() {
            let refs: Vec<&FieldWord> = to_convert_pairs
                .iter()
                .map(|&(idx, head)| wires[idx].as_ref().unwrap()[head].field())
                .collect();
            let converted = e.field_to_bits_many(&refs, dom)?;
            for ((idx, head), bits_w) in to_convert_pairs.into_iter().zip(converted) {
                encodings[idx][head] = Some(bits_w);
            }
        }
    }
    for (idx, node) in c.nodes.iter().enumerate() {
        if node.domain != Domain::Bit {
            wires[idx] = None;
        }
    }

    // 7. Assemble `SharedView`s in exact `c.nodes` / `c.outputs` topological order.
    let mut views: Vec<SharedView> = seeds
        .iter()
        .map(|seed| SharedView {
            seed: seed.clone(),
            inputs: Word::new(),
            products: Word::new(),
            outputs: Word::new(),
        })
        .collect();

    for (idx, node) in c.nodes.iter().enumerate() {
        let d = node.domain;
        match node.op {
            Op::Input => {
                if d == Domain::Bit {
                    let w = wires[idx].as_ref().unwrap();
                    for head in 0..3 {
                        outer_mpc::encode(&mut views[head].inputs, &[w[head].bit()]);
                    }
                } else {
                    let NodeTape::InputField { draws, .. } = node_tapes[idx] else {
                        unreachable!()
                    };
                    outer_mpc::encode(&mut views[0].inputs, &raw_draw_words[draws[0]]);
                    outer_mpc::encode(&mut views[1].inputs, &raw_draw_words[draws[1]]);
                    outer_mpc::encode(&mut views[2].inputs, encodings[idx][2].as_ref().unwrap());
                }
            }
            Op::Mul(_, _) => {
                if d == Domain::Bit {
                    let w = wires[idx].as_ref().unwrap();
                    for head in 0..3 {
                        outer_mpc::encode(&mut views[head].products, &[w[head].bit()]);
                    }
                } else {
                    for head in 0..3 {
                        outer_mpc::encode(
                            &mut views[head].products,
                            encodings[idx][head].as_ref().unwrap(),
                        );
                    }
                }
            }
            _ => {}
        }
    }

    for &out in &c.outputs {
        let d = c.nodes[out].domain;
        if d == Domain::Bit {
            let w = wires[out].as_ref().unwrap();
            for head in 0..3 {
                outer_mpc::encode(&mut views[head].outputs, &[w[head].bit()]);
            }
        } else {
            for head in 0..3 {
                outer_mpc::encode(
                    &mut views[head].outputs,
                    encodings[out][head].as_ref().unwrap(),
                );
            }
        }
    }

    Ok(views)
}

/// Compute the 256-bit `cSHAKE256("QSAG.MIGRATE.VIEW.V3")` view commitment shares
/// for all 3 virtual heads in lockstep (`3x` fewer network rounds than sequential
/// sponges, `0` rounds for the public customization block, `0` intermediate stream
/// allocations, and `0` wire openings).
fn compute_view_commit_bits<T: Transport>(
    e: &mut Engine<T>,
    batch: usize,
    views: &[SharedView],
) -> Result<[Word; 3], Error> {
    let rep: Word = (0..64)
        .map(|bit| {
            e.constant((0..64).fold(0, |v, lane| {
                v | ((((batch * 64 + lane) as u64 >> bit) & 1) << lane)
            }))
        })
        .collect();
    let count6 = outer_mpc::public_bytes(e, &6u64.to_le_bytes());
    let head_bits: [Word; 3] =
        core::array::from_fn(|head| outer_mpc::public_bytes(e, &[head as u8]));
    let len_words =
        |bit_len: usize| outer_mpc::public_bytes(e, &((bit_len / 8) as u64).to_le_bytes());
    let len_rep = len_words(rep.len());
    let len_head = len_words(head_bits[0].len());
    let len_seed = len_words(views[0].seed.len());
    let len_in = len_words(views[0].inputs.len());
    let len_prod = len_words(views[0].products.len());
    let len_out = len_words(views[0].outputs.len());

    let mut sponges: [Sponge; 3] =
        core::array::from_fn(|_| Sponge::cshake_public(e, b"QSAG.MIGRATE.VIEW.V3"));

    let segments: [[&[Bit]; 3]; 13] = [
        [&count6, &count6, &count6],
        [&len_rep, &len_rep, &len_rep],
        [&rep, &rep, &rep],
        [&len_head, &len_head, &len_head],
        [&head_bits[0], &head_bits[1], &head_bits[2]],
        [&len_seed, &len_seed, &len_seed],
        [&views[0].seed, &views[1].seed, &views[2].seed],
        [&len_in, &len_in, &len_in],
        [&views[0].inputs, &views[1].inputs, &views[2].inputs],
        [&len_prod, &len_prod, &len_prod],
        [&views[0].products, &views[1].products, &views[2].products],
        [&len_out, &len_out, &len_out],
        [&views[0].outputs, &views[1].outputs, &views[2].outputs],
    ];

    for segs in segments {
        debug_assert_eq!(segs[0].len(), segs[1].len());
        debug_assert_eq!(segs[0].len(), segs[2].len());
        let seg_len = segs[0].len();
        let mut offset = 0usize;
        while offset < seg_len {
            let pos = sponges[0].pos;
            let take = (1088 - pos).min(seg_len - offset);
            for h in 0..3 {
                let dst = &mut sponges[h].state[pos..pos + take];
                let src = &segs[h][offset..offset + take];
                for (d, &s) in dst.iter_mut().zip(src) {
                    *d = *d ^ s;
                }
                sponges[h].pos = pos + take;
            }
            offset += take;
            if sponges[0].pos == 1088 {
                for sp in &mut sponges {
                    sp.pos = 0;
                }
                let (s0, rest) = sponges.split_first_mut().unwrap();
                let (s1, rest2) = rest.split_first_mut().unwrap();
                let s2 = &mut rest2[0];
                e.permutations(&mut [&mut s0.state, &mut s1.state, &mut s2.state])?;
            }
        }
    }

    for sp in &mut sponges {
        sp.pad_only(e, 0x04);
    }
    {
        let (s0, rest) = sponges.split_first_mut().unwrap();
        let (s1, rest2) = rest.split_first_mut().unwrap();
        let s2 = &mut rest2[0];
        e.permutations(&mut [&mut s0.state, &mut s1.state, &mut s2.state])?;
    }

    Ok(core::array::from_fn(|h| {
        sponges[h].state[..256].iter().copied().collect()
    }))
}

#[cfg(test)]
fn commit_views<T: Transport>(
    e: &mut Engine<T>,
    batch: usize,
    views: &[SharedView],
) -> Result<Vec<Vec<u64>>, Error> {
    let bits = compute_view_commit_bits(e, batch, views)?;
    bits.iter().map(|b| e.open(b)).collect()
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use crate::{
        circuit::Builder,
        legacy::LegacyOwnershipWitness,
        outer_mpc::{
            FaultInjection,
            tests::{Network, audited_networks, keys, run},
        },
    };
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    };

    // Run the concrete former XOR attack with the live custody state, outer
    // input replicas and actual verified published proof available. This is a
    // regression for that attack, not an exhaustive adversarial computation.
    pub(super) fn audit_old_attack<T: Transport>(
        state: &CoZkCustodianShare,
        engine: &Engine<T>,
        physical_input: &[Bit],
        inputs: &[[Word; 3]],
        proof: &MigrationZkProof,
    ) {
        let Some((messages, words)) = engine.transport.audit_transcript() else {
            return;
        };
        let mut candidates = Vec::with_capacity(MIT_REPETITIONS * 3);
        assert_eq!(state.party, engine.party);
        assert_eq!(physical_input.len(), 256);
        assert!(messages > 0 && words > 0);
        for (rep, opening) in proof.repetitions.iter().enumerate() {
            let e = opening.opened_e as usize;
            let hidden = (e + 2) % 3;
            let lane = rep % 64;
            for components in [1, 2, 3] {
                let partial: Vec<_> = inputs[rep / 64][hidden]
                    .iter()
                    .map(|b| match components {
                        1 => b.0[0],
                        2 => b.0[1],
                        _ => b.0[0] ^ b.0[1],
                    })
                    .collect();
                let local = outer_mpc::lane_bytes(&partial, lane);
                let mut recovered = [0u8; 32];
                for bit in 0..256 {
                    recovered[bit / 8] |=
                        (local[bit] ^ opening.pair[0].inputs[bit] ^ opening.pair[1].inputs[bit])
                            << (bit % 8);
                }
                candidates.push(recovered);
            }
            if e != state.party {
                let locals: [[Vec<u8>; 3]; 2] = core::array::from_fn(|j| {
                    core::array::from_fn(|mask| {
                        let partial: Vec<_> = inputs[rep / 64][(state.party + j) % 3]
                            .iter()
                            .map(|b| match mask {
                                0 => b.0[0],
                                1 => b.0[1],
                                _ => b.0[0] ^ b.0[1],
                            })
                            .collect();
                        outer_mpc::lane_bytes(&partial, lane)
                    })
                });
                let missing = (state.party + 2) % 3;
                let published = &opening.pair[usize::from(e != missing)].inputs;
                for a in &locals[0] {
                    for b in &locals[1] {
                        let mut recovered = [0u8; 32];
                        for bit in 0..256 {
                            recovered[bit / 8] |= (a[bit] ^ b[bit] ^ published[bit]) << (bit % 8);
                        }
                        candidates.push(recovered);
                    }
                }
            }
            for view in &opening.pair {
                let mut recovered = [0u8; 32];
                for bit in 0..256 {
                    let local = ((physical_input[bit].0[0] ^ physical_input[bit].0[1]) >> lane) & 1;
                    recovered[bit / 8] |= ((local as u8) ^ view.inputs[bit]) << (bit % 8);
                }
                candidates.push(recovered);
            }
        }
        engine.transport.audit_candidates(candidates);
    }

    #[test]
    fn canonical_tapes_reject_boundary_words_without_aborting_or_losing_cached_bits() {
        use qsag_accel::goldilocks::GOLDILOCKS_PRIME;
        run(|p, n| {
            let mut e = Engine::new(p, [0x61; 32], keys(p), n).unwrap();
            let draws: Vec<_> = [64, 128, 256]
                .into_iter()
                .flat_map(|start| {
                    (0..3).map(move |head| FieldTapeDraw {
                        head,
                        start,
                        domain: Domain::Gold,
                    })
                })
                .collect();
            let counts = [320; 3];
            let required = tape_counts(&draws, counts, 4).unwrap();
            let value = |head: usize, lane: usize, word: usize| {
                let rejects = (head + lane) % 4;
                if word > 0 && word <= rejects {
                    [GOLDILOCKS_PRIME, GOLDILOCKS_PRIME + 1, u64::MAX][word - 1]
                } else if word == rejects + 1 {
                    GOLDILOCKS_PRIME - 1
                } else {
                    (word + 100 * head + 1000 * lane) as u64
                }
            };
            let streams: Vec<_> = (0..3)
                .map(|head| {
                    let words: Vec<_> = (0..required[head])
                        .map(|bit| {
                            if p != 0 {
                                return 0;
                            }
                            (0..64).fold(0, |acc, lane| {
                                acc | (((value(head, lane, bit / 64) >> (bit % 64)) & 1) << lane)
                            })
                        })
                        .collect();
                    e.share(&words).unwrap()
                })
                .collect();
            // Two consecutive boundary words exceed this attempt budget, but are
            // not an invalid tape: the caller extends the PRG and replays it.
            assert!(
                canonical_tape_attempt(&mut e, &streams, &draws, counts, 2)
                    .unwrap()
                    .is_none()
            );
            let repaired = canonical_tape_attempt(&mut e, &streams, &draws, counts, 4)
                .unwrap()
                .unwrap();
            for (head, stream) in repaired.iter().enumerate() {
                assert_eq!(stream.len(), counts[head]);
                let opened = e.open(stream).unwrap();
                for lane in 0..64 {
                    let mut cursor = 1;
                    let mut expected = vec![value(head, lane, 0)];
                    for slot in 1..5 {
                        loop {
                            let v = value(head, lane, cursor);
                            cursor += 1;
                            if slot == 3 || v < GOLDILOCKS_PRIME {
                                expected.push(v);
                                break;
                            }
                        }
                    }
                    let bytes = outer_mpc::lane_bytes(&opened, lane);
                    let actual: Vec<_> = bytes
                        .chunks_exact(8)
                        .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
                        .collect();
                    assert_eq!(actual, expected, "head {head}, lane {lane}");
                }
            }
            let short: Vec<Word> = streams
                .iter()
                .map(|s| s[..320].iter().copied().collect())
                .collect();
            assert!(matches!(
                canonical_tape_attempt(&mut e, &short, &draws, counts, 4),
                Err(Error::InvalidTape)
            ));
            assert!(matches!(
                canonical_tape_attempt(&mut e, &streams[..2], &draws, counts, 4),
                Err(Error::InvalidTape)
            ));
            assert_eq!(tape_counts(&draws, counts, 0), Err(Error::InvalidTape));
            assert_eq!(
                tape_counts(&draws, counts, usize::MAX),
                Err(Error::InvalidTape)
            );
            let malformed = [FieldTapeDraw {
                head: 3,
                start: 0,
                domain: Domain::Gold,
            }];
            assert_eq!(tape_counts(&malformed, counts, 2), Err(Error::InvalidTape));
        });
    }

    #[test]
    fn shared_views_and_commitments_are_byte_identical_to_native() {
        run(|p, n| {
            let mut e = Engine::new(p, [51; 32], keys(p), n).unwrap();
            let c = Builder::default();
            let bit = c.input(1);
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let a = c.lift(bit, d);
                let b = c.add(a, c.small(d, 27));
                let z = c.mul(a, b);
                c.output(z);
                if d == Domain::Gold {
                    let inverse = c.inverse(z);
                    c.output(inverse);
                }
                for b in c.bits(z) {
                    c.output(b);
                }
            }
            let c = c.finish();
            let witness = e.share(&[if p == 0 { u64::MAX } else { 0 }]).unwrap();
            let seeds: Vec<_> = (0..3)
                .map(|head| {
                    e.share(
                        &(0..256)
                            .map(|i| {
                                if ((p + head + 1) >> (i % 8)) & 1 != 0 {
                                    u64::MAX
                                } else {
                                    0
                                }
                            })
                            .collect::<Vec<_>>(),
                    )
                    .unwrap()
                })
                .collect();
            let views = evaluate(&mut e, &c, &witness, &seeds).unwrap();
            let commitments = commit_views(&mut e, 0, &views).unwrap();
            let clear_seeds: Vec<[u8; 32]> = seeds
                .iter()
                .map(|s| {
                    outer_mpc::lane_bytes(&e.open(s).unwrap(), 0)
                        .try_into()
                        .unwrap()
                })
                .collect();
            let native = zk_engine::simulate(&c, clear_seeds.try_into().unwrap());
            for (head, view) in views.iter().enumerate() {
                let bytes = outer_mpc::lane_bytes(&e.open(&view.bytes()).unwrap(), 0);
                let expected: Vec<_> = [
                    native[head].seed.as_slice(),
                    &native[head].inputs,
                    &native[head].products,
                    &native[head].outputs,
                ]
                .concat();
                assert_eq!(bytes, expected);
                for lane in 0..64 {
                    assert_eq!(
                        outer_mpc::lane_bytes(&commitments[head], lane),
                        zk_engine::commit(lane, head, &native[head])
                    );
                }
            }
        });
    }

    #[test]
    fn published_pairs_do_not_complete_local_outer_shares_over_64_witnesses() {
        let witnesses: Vec<_> = (0..64u64)
            .map(|i| cshake256_framed_32(b"OUTER.PRIVACY.WITNESS", &[&i.to_le_bytes()]))
            .collect();
        run(|p, n| {
            let mut e = Engine::new(p, [53; 32], keys(p), n).unwrap();
            let c = Builder::default();
            for _ in 0..256 {
                c.input(0);
            }
            let c = c.finish();
            let own: Vec<_> = (0..256)
                .map(|i| {
                    (0..64).fold(0, |v, lane| {
                        let a = cshake256_framed_32(b"OUTER.PRIVACY.SHARE", &[&[0, lane as u8]]);
                        let b = cshake256_framed_32(b"OUTER.PRIVACY.SHARE", &[&[1, lane as u8]]);
                        let x = match p {
                            0 => a[i / 8],
                            1 => b[i / 8],
                            _ => witnesses[lane][i / 8] ^ a[i / 8] ^ b[i / 8],
                        };
                        v | ((((x >> (i % 8)) & 1) as u64) << lane)
                    })
                })
                .collect();
            let witness = e.share(&own).unwrap();
            let seeds: Vec<_> = (0..3u8)
                .map(|head| {
                    let own: Vec<_> = (0..256)
                        .map(|i| {
                            (0..64).fold(0, |v, lane| {
                                let seed = cshake256_framed_32(
                                    b"OUTER.PRIVACY.SEED",
                                    &[&[p as u8, head, lane as u8]],
                                );
                                v | ((((seed[i / 8] >> (i % 8)) & 1) as u64) << lane)
                            })
                        })
                        .collect();
                    e.share(&own).unwrap()
                })
                .collect();
            let views = evaluate(&mut e, &c, &witness, &seeds).unwrap();
            let published: Vec<_> = views
                .iter()
                .enumerate()
                .map(|(head, v)| {
                    let mask = (0..64).fold(0, |m, lane| {
                        if (lane % 3 + 2) % 3 != head {
                            m | (1u64 << lane)
                        } else {
                            m
                        }
                    });
                    let bits: Word = v
                        .inputs
                        .iter()
                        .map(|b| Bit([b.0[0] & mask, b.0[1] & mask]))
                        .collect();
                    e.open(&bits).unwrap()
                })
                .collect();
            for (lane, expected) in witnesses.iter().enumerate() {
                let hidden = (lane % 3 + 2) % 3;
                for components in [1u8, 2, 3] {
                    let partial: Vec<_> = views[hidden]
                        .inputs
                        .iter()
                        .map(|b| {
                            if components == 1 {
                                b.0[0]
                            } else if components == 2 {
                                b.0[1]
                            } else {
                                b.0[0] ^ b.0[1]
                            }
                        })
                        .collect();
                    let local = outer_mpc::lane_bytes(&partial, lane);
                    let a = outer_mpc::lane_bytes(&published[lane % 3], lane);
                    let b = outer_mpc::lane_bytes(&published[(lane % 3 + 1) % 3], lane);
                    let mut recovered = [0u8; 32];
                    for i in 0..256 {
                        recovered[i / 8] |= (local[i] ^ a[i] ^ b[i]) << (i % 8);
                    }
                    assert_ne!(
                        &recovered, expected,
                        "custodian {p}, lane {lane}, components {components}"
                    );
                }
            }
        });
    }

    // Bound both ceremonies and per-custodian batches, keeping the suite within
    // the bounded builder memory budget while overlapping network synchronization.
    static HEAVY_CEREMONIES: (std::sync::Mutex<usize>, std::sync::Condvar) =
        (std::sync::Mutex::new(0), std::sync::Condvar::new());
    struct CeremonySlot(usize);
    impl CeremonySlot {
        fn acquire(batches: usize) -> Self {
            let (active, ready) = &HEAVY_CEREMONIES;
            let mut count = active.lock().unwrap_or_else(|e| e.into_inner());
            let limit = 7;
            while *count + batches > limit {
                count = ready.wait(count).unwrap_or_else(|e| e.into_inner());
            }
            *count += batches;
            Self(batches)
        }
    }
    impl Drop for CeremonySlot {
        fn drop(&mut self) {
            let (active, ready) = &HEAVY_CEREMONIES;
            *active.lock().unwrap_or_else(|e| e.into_inner()) -= self.0;
            ready.notify_all();
        }
    }

    #[test]
    fn complete_distributed_bitcoin_proof_verifies() {
        complete_proof(false);
    }

    #[test]
    fn complete_distributed_ed25519_proof_verifies() {
        complete_proof(true);
    }

    fn complete_proof(ed: bool) {
        use std::io::Read;
        let _ceremony_guard = CeremonySlot::acquire(outer_mpc::tests::parallel_batches());
        let mut completed = false;
        for _attempt in 0..4 {
            let mut master = [0u8; 32];
            std::fs::File::open("/dev/urandom")
                .unwrap()
                .read_exact(&mut master)
                .unwrap();
            let derive = |label: &[u8], id: u8| cshake256_framed_32(label, &[&master, &[id]]);
            let witness = LegacyOwnershipWitness::from_raw_secret(derive(
                b"OUTER.FULL.WITNESS",
                u8::from(ed),
            ));
            let kind = if ed {
                witness.compute_slip0010_commitment()
            } else {
                witness.compute_bitcoin_hash160().unwrap()
            };
            let request = zk_engine::tests::request(kind);
            let scalar = witness.normalize_spending_scalar(&kind).unwrap();
            let statement = MigrationStatement {
                legacy_commitment: kind,
                target_pq_address: request.target,
                epoch_anchor: request.epoch,
                migration_domain: request.domain,
                migration_nullifier: scalar.compute_nullifier(&request.domain),
                witness_anchor: [0; 4],
            };
            let mut parts = [
                derive(b"OUTER.FULL.INPUT", 0),
                derive(b"OUTER.FULL.INPUT", 1),
                *scalar.as_le_bytes(),
            ];
            let masks = [parts[0], parts[1]];
            for (i, byte) in parts[2].iter_mut().enumerate() {
                *byte ^= masks[0][i] ^ masks[1][i];
            }
            let session = derive(b"OUTER.FULL.SESSION", 0);
            let pair_keys: [_; 3] =
                core::array::from_fn(|p| derive(b"OUTER.FULL.PAIR.KEY", p as u8));
            let entropy: [_; 3] = core::array::from_fn(|p| derive(b"OUTER.FULL.ENTROPY", p as u8));
            ct_zeroize_bytes(&mut master);
            let states: [_; 3] = core::array::from_fn(|p| {
                CoZkCustodianShare::new(
                    p,
                    session,
                    parts[p],
                    entropy[p],
                    [pair_keys[(p + 2) % 3], pair_keys[p]],
                )
                .unwrap()
            });
            let start = std::time::Instant::now();
            let outcomes = std::thread::scope(|scope| {
                let handles: Vec<_> = states
                    .into_iter()
                    .zip(audited_networks())
                    .map(|(state, (network, audit))| {
                        let public = statement.clone();
                        scope.spawn(move || (state.prove(&public, network), audit))
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });
            let mut errors = Vec::new();
            for (party, (result, audit)) in outcomes.into_iter().enumerate() {
                match result {
                    Ok(proof) => {
                        zk_engine::verify_migration_proof(
                            &statement,
                            &proof,
                            &statement.migration_domain,
                            statement.epoch_anchor,
                        )
                        .unwrap();
                        let candidates = audit.candidates();
                        let former_attack_rounds = proof
                            .repetitions
                            .iter()
                            .filter(|r| r.opened_e as usize != party)
                            .count();
                        assert_eq!(
                            candidates.len(),
                            MIT_REPETITIONS * 5 + former_attack_rounds * 9
                        );
                        for recovered in candidates {
                            assert_ne!(&recovered, scalar.as_le_bytes());
                        }
                    }
                    Err(error) => errors.push(error),
                }
            }
            if errors.is_empty() {
                std::eprintln!(
                    "distributed 438-rep {}: {:?}",
                    if ed { "Ed25519" } else { "Bitcoin HASH160" },
                    start.elapsed()
                );
                completed = true;
                break;
            }
            assert!(
                errors.contains(&Error::InvalidTape),
                "unexpected errors: {errors:?}"
            );
            assert!(
                errors
                    .iter()
                    .all(|e| matches!(e, Error::InvalidTape | Error::Transport))
            );
        }
        assert!(completed, "four independent tape rejections");
    }

    #[test]
    fn one_custodian_valid_mac_equivocation_aborts_every_output() {
        struct Equivocate(Network);
        impl Transport for Equivocate {
            fn exchange(&mut self, mut outgoing: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                if outgoing[0].sender == 0 && outgoing[0].sequence == 0 {
                    let m = &mut outgoing[0];
                    m.payload[0] ^= 1;
                    let bytes: Vec<_> = m.payload.iter().flat_map(|w| w.to_le_bytes()).collect();
                    m.tag = cshake256_framed_32(
                        b"QSAG.OUTER.MESSAGE.V1",
                        &[
                            &keys(0)[0],
                            &[62; 32],
                            &[m.sender as u8, m.recipient as u8],
                            &m.sequence.to_le_bytes(),
                            &bytes,
                        ],
                    );
                }
                self.0.exchange(outgoing)
            }
        }
        let witness = LegacyOwnershipWitness::from_raw_secret([7; 32]);
        let kind = witness.compute_bitcoin_hash160().unwrap();
        let request = zk_engine::tests::request(kind);
        let scalar = witness.normalize_spending_scalar(&kind).unwrap();
        let statement = MigrationStatement {
            legacy_commitment: kind,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: scalar.compute_nullifier(&request.domain),
            witness_anchor: [0; 4],
        };
        run(|p, n| {
            let result =
                CoZkCustodianShare::new(p, [62; 32], [0; 32], [(p + 1) as u8; 32], keys(p))
                    .unwrap()
                    .prove(&statement, Equivocate(n));
            if p == 2 {
                assert!(matches!(result, Err(Error::Disagreement(0))));
            } else {
                assert!(matches!(result, Err(Error::Transport)));
            }
        });
    }

    const PRECOMMIT_SEQ: u64 = (2 + 3 * MIT_REPETITIONS.div_ceil(64)) as u64;

    struct ZkbooFaultSpy {
        inner: Network,
        is_root: bool,
        fault: Option<FaultInjection>,
        precommit_or_view_opened: Arc<AtomicBool>,
    }
    impl Transport for ZkbooFaultSpy {
        fn max_parallel_batches(&self) -> usize {
            3
        }

        fn test_fault_raw(&self) -> Option<[usize; 4]> {
            self.fault.map(FaultInjection::to_raw)
        }
        fn on_public_or_view_open(&self) {
            self.precommit_or_view_opened.store(true, Ordering::SeqCst);
        }
        fn fork(&mut self, batch: usize) -> Option<Self> {
            self.inner.fork(batch).map(|child| Self {
                inner: child,
                is_root: false,
                // Inject the fault ONLY in batch 2 so all other batches are clean,
                // proving the cross-batch barrier also blocks clean batches from opening!
                fault: if batch == 2 { self.fault } else { None },
                precommit_or_view_opened: self.precommit_or_view_opened.clone(),
            })
        }
        fn exchange(&mut self, out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
            // Root sequence 0 = STATEMENT, 1 = witness, 2..PRECOMMIT_SEQ = batch seeds, PRECOMMIT_SEQ = PRECOMMIT!
            if self.is_root && out[0].sequence >= PRECOMMIT_SEQ {
                self.precommit_or_view_opened.store(true, Ordering::SeqCst);
            }
            self.inner.exchange(out)
        }
    }

    fn assert_zkboo_fault_aborts_cleanly(ed: bool, fault: FaultInjection, session_tag: u8) {
        let _ceremony_guard = CeremonySlot::acquire(3);
        for seed_try in 0..8u8 {
            let witness = LegacyOwnershipWitness::from_raw_secret([0x31 + seed_try; 32]);
            let kind = if ed {
                witness.compute_slip0010_commitment()
            } else {
                witness.compute_bitcoin_hash160().unwrap()
            };
            let request = zk_engine::tests::request(kind);
            let scalar = witness.normalize_spending_scalar(&kind).unwrap();
            let statement = MigrationStatement {
                legacy_commitment: kind,
                target_pq_address: request.target,
                epoch_anchor: request.epoch,
                migration_domain: request.domain,
                migration_nullifier: scalar.compute_nullifier(&request.domain),
                witness_anchor: [0; 4],
            };
            let p0 = [0x11; 32];
            let p1 = [0x22; 32];
            let mut p2 = *scalar.as_le_bytes();
            for i in 0..32 {
                p2[i] ^= p0[i] ^ p1[i];
            }
            let parts = [p0, p1, p2];
            let session = [session_tag.wrapping_add(seed_try); 32];
            let leaked: [Arc<AtomicBool>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

            let outcomes = std::thread::scope(|scope| {
                let handles: Vec<_> = outer_mpc::tests::networks()
                    .into_iter()
                    .enumerate()
                    .map(|(p, net)| {
                        let st = statement.clone();
                        let flag = leaked[p].clone();
                        scope.spawn(move || {
                            let spy = ZkbooFaultSpy {
                                inner: net,
                                is_root: true,
                                fault: (p == 1).then_some(fault),
                                precommit_or_view_opened: flag,
                            };
                            CoZkCustodianShare::new(
                                p,
                                session,
                                parts[p],
                                [0x50 + p as u8 + seed_try; 32],
                                keys(p),
                            )
                            .unwrap()
                            .prove(&st, spy)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });

            // If a random seed hit upfront `InvalidTape` before reaching the injected gate, retry next seed.
            if outcomes
                .iter()
                .any(|r| matches!(r, Err(Error::InvalidTape)))
            {
                continue;
            }
            for (p, res) in outcomes.into_iter().enumerate() {
                assert_eq!(
                    res,
                    Err(Error::MultiplicationCheck),
                    "custodian {p} must abort with MultiplicationCheck on ZKBoo fault"
                );
                assert!(
                    !leaked[p].load(Ordering::SeqCst),
                    "custodian {p} must NEVER reach PRECOMMIT or open commitments/views on ZKBoo fault!"
                );
            }
            return;
        }
        panic!("8 consecutive upfront InvalidTape rejections in ZKBoo fault test");
    }

    #[test]
    fn active_boolean_fault_in_zkboo_circuit_aborts_before_commitments_or_views_open() {
        // `call_countdown: 600` injects a 1-bit consistent-share fault inside ZKBoo circuit /
        // view-commitment evaluation on batch 2, after upfront `Tape` validation has passed.
        assert_zkboo_fault_aborts_cleanly(
            false,
            FaultInjection::BitAnd {
                call_countdown: 600,
                gate: 7,
                lane: 41,
            },
            0xd0,
        );
    }

    #[test]
    fn active_field_fault_in_zkboo_circuit_aborts_before_commitments_or_views_open() {
        assert_zkboo_fault_aborts_cleanly(
            false,
            FaultInjection::FieldMul {
                domain: Domain::Secp,
                call_countdown: 5,
                lane: 19,
            },
            0xe0,
        );
    }

    #[test]
    fn active_goldilocks_field_fault_in_zkboo_circuit_aborts_before_commitments_or_views_open() {
        assert_zkboo_fault_aborts_cleanly(
            true,
            FaultInjection::FieldMul {
                domain: Domain::Gold,
                call_countdown: 5,
                lane: 23,
            },
            0xf0,
        );
    }

    fn assert_input_substitution_aborts(ed: bool, delta_64bit: bool, session_tag: u8) {
        let _ceremony_guard = CeremonySlot::acquire(3);
        let mut verified = false;
        for seed_try in 0..8u8 {
            let witness = LegacyOwnershipWitness::from_raw_secret([0x41 + seed_try; 32]);
            let kind = if ed {
                witness.compute_slip0010_commitment()
            } else {
                witness.compute_bitcoin_hash160().unwrap()
            };
            let request = zk_engine::tests::request(kind);
            let scalar = witness.normalize_spending_scalar(&kind).unwrap();
            let statement = MigrationStatement {
                legacy_commitment: kind,
                target_pq_address: request.target,
                epoch_anchor: request.epoch,
                migration_domain: request.domain,
                migration_nullifier: scalar.compute_nullifier(&request.domain),
                witness_anchor: [0; 4],
            };
            let p0 = [0x15; 32];
            let p1 = [0x2a; 32];
            let mut p2 = *scalar.as_le_bytes();
            for i in 0..32 {
                p2[i] ^= p0[i] ^ p1[i];
            }
            // Malicious custodian 2 substitutes `share ^ Delta` (`64`-bit MITM delta or `1`-bit flip).
            if delta_64bit {
                for b in &mut p2[..8] {
                    *b ^= 0xa5;
                }
            } else {
                p2[0] ^= 0x08;
            }
            let parts = [p0, p1, p2];
            let session = [session_tag.wrapping_add(seed_try); 32];
            let leaked: [Arc<AtomicBool>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

            let outcomes = std::thread::scope(|scope| {
                let handles: Vec<_> = outer_mpc::tests::networks()
                    .into_iter()
                    .enumerate()
                    .map(|(p, net)| {
                        let st = statement.clone();
                        let flag = leaked[p].clone();
                        scope.spawn(move || {
                            let spy = ZkbooFaultSpy {
                                inner: net,
                                is_root: true,
                                fault: None,
                                precommit_or_view_opened: flag,
                            };
                            CoZkCustodianShare::new(
                                p,
                                session,
                                parts[p],
                                [0x60 + p as u8 + seed_try; 32],
                                keys(p),
                            )
                            .unwrap()
                            .prove(&st, spy)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });

            if outcomes
                .iter()
                .any(|r| matches!(r, Err(Error::InvalidTape)))
            {
                continue;
            }
            for (p, res) in outcomes.into_iter().enumerate() {
                assert_eq!(
                    res,
                    Err(Error::InvalidProof),
                    "custodian {p} must abort with InvalidProof on input key-share substitution"
                );
                assert!(
                    !leaked[p].load(Ordering::SeqCst),
                    "custodian {p} must NEVER open output residuals, commitments, or views on input substitution!"
                );
            }
            verified = true;
            break;
        }
        assert!(
            verified,
            "8 consecutive upfront InvalidTape rejections in input-substitution test"
        );
    }

    #[test]
    fn custodian_input_key_share_substitution_aborts_before_any_output_or_commitment_opens() {
        assert_input_substitution_aborts(false, true, 0xa0);
    }

    #[test]
    fn custodian_ed25519_input_key_share_substitution_aborts_before_any_output_or_commitment_opens()
    {
        assert_input_substitution_aborts(true, false, 0xb0);
    }
}
