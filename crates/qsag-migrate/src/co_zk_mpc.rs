//! Distributed 3-custodian prover emulation with active 1-of-3 malicious
//! multiplication verification over authenticated confidential pairwise channels.
//!
//! Privacy and integrity threshold: at most one corrupted custodian (`1`-of-`3`
//! honest majority), assuming confidential authenticated pairwise channels and
//! independently sampled private custodian entropy. Every Boolean `AND` gate and
//! prime-field multiplication is batch-verified with coin-flipped challenges
//! (`< 2^-126` Boolean soundness over `GF(2^128)`, `< 2^-128` prime-field
//! soundness over `GF(p)` / `GF(p^3)`) before any wire opening, masked A2B/B2A
//! conversion difference, view commitment, public output, or challenged ZKBoo
//! party view is reconstructed. Two colluding custodians can reconstruct
//! replicated secrets, and abort remains non-identifiable / unfair (`1` corrupt
//! custodian can force an abort). See `SECURITY.md` for exact scope.
pub use crate::outer_mpc::{Envelope, Error, Transport};
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

        let own: Vec<_> = self
            .witness
            .iter()
            .flat_map(|b| (0..8).map(move |i| if (b >> i) & 1 != 0 { u64::MAX } else { 0 }))
            .collect();
        let witness = e.share_uniform_lanes(&own)?;
        let circuit = crate::ownership::build(statement, &[0; 32]);

        let num_batches = MIT_REPETITIONS.div_ceil(64);
        let mut seeds = Vec::with_capacity(num_batches);
        for batch in 0..num_batches {
            let mut heads = Vec::with_capacity(3);
            for head in 0..3 {
                let lane_seeds: Vec<_> = (0..64)
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
                let own_seed: Vec<_> = (0..256)
                    .map(|i| {
                        lane_seeds.iter().enumerate().fold(0, |v, (lane, s)| {
                            v | (((s[i / 8] >> (i % 8)) & 1) as u64) << lane
                        })
                    })
                    .collect();
                heads.push(e.share(&own_seed)?);
            }
            seeds.push(heads);
        }

        // Phase 1: Evaluate all batches, compute shared view commitments, and run
        // mandatory active multiplication checks on EVERY batch BEFORE opening any
        // commitment, public circuit output, or ZKBoo view.
        let mut computed_batches = compute_batches(
            &mut e,
            &circuit,
            &witness,
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
            let rounds = open_batch_public_rounds(opening_engine, batch, &item.commit_bits, &item.views)?;
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
                let masked: Word = view
                    .bytes()
                    .iter()
                    .map(|b| Bit([b.0[0] & mask, b.0[1] & mask]))
                    .collect();
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
        zk_engine::verify_migration_proof(
            statement,
            &proof,
            &statement.migration_domain,
            statement.epoch_anchor,
        )
        .map_err(|_| Error::InvalidProof)?;
        e.agree(cshake256_framed_32(b"QSAG.OUTER.COMPLETE.V1", &[&root]))?;
        #[cfg(test)]
        tests::audit_old_attack(&self, &e, &witness, &audit_inputs, &proof);
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
    let mut flat = Vec::with_capacity(3 * 256 + 3 * out_len);
    for cb in commit_bits {
        flat.extend_from_slice(cb);
    }
    for v in views {
        flat.extend_from_slice(&v.outputs);
    }
    let opened = e.open(&flat)?;
    let count = core::cmp::min(64, MIT_REPETITIONS - batch * 64);
    let commits_clear: [&[u64]; 3] = [
        &opened[0..256],
        &opened[256..512],
        &opened[512..768],
    ];
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
        return std::thread::scope(|scope| {
            let handles: Vec<_> = children
                .into_iter()
                .enumerate()
                .map(|(batch, transport)| {
                    scope.spawn(move || {
                        let batch_session = cshake256_framed_32(
                            b"QSAG.OUTER.BATCH.V1",
                            &[&session, &(batch as u64).to_le_bytes()],
                        );
                        let mut batch_entropy = cshake256_framed_32(
                            b"QSAG.OUTER.BATCH.ENTROPY.V1",
                            &[&entropy, &session, &(batch as u64).to_le_bytes()],
                        );
                        let mut engine = Engine::new(party, batch_session, keys, transport)?;
                        engine.mix_entropy(&batch_entropy);
                        ct_zeroize_bytes(&mut batch_entropy);
                        let mut result =
                            compute_batch(&mut engine, c, witness, &seeds[batch], batch)?;
                        result.engine = Some(engine);
                        Ok(result)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().map_err(|_| Error::Transport)?)
                .collect()
        });
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
    fn bytes(&self) -> Word {
        let mut out = Vec::with_capacity(
            self.seed.len() + self.inputs.len() + self.products.len() + self.outputs.len(),
        );
        out.extend_from_slice(&self.seed);
        out.extend_from_slice(&self.inputs);
        out.extend_from_slice(&self.products);
        out.extend_from_slice(&self.outputs);
        out
    }
}
impl Drop for SharedView {
    fn drop(&mut self) {
        for v in [
            &mut self.seed,
            &mut self.inputs,
            &mut self.products,
            &mut self.outputs,
        ] {
            for b in v {
                ct_zeroize_u64s(&mut b.0);
            }
        }
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
            Self::Field(vec![[[0; 4]; 2]; 64])
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
            Self::Field(f) => {
                for pair in f {
                    for part in pair {
                        ct_zeroize_u64s(part);
                    }
                }
            }
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

fn fold_valid_bits<T: Transport>(e: &mut Engine<T>, mut groups: [Vec<Bit>; 3]) -> Result<[Bit; 3], Error> {
    for g in &mut groups {
        if g.is_empty() {
            g.push(e.constant(u64::MAX));
        }
    }
    while groups.iter().any(|g| g.len() > 1) {
        let mut pairs = Vec::new();
        for g in &groups {
            for pair in g.chunks_exact(2) {
                pairs.push((pair[0], pair[1]));
            }
        }
        let prods = e.and(&pairs)?;
        let mut cur = 0usize;
        for g in &mut groups {
            let num_pairs = g.len() / 2;
            let mut next = Vec::with_capacity(num_pairs + (g.len() % 2));
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

fn fold_all_true_bits<T: Transport>(e: &mut Engine<T>, mut bits: Vec<Bit>) -> Result<Bit, Error> {
    if bits.is_empty() {
        return Ok(e.constant(u64::MAX));
    }
    while bits.len() > 1 {
        let mut pairs = Vec::with_capacity(bits.len() / 2);
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
                    (NodeTape::InputField { target, draws: [d0, d1] }, waves[target] + 1)
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
    let squeezed = outer_mpc::squeeze_sponges_lockstep(
        e,
        &mut tape_sponges,
        &[
            cursors[0].sponge_bits,
            cursors[1].sponge_bits,
            cursors[2].sponge_bits,
        ],
    )?;

    // 3. Batch-check `< modulus` across all field draws per domain and open `valid` upfront.
    let mut valid_groups: [Vec<Bit>; 3] = core::array::from_fn(|_| Vec::new());
    let mut raw_draw_words: Vec<Word> = field_draws
        .iter()
        .map(|fd| squeezed[fd.head][fd.start..fd.start + fd.domain.width()].to_vec())
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
        for rw in &mut raw_draw_words {
            for b in rw {
                ct_zeroize_u64s(&mut b.0);
            }
        }
        return Err(Error::InvalidTape);
    }

    // 4. Batch-convert all validated field tape draws (`bits_to_field_many` per domain).
    let mut draw_fields: Vec<Option<FieldWord>> = (0..field_draws.len()).map(|_| None).collect();
    for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
        let mut idxs = Vec::new();
        let mut dom_words = Vec::new();
        for (idx, fd) in field_draws.iter().enumerate() {
            if fd.domain == dom {
                idxs.push(idx);
                dom_words.push(raw_draw_words[idx].clone());
            }
        }
        if !dom_words.is_empty() {
            let converted = e.bits_to_field_many(&dom_words, dom)?;
            for (idx, fw) in idxs.into_iter().zip(converted) {
                draw_fields[idx] = Some(fw);
            }
        }
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
                let mut lift_bits = Vec::new();
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
                    encodings[a][owner] = Some(vec![wires[a].as_ref().unwrap()[owner].bit()]);
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
            let mut bit_mul_pairs = Vec::new();
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
