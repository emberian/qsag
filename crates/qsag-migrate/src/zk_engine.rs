//! Ordered-pair ZKBoo with exact mixed-domain replay across 438 repetitions.
use crate::{
    circuit::{Circuit, Domain, Op, Value, ZERO, local},
    legacy::{LegacyCommitmentKind, LegacyOwnershipWitness},
};
use alloc::vec::Vec;
use core::fmt;
use qsag_accel::{
    AcceleratorBackend,
    ct::{ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::GOLDILOCKS_PRIME,
    keccak::{InterleavedTranscript, Shake256, cshake256_framed_32},
};
use qsag_addr::QsagAddress;
pub const MIT_PARTIES: usize = 3;
/// Classical error `(2/3)^438 = 2^-256.2135753159 < 2^-256`;
/// QROM Grover error `sqrt((2/3)^438) = (2/3)^219 = 2^-128.1067876579 < 2^-128`. See `SECURITY.md`.
pub const MIT_REPETITIONS: usize = 438;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MigrateError {
    WitnessMismatchWithLegacyCommitment,
    MalformedProofStructure,
    ViewsMerkleRootMismatch,
    OpenedPartyGateFailed { rep: usize, gate: usize },
    PublicOutputShareMismatch,
    InvalidSharingParameters,
    SessionMismatch,
    UnexpectedMessage,
    EntropyUnavailable,
    InconsistentReplica,
}
/// Public statement of a Classical-to-PQ Migration ZK Proof (`Π_zk_migrate`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MigrationStatement {
    pub legacy_commitment: LegacyCommitmentKind,
    pub target_pq_address: QsagAddress,
    pub epoch_anchor: u64,
    /// Replay domain shared by every destination in a migration campaign.
    pub migration_domain: [u8; 32],
    /// Context-bound nullifier; replay tracking must be supplied by the caller.
    pub migration_nullifier: [u64; 4],
    /// Reserved public binding; must be zero in protocol version 3.
    pub witness_anchor: [u64; 4],
}

impl MigrationStatement {
    /// Full digest limbs of both commitments and an injective two-limb epoch.
    pub fn public_context_limbs(&self) -> [u64; 10] {
        let leg = qsag_accel::poseidon2::poseidon2_hash_limbs(
            0x4D49_475F_4C45_4731,
            &self.legacy_commitment.to_canonical_limbs56(),
        );
        let addr = &self.target_pq_address;
        let pq = qsag_accel::poseidon2::poseidon2_hash_framed_limbs4(
            0x4D49_475F_5051_3031,
            &[
                addr.hrp.as_bytes(),
                &[addr.version as u8],
                &(addr.suite_tag as u16).to_be_bytes(),
                &[addr.kind as u8],
                &addr.commitment_256,
            ],
        );
        [
            leg[0],
            leg[1],
            leg[2],
            leg[3],
            pq[0],
            pq[1],
            pq[2],
            pq[3],
            self.epoch_anchor & 0xffff_ffff,
            self.epoch_anchor >> 32,
        ]
    }

    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(192);
        out.extend_from_slice(&self.migration_domain);
        for l in self.legacy_commitment.to_canonical_limbs56() {
            out.extend_from_slice(&l.to_le_bytes());
        }
        out.extend_from_slice(&(self.target_pq_address.hrp.len() as u64).to_le_bytes());
        out.extend_from_slice(self.target_pq_address.hrp.as_bytes());
        out.push(self.target_pq_address.version as u8);
        out.extend_from_slice(&(self.target_pq_address.suite_tag as u16).to_be_bytes());
        out.push(self.target_pq_address.kind as u8);
        out.extend_from_slice(&self.target_pq_address.commitment_256);
        out.extend_from_slice(&self.epoch_anchor.to_le_bytes());
        for (n, a) in self.migration_nullifier.iter().zip(&self.witness_anchor) {
            out.extend_from_slice(&n.to_le_bytes());
            out.extend_from_slice(&a.to_le_bytes());
        }
        out
    }
}

/// Only selected openings are public. Secret tapes are erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub struct PartyView {
    pub seed: [u8; 32],
    pub inputs: Vec<u8>,
    pub products: Vec<u8>,
    pub outputs: Vec<u8>,
}
impl fmt::Debug for PartyView {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PartyView")
            .field("products_bytes", &self.products.len())
            .field("secrets", &"<REDACTED>")
            .finish()
    }
}
impl Drop for PartyView {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.seed);
        ct_zeroize_bytes(&mut self.inputs);
        ct_zeroize_bytes(&mut self.products);
        ct_zeroize_bytes(&mut self.outputs);
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedRepetitionView {
    pub opened_e: u8,
    pub pair: [PartyView; 2],
    pub hidden_party_commit: [u8; 32],
    pub hidden_outputs: Vec<u8>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MigrationZkProof {
    pub views_merkle_root: [u8; 32],
    pub repetitions: Vec<OpenedRepetitionView>,
}

pub(crate) struct Tape {
    sponge: Shake256,
    bit_buf: u64,
    bit_rem: u8,
}
impl Drop for Tape {
    fn drop(&mut self) {
        // Shake256 erases its internal state through its own Drop implementation.
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.bit_buf), 0);
            qsag_asm::volatile_fill(core::slice::from_mut(&mut self.bit_rem), 0);

    }
}
impl Tape {
    pub(crate) fn new(seed: &[u8; 32]) -> Self {
        let mut s = Shake256::new();
        s.absorb(b"QSAG.MIGRATE.TAPE.V3");
        s.absorb(seed);
        s.finalize(0x1f);
        Self {
            sponge: s,
            bit_buf: 0,
            bit_rem: 0,
        }
    }
    #[inline]
    pub(crate) fn sample(&mut self, d: Domain) -> Value {
        if d == Domain::Bit {
            if self.bit_rem == 0 {
                let mut raw = [0; 8];
                self.sponge.squeeze(&mut raw);
                self.bit_buf = u64::from_le_bytes(raw);
                self.bit_rem = 64;
            }
            let bit = self.bit_buf & 1;
            self.bit_buf >>= 1;
            self.bit_rem -= 1;
            return [bit, 0, 0, 0];
        }
        if d == Domain::Gold {
            loop {
                let mut raw = [0; 8];
                self.sponge.squeeze(&mut raw);
                let v = u64::from_le_bytes(raw);
                if v < GOLDILOCKS_PRIME {
                    return [v, 0, 0, 0];
                }
            }
        }
        loop {
            let mut raw = [0; 32];
            self.sponge.squeeze(&mut raw[..d.width().div_ceil(8)]);
            let mut v = crate::scalar::decode(&raw);
            ct_zeroize_bytes(&mut raw);
            if d == Domain::Ed {
                v[3] &= 0x7fff_ffff_ffff_ffff;
            }
            if d.canonical(v) {
                return v;
            }
        }
    }
}
#[inline]
pub(crate) fn put(out: &mut Vec<u8>, d: Domain, v: Value) {
    if d == Domain::Bit {
        out.push((v[0] & 1) as u8);
        return;
    }
    if d == Domain::Gold {
        out.extend_from_slice(&v[0].to_le_bytes());
        return;
    }
    let bytes = crate::scalar::encode(v);
    out.extend_from_slice(&bytes[..d.width().div_ceil(8)]);
}
#[inline]
pub(crate) fn take(input: &mut &[u8], d: Domain) -> Result<Value, MigrateError> {
    let len = d.width().div_ceil(8);
    if input.len() < len {
        return Err(MigrateError::MalformedProofStructure);
    }
    if d == Domain::Bit || d == Domain::Gold {
        let v = if d == Domain::Bit {
            u64::from(input[0])
        } else {
            u64::from_le_bytes(input[..8].try_into().unwrap())
        };
        *input = &input[len..];
        if (d == Domain::Bit && v > 1) || (d == Domain::Gold && v >= GOLDILOCKS_PRIME) {
            return Err(MigrateError::MalformedProofStructure);
        }
        return Ok([v, 0, 0, 0]);
    }
    let mut raw = [0; 32];
    raw[..len].copy_from_slice(&input[..len]);
    *input = &input[len..];
    let v = crate::scalar::decode(&raw);
    if !d.canonical(v) {
        return Err(MigrateError::MalformedProofStructure);
    }
    Ok(v)
}
pub(crate) struct Wires(pub(crate) Vec<Value>);
impl Drop for Wires {
    fn drop(&mut self) {
        ct_zeroize_u64s(self.0.as_mut_slice().as_flattened_mut());
    }
}
#[inline]
pub(crate) fn gate(d: Domain, a: [Value; 2], b: [Value; 2], r: [Value; 2]) -> Value {
    if d == Domain::Bit {
        return [
            (a[0][0] & b[0][0]) ^ (a[0][0] & b[1][0]) ^ (a[1][0] & b[0][0]) ^ r[0][0] ^ r[1][0],
            0,
            0,
            0,
        ];
    }
    d.add(
        d.add(
            d.add(d.mul(a[0], b[0]), d.mul(a[0], b[1])),
            d.mul(a[1], b[0]),
        ),
        d.sub(r[0], r[1]),
    )
}
pub(crate) fn simulate(c: &Circuit, seeds: [[u8; 32]; 3]) -> [PartyView; 3] {
    let mut tapes = seeds.map(|s| Tape::new(&s));
    let mut views = seeds.map(|seed| PartyView {
        seed,
        inputs: Vec::new(),
        products: Vec::new(),
        outputs: Vec::new(),
    });
    let mut wires: [Wires; 3] = core::array::from_fn(|_| Wires(Vec::with_capacity(c.nodes.len())));
    for node in &c.nodes {
        let d = node.domain;
        let value = match node.op {
            Op::Input => {
                let a = tapes[0].sample(d);
                let b = tapes[1].sample(d);
                let shares = [a, b, d.sub(node.value, d.add(a, b))];
                for (view, v) in views.iter_mut().zip(shares) {
                    put(&mut view.inputs, d, v);
                }
                shares
            }
            Op::Mul(a, b) => {
                let masks = core::array::from_fn::<_, 3, _>(|p| tapes[p].sample(d));
                let shares = core::array::from_fn(|p| {
                    let n = (p + 1) % 3;
                    gate(
                        d,
                        [wires[p].0[a], wires[n].0[a]],
                        [wires[p].0[b], wires[n].0[b]],
                        [masks[p], masks[n]],
                    )
                });
                for (view, v) in views.iter_mut().zip(shares) {
                    put(&mut view.products, d, v);
                }
                shares
            }
            _ => core::array::from_fn(|p| local(node, p, &wires[p].0)),
        };
        for (w, v) in wires.iter_mut().zip(value) {
            w.0.push(v);
        }
    }
    for (v, w) in views.iter_mut().zip(&wires) {
        for &i in &c.outputs {
            put(&mut v.outputs, c.nodes[i].domain, w.0[i]);
        }
    }
    views
}
pub(crate) fn commit(rep: usize, p: usize, view: &PartyView) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.MIGRATE.VIEW.V3",
        &[
            &(rep as u64).to_le_bytes(),
            &[p as u8],
            &view.seed,
            &view.inputs,
            &view.products,
            &view.outputs,
        ],
    )
}
pub(crate) fn rep_root(rep: usize, commits: &[[u8; 32]; 3], outputs: [&[u8]; 3]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.MIGRATE.REPETITION.V3",
        &[
            &(rep as u64).to_le_bytes(),
            &commits[0],
            &commits[1],
            &commits[2],
            outputs[0],
            outputs[1],
            outputs[2],
        ],
    )
}
fn seeds(entropy: &[u8; 32], statement: &[u8], rep: usize) -> [[u8; 32]; 3] {
    core::array::from_fn(|p| {
        cshake256_framed_32(
            b"QSAG.MIGRATE.SEEDS.V3",
            &[entropy, statement, &(rep as u64).to_le_bytes(), &[p as u8]],
        )
    })
}
pub(crate) fn challenges(t: &mut InterleavedTranscript) -> [u8; MIT_REPETITIONS] {
    let mut seed = [0; 32];
    t.squeeze_bytes(b"ORDERED_PAIR_SEED", &mut seed);
    let mut stream = Shake256::new();
    stream.absorb(b"QSAG.MIGRATE.CHALLENGES.V3");
    stream.absorb(&seed);
    stream.finalize(0x1f);
    let mut out = [0; MIT_REPETITIONS];
    let mut i = 0;
    while i < out.len() {
        let mut block = [0; 64];
        stream.squeeze(&mut block);
        for b in block {
            if b < 252 && i < out.len() {
                out[i] = b % 3;
                i += 1;
            }
        }
    }
    t.absorb(b"ORDERED_PAIRS", &out);
    out
}

pub(crate) fn transcript(statement: &MigrationStatement, root: &[u8; 32]) -> InterleavedTranscript {
    let mut t = InterleavedTranscript::new(b"QSAG.MIGRATE.V3", &statement.to_transcript_bytes());
    t.absorb(b"VIEWS", root);
    t
}

/// Compatibility entry point: the epoch identifies the replay domain. Applications
/// needing an independent campaign identifier should use the explicit-domain API.
pub fn prove_migration_ownership<B: AcceleratorBackend>(
    witness: &LegacyOwnershipWitness,
    legacy: LegacyCommitmentKind,
    target: QsagAddress,
    epoch: u64,
    entropy: [u8; 32],
    accel: &B,
) -> Result<(MigrationStatement, MigrationZkProof), MigrateError> {
    let domain = cshake256_framed_32(b"QSAG.MIGRATE.CAMPAIGN.V3", &[&epoch.to_le_bytes()]);
    prove_migration_in_domain(
        witness,
        MigrationRequest {
            legacy,
            target,
            epoch,
            domain,
        },
        entropy,
        accel,
    )
}
#[derive(Clone, Debug)]
pub struct MigrationRequest {
    pub legacy: LegacyCommitmentKind,
    pub target: QsagAddress,
    pub epoch: u64,
    pub domain: [u8; 32],
}
/// Obtain fresh kernel entropy and hedge it with the witness and full statement.
#[cfg(all(feature="std",unix))]
pub fn prove_migration_in_domain_os_rng<B: AcceleratorBackend>(
    witness:&LegacyOwnershipWitness,request:MigrationRequest,accel:&B,
)->Result<(MigrationStatement,MigrationZkProof),MigrateError> {
    use std::io::Read;
    let mut entropy=[0;32];
    let read=std::fs::File::open("/dev/urandom").and_then(|mut f|f.read_exact(&mut entropy));
    if read.is_err(){ct_zeroize_bytes(&mut entropy);return Err(MigrateError::EntropyUnavailable);}
    let result=prove_migration_in_domain(witness,request,entropy,accel);
    ct_zeroize_bytes(&mut entropy);result
}
pub fn prove_migration_in_domain<B: AcceleratorBackend>(
    witness: &LegacyOwnershipWitness,
    request: MigrationRequest,
    mut entropy: [u8; 32],
    _accel: &B,
) -> Result<(MigrationStatement, MigrationZkProof), MigrateError> {
    let result = (|| {
        if !witness.matches_commitment(&request.legacy) {
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let scalar = witness
            .normalize_spending_scalar(&request.legacy)
            .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?;
        let statement = MigrationStatement {
            legacy_commitment: request.legacy,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: scalar.compute_nullifier(&request.domain),
            witness_anchor: [0; 4],
        };
        let circuit = crate::ownership::build(&statement, scalar.as_le_bytes());
        if circuit
            .outputs
            .iter()
            .any(|&w| circuit.nodes[w].value != ZERO)
        {
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let bytes = statement.to_transcript_bytes();
        entropy = cshake256_framed_32(
            b"QSAG.MIGRATE.HEDGE.V4",
            &[&entropy, scalar.as_le_bytes(), &bytes],
        );
        let mut all_views = Vec::with_capacity(MIT_REPETITIONS);
        let mut roots = Vec::with_capacity(MIT_REPETITIONS * 32);
        for rep in 0..MIT_REPETITIONS {
            let views = simulate(&circuit, seeds(&entropy, &bytes, rep));
            let commits = core::array::from_fn(|p| commit(rep, p, &views[p]));
            roots.extend_from_slice(&rep_root(
                rep,
                &commits,
                core::array::from_fn(|p| views[p].outputs.as_slice()),
            ));
            all_views.push((views, commits));
        }
        let root = cshake256_framed_32(b"QSAG.MIGRATE.ROOT.V3", &[&roots]);
        let mut t = transcript(&statement, &root);
        let es = challenges(&mut t);
        let mut repetitions = Vec::with_capacity(MIT_REPETITIONS);
        for ((mut views, commits), &e) in all_views.into_iter().zip(&es) {
            let e_idx = e as usize;
            let hidden = (e_idx + 2) % 3;
            let hidden_outputs = core::mem::take(&mut views[hidden].outputs);
            repetitions.push(OpenedRepetitionView {
                opened_e: e,
                pair: [views[e_idx].clone(), views[(e_idx + 1) % 3].clone()],
                hidden_party_commit: commits[hidden],
                hidden_outputs,
            });
        }
        Ok((
            statement,
            MigrationZkProof {
                views_merkle_root: root,
                repetitions,
            },
        ))
    })();
    ct_zeroize_bytes(&mut entropy);
    result
}

fn replay(c: &Circuit, rep: usize, view: &OpenedRepetitionView) -> Result<(), MigrateError> {
    let e = view.opened_e as usize;
    let mut tapes = view.pair.each_ref().map(|v| Tape::new(&v.seed));
    let mut inputs = view.pair.each_ref().map(|v| v.inputs.as_slice());
    let mut products = view.pair.each_ref().map(|v| v.products.as_slice());
    let mut wires: [Wires; 2] = core::array::from_fn(|_| Wires(Vec::with_capacity(c.nodes.len())));
    for (gate_index, node) in c.nodes.iter().enumerate() {
        let d = node.domain;
        let values = match node.op {
            Op::Input => {
                let mut values = [ZERO; 2];
                for (j, v) in values.iter_mut().enumerate() {
                    *v = take(&mut inputs[j], d)?;
                    if (e + j) % 3 != 2 && *v != tapes[j].sample(d) {
                        return Err(MigrateError::MalformedProofStructure);
                    }
                }
                values
            }
            Op::Mul(a, b) => {
                let masks = [tapes[0].sample(d), tapes[1].sample(d)];
                let claimed = take(&mut products[0], d)?;
                let next = take(&mut products[1], d)?;
                let actual = gate(
                    d,
                    [wires[0].0[a], wires[1].0[a]],
                    [wires[0].0[b], wires[1].0[b]],
                    masks,
                );
                if claimed != actual {
                    return Err(MigrateError::OpenedPartyGateFailed {
                        rep,
                        gate: gate_index,
                    });
                }
                [claimed, next]
            }
            _ => core::array::from_fn(|j| local(node, (e + j) % 3, &wires[j].0)),
        };
        for (w, v) in wires.iter_mut().zip(values) {
            w.0.push(v);
        }
    }
    if inputs.iter().chain(&products).any(|s| !s.is_empty()) {
        return Err(MigrateError::MalformedProofStructure);
    }
    let mut outputs = view.pair.each_ref().map(|v| v.outputs.as_slice());
    let mut hidden = view.hidden_outputs.as_slice();
    for &w in &c.outputs {
        let d = c.nodes[w].domain;
        let a = take(&mut outputs[0], d)?;
        let b = take(&mut outputs[1], d)?;
        let h = take(&mut hidden, d)?;
        if a != wires[0].0[w] || b != wires[1].0[w] || d.add(d.add(a, b), h) != ZERO {
            return Err(MigrateError::PublicOutputShareMismatch);
        }
    }
    if !hidden.is_empty() || outputs.iter().any(|s| !s.is_empty()) {
        return Err(MigrateError::MalformedProofStructure);
    }
    Ok(())
}

pub fn verify_migration_proof(
    statement: &MigrationStatement,
    proof: &MigrationZkProof,
    expected_domain: &[u8; 32],
    expected_epoch: u64,
) -> Result<(), MigrateError> {
    if &statement.migration_domain != expected_domain || statement.epoch_anchor != expected_epoch {
        return Err(MigrateError::SessionMismatch);
    }
    if proof.repetitions.len() != MIT_REPETITIONS
        || statement.witness_anchor != [0; 4]
        || statement
            .migration_nullifier
            .iter()
            .any(|&v| v >= GOLDILOCKS_PRIME)
    {
        return Err(MigrateError::MalformedProofStructure);
    }
    let mut t = transcript(statement, &proof.views_merkle_root);
    let es = challenges(&mut t);
    // Authenticate both openings and all output shares before any gate replay.
    let mut roots = Vec::with_capacity(MIT_REPETITIONS * 32);
    for (rep, (view, &e)) in proof.repetitions.iter().zip(&es).enumerate() {
        if view.opened_e != e {
            return Err(MigrateError::MalformedProofStructure);
        }
        let e = e as usize;
        let mut commits = [[0; 32]; 3];
        commits[e] = commit(rep, e, &view.pair[0]);
        commits[(e + 1) % 3] = commit(rep, (e + 1) % 3, &view.pair[1]);
        commits[(e + 2) % 3] = view.hidden_party_commit;
        let mut outs = [&[][..]; 3];
        outs[e] = &view.pair[0].outputs;
        outs[(e + 1) % 3] = &view.pair[1].outputs;
        outs[(e + 2) % 3] = &view.hidden_outputs;
        roots.extend_from_slice(&rep_root(rep, &commits, outs));
    }
    if cshake256_framed_32(b"QSAG.MIGRATE.ROOT.V3", &[&roots]) != proof.views_merkle_root {
        return Err(MigrateError::ViewsMerkleRootMismatch);
    }
    let circuit = crate::ownership::build(statement, &[0; 32]);
    for (rep, view) in proof.repetitions.iter().enumerate() {
        replay(&circuit, rep, view)?;
    }
    Ok(())
}

impl core::fmt::Display for MigrateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for MigrateError {}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::circuit::Builder;
    use qsag_accel::CpuReferenceBackend;
    use qsag_addr::{KeyIdentityKind, WitnessSuiteTag};
    pub(crate) fn request(legacy: LegacyCommitmentKind) -> MigrationRequest {
        MigrationRequest {
            legacy,
            target: QsagAddress::from_pubkey_poseidon2(
                "qsp",
                WitnessSuiteTag::MlDsa65,
                KeyIdentityKind::SingleOrThreshold,
                b"destination",
            )
            .unwrap(),
            epoch: 19,
            domain: [23; 32],
        }
    }
    #[test]
    fn buffered_tapes_and_canonical_encodings() {
        let seed = [93; 32];
        let mut tape = Tape::new(&seed);
        let mut stream = Shake256::new();
        stream.absorb(b"QSAG.MIGRATE.TAPE.V3");
        stream.absorb(&seed);
        stream.finalize(0x1f);
        for _ in 0..3 {
            let mut block = [0; 8];
            stream.squeeze(&mut block);
            let bits = u64::from_le_bytes(block);
            for i in 0..64 {
                assert_eq!(tape.sample(Domain::Bit), [(bits >> i) & 1, 0, 0, 0]);
                if i == 17 {
                    stream.squeeze(&mut block);
                    let gold = u64::from_le_bytes(block);
                    assert!(gold < GOLDILOCKS_PRIME);
                    assert_eq!(tape.sample(Domain::Gold), [gold, 0, 0, 0]);
                }
            }
        }
        for d in [Domain::Bit, Domain::Gold, Domain::Secp, Domain::Ed] {
            let last = crate::scalar::sub(d.modulus(), [1, 0, 0, 0], d.modulus());
            for value in [ZERO, last] {
                let mut bytes = Vec::new();
                put(&mut bytes, d, value);
                let mut input = bytes.as_slice();
                assert_eq!(take(&mut input, d), Ok(value));
                assert!(input.is_empty());
                let mut short = &bytes[..bytes.len() - 1];
                assert!(take(&mut short, d).is_err());
            }
            let bytes = crate::scalar::encode(d.modulus());
            let mut input = &bytes[..d.width().div_ceil(8)];
            assert!(take(&mut input, d).is_err());
        }
    }

    #[test]
    fn inverse_witnesses_are_constrained_in_every_opening() {
        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            let c = Builder::default();
            let bit = c.input(1);
            let a = c.scale(c.lift(bit, d), 7);
            let inv = c.inverse(a);
            let mut circuit = c.finish();
            for valid in [true, false] {
                if !valid {
                    circuit.nodes[inv].value = ZERO;
                }
                let views = simulate(&circuit, [[11; 32], [12; 32], [13; 32]]);
                for e in 0..3 {
                    let opening = OpenedRepetitionView {
                        opened_e: e as u8,
                        pair: [views[e].clone(), views[(e + 1) % 3].clone()],
                        hidden_party_commit: [0; 32],
                        hidden_outputs: views[(e + 2) % 3].outputs.clone(),
                    };
                    assert_eq!(replay(&circuit, 0, &opening).is_ok(), valid);
                }
            }
        }
    }

    #[test]
    fn mit_repetitions_achieves_256bit_classical_and_128bit_qrom_grover_soundness() {
        assert_eq!(MIT_REPETITIONS, 438);
        // Exact integer witness: `8 * 3^73 > 13 * 2^115` and `13^3 = 2197 > 2048 = 4 * 8^3`,
        // implying `3^219 > 2^219 * 2^128` (QROM Grover `< 2^-128`) and `3^438 > 2^438 * 2^256`.
        let lhs = 8u128 * 3u128.pow(73);
        let rhs = 13u128 * (1u128 << 115);
        assert!(lhs > rhs);
        assert!(13u128.pow(3) > 4 * 8u128.pow(3));
    }

    #[test]
    fn every_domain_and_ordered_pair_checks_exact_residuals() {
        let c = Builder::default();
        let a = c.input(1);
        let b = c.input(0);
        for d in [Domain::Bit, Domain::Gold, Domain::Secp, Domain::Ed] {
            let aa = if d == Domain::Bit { a } else { c.lift(a, d) };
            let bb = if d == Domain::Bit { b } else { c.lift(b, d) };
            c.equal(c.mul(aa, aa), aa);
            c.equal(c.mul(aa, bb), bb);
            if d != Domain::Bit {
                let bits = c.bits(c.sub(bb, aa));
                let packed = c.pack(&bits, d);
                c.equal(packed, c.sub(bb, aa));
            }
        }
        let circuit = c.finish();
        let views = simulate(&circuit, [[1; 32], [2; 32], [3; 32]]);
        for (e, _) in views.iter().enumerate() {
            let opening = OpenedRepetitionView {
                opened_e: e as u8,
                pair: [views[e].clone(), views[(e + 1) % 3].clone()],
                hidden_party_commit: [0; 32],
                hidden_outputs: views[(e + 2) % 3].outputs.clone(),
            };
            assert_eq!(replay(&circuit, 0, &opening), Ok(()));
            let mut changed = opening.clone();
            changed.pair[0].products[0] ^= 1;
            assert!(replay(&circuit, 0, &changed).is_err());
            let mut changed = opening;
            changed.pair[1].products[0] ^= 1;
            assert!(replay(&circuit, 0, &changed).is_err());
        }
    }
    #[test]
    fn complete_ownership_proofs_all_modes_and_tampering() {
        let mut key = [0; 32];
        key[31] = 1;
        let witness = LegacyOwnershipWitness::from_raw_secret(key);
        let modes = [
            witness.compute_bitcoin_hash160().unwrap(),
            witness.compute_taproot_tweaked_xonly().unwrap(),
            witness.compute_ethereum_keccak20().unwrap(),
            witness.compute_slip0010_commitment(),
        ];
        for kind in modes {
            let (statement, mut proof) = prove_migration_in_domain(
                &witness,
                request(kind),
                [31; 32],
                &CpuReferenceBackend::new(),
            )
            .unwrap();
            assert_eq!(
                verify_migration_proof(
                    &statement,
                    &proof,
                    &statement.migration_domain,
                    statement.epoch_anchor
                ),
                Ok(())
            );
            assert_eq!(
                verify_migration_proof(&statement, &proof, &[0xff; 32], statement.epoch_anchor),
                Err(MigrateError::SessionMismatch)
            );
            assert_eq!(
                verify_migration_proof(
                    &statement,
                    &proof,
                    &statement.migration_domain,
                    statement.epoch_anchor.wrapping_add(1)
                ),
                Err(MigrateError::SessionMismatch)
            );
            let mut changed = statement.clone();
            changed.target_pq_address.commitment_256[0] ^= 1;
            assert!(
                verify_migration_proof(
                    &changed,
                    &proof,
                    &changed.migration_domain,
                    changed.epoch_anchor
                )
                .is_err()
            );
            let mut changed = statement.clone();
            changed.migration_domain[0] ^= 1;
            assert!(
                verify_migration_proof(
                    &changed,
                    &proof,
                    &changed.migration_domain,
                    changed.epoch_anchor
                )
                .is_err()
            );
            let mut changed = statement.clone();
            changed.migration_nullifier[0] ^= 1;
            assert!(
                verify_migration_proof(
                    &changed,
                    &proof,
                    &changed.migration_domain,
                    changed.epoch_anchor
                )
                .is_err()
            );
            let mut changed = statement.clone();
            changed.epoch_anchor += 1;
            assert!(
                verify_migration_proof(
                    &changed,
                    &proof,
                    &changed.migration_domain,
                    changed.epoch_anchor
                )
                .is_err()
            );
            for index in [0, 1] {
                proof.repetitions[0].pair[index].products[0] ^= 1;
                assert!(
                    verify_migration_proof(
                        &statement,
                        &proof,
                        &statement.migration_domain,
                        statement.epoch_anchor
                    )
                    .is_err()
                );
                proof.repetitions[0].pair[index].products[0] ^= 1;
            }
            proof.repetitions[0].hidden_outputs[0] ^= 1;
            assert!(
                verify_migration_proof(
                    &statement,
                    &proof,
                    &statement.migration_domain,
                    statement.epoch_anchor
                )
                .is_err()
            );
            proof.repetitions[0].hidden_outputs[0] ^= 1;
            let other = LegacyOwnershipWitness::from_raw_secret([3; 32]);
            assert!(
                prove_migration_in_domain(
                    &other,
                    request(kind),
                    [4; 32],
                    &CpuReferenceBackend::new()
                )
                .is_err()
            );
            proof.repetitions.pop();
            assert!(
                verify_migration_proof(
                    &statement,
                    &proof,
                    &statement.migration_domain,
                    statement.epoch_anchor
                )
                .is_err()
            );
        }
    }
}
