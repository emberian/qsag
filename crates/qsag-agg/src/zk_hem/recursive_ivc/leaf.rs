//! JortsPoseidon2 signature and policy membership at a sparse u64 directory slot.
use super::super::{
    multisig::{self, MultisigParams, MultisigSigner, Policy, Slot},
    relation::{ConstraintSystem, Lc},
};
use super::*;
use alloc::collections::BTreeMap;
pub(super) const COMMITTEE: MultisigParams = MultisigParams {
    capacity: 64,
    depth: 8,
};
const REGISTRY_DOMAIN: usize = 0x524547;
fn address_leaf(addr: [F; 4]) -> Digest {
    let mut tr = Duplex::new();
    tr.frame(&mut Native::default(), b"IVC-REG-LEAF", &addr);
    core::array::from_fn(|i| tr.0[i])
}
/// A 64-level sparse directory keyed by shard ID. Policies use the threshold
/// and member-tree address checked by the Jorts multisignature relation.
pub struct IvcPolicyRegistry {
    pub(super) committee: MultisigParams,
    levels: Vec<BTreeMap<u64, Digest>>,
    defaults: Vec<Digest>,
}
impl IvcPolicyRegistry {
    pub const POLICY_DEPTH: usize = COMMITTEE.depth;
    /// Signature slots per default leaf. Multiple leaves can cover the entire member tree.
    pub const MAX_SIGNERS_PER_SHARD: usize = COMMITTEE.capacity;
    pub fn new(entries: &[(u64, Policy)]) -> Option<Self> {
        Self::with_committee(COMMITTEE, entries)
    }

    pub fn with_committee(committee: MultisigParams, entries: &[(u64, Policy)]) -> Option<Self> {
        if !committee.valid() || committee.depth > 8 {
            return None;
        }
        let mut leaves = BTreeMap::new();
        for (i, p) in entries {
            if p.depth() != committee.depth
                || leaves.insert(*i, address_leaf(p.address())).is_some()
            {
                return None;
            }
        }
        let mut levels = vec![leaves];
        let mut defaults = vec![[F::ZERO; 7]];
        for h in 0..64 {
            let prev = &levels[h];
            let default = defaults[h];
            let fold = |l: &Digest, r: &Digest| {
                crate::sponge::poseidon2_gl24_compress_merkle(
                    l,
                    r,
                    &[f(REGISTRY_DOMAIN as u64), f(h as u64)],
                )
            };
            let mut next = BTreeMap::new();
            for &idx in prev.keys() {
                next.entry(idx / 2).or_insert_with(|| {
                    fold(
                        prev.get(&(idx & !1)).unwrap_or(&default),
                        prev.get(&(idx | 1)).unwrap_or(&default),
                    )
                });
            }
            levels.push(next);
            defaults.push(fold(&default, &default));
        }
        Some(Self {
            committee,
            levels,
            defaults,
        })
    }
    pub fn root(&self) -> [u8; 32] {
        let root = self.levels[64].get(&0).unwrap_or(&self.defaults[64]);
        crate::sponge::limbs4_to_le_bytes32(core::array::from_fn(|i| root[i]))
    }
    fn path(&self, index: u64) -> [Digest; 64] {
        core::array::from_fn(|i| {
            *self.levels[i]
                .get(&((index >> i) ^ 1))
                .unwrap_or(&self.defaults[i])
        })
    }
}
pub struct IvcShard<'a> {
    pub shard_id: u64,
    pub policy: &'a Policy,
    pub signers: &'a [MultisigSigner],
}
fn signed<W: Base, B: Wide<W = W>>(b: &mut B, words: &[W]) -> [W; 4] {
    let mut tr = Duplex::new();
    let mut msg = words[..10].to_vec();
    msg.extend_from_slice(&words[23..STATEMENT_WORDS]);
    tr.frame(b, b"IVC-JORTS-MESSAGE", &msg);
    core::array::from_fn(|i| tr.0[i].clone())
}
pub fn ivc_signing_message(root: [u8; 32], shard_id: u64, message_digest: [u8; 32]) -> [u8; 32] {
    let stmt = IvcSubtreeStatement {
        policy_registry_root: root,
        shard_lo: shard_id,
        shard_hi: 0,
        total_signers: 0,
        shard_threshold: 0,
        signer_bitmap: [0; IVC_BITMAP_BYTES],
        message_digest,
    };
    crate::sponge::limbs4_to_le_bytes32(signed(&mut Native::default(), &stmt.public_inputs()))
}
pub(super) struct Witness {
    committee: MultisigParams,
    slots: Vec<Slot>,
    threshold: u32,
    address: [F; 4],
    path: [Digest; 64],
}
impl Witness {
    #[cfg(test)]
    pub(super) fn corrupt_chain(&mut self) {
        self.slots[0].corrupt_chain_for_test();
    }
    pub fn blank(committee: MultisigParams) -> Self {
        Self {
            committee,
            slots: vec![Slot::placeholder(committee.depth); committee.capacity],
            threshold: 1,
            address: [F::ZERO; 4],
            path: [[F::ZERO; 7]; 64],
        }
    }
    pub fn new(
        reg: &IvcPolicyRegistry,
        stmt: &IvcSubtreeStatement,
        s: &IvcShard<'_>,
    ) -> Option<Self> {
        Self::for_committee(reg, stmt, s, reg.committee)
    }
    pub(super) fn for_committee(
        reg: &IvcPolicyRegistry,
        stmt: &IvcSubtreeStatement,
        s: &IvcShard<'_>,
        committee: MultisigParams,
    ) -> Option<Self> {
        if committee.depth != reg.committee.depth {
            return None;
        }
        let message = ivc_signing_message(reg.root(), s.shard_id, stmt.message_digest);
        let address = s.policy.address();
        if reg.levels[0].get(&s.shard_id) != Some(&address_leaf(address)) {
            return None;
        }
        Some(Self {
            committee,
            slots: multisig::slots_for(committee, s.policy, &message, s.signers, false).ok()?,
            threshold: s.policy.threshold(),
            address,
            path: reg.path(s.shard_id),
        })
    }
}
pub(super) fn populate(
    cs: &mut ConstraintSystem,
    cfg: &IvcStepConfig,
    stmt: &IvcSubtreeStatement,
    w: &Witness,
) {
    let s: Vec<Lc> = stmt
        .public_inputs()
        .iter()
        .map(|&v| cs.public_input(v).into())
        .collect();
    let dummy =
        r1cs::Claim::from_acc(&r1cs::Acc::dummy(cfg.log_cells)).digest(&mut Native::default());
    let acc: [Lc; 7] = dummy.map(|v| cs.public_input(v).into());
    for (x, y) in acc.iter().zip(dummy) {
        cs.enforce_equal(x, &Lc::constant(y));
    }
    populate_signature(cs, &s, w);
}

pub(super) fn populate_signature(cs: &mut ConstraintSystem, s: &[Lc], w: &Witness) {
    for x in s[..8].iter().chain(&s[10..15]).chain(&s[23..]) {
        bits(cs, x, 32);
    }
    let bitmap: Vec<_> = s[15..23].iter().flat_map(|x| bits(cs, x, 32)).collect();
    tree::add64(
        cs,
        &s[8..10],
        &[Lc::constant(F::ONE), Lc::zero()],
        &s[10..12],
        false,
    );
    let addr = w.address.map(|v| Backend::alloc(cs, v));
    let mut tr = Duplex::new();
    tr.frame(cs, b"IVC-REG-LEAF", &addr);
    let mut cur: [Lc; 7] = core::array::from_fn(|i| tr.0[i].clone());
    let index_bits: Vec<_> = s[8..10].iter().flat_map(|x| bits(cs, x, 32)).collect();
    for (h, (bit, hash)) in index_bits.iter().zip(w.path).enumerate() {
        let sib = hash.map(|x| Backend::alloc(cs, x));
        let l = core::array::from_fn(|i| select(cs, bit, &sib[i], &cur[i]));
        let r = core::array::from_fn(|i| cur[i].plus(&sib[i]).minus(&l[i]));
        cur = compress(cs, REGISTRY_DOMAIN, h, &l, &r);
    }
    let pack = |v: &[Lc]| {
        v.iter()
            .enumerate()
            .fold(Lc::zero(), |a, (i, b)| a.plus(&b.scaled(f(1 << i))))
    };
    for (x, pair) in cur.iter().zip(s[..8].as_chunks::<2>().0) {
        let bs = bits_canonical_u64(cs, x);
        cs.enforce_equal(&pack(&bs[..32]), &pair[0]);
        cs.enforce_equal(&pack(&bs[32..]), &pair[1]);
    }
    let sig_words = signed(cs, s);
    let mut bytes: Vec<_> = sig_words
        .iter()
        .flat_map(|v| {
            bits_canonical_u64(cs, v)
                .as_chunks::<8>()
                .0
                .iter()
                .map(|c| pack(c))
                .collect::<Vec<_>>()
        })
        .collect();
    // MU_MESSAGE_OFFSET=79, giving two preceding zero bytes in the first
    // message-dependent seven-byte big-endian limb, and one trailing zero.
    bytes.splice(..0, [Lc::zero(), Lc::zero()]);
    bytes.push(Lc::zero());
    let mu: Vec<_> = bytes
        .as_chunks::<7>()
        .0
        .iter()
        .map(|c| c.iter().fold(Lc::zero(), |a, x| a.scaled(f(256)).plus(x)))
        .collect();
    let (count, indices, threshold) =
        multisig::check_slots(cs, w.committee, &addr, &mu, w.threshold, &w.slots, false);
    cs.enforce_equal(&threshold, &s[14]);
    let members = 1 << w.committee.depth;
    for bit in &bitmap[members..] {
        cs.enforce_zero(bit.clone());
    }
    let weight = bitmap.iter().fold(Lc::zero(), |sum, bit| sum.plus(bit));
    cs.enforce_equal(&weight, &count);
    // Strictly increasing active indices select distinct set bits. Equal
    // cardinalities then exclude every unselected bit.
    for (active, index) in indices {
        let mut level = bitmap[..members].to_vec();
        for bit in index {
            level = level
                .as_chunks::<2>()
                .0
                .iter()
                .map(|[lo, hi]| select(cs, &bit, hi, lo))
                .collect();
        }
        cs.enforce_mul(active, Lc::constant(F::ONE).minus(&level[0]), Lc::zero());
    }
    cs.enforce_equal(&count, &s[12]);
    cs.enforce_zero(s[13].clone());
}
