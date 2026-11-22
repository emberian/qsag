//! Offline attenuation with a constant-sum base-4 one-time signature.
//!
//! Each signature authenticates the token, audience, parent key, hop position, caveat and
//! next key. Its 128 digits sum to 192: moving forward on chains cannot authenticate a
//! different digest with that sum. The terminal key's seed is a private circuit witness,
//! so public ancestors and signatures do not authorize truncation. Seeds must be fresh,
//! uniformly random and never reused. Consuming the Rust value prevents accidental reuse;
//! it cannot prevent a malicious holder from retaining its original authority.
use super::*;

const CHAINS: usize = 128;
const TARGET_SUM: u64 = 192;
pub(super) const MINT_DOMAIN: u64 = 0x4341_504F_4D49_4E31;
const SECRET_DOMAIN: u64 = 0x4341_504F_5345_4331;
const CHAIN_DOMAIN: u64 = 0x4341_504F_4348_4E31;
const KEY_DOMAIN: u64 = 0x4341_504F_4B45_5931;
const HOP_DOMAIN: u64 = 0x4341_504F_484F_5031;

struct FreshSecret(Digest);
impl Drop for FreshSecret {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.0, F::ZERO);
    }
}

fn hash(words: &[F]) -> Digest {
    first4(sponge12_native(words))
}
fn hash_gadget(cs: &mut ConstraintSystem, words: &[Lc]) -> [Lc; 4] {
    first4_lc(&sponge12(cs, words))
}
fn chain(mut node: Digest, index: usize, from: u64, to: u64) -> Digest {
    for step in from..to {
        node = hash(&[
            node[0],
            node[1],
            node[2],
            node[3],
            f(CHAIN_DOMAIN),
            f(index as u64),
            f(step),
        ]);
    }
    node
}
fn secret_node(secret: &Digest, index: usize) -> Digest {
    hash(&[
        secret[0],
        secret[1],
        secret[2],
        secret[3],
        f(SECRET_DOMAIN),
        f(index as u64),
    ])
}
fn public_key(secret: &Digest) -> Digest {
    let mut endpoints = Vec::with_capacity(4 * CHAINS + 1);
    endpoints.push(f(KEY_DOMAIN));
    for i in 0..CHAINS {
        endpoints.extend(chain(secret_node(secret, i), i, 0, 3));
    }
    let pk = hash(&endpoints);
    qsag_asm::volatile_fill(&mut endpoints, F::ZERO);
    pk
}

#[derive(Clone)]
pub(super) struct SignedHop {
    next_pk: Digest,
    nonce: u32,
    signature: Vec<Digest>,
}
impl SignedHop {
    fn placeholder() -> Self {
        Self {
            next_pk: [F::ZERO; 4],
            nonce: 0,
            signature: vec![[F::ZERO; 4]; CHAINS],
        }
    }
}
impl Drop for SignedHop {
    fn drop(&mut self) {
        for node in &mut self.signature {
            qsag_asm::volatile_fill(node, F::ZERO);
        }
    }
}
#[derive(Clone)]
pub(super) struct DelegationSlot {
    pub(super) secret: Digest,
    pub(super) hops: Vec<SignedHop>,
}
impl Drop for DelegationSlot {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.secret, F::ZERO);
    }
}

/// An offline delegatable bearer. Deliberately not `Clone` or serializable: the current
/// one-time secret is consumed by attenuation and wiped on drop. Earlier signatures and
/// the root public key grant no authority without the current secret.
pub struct DelegatedBearerCapability {
    token_id: TokenId,
    audience: Digest,
    root_pk: Digest,
    current_pk: Digest,
    secret: Digest,
    caveats: Vec<CapCaveat>,
    hops: Vec<SignedHop>,
}
impl Drop for DelegatedBearerCapability {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.secret, F::ZERO);
        qsag_asm::volatile_fill(&mut self.token_id, F::ZERO);
    }
}
impl DelegatedBearerCapability {
    /// Create the initial capability. The issuer enrolls `mint_leaf()` once. `secret` is
    /// a fresh uniformly random four-limb seed, never used for another capability.
    pub fn issue(
        token_id: TokenId,
        audience: Digest,
        secret: Digest,
    ) -> Result<Self, CapabilityZkError> {
        let secret = FreshSecret(secret);
        if !is_usable_token_id(&token_id) {
            return Err(CapabilityZkError::SentinelTokenIdReserved);
        }
        let pk = public_key(&secret.0);
        Ok(Self {
            token_id,
            audience,
            root_pk: pk,
            current_pk: pk,
            secret: secret.0,
            caveats: Vec::new(),
            hops: Vec::new(),
        })
    }
    pub fn token_id(&self) -> &TokenId {
        &self.token_id
    }
    pub fn caveats(&self) -> &[CapCaveat] {
        &self.caveats
    }
    pub fn mint_leaf(&self) -> Digest {
        let mut words = Vec::new();
        words.extend(self.token_id);
        words.extend(self.audience);
        words.extend(self.root_pk);
        words.push(f(MINT_DOMAIN));
        hash(&words)
    }
    pub fn presentation_tag(&self, context: &[u8]) -> Digest {
        compute_presentation_tag(&self.current_pk, &self.token_id, &context_digest(context))
    }
    /// Add one conjunctive caveat without issuer contact. `next_secret` must be fresh
    /// randomness supplied by the delegator; transfer only the returned bearer to the
    /// delegate. The old secret is wiped before return, including on error.
    pub fn attenuate_offline(
        mut self,
        caveat: CapCaveat,
        next_secret: Digest,
    ) -> Result<Self, CapabilityZkError> {
        let next_secret = FreshSecret(next_secret);
        if self.hops.len() == MAX_CAP_HOPS {
            return Err(CapabilityZkError::TooManyCaveats);
        }
        let next_pk = public_key(&next_secret.0);
        if next_pk == self.current_pk
            || next_pk == self.root_pk
            || self.hops.iter().any(|h| h.next_pk == next_pk)
        {
            return Err(CapabilityZkError::InvalidTag);
        }
        let (kind, payload) = caveat.encode_words();
        let mut words = Vec::new();
        words.push(f(HOP_DOMAIN));
        words.extend(self.token_id);
        words.extend(self.audience);
        words.extend(self.current_pk);
        words.push(f(self.hops.len() as u64));
        words.push(f(kind));
        words.extend(payload);
        words.extend(next_pk);
        let mut digits = [0u64; CHAINS];
        let mut nonce = 0u32;
        loop {
            let mut msg = words.clone();
            msg.push(f(u64::from(nonce)));
            let digest = hash(&msg);
            for (i, d) in digits.iter_mut().enumerate() {
                *d = (digest[i / 32].to_canonical_u64() >> (2 * (i % 32))) & 3;
            }
            if digits.iter().sum::<u64>() == TARGET_SUM {
                break;
            }
            nonce = nonce.checked_add(1).ok_or(CapabilityZkError::InvalidTag)?;
        }
        let signature = digits
            .iter()
            .enumerate()
            .map(|(i, &d)| chain(secret_node(&self.secret, i), i, 0, d))
            .collect();
        qsag_asm::volatile_fill(&mut self.secret, F::ZERO);
        self.secret = next_secret.0;
        self.current_pk = next_pk;
        self.caveats.push(caveat);
        self.hops.push(SignedHop {
            next_pk,
            nonce,
            signature,
        });
        Ok(self)
    }
}

pub(super) fn secret_public_gadget(cs: &mut ConstraintSystem, secret: &Digest) -> [Lc; 4] {
    let sk = alloc4(cs, secret);
    let mut endpoints = vec![Lc::constant(f(KEY_DOMAIN))];
    for i in 0..CHAINS {
        let mut input = sk.to_vec();
        input.extend([Lc::constant(f(SECRET_DOMAIN)), Lc::constant(f(i as u64))]);
        let mut node = hash_gadget(cs, &input);
        for step in 0..3 {
            let mut input = node.to_vec();
            input.extend([
                Lc::constant(f(CHAIN_DOMAIN)),
                Lc::constant(f(i as u64)),
                Lc::constant(f(step)),
            ]);
            node = hash_gadget(cs, &input);
        }
        endpoints.extend(node);
    }
    hash_gadget(cs, &endpoints)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn hop_gadget(
    cs: &mut ConstraintSystem,
    active: &Lc,
    parent: &[Lc; 4],
    token: &[Lc; 4],
    audience: &[Lc; 4],
    kind: &Lc,
    payload: &[Lc; 4],
    hop: usize,
    witness: &SignedHop,
) -> [Lc; 4] {
    let next = alloc4(cs, &witness.next_pk);
    let nonce_bits = alloc_bits(cs, u64::from(witness.nonce), 32);
    let mut msg = vec![Lc::constant(f(HOP_DOMAIN))];
    msg.extend_from_slice(token);
    msg.extend_from_slice(audience);
    msg.extend_from_slice(parent);
    msg.push(Lc::constant(f(hop as u64)));
    msg.push(kind.clone());
    msg.extend_from_slice(payload);
    msg.extend_from_slice(&next);
    msg.push(pack_bits(&nonce_bits));
    let digest = hash_gadget(cs, &msg);
    let bits: Vec<Lc> = digest
        .iter()
        .flat_map(|v| canonical_bits_and_halves32(cs, v).0)
        .collect();
    let mut sum = Lc::zero();
    let mut endpoints = vec![Lc::constant(f(KEY_DOMAIN))];
    for (i, digit) in bits.as_chunks::<2>().0.iter().enumerate() {
        sum = sum.plus(&digit[0]).plus(&digit[1].scaled(f(2)));
        let mut node = alloc4(cs, &witness.signature[i]);
        // Apply the remaining steps d..3. Conditions are d == 0, d <= 1, d <= 2.
        let both: Lc = cs.mul(&digit[0], &digit[1]).into();
        let gates = [
            Lc::constant(F::ONE)
                .minus(&digit[0])
                .minus(&digit[1])
                .plus(&both),
            Lc::constant(F::ONE).minus(&digit[1]),
            Lc::constant(F::ONE).minus(&both),
        ];
        for (step, gate) in gates.iter().enumerate() {
            let mut input = node.to_vec();
            input.extend([
                Lc::constant(f(CHAIN_DOMAIN)),
                Lc::constant(f(i as u64)),
                Lc::constant(f(step as u64)),
            ]);
            let stepped = hash_gadget(cs, &input);
            node = select4(cs, gate, &stepped, &node);
        }
        endpoints.extend(node);
    }
    cs.enforce_mul(active.clone(), sum.plus_const(-f(TARGET_SUM)), Lc::zero());
    let recovered = hash_gadget(cs, &endpoints);
    for i in 0..4 {
        cs.enforce_mul(active.clone(), recovered[i].minus(&parent[i]), Lc::zero());
    }
    select4(cs, active, &next, parent)
}

/// Private opening data for a delegated capability. Only the initial mint leaf is enrolled.
pub struct DelegatedPresentationInput {
    pub capability: DelegatedBearerCapability,
    pub issuer_index: usize,
    pub issuer_siblings: Vec<Digest>,
    pub non_membership: RevocationNonMembershipWitness,
}
impl DelegatedPresentationInput {
    fn slot(&self, params: CapabilityParams) -> Result<CapSlot, CapabilityZkError> {
        let cap = &self.capability;
        if cap.hops.len() > params.max_hops
            || self.issuer_siblings.len() != params.issuer_depth
            || self.issuer_index >= 1usize << params.issuer_depth
            || self.non_membership.path_lo.len() != params.revocation_depth
            || self.non_membership.path_hi.len() != params.revocation_depth
            || self.non_membership.left_index >= (1usize << params.revocation_depth) - 1
        {
            return Err(CapabilityZkError::InvalidParams);
        }
        let mut slot = CapSlot::placeholder(params);
        slot.token_id = cap.token_id;
        slot.root_tag = cap.root_pk;
        slot.final_tag = cap.current_pk;
        for (h, caveat) in slot.hops.iter_mut().zip(&cap.caveats) {
            let (kind, payload) = caveat.encode_words();
            *h = HopSlot {
                active: true,
                kind,
                payload,
            };
        }
        slot.issuer_index = self.issuer_index;
        slot.issuer_siblings.clone_from(&self.issuer_siblings);
        slot.rev_left_index = self.non_membership.left_index;
        slot.revoked_lo = self.non_membership.revoked_lo;
        slot.revoked_hi = self.non_membership.revoked_hi;
        slot.path_lo.clone_from(&self.non_membership.path_lo);
        slot.path_hi.clone_from(&self.non_membership.path_hi);
        let mut hops = cap.hops.clone();
        hops.resize_with(params.max_hops, SignedHop::placeholder);
        slot.delegation = Some(DelegationSlot {
            secret: cap.secret,
            hops,
        });
        Ok(slot)
    }
}

/// Committed-mask presentation of offline delegation, including terminal-key possession
/// and all the registered mode's request, revocation and distinct-token checks.
/// It inherits the privacy and knowledge-soundness bounds of [`protocol::prove`].
pub struct DelegatedCapabilityRelation {
    inner: CapabilityRelation,
}
impl DelegatedCapabilityRelation {
    pub fn new(params: CapabilityParams) -> Result<Self, CapabilityZkError> {
        if !params.valid() {
            return Err(CapabilityZkError::InvalidParams);
        }
        let statement = CapabilityBatchStatement {
            issuer_root: [F::ZERO; 4],
            revocation_root: [F::ZERO; 4],
            revocation_epoch: 0,
            request: CapabilityRequest {
                audience: [F::ZERO; 4],
                resource: [F::ZERO; 4],
                actions: 0,
                amount: 0,
                now: 0,
            },
            presentation_tags: vec![[F::ZERO; 4]; params.batch_size],
        };
        let mut slots = vec![CapSlot::placeholder(params); params.batch_size];
        for slot in &mut slots {
            slot.delegation = Some(DelegationSlot {
                secret: [F::ZERO; 4],
                hops: vec![SignedHop::placeholder(); params.max_hops],
            });
        }
        let mut cs = ConstraintSystem::new();
        populate(&mut cs, params, &statement, b"", &slots);
        let (shape, mut z) = cs.finish_v2();
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        Ok(Self {
            inner: CapabilityRelation { params, shape },
        })
    }
    pub fn shape(&self) -> &Shape {
        &self.inner.shape
    }
    fn statement_bytes(&self, context: &[u8]) -> Vec<u8> {
        let mut bytes = self.inner.statement_bytes(context);
        // Distinct relation revision; no new textual domain label.
        bytes.extend_from_slice(&MINT_DOMAIN.to_le_bytes());
        bytes
    }
    pub fn prove(
        &self,
        statement: &CapabilityBatchStatement,
        inputs: &[DelegatedPresentationInput],
        context: &[u8],
        profile: Profile,
        seed: &[u8; 32],
    ) -> Result<ZkCapabilityBatchProof, CapabilityZkError> {
        if inputs.len() != self.inner.params.batch_size
            || statement.presentation_tags.len() != inputs.len()
        {
            return Err(CapabilityZkError::BatchLengthMismatch);
        }
        let slots = inputs
            .iter()
            .map(|i| i.slot(self.inner.params))
            .collect::<Result<Vec<_>, _>>()?;
        let mut cs = ConstraintSystem::witness_only();
        populate(&mut cs, self.inner.params, statement, context, &slots);
        let assignment = cs
            .finish_assignment(&self.inner.shape)
            .ok_or(CapabilityZkError::InvalidParams)?;
        let proof = v2::prove(
            &self.inner.shape,
            assignment,
            &self.statement_bytes(context),
            profile,
            seed,
        )
        .map_err(CapabilityZkError::Proof)?;
        Ok(ZkCapabilityBatchProof { proof })
    }
    pub fn verify(
        &self,
        statement: &CapabilityBatchStatement,
        context: &[u8],
        profile: Profile,
        proof: &ZkCapabilityBatchProof,
    ) -> bool {
        statement.presentation_tags.len() == self.inner.params.batch_size
            && v2::verify(
                &self.inner.shape,
                &public_inputs_vec(statement, context),
                &self.statement_bytes(context),
                profile,
                &proof.proof,
            )
    }
    pub fn decode(&self, bytes: &[u8], profile: Profile) -> Option<ZkCapabilityBatchProof> {
        ZkCapabilityBatchProof::from_bytes(bytes, &self.inner, profile)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    #[test]
    fn offline_two_hop_zk_and_adversarial_witnesses() {
        use std::time::Instant;
        let params = CapabilityParams {
            batch_size: 1,
            max_hops: 2,
            issuer_depth: 2,
            revocation_depth: 2,
        };
        let token = [f(10), f(11), f(12), f(13)];
        let audience = [f(21); 4];
        let cap =
            DelegatedBearerCapability::issue(token, audience, [f(101), f(102), f(103), f(104)])
                .unwrap();
        let issuer = CapabilityIssuerDirectory::new(2, &[cap.mint_leaf()]).unwrap();
        let root_pk = cap.root_pk;
        let start = Instant::now();
        let cap = cap
            .attenuate_offline(CapCaveat::Actions(3), [f(201), f(202), f(203), f(204)])
            .unwrap()
            .attenuate_offline(CapCaveat::MaxAmount(50), [f(301), f(302), f(303), f(304)])
            .unwrap();
        let delegate_ms = start.elapsed().as_secs_f64() * 1000.0;
        assert!(issuer.verify_opening(0, &cap.mint_leaf(), &issuer.opening(0).unwrap()));
        let rev = SortedRevocationTree::new(2, 7, &[]).unwrap();
        let statement = CapabilityBatchStatement {
            issuer_root: issuer.root(),
            revocation_root: rev.root(),
            revocation_epoch: 7,
            request: CapabilityRequest {
                audience,
                resource: [f(31); 4],
                actions: 1,
                amount: 25,
                now: 10,
            },
            presentation_tags: vec![cap.presentation_tag(b"offline test")],
        };
        let input = DelegatedPresentationInput {
            capability: cap,
            issuer_index: 0,
            issuer_siblings: issuer.opening(0).unwrap(),
            non_membership: rev.prove_non_membership(&token).unwrap(),
        };
        let relation = DelegatedCapabilityRelation::new(params).unwrap();
        let slot = input.slot(params).unwrap();
        let satisfied = |slot: &CapSlot, statement: &CapabilityBatchStatement| {
            let mut cs = ConstraintSystem::witness_only();
            populate(
                &mut cs,
                params,
                statement,
                b"offline test",
                core::slice::from_ref(slot),
            );
            let mut z = cs.finish_assignment(relation.shape()).unwrap();
            let ok = relation.shape().is_satisfied(&z);
            qsag_asm::volatile_fill(&mut z, F::ZERO);
            ok
        };
        assert!(satisfied(&slot, &statement));
        let mut bad = slot.clone();
        bad.hops[0].payload[1] = f(7);
        assert!(!satisfied(&bad, &statement));
        let mut bad = slot.clone();
        bad.delegation.as_mut().unwrap().hops[0].signature[9][0] += F::ONE;
        assert!(!satisfied(&bad, &statement));
        let mut bad = slot.clone();
        bad.delegation.as_mut().unwrap().secret[0] += F::ONE;
        assert!(!satisfied(&bad, &statement));
        let mut bad = slot.clone();
        // Strip all caveats and claim the public root key, retaining only the delegate secret.
        for hop in &mut bad.hops {
            hop.active = false;
            hop.kind = 0;
            hop.payload = [F::ZERO; 4];
        }
        bad.final_tag = root_pk;
        let mut forged = statement.clone();
        forged.presentation_tags[0] =
            compute_presentation_tag(&root_pk, &token, &context_digest(b"offline test"));
        assert!(!satisfied(&bad, &forged));
        let mut bad = slot.clone();
        bad.hops.swap(0, 1);
        bad.delegation.as_mut().unwrap().hops.swap(0, 1);
        assert!(!satisfied(&bad, &statement));
        let mut denied = statement.clone();
        denied.request.amount = 51;
        assert!(!satisfied(&slot, &denied));
        let start = Instant::now();
        let profile = Profile::TurboShakeJohnson400;
        let proof = relation
            .prove(&statement, &[input], b"offline test", profile, &[91; 32])
            .unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
        let start = Instant::now();
        assert!(relation.verify(&statement, b"offline test", profile, &proof));
        let verify_ms = start.elapsed().as_secs_f64() * 1000.0;
        assert!(!relation.verify(&statement, b"other context", profile, &proof));
        assert!(!relation.verify(&denied, b"offline test", profile, &proof));
        assert_eq!(relation.decode(&proof.to_bytes(), profile).unwrap(), proof);
        std::println!(
            "OFFLINE_WOTS_C hops=2 rows={} delegate_ms={delegate_ms:.2} prove_ms={prove_ms:.2} verify_ms={verify_ms:.2} bytes={}",
            relation.shape().num_rows(),
            proof.to_bytes().len()
        );
    }
}
