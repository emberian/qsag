//! Authenticated public boundary for the private quorum transition core.
//! Enrollment is trusted: provision independent custodian keys and a WAL-authority
//! key. A receipt MAC attests the authority's durable commit; this module does no IO.
use crate::keccak::Shake256Sponge;
use crate::tower::ct_eq_bytes32;
use crate::pants_and_quorum_guards::{BeltQuorumCore, BeltAuthorizationGrant, BeltQuorumPhase, PantsGuardError};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeltAuthError {
    Core(PantsGuardError),
    CustodianOutOfRange,
    InvalidCustodianTag,
    InvalidWalReceipt,
}

const fn encode_epoch(epoch: u64) -> [u8; 8] {
    [epoch as u8, (epoch >> 8) as u8, (epoch >> 16) as u8, (epoch >> 24) as u8,
     (epoch >> 32) as u8, (epoch >> 40) as u8, (epoch >> 48) as u8, (epoch >> 56) as u8]
}

/// Fixed-width encoding with separate domains for acknowledgments and receipts.
pub fn custodian_ack_tag(key: &[u8; 32], guard_key_commit: &[u8; 32], epoch: u64,
    msg_tag: &[u8; 32], custodian_id: u8) -> [u8; 32] {
    let mut sponge = Shake256Sponge::new_shake256();
    sponge.absorb(b"QSAG.BELT.ACK.v1");
    sponge.absorb(key);
    sponge.absorb(guard_key_commit);
    sponge.absorb(&encode_epoch(epoch));
    sponge.absorb(msg_tag);
    sponge.absorb(&[custodian_id]);
    let mut out = [0; 32];
    sponge.squeeze(&mut out);
    out
}

pub fn wal_receipt_tag(key: &[u8; 32], guard_key_commit: &[u8; 32], epoch: u64,
    msg_tag: &[u8; 32], receipt_digest: &[u8; 32]) -> [u8; 32] {
    let mut sponge = Shake256Sponge::new_shake256();
    sponge.absorb(b"QSAG.BELT.WAL.v1");
    sponge.absorb(key);
    sponge.absorb(guard_key_commit);
    sponge.absorb(&encode_epoch(epoch));
    sponge.absorb(msg_tag);
    sponge.absorb(receipt_digest);
    let mut out = [0; 32];
    sponge.squeeze(&mut out);
    out
}

pub enum BeltQuorumStepInput {
    ProposeOrRetryEpoch { proposed_epoch: u64, msg_tag: [u8; 32], receipt_digest: [u8; 32], receipt_tag: [u8; 32] },
    RecordCustodianAck { ack_epoch: u64, ack_msg_tag: [u8; 32], custodian_id: u8, auth_tag: [u8; 32] },
    AuthorizeShares { req_epoch: u64, req_msg_tag: [u8; 32] },
}
pub enum BeltQuorumStepOutput {
    EpochBound,
    AckRecorded(u32),
    SharesAuthorized(BeltAuthorizationGrant),
}

/// Affine guard. Neither the core state nor verification keys are publicly mutable.
/// Acknowledgments are unique within the currently bound epoch/message.
pub struct VerifiedBeltQuorumGuard {
    inner: BeltQuorumCore,
    guard_key_commit: [u8; 32],
    custodian_keys: [[u8; 32]; 64],
    wal_key: [u8; 32],
    ack_bitmap: u64,
}
impl VerifiedBeltQuorumGuard {
    pub fn new_validated(n: u32, t: u32, f: u32, q: u32, global_liveness: bool,
        initial_next_epoch: u64, max_jump_window: u64, guard_key_commit: [u8; 32],
        custodian_keys: [[u8; 32]; 64], wal_key: [u8; 32]) -> Result<Self, BeltAuthError> {
        if n > 64 { return Err(BeltAuthError::Core(PantsGuardError::InvalidBeltQuorumConfig)); }
        match BeltQuorumCore::new_validated(n, t, f, q, global_liveness, initial_next_epoch, max_jump_window) {
            Ok(inner) => Ok(Self { inner, guard_key_commit, custodian_keys, wal_key, ack_bitmap: 0 }),
            Err(e) => Err(BeltAuthError::Core(e)),
        }
    }
    pub const fn ack_count(&self) -> u32 { self.inner.ack_count() }
    pub const fn ack_bitmap(&self) -> u64 { self.ack_bitmap }
    pub const fn n(&self) -> u32 { self.inner.n() }
    pub const fn q(&self) -> u32 { self.inner.q() }
    pub const fn next_epoch(&self) -> u64 { self.inner.next_epoch() }
    pub const fn phase(&self) -> BeltQuorumPhase { self.inner.phase() }
    pub const fn is_poisoned(&self) -> bool { self.inner.is_poisoned() }
    pub const fn guard_key_commit(&self) -> [u8; 32] { self.guard_key_commit }

    pub fn propose_or_retry_epoch(mut self, epoch: u64, msg: [u8; 32],
        receipt_digest: [u8; 32], receipt_tag: [u8; 32]) -> (Self, Result<(), BeltAuthError>) {
        let expected = wal_receipt_tag(&self.wal_key, &self.guard_key_commit, epoch, &msg, &receipt_digest);
        let valid = ct_eq_bytes32(&expected, &receipt_tag);
        let same = if self.inner.has_bound_epoch() {
            if self.inner.bound_epoch() == epoch { true } else { false }
        } else { false };
        let (inner, result) = self.inner.propose_or_retry_epoch(epoch, msg, valid);
        self.inner = inner;
        let succeeded = match result { Ok(()) => true, Err(_) => false };
        if self.inner.is_poisoned() || (!same && succeeded) { self.ack_bitmap = 0; }
        if !valid { return (self, Err(BeltAuthError::InvalidWalReceipt)); }
        match result { Ok(()) => (self, Ok(())), Err(e) => (self, Err(BeltAuthError::Core(e))) }
    }
    pub fn record_custodian_ack(mut self, epoch: u64, msg: [u8; 32], custodian_id: u8,
        auth_tag: [u8; 32]) -> (Self, Result<u32, BeltAuthError>) {
        if custodian_id as usize >= self.inner.n() as usize || custodian_id >= 64 {
            return (self, Err(BeltAuthError::CustodianOutOfRange));
        }
        let expected = custodian_ack_tag(&self.custodian_keys[custodian_id as usize],
            &self.guard_key_commit, epoch, &msg, custodian_id);
        if !ct_eq_bytes32(&expected, &auth_tag) { return (self, Err(BeltAuthError::InvalidCustodianTag)); }
        // Check the binding even on duplicates; a valid MAC for another epoch is not an ack here.
        if self.inner.is_poisoned() { return (self, Err(BeltAuthError::Core(PantsGuardError::BeltGuardPoisoned))); }
        if !self.inner.has_bound_epoch() { return (self, Err(BeltAuthError::Core(PantsGuardError::NoEpochBound))); }
        if epoch != self.inner.bound_epoch() { return (self, Err(BeltAuthError::Core(PantsGuardError::EpochMismatch))); }
        if !ct_eq_bytes32(&msg, &self.inner.bound_msg_tag()) {
            let (inner, result) = self.inner.record_custodian_ack(epoch, msg);
            self.inner = inner;
            self.ack_bitmap = 0;
            return match result { Ok(n) => (self, Ok(n)), Err(e) => (self, Err(BeltAuthError::Core(e))) };
        }
        let bit = 1u64 << custodian_id;
        if self.ack_bitmap & bit != 0 { let count = self.inner.ack_count(); return (self, Ok(count)); }
        let (inner, result) = self.inner.record_custodian_ack(epoch, msg);
        self.inner = inner;
        match result {
            Ok(n) => { self.ack_bitmap |= bit; (self, Ok(n)) },
            Err(e) => { if self.inner.is_poisoned() { self.ack_bitmap = 0; } (self, Err(BeltAuthError::Core(e))) },
        }
    }
    pub fn authorize_shares(mut self, epoch: u64, msg: [u8; 32]) -> (Self, Result<BeltAuthorizationGrant, BeltAuthError>) {
        let (inner, result) = self.inner.authorize_shares(epoch, msg);
        self.inner = inner;
        if self.inner.is_poisoned() { self.ack_bitmap = 0; }
        match result { Ok(grant) => (self, Ok(grant)), Err(e) => (self, Err(BeltAuthError::Core(e))) }
    }
    pub fn step(self, input: BeltQuorumStepInput) -> (Self, Result<BeltQuorumStepOutput, BeltAuthError>) {
        match input {
            BeltQuorumStepInput::ProposeOrRetryEpoch { proposed_epoch, msg_tag, receipt_digest, receipt_tag } => {
                let (next, result) = self.propose_or_retry_epoch(proposed_epoch, msg_tag, receipt_digest, receipt_tag);
                match result { Ok(()) => (next, Ok(BeltQuorumStepOutput::EpochBound)), Err(e) => (next, Err(e)) }
            },
            BeltQuorumStepInput::RecordCustodianAck { ack_epoch, ack_msg_tag, custodian_id, auth_tag } => {
                let (next, result) = self.record_custodian_ack(ack_epoch, ack_msg_tag, custodian_id, auth_tag);
                match result { Ok(n) => (next, Ok(BeltQuorumStepOutput::AckRecorded(n))), Err(e) => (next, Err(e)) }
            },
            BeltQuorumStepInput::AuthorizeShares { req_epoch, req_msg_tag } => {
                let (next, result) = self.authorize_shares(req_epoch, req_msg_tag);
                match result { Ok(g) => (next, Ok(BeltQuorumStepOutput::SharesAuthorized(g))), Err(e) => (next, Err(e)) }
            },
        }
    }
}
