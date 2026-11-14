//! Session- and round-bound single-use guard for releasing an opening.
//!
//! Production opening rounds (the policy sigma opening, the quorum plane opening) end in the
//! same decision: every peer opening matches the commitment frozen before it, the opened lanes
//! XOR to zero, and the result belongs to the session, round and transcript this party is in.
//! The lanes are elements of GF(2^128) under addition only, so the decision does not depend on
//! the basis the caller multiplies in.
//!
//! [`ConsumingOpeningGuard2Lane`] folds the openings and makes that decision exactly once.
//! [`OpeningReleasePermit`] has private fields and no constructor other than an accepting
//! [`ConsumingOpeningGuard2Lane::verify_once`]. Recomputing each commitment from the opened
//! values is the caller's step; the guard compares the two digests in constant time.

use crate::tower::ct_eq_bytes32;

/// Proof that one opening round was accepted by its guard. Neither `Clone` nor `Copy`.
pub struct OpeningReleasePermit {
    session_id: [u8; 32],
    round_id: u64,
    openings: u64,
}

impl OpeningReleasePermit {
    pub const fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    pub const fn round_id(&self) -> u64 {
        self.round_id
    }

    /// Number of openings the accepted round folded.
    pub const fn openings(&self) -> u64 {
        self.openings
    }
}

/// One opening round of a provisioned session, round and transcript binding.
/// Neither `Clone` nor `Copy`; `verify_once` spends it whatever the outcome.
pub struct ConsumingOpeningGuard2Lane {
    session_id: [u8; 32],
    round_id: u64,
    binding: [u8; 32],
    expected_openings: u64,
    absorbed: u64,
    sum_lanes: [u128; 2],
    all_committed: bool,
    consumed: bool,
}

impl ConsumingOpeningGuard2Lane {
    pub const fn new(
        session_id: [u8; 32],
        round_id: u64,
        binding: [u8; 32],
        expected_openings: u64,
    ) -> Self {
        Self {
            session_id,
            round_id,
            binding,
            expected_openings,
            absorbed: 0,
            sum_lanes: [0, 0],
            all_committed: true,
            consumed: false,
        }
    }

    pub const fn is_consumed(&self) -> bool {
        self.consumed
    }

    pub const fn absorbed(&self) -> u64 {
        self.absorbed
    }

    /// Fold one opening: `commitment` is the digest frozen before the opening, `recomputed`
    /// the digest of the opened values, `lanes` the opened lanes. A spent guard ignores it.
    /// A count that would overflow can never equal the expected count again.
    pub fn absorb_opening(
        self,
        commitment: &[u8; 32],
        recomputed: &[u8; 32],
        lanes: [u128; 2],
    ) -> Self {
        if self.consumed {
            return self;
        }
        let committed = ct_eq_bytes32(commitment, recomputed);
        if self.absorbed == u64::MAX {
            return Self {
                session_id: self.session_id,
                round_id: self.round_id,
                binding: self.binding,
                expected_openings: self.expected_openings,
                absorbed: self.absorbed,
                sum_lanes: [self.sum_lanes[0] ^ lanes[0], self.sum_lanes[1] ^ lanes[1]],
                all_committed: false,
                consumed: false,
            };
        }
        Self {
            session_id: self.session_id,
            round_id: self.round_id,
            binding: self.binding,
            expected_openings: self.expected_openings,
            absorbed: self.absorbed + 1,
            sum_lanes: [self.sum_lanes[0] ^ lanes[0], self.sum_lanes[1] ^ lanes[1]],
            all_committed: self.all_committed && committed,
            consumed: false,
        }
    }

    /// The single release decision. Accepts only an unspent guard whose session, round and
    /// binding equal the request, that folded exactly the expected nonzero number of openings,
    /// every one of them matching its commitment, with both lane sums zero. The returned guard
    /// is spent and holds no lane sums.
    pub fn verify_once(
        self,
        session_id: &[u8; 32],
        round_id: u64,
        binding: &[u8; 32],
    ) -> (Self, Option<OpeningReleasePermit>) {
        let spent = Self {
            session_id: self.session_id,
            round_id: self.round_id,
            binding: self.binding,
            expected_openings: self.expected_openings,
            absorbed: self.absorbed,
            sum_lanes: [0, 0],
            all_committed: false,
            consumed: true,
        };
        if self.consumed {
            return (spent, None);
        }
        if !ct_eq_bytes32(&self.session_id, session_id) {
            return (spent, None);
        }
        if self.round_id != round_id {
            return (spent, None);
        }
        if !ct_eq_bytes32(&self.binding, binding) {
            return (spent, None);
        }
        if self.expected_openings == 0 {
            return (spent, None);
        }
        if self.absorbed != self.expected_openings {
            return (spent, None);
        }
        if !self.all_committed {
            return (spent, None);
        }
        if (self.sum_lanes[0] | self.sum_lanes[1]) != 0 {
            return (spent, None);
        }
        let permit = OpeningReleasePermit {
            session_id: self.session_id,
            round_id: self.round_id,
            openings: self.absorbed,
        };
        (spent, Some(permit))
    }
}
