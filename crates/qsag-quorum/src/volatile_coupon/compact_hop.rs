//! Indexed Compact1122 capability hops. Each child consumes a distinct OTS key.
//!
//! The certified identity includes BOTH `root` and `leaves`. A capability's signed
//! statement binds that identity, its leaf index, and the complete child payload
//! (including any caveats). Verification does not infer policy semantics from the
//! payload. Callers must encode those semantics canonically.
//!
//! These are the existing durable `qsag-fts` keys, not volatile coupon secrets.
//! Their WAL remains mandatory. Provision independent keys and never recreate a
//! used key from a seed; a Merkle index cannot repair OTS seed reuse.

use super::{
    CouponError, HopBundle, HopBundleRoot, IndexedHopProof, Node, hash, verify_hop_membership,
};
use qsag_fts::{
    FrontierDpTable, FrontierFtsProfile, FrontierFtsPublicKey, FrontierFtsSignature,
    FrontierFtsSigningKey, verify_frontier_fts,
};
use std::collections::BTreeSet;

fn key_id(key: &FrontierFtsPublicKey) -> Result<Node, CouponError> {
    if key.profile != FrontierFtsProfile::Compact1122 || key.root.len() != 32 {
        return Err(CouponError::InvalidParameters);
    }
    Ok(hash(
        b"QSAG.CAPABILITY.COMPACT1122.KEY/v1",
        &[&key.pk_seed, &key.root],
    ))
}

fn statement(bundle: HopBundleRoot, index: usize, child: &[u8]) -> Node {
    hash(
        b"QSAG.CAPABILITY.COMPACT1122.CHILD/v1",
        &[
            &bundle.root,
            &(bundle.leaves as u64).to_be_bytes(),
            &(index as u64).to_be_bytes(),
            child,
        ],
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compact1122Hop {
    pub key: FrontierFtsPublicKey,
    pub membership: IndexedHopProof,
    pub signature: FrontierFtsSignature,
}

/// B independent one-time keys, with at most one attempted release at each index.
/// Failed signing attempts burn their index too, matching the underlying FTS latch.
pub struct Compact1122Bundle {
    bundle: HopBundle,
    keys: Vec<Option<FrontierFtsSigningKey>>,
    dp: FrontierDpTable,
}

impl Compact1122Bundle {
    pub fn new(keys: Vec<FrontierFtsSigningKey>) -> Result<Self, CouponError> {
        let mut ids = Vec::with_capacity(keys.len());
        let mut unique = BTreeSet::new();
        for key in &keys {
            let id = key_id(&key.pk)?;
            if key.profile != FrontierFtsProfile::Compact1122
                || key.uses_completed() != 0
                || key.uses_remaining() != 1
                || !unique.insert(id)
            {
                return Err(CouponError::InvalidParameters);
            }
            ids.push(id);
        }
        Ok(Self {
            bundle: HopBundle::new(&ids)?,
            keys: keys.into_iter().map(Some).collect(),
            dp: FrontierDpTable::build(FrontierFtsProfile::Compact1122),
        })
    }

    pub fn identity(&self) -> HopBundleRoot {
        self.bundle.identity()
    }

    pub fn sign_child(
        &mut self,
        index: usize,
        child: &[u8],
        hedging_nonce: &Node,
    ) -> Result<Compact1122Hop, CouponError> {
        let membership = self.bundle.proof(index)?;
        let msg = statement(self.identity(), index, child);
        let mut key = self.keys[index].take().ok_or(CouponError::MissingOrSpent)?;
        let signature = key
            .sign(&self.dp, &msg, hedging_nonce)
            .map_err(|_| CouponError::Certificate)?;
        let hop = Compact1122Hop {
            key: key.pk.clone(),
            membership,
            signature,
        };
        if !verify_compact1122_hop(self.identity(), child, &hop, &self.dp) {
            return Err(CouponError::Certificate);
        }
        Ok(hop)
    }
}

pub fn verify_compact1122_hop(
    certified: HopBundleRoot,
    child: &[u8],
    hop: &Compact1122Hop,
    dp: &FrontierDpTable,
) -> bool {
    let Ok(id) = key_id(&hop.key) else {
        return false;
    };
    verify_hop_membership(certified, &id, &hop.membership)
        && verify_frontier_fts(
            &hop.key,
            dp,
            &statement(certified, hop.membership.index, child),
            &hop.signature,
        )
        .is_ok()
}

/// Verify an offline fan-out, rejecting reuse even when two children are identical.
pub fn verify_compact1122_fanout(
    certified: HopBundleRoot,
    children: &[(&[u8], &Compact1122Hop)],
    dp: &FrontierDpTable,
) -> bool {
    if children.is_empty() || children.len() > certified.leaves {
        return false;
    }
    let mut indices = BTreeSet::new();
    let mut keys = BTreeSet::new();
    children.iter().all(|(child, hop)| {
        indices.insert(hop.membership.index)
            && key_id(&hop.key).is_ok_and(|key| keys.insert(key))
            && verify_compact1122_hop(certified, child, hop, dp)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_fts::{FrontierFtsError, FtsEpochWal};

    // Only a test persistence fixture. The production helper delegates to the
    // real FTS key's mandatory durable WAL and does not install this implementation.
    struct TestWal(u8);
    impl FtsEpochWal for TestWal {
        fn uses_completed(&self, _: &Node) -> Result<u8, FrontierFtsError> {
            Ok(self.0)
        }
        fn reserve_use(&mut self, _: &Node, next: u8) -> Result<(), FrontierFtsError> {
            if next != self.0 + 1 {
                return Err(FrontierFtsError::PersistenceFailed);
            }
            self.0 = next;
            Ok(())
        }
    }
    fn key(seed: u8) -> FrontierFtsSigningKey {
        FrontierFtsSigningKey::keygen(
            FrontierFtsProfile::Compact1122,
            [seed; 32],
            [seed.wrapping_add(1); 32],
            [0x71; 32],
            false,
            &qsag_accel::CpuReferenceBackend::new(),
        )
        .attach_wal(Box::new(TestWal(0)))
        .unwrap()
    }

    #[test]
    fn compact1122_indexed_fanout_rejects_reuse_relabel_and_caveat_stripping() {
        let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let mut bundle = Compact1122Bundle::new(vec![key(1), key(3), key(5)]).unwrap();
        let id = bundle.identity();
        let a = bundle
            .sign_child(0, b"child A; read only", &[9; 32])
            .unwrap();
        let b = bundle
            .sign_child(2, b"child B; expires tomorrow", &[10; 32])
            .unwrap();
        assert_eq!(
            a.signature.to_bytes(FrontierFtsProfile::Compact1122).len(),
            1122
        );
        assert!(verify_compact1122_fanout(
            id,
            &[
                (b"child A; read only", &a),
                (b"child B; expires tomorrow", &b)
            ],
            &dp
        ));
        assert!(matches!(
            bundle.sign_child(0, b"child C", &[11; 32]),
            Err(CouponError::MissingOrSpent)
        ));
        assert!(bundle.sign_child(3, b"padding", &[11; 32]).is_err());
        assert!(!verify_compact1122_fanout(
            id,
            &[(b"child A; read only", &a), (b"child A; read only", &a)],
            &dp
        ));
        assert!(!verify_compact1122_hop(id, b"child A", &a, &dp));
        let mut altered = a.clone();
        altered.membership.index = 1;
        assert!(!verify_compact1122_hop(
            id,
            b"child A; read only",
            &altered,
            &dp
        ));
        altered = a.clone();
        altered.membership.siblings.pop();
        assert!(!verify_compact1122_hop(
            id,
            b"child A; read only",
            &altered,
            &dp
        ));
        assert!(!verify_compact1122_hop(
            HopBundleRoot { leaves: 4, ..id },
            b"child A; read only",
            &a,
            &dp
        ));
        assert!(Compact1122Bundle::new(vec![key(1), key(1)]).is_err());
        assert!(Compact1122Bundle::new(vec![]).is_err());
    }
}
