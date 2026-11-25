//! Volatile all-of-subset coupon custody and authenticated commit-before-open.
//!
//! Uses the existing 256-bit, 128-chain WOTS+C primitive. `mint` runs the
//! dealerless binary-SPDZ chain sweep directly into locked slots and independently
//! rerandomizes each retained state. Its Baggy adapter certifies descriptors under
//! a `PORS+FP` root on any
//! [`qsag_core::baggy::BaggyEngine`], with an authenticated RAM-only Waistband option.
//! `compact_hop` supplies real Compact1122 indexed one-time capability bundles.
//!
//! Linux private anonymous mappings are locked, excluded from core dumps, wiped on
//! fork, and zeroized before unmapping. Failure of any OS protection fails closed.
//! macOS locks coupon mappings, sets zero-on-unmap and disables fork inheritance.
//! Process-wide protected minting is available on Linux.
//! PID binding also rejects fork-inherited handles. Live hypervisor RAM snapshots,
//! hibernation, privileged memory reads, and restored entropy sources are excluded.
//! Coupon opening and combination have no disk serialization, WAL or write path.
//! Minting has no deterministic remint input. Compact1122 keys separately retain
//! the durability requirements of the existing FTS implementation.
//!
//! The local transition implements `consume` in
//! `lean/Qsag/Custody/VolatileCoupon.lean`: authenticate and validate,
//! remove the entire slot, copy only the selected shares, erase every other share,
//! then return. An unauthenticated request cannot spend a slot. A valid malicious
//! initiator can still exhaust its authorized pool; network loss burns a coupon.
//! Fixed minting subsets require *every* member, irrespective of the parent t-of-n
//! configuration. Changing subsets requires minting a different coupon.
//!
//! The online signature is [`BaggySig`]: the coupon's public descriptor, the root's
//! [`RootSignature`] on it, and the coupon's WOTS+C opening on the message. It has a
//! canonical wire form ([`BaggySig::to_wire_bytes`]) and is checked by
//! [`baggy_verify`] against the root public key alone, with no state. Producing one
//! online touches no disk. It is not a bare [`RootSignature`] over the message: a verifier
//! of bare root signatures does not accept it, and it expires with its coupon.
//!
//! Thresholds: the root certificate has the threshold of the engine that signed it
//! (2-of-3 replicated, or `t`-of-`n` on [`qsag_core::spdz_sweep::SpdzSweepEngine`]);
//! a coupon needs every member of its fixed subset. Neither implies the other.

use crate::quorum_jorts::{WOTS_CHAINS, WOTS_STEPS, chain_walk, digits_at};
use alloc::{vec, vec::Vec};
use qsag_core::baggy::{
    BaggyParams, BaggyPublicKey, BaggySig as RootSignature, baggy_verify as verify_root,
};
use qsag_core::sponge::keccak::Cshake256Xof;
use qsag_core::wipe::ct_eq_bytes32;

#[cfg(any(test, feature = "std"))]
pub mod compact_hop;
#[cfg(all(
    any(test, feature = "std"),
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod custody;
#[cfg(all(
    any(test, feature = "std"),
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
pub use custody::*;

type Node = [u8; 32];
/// Locked bytes required for one all-of-S share table.
pub const SHARE_BYTES: usize = WOTS_CHAINS * WOTS_STEPS * 32;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CouponError {
    InvalidParameters,
    MemoryProtection,
    Entropy,
    Forked,
    Authentication,
    Certificate,
    Expired,
    InvalidCodeword,
    AlreadyInstalled,
    MissingOrSpent,
    InvalidOpenings,
    Clock,
    Staging,
}
impl core::fmt::Display for CouponError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "volatile coupon: {self:?}")
    }
}
impl core::error::Error for CouponError {}

fn framed(xof: &mut Cshake256Xof, value: &[u8]) {
    xof.absorb(&(value.len() as u64).to_be_bytes());
    xof.absorb(value);
}
fn hash(domain: &[u8], parts: &[&[u8]]) -> Node {
    let mut xof = Cshake256Xof::new(domain);
    for part in parts {
        framed(&mut xof, part);
    }
    let mut out = [0; 32];
    xof.squeeze(&mut out);
    out
}

/// All public parameters of ONE all-of-S coupon. `members` is sorted and distinct.
/// The leaf number is a domain separator, not an incrementing persistent counter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CouponDescriptor {
    pub parent: BaggyPublicKey,
    pub threshold: usize,
    pub parties: usize,
    pub members: Vec<u32>,
    pub pk_seed: Node,
    pub leaf: u64,
    pub chain_ends: Vec<Node>,
    pub expires_at: u64,
}
impl CouponDescriptor {
    pub fn validate(&self) -> Result<(), CouponError> {
        if self.threshold < 2
            || self.threshold > self.parties
            || self.members.len() != self.threshold
            || self.members.windows(2).any(|w| w[0] >= w[1])
            || self
                .members
                .iter()
                .any(|&p| u64::from(p) >= self.parties as u64)
            || self.chain_ends.len() != WOTS_CHAINS
        {
            return Err(CouponError::InvalidParameters);
        }
        Ok(())
    }
    /// Injectively framed, domain-separated statement to certify during minting.
    /// The initiator request binds its hash, hence pk, S, policy, expiry and coupon ID.
    pub fn certificate_message(&self) -> Result<Vec<u8>, CouponError> {
        self.validate()?;
        let mut out = Vec::new();
        out.extend_from_slice(b"QSAG.VOLATILE.WOTSC128.CERT/v1");
        out.extend_from_slice(&self.parent.pk_seed);
        out.extend_from_slice(&self.parent.pk_root);
        out.extend_from_slice(&(self.threshold as u64).to_be_bytes());
        out.extend_from_slice(&(self.parties as u64).to_be_bytes());
        for p in &self.members {
            out.extend_from_slice(&p.to_be_bytes());
        }
        out.extend_from_slice(&self.pk_seed);
        out.extend_from_slice(&self.leaf.to_be_bytes());
        out.extend_from_slice(&self.expires_at.to_be_bytes());
        for tip in &self.chain_ends {
            out.extend_from_slice(tip);
        }
        Ok(out)
    }
    pub fn id(&self) -> Result<Node, CouponError> {
        Ok(hash(
            b"QSAG.VOLATILE.COUPON_ID/v1",
            &[&self.certificate_message()?],
        ))
    }
}

/// Only a successful concrete Baggy verification constructs this enrollment token.
#[derive(Clone)]
pub struct CertifiedCoupon {
    descriptor: CouponDescriptor,
    certificate: RootSignature,
}
impl CertifiedCoupon {
    pub fn verify(
        parent: &BaggyPublicKey,
        params: &BaggyParams,
        descriptor: CouponDescriptor,
        certificate: RootSignature,
    ) -> Result<Self, CouponError> {
        if &descriptor.parent != parent
            || !verify_root(
                params,
                parent,
                &descriptor.certificate_message()?,
                &certificate,
            )
        {
            return Err(CouponError::Certificate);
        }
        Ok(Self {
            descriptor,
            certificate,
        })
    }
    pub fn descriptor(&self) -> &CouponDescriptor {
        &self.descriptor
    }
}

#[derive(Clone, Debug)]
pub struct SignRequest {
    pub coupon_id: Node,
    pub message: Vec<u8>,
    pub counter: u32,
    pub initiator_mac: Node,
}
impl SignRequest {
    pub fn message_hash(coupon_id: &Node, message: &[u8]) -> Node {
        hash(b"QSAG.VOLATILE.MESSAGE/v1", &[coupon_id, message])
    }
}

/// The stateless online signature: a certified coupon and its one-time opening on the
/// message. See the module documentation.
#[derive(Clone)]
pub struct BaggySig {
    pub coupon: CertifiedCoupon,
    pub counter: u32,
    pub nodes: Vec<Node>,
}

impl BaggySig {
    /// `be16(threshold) || be16(parties) || members (be32 each) || pk_seed || be64(leaf)
    /// || be64(expires_at) || chain ends || be32(len) || root certificate || be32(counter)
    /// || nodes`. The parent key is not encoded: the verifier supplies the one it trusts.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, CouponError> {
        let d = &self.coupon.descriptor;
        d.validate()?;
        let (Ok(threshold), Ok(parties)) = (u16::try_from(d.threshold), u16::try_from(d.parties))
        else {
            return Err(CouponError::InvalidParameters);
        };
        if self.nodes.len() != WOTS_CHAINS {
            return Err(CouponError::InvalidOpenings);
        }
        let certificate = self.coupon.certificate.to_wire_bytes();
        let mut out = Vec::new();
        out.extend_from_slice(&threshold.to_be_bytes());
        out.extend_from_slice(&parties.to_be_bytes());
        for member in &d.members {
            out.extend_from_slice(&member.to_be_bytes());
        }
        out.extend_from_slice(&d.pk_seed);
        out.extend_from_slice(&d.leaf.to_be_bytes());
        out.extend_from_slice(&d.expires_at.to_be_bytes());
        out.extend_from_slice(d.chain_ends.as_flattened());
        out.extend_from_slice(&(certificate.len() as u32).to_be_bytes());
        out.extend_from_slice(&certificate);
        out.extend_from_slice(&self.counter.to_be_bytes());
        out.extend_from_slice(self.nodes.as_flattened());
        Ok(out)
    }

    /// Inverse of [`Self::to_wire_bytes`] for the root key `parent` under `params`. The
    /// whole input must be used, and the root certificate is verified here: a value of
    /// this type always carries a certificate that `parent` signed. The message is checked
    /// by [`baggy_verify`].
    pub fn from_wire_bytes(
        parent: &BaggyPublicKey,
        params: &BaggyParams,
        raw: &[u8],
    ) -> Result<Self, CouponError> {
        fn take<'a>(rest: &mut &'a [u8], n: usize) -> Result<&'a [u8], CouponError> {
            let (head, tail) = rest
                .split_at_checked(n)
                .ok_or(CouponError::InvalidParameters)?;
            *rest = tail;
            Ok(head)
        }
        fn be<const N: usize>(bytes: &[u8]) -> Result<[u8; N], CouponError> {
            bytes.try_into().map_err(|_| CouponError::InvalidParameters)
        }
        let mut rest = raw;
        let nodes = |bytes: &[u8]| bytes.as_chunks::<32>().0.to_vec();
        let threshold = usize::from(u16::from_be_bytes(be(take(&mut rest, 2)?)?));
        let parties = usize::from(u16::from_be_bytes(be(take(&mut rest, 2)?)?));
        let mut members = Vec::with_capacity(threshold);
        for _ in 0..threshold {
            members.push(u32::from_be_bytes(be(take(&mut rest, 4)?)?));
        }
        let pk_seed = be(take(&mut rest, 32)?)?;
        let leaf = u64::from_be_bytes(be(take(&mut rest, 8)?)?);
        let expires_at = u64::from_be_bytes(be(take(&mut rest, 8)?)?);
        let chain_ends = nodes(take(&mut rest, 32 * WOTS_CHAINS)?);
        let certificate_len = u32::from_be_bytes(be(take(&mut rest, 4)?)?) as usize;
        let certificate = RootSignature::from_wire_bytes(params, take(&mut rest, certificate_len)?)
            .ok_or(CouponError::Certificate)?;
        let counter = u32::from_be_bytes(be(take(&mut rest, 4)?)?);
        let opened = nodes(take(&mut rest, 32 * WOTS_CHAINS)?);
        if !rest.is_empty() {
            return Err(CouponError::InvalidParameters);
        }
        let descriptor = CouponDescriptor {
            parent: *parent,
            threshold,
            parties,
            members,
            pk_seed,
            leaf,
            chain_ends,
            expires_at,
        };
        Ok(Self {
            coupon: CertifiedCoupon::verify(parent, params, descriptor, certificate)?,
            counter,
            nodes: opened,
        })
    }
}

/// A signature and the clock reading used to check its certified expiry.
pub struct TimedBaggySig<'a> {
    sig: &'a BaggySig,
    time: Option<u64>,
}

impl<'a> From<(&'a BaggySig, u64)> for TimedBaggySig<'a> {
    fn from((sig, time): (&'a BaggySig, u64)) -> Self {
        Self {
            sig,
            time: Some(time),
        }
    }
}

#[cfg(any(test, feature = "std"))]
impl<'a> From<&'a BaggySig> for TimedBaggySig<'a> {
    fn from(sig: &'a BaggySig) -> Self {
        Self {
            sig,
            time: now().ok(),
        }
    }
}

/// Verify the root certificate, expiry, codeword and one-time chains. Pass
/// `(&signature, trusted_unix_seconds)` on any platform. With `std`, passing
/// `&signature` reads the system clock and rejects on clock failure.
pub fn baggy_verify<'a>(
    parent: &BaggyPublicKey,
    params: &BaggyParams,
    message: &[u8],
    signature: impl Into<TimedBaggySig<'a>>,
) -> bool {
    let TimedBaggySig { sig, time } = signature.into();
    time.is_some_and(|time| baggy_verify_at(parent, params, message, sig, time))
}

pub use baggy_verify as verify;

#[cfg(any(test, feature = "std"))]
fn now() -> Result<u64, CouponError> {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .map_err(|_| CouponError::Clock)
}

/// Concrete verification pins the parent key, checks its certificate, expiry, the
/// codeword sum and every one-time chain. It never trusts an enrollment token alone.
pub fn baggy_verify_at(
    parent: &BaggyPublicKey,
    params: &BaggyParams,
    message: &[u8],
    sig: &BaggySig,
    time: u64,
) -> bool {
    let d = &sig.coupon.descriptor;
    let Ok(certificate_message) = d.certificate_message() else {
        return false;
    };
    let Ok(id) = d.id() else {
        return false;
    };
    if d.parent != *parent
        || time > d.expires_at
        || sig.nodes.len() != WOTS_CHAINS
        || !verify_root(
            params,
            parent,
            &certificate_message,
            &sig.coupon.certificate,
        )
    {
        return false;
    }
    let Some(digits) = digits_at(&SignRequest::message_hash(&id, message), sig.counter) else {
        return false;
    };
    digits
        .iter()
        .zip(&sig.nodes)
        .enumerate()
        .all(|(chain, (&step, node))| {
            ct_eq_bytes32(
                &chain_walk(
                    &d.pk_seed,
                    d.leaf,
                    chain,
                    usize::from(step),
                    WOTS_STEPS,
                    node,
                ),
                &d.chain_ends[chain],
            )
        })
}

/// A certified bundle identity. The certificate must bind both fields; the verifier
/// receives this trusted identity, never a caller-selected replacement leaf count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HopBundleRoot {
    pub leaves: usize,
    pub root: Node,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexedHopProof {
    pub index: usize,
    pub siblings: Vec<Node>,
}

/// Public indexed Merkle bundle of independent ONE-TIME hop verification keys.
/// A branching capability spends a different leaf for each child. Reusing a leaf
/// for two children is not made safe by Merkle authentication.
pub struct HopBundle {
    identity: HopBundleRoot,
    levels: Vec<Vec<Node>>,
}

fn hop_leaf(index: usize, pk: &Node) -> Node {
    hash(
        b"QSAG.CAPABILITY.INDEXED_LEAF/v1",
        &[&(index as u64).to_be_bytes(), pk],
    )
}
fn hop_node(left: &Node, right: &Node) -> Node {
    hash(b"QSAG.CAPABILITY.MERKLE_NODE/v1", &[left, right])
}
impl HopBundle {
    /// Pads to the next power of two with domain-separated non-signing leaves.
    /// Every authentication path has exactly ceil(log2(public_keys.len())) nodes.
    pub fn new(public_keys: &[Node]) -> Result<Self, CouponError> {
        let capacity = public_keys
            .len()
            .checked_next_power_of_two()
            .ok_or(CouponError::InvalidParameters)?;
        if public_keys.is_empty() {
            return Err(CouponError::InvalidParameters);
        }
        let mut bottom = Vec::new();
        bottom
            .try_reserve_exact(capacity)
            .map_err(|_| CouponError::InvalidParameters)?;
        for index in 0..capacity {
            bottom.push(if let Some(pk) = public_keys.get(index) {
                hop_leaf(index, pk)
            } else {
                hash(
                    b"QSAG.CAPABILITY.PADDING/v1",
                    &[&(index as u64).to_be_bytes()],
                )
            });
        }
        let mut levels = vec![bottom];
        let mut width = capacity;
        while width > 1 {
            let previous = &levels[levels.len() - 1];
            let mut next = Vec::new();
            next.try_reserve_exact(width / 2)
                .map_err(|_| CouponError::InvalidParameters)?;
            for pair in previous.as_chunks::<2>().0 {
                next.push(hop_node(&pair[0], &pair[1]));
            }
            levels.push(next);
            width /= 2;
        }
        let root = levels[levels.len() - 1][0];
        Ok(Self {
            identity: HopBundleRoot {
                leaves: public_keys.len(),
                root,
            },
            levels,
        })
    }
    pub fn identity(&self) -> HopBundleRoot {
        self.identity
    }
    pub fn proof(&self, index: usize) -> Result<IndexedHopProof, CouponError> {
        if index >= self.identity.leaves {
            return Err(CouponError::InvalidParameters);
        }
        let mut at = index;
        let mut siblings = Vec::with_capacity(self.levels.len() - 1);
        for level in &self.levels[..self.levels.len() - 1] {
            siblings.push(level[at ^ 1]);
            at /= 2;
        }
        Ok(IndexedHopProof { index, siblings })
    }
}
/// Replacing the key at a fixed valid index while preserving this root produces
/// the collision event in `indexed_bundle_key_binding`. Message unforgeability
/// additionally requires the actual hop OTS verifier and one-time use at that index.
pub fn verify_hop_membership(identity: HopBundleRoot, key: &Node, proof: &IndexedHopProof) -> bool {
    let Some(capacity) = identity.leaves.checked_next_power_of_two() else {
        return false;
    };
    if identity.leaves == 0
        || proof.index >= identity.leaves
        || proof.siblings.len() != capacity.trailing_zeros() as usize
    {
        return false;
    }
    let mut node = hop_leaf(proof.index, key);
    let mut at = proof.index;
    for sibling in &proof.siblings {
        node = if at & 1 == 0 {
            hop_node(&node, sibling)
        } else {
            hop_node(sibling, &node)
        };
        at >>= 1;
    }
    ct_eq_bytes32(&node, &identity.root)
}
