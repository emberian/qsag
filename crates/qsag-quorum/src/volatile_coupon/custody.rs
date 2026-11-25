//! Host-backed secret storage and online coupon operations.
use super::*;
use qsag_core::wipe::wipe_bytes;
use std::collections::BTreeMap;

#[cfg(target_os = "linux")]
#[path = "mint.rs"]
pub mod mint;

const OPENING_BYTES: usize = WOTS_CHAINS * 32;

#[cfg(all(test, target_os = "linux"))]
pub(crate) use memory::{cap_allocator_arenas, release_free_heap};

// This is the sole OS-FFI boundary. All cryptographic and protocol code is safe Rust.
#[allow(unsafe_code)]
mod memory {
    use super::CouponError;
    #[cfg(target_os = "linux")]
    use std::ffi::c_long;
    use std::ffi::{c_int, c_void};
    use std::ptr::NonNull;

    unsafe extern "C" {
        fn mmap(
            addr: *mut c_void,
            len: usize,
            prot: c_int,
            flags: c_int,
            fd: c_int,
            offset: i64,
        ) -> *mut c_void;
        fn mlock(addr: *const c_void, len: usize) -> c_int;
        fn madvise(addr: *mut c_void, len: usize, advice: c_int) -> c_int;
        fn munmap(addr: *mut c_void, len: usize) -> c_int;
        fn getpagesize() -> c_int;
        #[cfg(target_os = "macos")]
        fn minherit(addr: *mut c_void, len: usize, inherit: c_int) -> c_int;
        #[cfg(target_os = "linux")]
        fn mlockall(flags: c_int) -> c_int;
        #[cfg(target_os = "linux")]
        fn prctl(option: c_int, ...) -> c_int;
        #[cfg(all(target_os = "linux", target_env = "gnu"))]
        fn mallopt(param: c_int, value: c_int) -> c_int;
        #[cfg(all(test, target_os = "linux", target_env = "gnu"))]
        fn malloc_trim(pad: usize) -> c_int;
    }

    /// Cap the process allocator at two arenas (`M_ARENA_MAX`). Advisory: an allocator
    /// without this knob keeps its own policy, so the result is ignored.
    #[cfg(target_os = "linux")]
    pub(crate) fn cap_allocator_arenas() {
        #[cfg(target_env = "gnu")]
        const M_ARENA_MAX: c_int = -8;
        // SAFETY: `mallopt` only stores an allocator tuning parameter; it takes no
        // pointers and is safe to call at any time from any thread.
        #[cfg(target_env = "gnu")]
        let _ = unsafe { mallopt(M_ARENA_MAX, 2) };
    }

    /// Return free heap pages of every allocator arena to the operating system.
    #[cfg(all(test, target_os = "linux"))]
    pub(crate) fn release_free_heap() {
        // SAFETY: `malloc_trim` takes no pointers and only releases memory the allocator
        // already considers free; it is safe to call concurrently with allocation.
        #[cfg(target_env = "gnu")]
        let _ = unsafe { malloc_trim(0) };
    }

    /// Process-wide protection for the existing heap/stack MPC engine. Call in a
    /// dedicated mint worker BEFORE creating its secret RNGs or loading key shares.
    /// This permanently disables core dumps and locks current and future mappings;
    /// it is intentionally not undone on Drop. Insufficient RLIMIT_MEMLOCK fails
    /// closed. Allocation beyond that limit can abort the worker. It also caps the
    /// process allocator at two arenas, which bounds the locked heap.
    ///
    /// Do not fork a worker while MPC scratch exists: only the final LockedBytes
    /// slots have WIPEONFORK. Forked handles cannot invoke minting. Privileged RAM
    /// snapshots and code that bypasses this API remain outside the threat model.
    #[cfg(target_os = "linux")]
    pub struct ProtectedMintProcess {
        pid: u32,
    }
    #[cfg(target_os = "linux")]
    impl ProtectedMintProcess {
        pub fn enable() -> Result<Self, CouponError> {
            // PR_SET_DUMPABLE=4, MCL_CURRENT|MCL_FUTURE=3. Never put keys into the
            // worker until both calls have succeeded.
            if unsafe { prctl(4, 0 as c_long, 0 as c_long, 0 as c_long, 0 as c_long) } != 0
                || unsafe { mlockall(3) } != 0
            {
                return Err(CouponError::MemoryProtection);
            }
            // Under MCL_FUTURE every allocator arena a worker thread creates stays
            // resident, and minting spawns many short-lived workers: the 2-of-3 two-coupon
            // mint held 7.8 GB with default arenas and 3.6 GB with two, at equal wall time.
            cap_allocator_arenas();
            Ok(Self {
                pid: std::process::id(),
            })
        }
        pub(super) fn check(&self) -> Result<(), CouponError> {
            if self.pid != std::process::id() {
                return Err(CouponError::Forked);
            }
            // Reassert locking in case other application code called munlockall.
            if unsafe { prctl(3, 0 as c_long, 0 as c_long, 0 as c_long, 0 as c_long) } != 0
                || unsafe { mlockall(3) } != 0
            {
                return Err(CouponError::MemoryProtection);
            }
            Ok(())
        }
    }
    /// Owned secret storage. No Clone, Debug contents, serialization, or raw-pointer API.
    pub struct LockedBytes {
        ptr: NonNull<u8>,
        len: usize,
        mapped: usize,
        pid: u32,
    }
    // SAFETY: the mapping is exclusively owned, never reallocated, and only accessed
    // through references whose lifetimes are bounded by this owner. Moving it does
    // not move its backing pages. It is deliberately not Sync.
    unsafe impl Send for LockedBytes {}
    impl core::fmt::Debug for LockedBytes {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("LockedBytes(<REDACTED>)")
        }
    }
    impl LockedBytes {
        pub fn new(len: usize) -> Result<Self, CouponError> {
            if len == 0 || len > isize::MAX as usize {
                return Err(CouponError::InvalidParameters);
            }
            // SAFETY: getpagesize takes no arguments.
            let page = unsafe { getpagesize() };
            if page <= 0 {
                return Err(CouponError::MemoryProtection);
            }
            let page = page as usize;
            let mapped = len
                .checked_add(page - 1)
                .map(|n| n / page * page)
                .ok_or(CouponError::InvalidParameters)?;
            if mapped > isize::MAX as usize {
                return Err(CouponError::InvalidParameters);
            }
            #[cfg(target_os = "linux")]
            const MAP_ANON: c_int = 0x20;
            #[cfg(target_os = "macos")]
            const MAP_ANON: c_int = 0x1000;
            // SAFETY: anonymous private mapping, no file descriptor or shared alias.
            let raw = unsafe { mmap(std::ptr::null_mut(), mapped, 3, 2 | MAP_ANON, -1, 0) };
            if raw as isize == -1 {
                return Err(CouponError::MemoryProtection);
            }
            let Some(ptr) = NonNull::new(raw.cast::<u8>()) else {
                // Even a mapping at address zero must be released, never dereferenced.
                unsafe {
                    munmap(raw, mapped);
                }
                return Err(CouponError::MemoryProtection);
            };
            // No secret enters the mapping until all three protections succeed.
            #[cfg(target_os = "linux")]
            let protected = unsafe {
                mlock(raw, mapped) == 0
                    && madvise(raw, mapped, 16) == 0
                    && madvise(raw, mapped, 18) == 0 // DONTDUMP, WIPEONFORK
            };
            #[cfg(target_os = "macos")]
            let protected = unsafe {
                mlock(raw, mapped) == 0
                    && madvise(raw, mapped, 6) == 0 // MADV_ZERO_WIRED_PAGES
                    && minherit(raw, mapped, 2) == 0 // VM_INHERIT_NONE
            };
            if !protected {
                unsafe {
                    munmap(raw, mapped);
                }
                return Err(CouponError::MemoryProtection);
            }
            Ok(Self {
                ptr,
                len,
                mapped,
                pid: std::process::id(),
            })
        }
        pub fn random(len: usize) -> Result<Self, CouponError> {
            let mut out = Self::new(len)?;
            // Read-only OS randomness; bytes are written straight into locked pages.
            qsag_core::wipe::fill_os_random(out.as_mut_slice()?)
                .map_err(|_| CouponError::Entropy)?;
            Ok(out)
        }
        pub fn len(&self) -> usize {
            self.len
        }
        pub fn is_empty(&self) -> bool {
            self.len == 0
        }
        pub fn as_slice(&self) -> Result<&[u8], CouponError> {
            if self.pid != std::process::id() {
                return Err(CouponError::Forked);
            }
            // SAFETY: live mapping, initialized by mmap, within its requested length.
            Ok(unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) })
        }
        /// MPC producers write their final local shares directly into these pages.
        /// They must also protect and erase their own intermediate state.
        pub fn as_mut_slice(&mut self) -> Result<&mut [u8], CouponError> {
            if self.pid != std::process::id() {
                return Err(CouponError::Forked);
            }
            // SAFETY: exclusive owner borrow and no other exposed mutable alias.
            Ok(unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) })
        }
        #[cfg(test)]
        pub(super) fn pid_for_test_restore(&mut self) {
            self.pid = std::process::id();
        }
        #[cfg(test)]
        pub(super) fn simulate_fork(&mut self) {
            self.pid = self.pid.wrapping_add(1);
        }
    }
    impl Drop for LockedBytes {
        fn drop(&mut self) {
            // A macOS child does not inherit the mapping. The address may
            // already have been reused, so neither wipe nor unmap it there.
            #[cfg(target_os = "macos")]
            if self.pid != std::process::id() {
                return;
            }
            // SAFETY: this owner retains the complete mapping until munmap. Wipe its
            // padding too. munmap releases the mlock without an unlocked secret window.
            unsafe {
                qsag_asm::ct_memzero(std::slice::from_raw_parts_mut(
                    self.ptr.as_ptr(),
                    self.mapped,
                ));
                munmap(self.ptr.as_ptr().cast(), self.mapped);
            }
        }
    }
}
pub use memory::LockedBytes;
#[cfg(target_os = "linux")]
pub use memory::ProtectedMintProcess;

/// An initiator credential provisioned over an authenticated confidential channel.
/// Share the same key with the authorized custodians; never with an unauthenticated
/// relay. Callers own the provisioning policy. Key material stays locked here.
#[derive(Debug)]
pub struct InitiatorKey(LockedBytes);
impl InitiatorKey {
    pub fn generate() -> Result<Self, CouponError> {
        Self::from_locked(LockedBytes::random(32)?)
    }
    pub fn from_locked(bytes: LockedBytes) -> Result<Self, CouponError> {
        if bytes.len() != 32 {
            return Err(CouponError::InvalidParameters);
        }
        bytes.as_slice()?;
        Ok(Self(bytes))
    }
    fn mac(&self, domain: &[u8], parts: &[&[u8]]) -> Result<Node, CouponError> {
        let mut xof = Cshake256Xof::new(domain);
        framed(&mut xof, self.0.as_slice()?);
        for part in parts {
            framed(&mut xof, part);
        }
        let mut out = [0; 32];
        xof.squeeze(&mut out);
        Ok(out)
    }
}

impl SignRequest {
    pub fn authorize(
        key: &InitiatorKey,
        coupon: &CouponDescriptor,
        message: Vec<u8>,
        counter: u32,
    ) -> Result<Self, CouponError> {
        let mut req = Self {
            coupon_id: coupon.id()?,
            message,
            counter,
            initiator_mac: [0; 32],
        };
        req.digits()?;
        req.initiator_mac = key.mac(b"QSAG.VOLATILE.REQUEST/v1", &[&req.commitment()])?;
        Ok(req)
    }
    fn commitment(&self) -> Node {
        hash(
            b"QSAG.VOLATILE.COMMIT/v1",
            &[&self.coupon_id, &self.message, &self.counter.to_be_bytes()],
        )
    }
    fn digits(&self) -> Result<Vec<u8>, CouponError> {
        digits_at(
            &Self::message_hash(&self.coupon_id, &self.message),
            self.counter,
        )
        .ok_or(CouponError::InvalidCodeword)
    }
}

struct Slot {
    coupon: CertifiedCoupon,
    material: Option<LockedBytes>,
    waistband_mac: Node,
}
/// One custodian's online pool. `&mut self` serializes take-and-wipe; use a Mutex when
/// multiple request handlers share a pool. Spent IDs stay recorded until pool drop.
pub struct CouponPool {
    party: u32,
    parent: BaggyPublicKey,
    initiator: InitiatorKey,
    cache_key: InitiatorKey,
    slots: BTreeMap<Node, Slot>,
}
impl CouponPool {
    pub fn new(
        party: u32,
        parent: BaggyPublicKey,
        initiator: InitiatorKey,
    ) -> Result<Self, CouponError> {
        Ok(Self {
            party,
            parent,
            initiator,
            cache_key: InitiatorKey::generate()?,
            slots: BTreeMap::new(),
        })
    }
    /// Install exactly 128*3*32 bytes, chain-major, steps 0/1/2. The MPC producer
    /// must independently mask every chain state across ALL descriptor members.
    /// A long-term Shamir share or a seed that can recreate spent nodes is invalid.
    pub fn install(
        &mut self,
        coupon: CertifiedCoupon,
        material: LockedBytes,
    ) -> Result<(), CouponError> {
        let d = &coupon.descriptor;
        d.validate()?;
        if d.parent != self.parent
            || !d.members.contains(&self.party)
            || material.len() != SHARE_BYTES
        {
            return Err(CouponError::InvalidParameters);
        }
        material.as_slice()?;
        if now()? > d.expires_at {
            return Err(CouponError::Expired);
        }
        let id = d.id()?;
        if self.slots.contains_key(&id) {
            return Err(CouponError::AlreadyInstalled);
        }
        let waistband_mac = self
            .cache_key
            .mac(b"QSAG.VOLATILE.WAISTBAND/v1", &[&d.certificate_message()?])?;
        self.slots.insert(
            id,
            Slot {
                coupon,
                material: Some(material),
                waistband_mac,
            },
        );
        Ok(())
    }
    pub fn open(&mut self, req: &SignRequest) -> Result<CouponOpening, CouponError> {
        // Check request authorization before any coupon lookup, allocation, or mutation.
        let binding = req.commitment();
        let mut expected = self
            .initiator
            .mac(b"QSAG.VOLATILE.REQUEST/v1", &[&binding])?;
        let valid = ct_eq_bytes32(&expected, &req.initiator_mac);
        wipe_bytes(&mut expected);
        if !valid {
            return Err(CouponError::Authentication);
        }
        let slot = self
            .slots
            .get_mut(&req.coupon_id)
            .ok_or(CouponError::MissingOrSpent)?;
        let d = &slot.coupon.descriptor;
        if now()? > d.expires_at {
            return Err(CouponError::Expired);
        }
        let mut expected_cache = self
            .cache_key
            .mac(b"QSAG.VOLATILE.WAISTBAND/v1", &[&d.certificate_message()?])?;
        let cache_ok = ct_eq_bytes32(&expected_cache, &slot.waistband_mac);
        wipe_bytes(&mut expected_cache);
        if !cache_ok || d.id()? != req.coupon_id {
            return Err(CouponError::Authentication);
        }
        let digits = req.digits()?;
        if slot.material.is_none() {
            return Err(CouponError::MissingOrSpent);
        }
        // Allocate the response before consuming: memory-pressure failures cannot burn.
        let mut selected = LockedBytes::new(OPENING_BYTES)?;
        let material = slot.material.take().ok_or(CouponError::MissingOrSpent)?;
        let source = material.as_slice()?;
        let dest = selected.as_mut_slice()?;
        for (chain, &step) in digits.iter().enumerate() {
            if usize::from(step) < WOTS_STEPS {
                let offset = (chain * WOTS_STEPS + usize::from(step)) * 32;
                dest[chain * 32..(chain + 1) * 32].copy_from_slice(&source[offset..offset + 32]);
            }
            // Step 3 is public. All members send zero and the combiner uses the tip.
        }
        drop(material); // volatile wipe of ALL unselected states before any response escapes
        Ok(CouponOpening {
            party: self.party,
            coupon_id: req.coupon_id,
            binding,
            selected,
        })
    }
}
/// A local response remains locked until combination or transport takes it. Its
/// selected bytes are deliberately absent from Debug and serialization derives.
#[derive(Debug)]
pub struct CouponOpening {
    party: u32,
    coupon_id: Node,
    binding: Node,
    selected: LockedBytes,
}
impl CouponOpening {
    /// Reconstruct a response received over an authenticated confidential channel.
    /// Parsing must fill `selected` directly in locked storage. `combine` still
    /// checks the fixed sender set, request binding and cryptographic chain ends.
    pub fn from_received(
        party: u32,
        coupon_id: Node,
        binding: Node,
        selected: LockedBytes,
    ) -> Result<Self, CouponError> {
        if selected.len() != OPENING_BYTES {
            return Err(CouponError::InvalidOpenings);
        }
        selected.as_slice()?;
        Ok(Self {
            party,
            coupon_id,
            binding,
            selected,
        })
    }
    pub fn party(&self) -> u32 {
        self.party
    }
    pub fn coupon_id(&self) -> &Node {
        &self.coupon_id
    }
    pub fn request_binding(&self) -> &Node {
        &self.binding
    }
    /// Send only over an authenticated confidential transport; discard after send.
    pub fn selected_bytes(&self) -> Result<&[u8], CouponError> {
        self.selected.as_slice()
    }
}

/// All responses must bind the same request and contain each fixed member once.
/// The final forward-chain check detects arbitrary corrupt response shares.
pub fn combine(
    coupon: &CertifiedCoupon,
    req: &SignRequest,
    openings: &[CouponOpening],
) -> Result<BaggySig, CouponError> {
    let d = &coupon.descriptor;
    if now()? > d.expires_at {
        return Err(CouponError::Expired);
    }
    if d.id()? != req.coupon_id || openings.len() != d.members.len() {
        return Err(CouponError::InvalidOpenings);
    }
    let binding = req.commitment();
    let digits = req.digits()?;
    let mut nodes = vec![[0; 32]; WOTS_CHAINS];
    for &member in &d.members {
        let mut matches = openings.iter().filter(|o| o.party == member);
        let o = matches.next().ok_or(CouponError::InvalidOpenings)?;
        if matches.next().is_some() || o.coupon_id != req.coupon_id || o.binding != binding {
            return Err(CouponError::InvalidOpenings);
        }
        for (dst, src) in nodes
            .as_flattened_mut()
            .iter_mut()
            .zip(o.selected.as_slice()?)
        {
            *dst ^= src;
        }
    }
    for (chain, (&step, node)) in digits.iter().zip(&mut nodes).enumerate() {
        if usize::from(step) == WOTS_STEPS {
            *node = d.chain_ends[chain];
        }
        let tip = chain_walk(
            &d.pk_seed,
            d.leaf,
            chain,
            usize::from(step),
            WOTS_STEPS,
            node,
        );
        if !ct_eq_bytes32(&tip, &d.chain_ends[chain]) {
            return Err(CouponError::InvalidOpenings);
        }
    }
    Ok(BaggySig {
        coupon: coupon.clone(),
        counter: req.counter,
        nodes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quorum_jorts::{chain_step, grind};
    use qsag_core::baggy::{baggy_reference_keygen, baggy_reference_sign};
    use qsag_core::tsw_baggy::PqSecretKey;

    pub(super) fn key() -> InitiatorKey {
        let mut bytes = LockedBytes::new(32).unwrap();
        bytes.as_mut_slice().unwrap().fill(0x57);
        InitiatorKey::from_locked(bytes).unwrap()
    }

    // Test-only trusted dealer, using the real production Baggy profile and chain
    // functions. There is no fake certificate verifier or reduced cryptographic bound.
    fn fixture(t: usize, n: usize) -> (CertifiedCoupon, Vec<CouponPool>) {
        fixture_with(&BaggyParams::SHA3_128F, t, n)
    }
    fn fixture_with(
        params: &BaggyParams,
        t: usize,
        n: usize,
    ) -> (CertifiedCoupon, Vec<CouponPool>) {
        let sk = PqSecretKey {
            sk_seed: [0x19; 32],
            sk_prf: [0x42; 32],
            pk_seed: [0x83; 32],
        };
        let parent = baggy_reference_keygen(params, &sk).unwrap();
        let mut d = CouponDescriptor {
            parent,
            threshold: t,
            parties: n,
            members: (n - t..n).map(|p| p as u32).collect(),
            pk_seed: [0x65; 32],
            leaf: 0,
            chain_ends: vec![],
            expires_at: now().unwrap() + 600,
        };
        let mut material: Vec<_> = (0..t)
            .map(|_| LockedBytes::random(SHARE_BYTES).unwrap())
            .collect();
        let seeds = LockedBytes::random(WOTS_CHAINS * 32).unwrap();
        for chain in 0..WOTS_CHAINS {
            let mut node = [0; 32];
            node.copy_from_slice(&seeds.as_slice().unwrap()[32 * chain..32 * (chain + 1)]);
            for step in 0..WOTS_STEPS {
                let offset = (WOTS_STEPS * chain + step) * 32;
                let mut last_share = node;
                for share in &material[..t - 1] {
                    for (x, &mask) in last_share
                        .iter_mut()
                        .zip(&share.as_slice().unwrap()[offset..offset + 32])
                    {
                        *x ^= mask;
                    }
                }
                material[t - 1].as_mut_slice().unwrap()[offset..offset + 32]
                    .copy_from_slice(&last_share);
                wipe_bytes(&mut last_share);
                node = chain_step(&d.pk_seed, d.leaf, chain as u32, step as u32, &node);
            }
            d.chain_ends.push(node);
        }
        let certificate =
            baggy_reference_sign(params, &sk, &parent, &d.certificate_message().unwrap()).unwrap();
        let certified = CertifiedCoupon::verify(&parent, params, d.clone(), certificate).unwrap();
        let pools = d
            .members
            .iter()
            .zip(material)
            .map(|(&p, m)| {
                let mut pool = CouponPool::new(p, parent, key()).unwrap();
                pool.install(certified.clone(), m).unwrap();
                pool
            })
            .collect();
        (certified, pools)
    }
    pub(super) fn request(coupon: &CertifiedCoupon, message: &[u8]) -> SignRequest {
        let d = coupon.descriptor();
        let ctr = grind(&SignRequest::message_hash(&d.id().unwrap(), message))
            .unwrap()
            .0;
        SignRequest::authorize(&key(), d, message.to_vec(), ctr).unwrap()
    }

    #[test]
    fn indexed_hop_bundles_bind_index_key_depth_and_padding() {
        for leaves in [1usize, 3, 16, 65] {
            let keys: Vec<_> = (0..leaves)
                .map(|i| hash(b"test-public-hop-key", &[&(i as u64).to_be_bytes()]))
                .collect();
            let bundle = HopBundle::new(&keys).unwrap();
            for (i, key) in keys.iter().enumerate() {
                let proof = bundle.proof(i).unwrap();
                assert_eq!(
                    proof.siblings.len(),
                    leaves.next_power_of_two().trailing_zeros() as usize
                );
                assert!(verify_hop_membership(bundle.identity(), key, &proof));
                let mut wrong_key = *key;
                wrong_key[0] ^= 1;
                assert!(!verify_hop_membership(
                    bundle.identity(),
                    &wrong_key,
                    &proof
                ));
                let mut wrong_index = proof.clone();
                wrong_index.index = (i + 1) % leaves;
                if leaves > 1 {
                    assert!(!verify_hop_membership(bundle.identity(), key, &wrong_index));
                }
                let mut wrong_depth = proof.clone();
                wrong_depth.siblings.push([0; 32]);
                assert!(!verify_hop_membership(bundle.identity(), key, &wrong_depth));
            }
            assert!(bundle.proof(leaves).is_err());
        }
        assert!(HopBundle::new(&[]).is_err());
    }

    #[test]
    fn baggy_sig_round_trips_on_the_wire_and_binds_every_field() {
        let params = BaggyParams::SHA3_128F;
        let (coupon, mut pools) = fixture_with(&params, 3, 5);
        let parent = coupon.descriptor.parent;
        let req = request(&coupon, b"stateless online signature");
        let openings: Vec<_> = pools.iter_mut().map(|p| p.open(&req).unwrap()).collect();
        let sig: BaggySig = combine(&coupon, &req, &openings).unwrap();
        // The root certificate is a PORS+FP signature within the pruning bound.
        let opening = &sig.coupon.certificate.pors;
        assert!(!sig.coupon.certificate.pors.secrets.is_empty());
        assert_eq!(opening.secrets.len(), 28);
        assert!(opening.auth.len() <= 128);
        assert!(baggy_verify(&parent, &params, &req.message, &sig));
        let expiry = coupon.descriptor.expires_at;
        assert!(baggy_verify_at(
            &parent,
            &params,
            &req.message,
            &sig,
            expiry
        ));
        assert!(!baggy_verify_at(
            &parent,
            &params,
            &req.message,
            &sig,
            expiry + 1
        ));

        let raw = sig.to_wire_bytes().unwrap();
        // Descriptor (64 + 4 t + 4096), length-prefixed certificate, counter, 128 nodes.
        let overhead = 2 + 2 + 4 * 3 + 32 + 8 + 8 + 4096 + 4 + 4 + 4096;
        assert!(raw.len() <= overhead + params.sig_bytes_checked().unwrap());
        let back = BaggySig::from_wire_bytes(&parent, &params, &raw).unwrap();
        assert_eq!(back.to_wire_bytes().unwrap(), raw);
        assert!(baggy_verify(&parent, &params, &req.message, &back));
        assert!(!baggy_verify(&parent, &params, b"another message", &back));

        // Another parameter set, root key, or truncated/extended input is refused.
        assert!(BaggySig::from_wire_bytes(&parent, &BaggyParams::TEST_SMALL, &raw).is_err());
        let other = BaggyPublicKey {
            pk_root: [9; 32],
            ..parent
        };
        assert!(BaggySig::from_wire_bytes(&other, &params, &raw).is_err());
        assert!(BaggySig::from_wire_bytes(&parent, &params, &raw[..raw.len() - 1]).is_err());
        let mut long = raw.clone();
        long.push(0);
        assert!(BaggySig::from_wire_bytes(&parent, &params, &long).is_err());

        // One flipped bit in each field: the envelope does not decode, or does not verify.
        let certificate_at = 2 + 2 + 12 + 32 + 8 + 8 + 4096 + 4;
        for offset in [
            1,                    // threshold
            3,                    // parties
            7,                    // a member
            20,                   // coupon pk_seed
            55,                   // leaf
            63,                   // expiry
            100,                  // a chain end
            certificate_at - 1,   // certificate length
            certificate_at + 5,   // certificate randomiser
            certificate_at + 40,  // a PORS+FP secret
            raw.len() - 4096 - 1, // counter
            raw.len() - 1,        // an opened chain node
        ] {
            let mut bad = raw.clone();
            bad[offset] ^= 1;
            if let Ok(decoded) = BaggySig::from_wire_bytes(&parent, &params, &bad) {
                assert!(
                    !baggy_verify(&parent, &params, &req.message, &decoded),
                    "offset {offset}"
                );
            }
        }
        // The fields ahead of the certificate are all covered by it: those never decode.
        for offset in [1, 3, 7, 20, 55, 63, 100] {
            let mut bad = raw.clone();
            bad[offset] ^= 1;
            assert!(BaggySig::from_wire_bytes(&parent, &params, &bad).is_err());
        }
    }

    #[test]
    fn volatile_coupon_parametric_fixed_subset_signatures() {
        for (t, n) in [(2, 3), (3, 5), (4, 6), (3, 3), (2, 257)] {
            let (coupon, mut pools) = fixture(t, n);
            let req = request(&coupon, b"authorized transaction");
            let openings: Vec<_> = pools.iter_mut().map(|p| p.open(&req).unwrap()).collect();
            let sig = combine(&coupon, &req, &openings).unwrap();
            assert!(verify(
                &coupon.descriptor.parent,
                &BaggyParams::SHA3_128F,
                &req.message,
                &sig
            ));
            assert!(!verify(
                &coupon.descriptor.parent,
                &BaggyParams::SHA3_128F,
                b"changed",
                &sig
            ));
            assert!(matches!(
                combine(&coupon, &req, &openings[..t - 1]),
                Err(CouponError::InvalidOpenings)
            ));
            for pool in &mut pools {
                assert!(matches!(pool.open(&req), Err(CouponError::MissingOrSpent)));
                assert!(pool.slots.values().all(|s| s.material.is_none()));
                assert_eq!(
                    pool.install(coupon.clone(), LockedBytes::new(SHARE_BYTES).unwrap()),
                    Err(CouponError::AlreadyInstalled)
                );
            }
        }
    }

    #[test]
    fn volatile_coupon_certificate_binds_every_public_parameter() {
        let (coupon, _) = fixture(2, 3);
        let parent = coupon.descriptor.parent;
        for field in 0..8 {
            let mut d = coupon.descriptor.clone();
            match field {
                0 => d.parent.pk_root[0] ^= 1,
                1 => d.parties += 1,
                2 => d.members[0] = 0,
                3 => d.pk_seed[0] ^= 1,
                4 => d.leaf += 1,
                5 => d.expires_at += 1,
                6 => d.chain_ends[0][0] ^= 1,
                _ => d.threshold += 1,
            }
            assert!(
                CertifiedCoupon::verify(
                    &parent,
                    &BaggyParams::SHA3_128F,
                    d,
                    coupon.certificate.clone()
                )
                .is_err()
            );
        }
        let mut certificate = coupon.certificate.clone();
        certificate.r[0] ^= 1;
        assert!(
            CertifiedCoupon::verify(
                &parent,
                &BaggyParams::SHA3_128F,
                coupon.descriptor.clone(),
                certificate
            )
            .is_err()
        );
    }

    #[test]
    fn volatile_coupon_authentication_precedes_consumption() {
        let (coupon, mut pools) = fixture(2, 3);
        let req = request(&coupon, b"approved");
        for field in 0..4 {
            let mut bad = req.clone();
            match field {
                0 => bad.message.push(0),
                1 => bad.coupon_id[0] ^= 1,
                2 => bad.counter ^= 1,
                _ => bad.initiator_mac[0] ^= 1,
            }
            assert!(matches!(
                pools[0].open(&bad),
                Err(CouponError::Authentication)
            ));
            assert!(pools[0].slots[&req.coupon_id].material.is_some());
        }
        let mut bad_codeword = req.clone();
        while bad_codeword.digits().is_ok() {
            bad_codeword.counter += 1;
        }
        bad_codeword.initiator_mac = key()
            .mac(b"QSAG.VOLATILE.REQUEST/v1", &[&bad_codeword.commitment()])
            .unwrap();
        assert!(matches!(
            pools[0].open(&bad_codeword),
            Err(CouponError::InvalidCodeword)
        ));
        assert!(pools[0].slots[&req.coupon_id].material.is_some());
        pools[0]
            .slots
            .get_mut(&req.coupon_id)
            .unwrap()
            .coupon
            .descriptor
            .chain_ends[0][0] ^= 1;
        assert!(matches!(
            pools[0].open(&req),
            Err(CouponError::Authentication)
        ));
        assert!(pools[0].slots[&req.coupon_id].material.is_some());
        pools[0]
            .slots
            .get_mut(&req.coupon_id)
            .unwrap()
            .coupon
            .descriptor
            .chain_ends[0][0] ^= 1;
        assert!(pools[0].open(&req).is_ok());
    }

    #[test]
    fn volatile_coupon_split_brain_and_corrupt_openings_fail() {
        let (coupon, mut pools) = fixture(3, 5);
        let a = request(&coupon, b"branch A");
        let b = request(&coupon, b"branch B");
        let mixed = vec![
            pools[0].open(&a).unwrap(),
            pools[1].open(&b).unwrap(),
            pools[2].open(&a).unwrap(),
        ];
        assert!(matches!(
            combine(&coupon, &a, &mixed),
            Err(CouponError::InvalidOpenings)
        ));
        assert!(matches!(
            combine(&coupon, &b, &mixed),
            Err(CouponError::InvalidOpenings)
        ));
        assert!(matches!(
            pools[1].open(&a),
            Err(CouponError::MissingOrSpent)
        ));
        let (coupon, mut pools) = fixture(2, 3);
        let req = request(&coupon, b"corrupt partial");
        let mut openings: Vec<_> = pools.iter_mut().map(|p| p.open(&req).unwrap()).collect();
        let chain = req
            .digits()
            .unwrap()
            .iter()
            .position(|&d| usize::from(d) < WOTS_STEPS)
            .unwrap();
        openings[0].selected.as_mut_slice().unwrap()[chain * 32] ^= 1;
        assert!(matches!(
            combine(&coupon, &req, &openings),
            Err(CouponError::InvalidOpenings)
        ));
    }

    #[test]
    fn volatile_coupon_concurrent_requests_release_once_and_reboot_is_empty() {
        let (coupon, mut pools) = fixture(2, 3);
        let req = request(&coupon, b"concurrent");
        let pool = std::sync::Mutex::new(pools.remove(0));
        let successes = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|_| scope.spawn(|| pool.lock().unwrap().open(&req).is_ok()))
                .collect();
            handles
                .into_iter()
                .map(|h| usize::from(h.join().unwrap()))
                .sum::<usize>()
        });
        assert_eq!(successes, 1);
        drop(pool);
        let mut restarted = CouponPool::new(
            coupon.descriptor.members[0],
            coupon.descriptor.parent,
            key(),
        )
        .unwrap();
        assert!(matches!(
            restarted.open(&req),
            Err(CouponError::MissingOrSpent)
        ));
    }

    #[test]
    fn volatile_coupon_memory_is_locked_nondumpable_and_fork_guarded() {
        let mut secret = LockedBytes::random(4096).unwrap();
        assert!(secret.as_slice().unwrap().iter().any(|&b| b != 0));
        // Read-only inspection of the actual kernel VMA flags, not a mock allocator.
        #[cfg(target_os = "linux")]
        {
            let addr = secret.as_slice().unwrap().as_ptr() as usize;
            let smaps = std::fs::read_to_string("/proc/self/smaps").unwrap();
            let mut in_mapping = false;
            let mut flags = None;
            for line in smaps.lines() {
                if let Some(range) = line.split_whitespace().next()
                    && let Some((a, b)) = range.split_once('-')
                    && let (Ok(a), Ok(b)) =
                        (usize::from_str_radix(a, 16), usize::from_str_radix(b, 16))
                {
                    in_mapping = a <= addr && addr < b;
                }
                if in_mapping && line.starts_with("VmFlags:") {
                    flags = Some(line);
                    break;
                }
            }
            let flags = flags.unwrap();
            for flag in ["lo", "dd", "wf"] {
                assert!(flags.split_whitespace().any(|f| f == flag), "{flags}");
            }
        }
        secret.simulate_fork();
        assert!(matches!(secret.as_slice(), Err(CouponError::Forked)));
        assert!(matches!(secret.as_mut_slice(), Err(CouponError::Forked)));
        secret.pid_for_test_restore();
    }
}
