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
