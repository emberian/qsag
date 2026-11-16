//! Memory budget shared by the memory-heavy tests of this test binary (same policy as `qsag_core`).
//!
//! The default harness runs one test per CPU. Several end-to-end MPC tests hold one to
//! three gigabytes of staged correlations each; twenty of them at once exceed the 16 GiB
//! build cgroup and the whole binary is killed. A heavy test reserves its measured peak
//! here before it allocates and waits until the reservations in flight fit the budget, so
//! `cargo test` needs no `--test-threads` flag to stay inside the cap.

extern crate std;

use std::sync::{Condvar, Mutex};

/// Megabytes that reserving tests may hold together. Every test above 150 MB reserves.
const BUDGET_MB: usize = 12_500;

static IN_USE_MB: Mutex<usize> = Mutex::new(0);
static RELEASED: Condvar = Condvar::new();

/// A reservation; dropping it returns the memory to the budget.
pub(crate) struct Reservation(usize);

/// Block until `mb` megabytes fit in the budget, then hold them until the guard drops.
/// A request larger than the whole budget is granted once nothing else is reserved.
pub(crate) fn reserve_mb(mb: usize) -> Reservation {
    // The staging workers are short-lived threads that each leave an allocator arena
    // behind; two arenas cut the measured peaks of the staging tests by 25 to 55 percent.
    #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
    {
        static ARENAS: std::sync::Once = std::sync::Once::new();
        ARENAS.call_once(crate::volatile_coupon::cap_allocator_arenas);
    }
    let mut in_use = IN_USE_MB.lock().unwrap_or_else(|e| e.into_inner());
    while *in_use != 0 && *in_use + mb > BUDGET_MB {
        in_use = RELEASED.wait(in_use).unwrap_or_else(|e| e.into_inner());
    }
    *in_use += mb;
    Reservation(mb)
}

impl Drop for Reservation {
    fn drop(&mut self) {
        // A finished test's freed buffers otherwise stay resident in the harness process
        // (5.4 GB observed) while the budget counts them as returned.
        #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
        crate::volatile_coupon::release_free_heap();
        let mut in_use = IN_USE_MB.lock().unwrap_or_else(|e| e.into_inner());
        *in_use -= self.0;
        RELEASED.notify_all();
    }
}
