//! Bound heavyweight proof witnesses independently of fine-grained arithmetic workers.
//! Default one active batch keeps CPU traces from accumulating behind the exclusive GPU arena.
//! QSAG_PROVER_JOBS opts into more concurrent witnesses; it is NOT a byte-memory guarantee.
//! Each batch retains its original statement/transcript and cryptographic batching.
use std::sync::{Condvar, Mutex, OnceLock};

pub(crate) fn prover_parallel_jobs() -> usize {
    static JOBS: OnceLock<usize> = OnceLock::new();
    (*JOBS.get_or_init(|| std::env::var("QSAG_PROVER_JOBS").ok()
        .and_then(|x| x.parse::<usize>().ok()).filter(|&x|x>0).unwrap_or(1)))
        .min(crate::parallel_workers()).max(1)
}
static ACTIVE: Mutex<usize> = Mutex::new(0);
static READY: Condvar = Condvar::new();
pub(crate) struct Permit;
pub(crate) fn acquire() -> Permit {
    let mut active = ACTIVE.lock().unwrap_or_else(|e|e.into_inner());
    while *active >= prover_parallel_jobs() {
        active = READY.wait(active).unwrap_or_else(|e|e.into_inner());
    }
    *active += 1;
    Permit
}
impl Drop for Permit {
    fn drop(&mut self) {
        let mut active = ACTIVE.lock().unwrap_or_else(|e|e.into_inner());
        *active -= 1;
        READY.notify_all();
    }
}
