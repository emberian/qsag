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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn admission_bounds_live_witnesses_and_releases_on_unwind() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let live = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let (live, peak)=(&live, &peak);
                scope.spawn(move || {
                    let _permit=acquire();
                    let n=live.fetch_add(1,Ordering::SeqCst)+1;
                    peak.fetch_max(n,Ordering::SeqCst);
                    for _ in 0..32 {std::thread::yield_now();}
                    live.fetch_sub(1,Ordering::SeqCst);
                });
            }
        });
        assert!(peak.load(Ordering::SeqCst)<=prover_parallel_jobs());
        let result=std::panic::catch_unwind(|| {let _permit=acquire();panic!("unwind");});
        assert!(result.is_err());
        let _next=acquire();
    }
}
