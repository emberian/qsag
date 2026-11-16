//! Bound heavyweight proof witnesses independently of fine-grained arithmetic workers.
//! Default one active batch keeps CPU traces from accumulating behind the exclusive GPU arena.
//! QSAG_PROVER_JOBS opts into more concurrent witnesses; it is NOT a byte-memory guarantee.
//! Each batch retains its original statement/transcript and cryptographic batching.
use std::sync::{Condvar, Mutex, OnceLock};

pub(crate) fn prover_parallel_jobs() -> usize {
    static JOBS: OnceLock<usize> = OnceLock::new();
    (*JOBS.get_or_init(|| {
        std::env::var("QSAG_PROVER_JOBS")
            .ok()
            .and_then(|x| x.parse::<usize>().ok())
            .filter(|&x| x > 0)
            .unwrap_or(1)
    }))
    .min(crate::parallel_workers())
    .max(1)
}
struct AdmissionState {
    active_threads: usize,
    holders: alloc::vec::Vec<(std::thread::ThreadId, usize)>,
}

static STATE: Mutex<AdmissionState> = Mutex::new(AdmissionState {
    active_threads: 0,
    holders: alloc::vec::Vec::new(),
});
static READY: Condvar = Condvar::new();
pub(crate) struct Permit {
    owner: std::thread::ThreadId,
}
pub(crate) fn acquire() -> Permit {
    let tid = std::thread::current().id();
    let mut state = STATE.lock().unwrap_or_else(|e| e.into_inner());
    if let Some((_, depth)) = state.holders.iter_mut().find(|(id, _)| *id == tid) {
        *depth += 1;
        return Permit { owner: tid };
    }
    let limit = prover_parallel_jobs();
    while state.active_threads >= limit {
        state = READY.wait(state).unwrap_or_else(|e| e.into_inner());
    }
    state.active_threads += 1;
    state.holders.push((tid, 1));
    Permit { owner: tid }
}
impl Drop for Permit {
    fn drop(&mut self) {
        // CPU-only work may transfer this permit; Vulkan arena leases remain thread-bound.
        let tid = self.owner;
        let mut state = STATE.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(pos) = state.holders.iter().position(|(id, _)| *id == tid) {
            if state.holders[pos].1 > 1 {
                state.holders[pos].1 -= 1;
                return;
            }
            state.holders.swap_remove(pos);
            state.active_threads -= 1;
            READY.notify_all();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn transferred_permit_releases_the_original_owner() {
        let tid = std::thread::current().id();
        let permit = acquire();
        std::thread::spawn(move || drop(permit)).join().unwrap();
        let state = STATE.lock().unwrap_or_else(|e| e.into_inner());
        assert!(!state.holders.iter().any(|(owner, _)| *owner == tid));
    }
    #[test]
    fn admission_bounds_live_witnesses_and_releases_on_unwind() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let live = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let (live, peak) = (&live, &peak);
                scope.spawn(move || {
                    let _permit = acquire();
                    let n = live.fetch_add(1, Ordering::SeqCst) + 1;
                    peak.fetch_max(n, Ordering::SeqCst);
                    for _ in 0..32 {
                        std::thread::yield_now();
                    }
                    live.fetch_sub(1, Ordering::SeqCst);
                });
            }
        });
        assert!(peak.load(Ordering::SeqCst) <= prover_parallel_jobs());
        let result = std::panic::catch_unwind(|| {
            let _permit = acquire();
            panic!("unwind");
        });
        assert!(result.is_err());
        let _next = acquire();
    }
}
