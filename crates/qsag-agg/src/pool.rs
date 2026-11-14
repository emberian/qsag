//! Persistent worker pool for the verifier's short data-parallel bursts.
//!
//! A `Hem` verification is a few milliseconds long and alternates sequential Fiat–Shamir work
//! with bursts of independent per-query arithmetic. Spawning scoped OS threads per burst costs
//! more than the burst itself, so verification submits index ranges to a lazily started pool of
//! `parallel_workers() - 1` threads by default (`QSAG_VERIFY_WORKERS` includes the caller).
//! The submitting thread always works on its own call
//! too, so a saturated or empty pool degrades to inline execution and can never deadlock.
//!
//! Jobs are `'static` (the crate forbids `unsafe`, so no lifetime erasure): callers move
//! reference-counted copies of the public proof data into the closure.

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::any::Any;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, OnceLock};

trait Help: Send + Sync {
    /// Claim and run chunks of one call until none are left.
    fn help(&self);
}

struct Pool {
    queue: Mutex<VecDeque<Arc<dyn Help>>>,
    ready: Condvar,
    threads: usize,
}

fn pool() -> Option<&'static Arc<Pool>> {
    static POOL: OnceLock<Option<Arc<Pool>>> = OnceLock::new();
    POOL.get_or_init(|| {
        let workers = std::env::var("QSAG_VERIFY_WORKERS")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|&workers| workers > 0)
            .unwrap_or_else(crate::parallel_workers)
            .min(crate::parallel_workers());
        let want = workers.saturating_sub(1);
        if want == 0 {
            return None;
        }
        let pool = Arc::new(Pool {
            queue: Mutex::new(VecDeque::new()),
            ready: Condvar::new(),
            threads: want,
        });
        let mut started = 0usize;
        for _ in 0..want {
            let worker_pool = Arc::clone(&pool);
            let spawned = std::thread::Builder::new()
                .name(std::string::String::from("qsag-agg-verify"))
                .spawn(move || {
                    loop {
                        let ticket = {
                            let mut queue = lock(&worker_pool.queue);
                            loop {
                                if let Some(ticket) = queue.pop_front() {
                                    break ticket;
                                }
                                queue = match worker_pool.ready.wait(queue) {
                                    Ok(guard) => guard,
                                    Err(poisoned) => poisoned.into_inner(),
                                };
                            }
                        };
                        ticket.help();
                    }
                });
            if spawned.is_ok() {
                started += 1;
            }
        }
        (started > 0).then_some(pool)
    })
    .as_ref()
}

/// Chunk bodies run under `catch_unwind`, so a poisoned lock still guards consistent data.
fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    match mutex.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    }
}

struct Call<T, F> {
    f: F,
    count: usize,
    chunk: usize,
    num_chunks: usize,
    next_chunk: AtomicUsize,
    state: Mutex<CallState<T>>,
    finished: Condvar,
}

struct CallState<T> {
    slots: Vec<Option<Vec<T>>>,
    remaining: usize,
    panic: Option<Box<dyn Any + Send>>,
}

impl<T, F> Help for Call<T, F>
where
    T: Send,
    F: Fn(usize) -> T + Send + Sync,
{
    fn help(&self) {
        loop {
            let c = self.next_chunk.fetch_add(1, Ordering::Relaxed);
            if c >= self.num_chunks {
                return;
            }
            let start = c * self.chunk;
            let end = (start + self.chunk).min(self.count);
            let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                (start..end).map(&self.f).collect::<Vec<T>>()
            }));
            let mut state = lock(&self.state);
            match out {
                Ok(values) => state.slots[c] = Some(values),
                Err(payload) => state.panic = Some(payload),
            }
            state.remaining -= 1;
            if state.remaining == 0 {
                self.finished.notify_all();
            }
        }
    }
}

/// Evaluate `f(0), .., f(count - 1)` in index order, `chunk` indices per work item, sharing the
/// work between the calling thread and idle pool workers. A panic in `f` is re-raised here.
pub(crate) fn map_indices<T, F>(count: usize, chunk: usize, f: F) -> Vec<T>
where
    T: Send + 'static,
    F: Fn(usize) -> T + Send + Sync + 'static,
{
    let chunk = chunk.max(1);
    let num_chunks = count.div_ceil(chunk);
    if num_chunks <= 1 {
        return (0..count).map(f).collect();
    }
    let Some(pool) = pool() else {
        return (0..count).map(f).collect();
    };
    let call = Arc::new(Call {
        f,
        count,
        chunk,
        num_chunks,
        next_chunk: AtomicUsize::new(0),
        state: Mutex::new(CallState {
            slots: (0..num_chunks).map(|_| None).collect(),
            remaining: num_chunks,
            panic: None,
        }),
        finished: Condvar::new(),
    });
    let tickets = (num_chunks - 1).min(pool.threads);
    {
        let mut queue = lock(&pool.queue);
        for _ in 0..tickets {
            queue.push_back(Arc::clone(&call) as Arc<dyn Help>);
        }
    }
    if tickets >= pool.threads {
        pool.ready.notify_all();
    } else {
        for _ in 0..tickets {
            pool.ready.notify_one();
        }
    }
    call.help();
    let mut state = lock(&call.state);
    while state.remaining > 0 {
        state = match call.finished.wait(state) {
            Ok(guard) => guard,
            Err(poisoned) => poisoned.into_inner(),
        };
    }
    if let Some(payload) = state.panic.take() {
        drop(state);
        std::panic::resume_unwind(payload);
    }
    let mut out = Vec::with_capacity(count);
    for slot in state.slots.iter_mut() {
        match slot.take() {
            Some(values) => out.extend(values),
            None => unreachable!("every chunk completed without a panic"),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_indices_is_ordered_complete_and_reentrant() {
        for (count, chunk) in [(0usize, 1usize), (1, 1), (7, 3), (258, 2), (1000, 17)] {
            let got = map_indices(count, chunk, |i| i * i + 1);
            let want: Vec<_> = (0..count).map(|i| i * i + 1).collect();
            assert_eq!(got, want);
        }
        // Calls made from inside pool work must complete (callers always self-serve).
        let nested = map_indices(64, 1, |i| map_indices(33, 2, move |j| i + j).len());
        assert_eq!(nested, alloc::vec![33usize; 64]);
    }

    #[test]
    fn map_indices_propagates_a_worker_panic() {
        let caught = std::panic::catch_unwind(|| {
            map_indices(128, 1, |i| {
                assert!(i != 77, "planted failure");
                i
            })
        });
        assert!(caught.is_err());
        // The pool stays usable afterwards.
        assert_eq!(map_indices(16, 1, |i| i).len(), 16);
    }
}
