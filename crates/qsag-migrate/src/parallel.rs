//! Ordered, bounded repetition scheduling with a no-std serial fallback.
use alloc::vec::Vec;

pub(crate) fn map<T: Send, F: Fn(usize) -> T + Sync>(len: usize, f: F) -> Vec<T> {
    #[cfg(any(feature = "std", test))]
    {
        let workers = std::thread::available_parallelism()
            .map_or(1, |n| n.get())
            .min(16);
        let chunk = len.div_ceil(workers).max(1);
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..len)
                .step_by(chunk)
                .map(|start| {
                    let f = &f;
                    scope
                        .spawn(move || (start..(start + chunk).min(len)).map(f).collect::<Vec<_>>())
                })
                .collect();
            handles
                .into_iter()
                .flat_map(|h| h.join().expect("repetition worker panicked"))
                .collect()
        })
    }
    #[cfg(not(any(feature = "std", test)))]
    (0..len).map(f).collect()
}
