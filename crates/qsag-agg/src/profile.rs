//! Opt-in inclusive phase timings. Nested and concurrent spans must not be summed.

pub(crate) struct Span {
    #[cfg(feature = "std")]
    state: Option<(&'static str, std::time::Instant)>,
}

pub(crate) fn span(_name: &'static str) -> Span {
    Span {
        #[cfg(feature = "std")]
        state: {
            static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            ENABLED
                .get_or_init(|| std::env::var_os("QSAG_PROFILE").is_some())
                .then(|| (_name, std::time::Instant::now()))
        },
    }
}

impl Drop for Span {
    fn drop(&mut self) {
        #[cfg(feature = "std")]
        if let Some((name, start)) = self.state {
            std::eprintln!(
                "qsag_phase {name} {:.3} ms",
                start.elapsed().as_secs_f64() * 1000.0
            );
        }
    }
}
