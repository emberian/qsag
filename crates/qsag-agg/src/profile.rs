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
            let (rss, peak) = resident_mib();
            std::eprintln!(
                "qsag_phase {name} {:.3} ms rss_mib={rss} peak_mib={peak}",
                start.elapsed().as_secs_f64() * 1000.0
            );
        }
    }
}

/// Current and peak resident set of this process in MiB (`0` where `/proc` is absent).
#[cfg(feature = "std")]
fn resident_mib() -> (u64, u64) {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let field = |key: &str| {
        status
            .lines()
            .find_map(|line| line.strip_prefix(key))
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|kib| kib.parse::<u64>().ok())
            .map_or(0, |kib| kib / 1024)
    };
    (field("VmRSS:"), field("VmHWM:"))
}
