//! Read the QSAG shell capabilities, verifier status and three diagnostic words.
#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
fn main() -> Result<(), String> {
    use qsag_accel::aws_f2::{AwsF2Backend, linux::PciBars};
    use std::path::Path;
    let device = std::env::args_os()
        .nth(1)
        .ok_or("supply the AppPF PCI sysfs directory")?;
    let bars = PciBars::open(Path::new(&device)).map_err(|e| e.to_string())?;
    let mut backend = AwsF2Backend::attach(bars).map_err(|e| format!("{e:?}"))?;
    println!(
        "ASS2 diagnostics-only image: {}",
        backend.diagnostics_only().map_err(|e| format!("{e:?}"))?
    );
    for i in 0..backend.engine_count() {
        let status = backend
            .ni(i)
            .and_then(|mut ni| ni.status())
            .map_err(|e| format!("{e:?}"))?;
        println!("NI {i}: {} checks, pass={}", status.checks, status.pass);
    }
    for vat in 0..3 {
        let diag = backend.enclaves().diag(vat).map_err(|e| format!("{e:?}"))?;
        if diag >> 56 != 0x5a || diag as u16 != 0xa552 {
            return Err(format!("vat {vat} returned invalid READ_DIAG {diag:016x}"));
        }
        println!("vat {vat}: {diag:016x}");
    }
    Ok(())
}
#[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
fn main() {
    eprintln!("aws_f2_smoke requires 64-bit Linux and --features std");
    std::process::exit(2);
}
