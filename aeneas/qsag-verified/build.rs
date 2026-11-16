use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    // The parity mirror retains this production-only feature guard without enabling it.
    println!("cargo:rustc-check-cfg=cfg(feature, values(\"testing-ephemeral\"))");
    let rustc_bin = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let rustc_str = rustc_bin.to_string_lossy();
    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));

    // Charon only extracts `--lib` and never builds integration tests; skip parity staging under Charon.
    if rustc_str.contains("charon") {
        fs::write(out_dir.join("qsag_core_mods.rs"), "").expect("write empty core module stub");
        return;
    }

    let core_candidates = [
        manifest_dir.join("../../crates/qsag-core/src"),
        manifest_dir.join("../crates/qsag-core/src"),
    ];
    let core_src = core_candidates
        .iter()
        .find(|dir| dir.join("wipe.rs").is_file())
        .cloned()
        .unwrap_or_else(|| manifest_dir.join("../../crates/qsag-core/src"));
    let core_src = core_src.canonicalize().unwrap_or(core_src);

    // The library must build when copied out of this repository for extraction.
    // Differential tests need production source, but the no_std library does not.
    if !core_src.join("wipe.rs").is_file() {
        fs::write(out_dir.join("qsag_core_mods.rs"), "").expect("write standalone module stub");
        return;
    }

    let asm_candidates = [
        manifest_dir.join("../../crates/qsag-asm/src"),
        manifest_dir.join("../crates/qsag-asm/src"),
    ];
    let asm_src = asm_candidates
        .iter()
        .find(|dir| dir.join("lib.rs").is_file())
        .cloned()
        .unwrap_or_else(|| manifest_dir.join("../../crates/qsag-asm/src"));
    let asm_src = asm_src.canonicalize().unwrap_or(asm_src);

    let mut modules = String::new();
    if asm_src.join("lib.rs").is_file() {
        let asm_mirror = out_dir.join("qsag_asm_mirror");
        fs::create_dir_all(&asm_mirror).expect("create qsag_asm mirror dir");
        // Mirror every top-level module of `qsag-asm`, so a module added there cannot
        // silently break the parity build (as `linear_map.rs` and `wipe.rs` once did).
        let mut asm_modules: Vec<String> = fs::read_dir(&asm_src)
            .expect("read qsag-asm sources")
            .map(|entry| entry.expect("read qsag-asm entry"))
            .filter(|entry| entry.file_type().expect("qsag-asm file type").is_file())
            .filter_map(|entry| entry.file_name().into_string().ok())
            .filter(|name| name.ends_with(".rs"))
            .collect();
        asm_modules.sort();
        for asm_rel in &asm_modules {
            let p = asm_src.join(asm_rel);
            if p.is_file() {
                println!("cargo:rerun-if-changed={}", p.display());
                let raw = fs::read_to_string(&p).expect("read qsag-asm file");
                let mut adapted = String::with_capacity(raw.len() + 64);
                for line in raw.lines() {
                    if line.trim().starts_with("#![") || line.trim().starts_with("//!") {
                        continue;
                    }
                    // `qsag-core` always enables `qsag-asm/alloc`, and the mirror is only
                    // compiled into the std-hosted parity test, so its `alloc` gate is open.
                    adapted.push_str(
                        &line
                            .replace("crate::", "crate::qsag_asm::")
                            .replace("feature = \"alloc\"", "all()"),
                    );
                    adapted.push('\n');
                }
                fs::write(asm_mirror.join(asm_rel), adapted).expect("write mirrored qsag-asm file");
            }
        }
        let asm_dir = asm_src.join("asm");
        let asm_dst = asm_mirror.join("asm");
        fs::create_dir_all(&asm_dst).expect("create assembly mirror directory");
        for entry in fs::read_dir(&asm_dir).expect("read assembly sources") {
            let entry = entry.expect("read assembly entry");
            if entry.file_type().expect("assembly file type").is_file() {
                println!("cargo:rerun-if-changed={}", entry.path().display());
                fs::copy(entry.path(), asm_dst.join(entry.file_name()))
                    .expect("mirror assembly source");
            }
        }
        modules.push_str(&format!(
            "#[allow(dead_code, unused_imports, clippy::all)]\n#[path = {:?}]\nmod qsag_asm;\n",
            asm_mirror.join("lib.rs")
        ));
    }

    // Production core delegates arithmetic, comparisons and SHA-2 to pure `qsag-accel` CPU modules.
    // Mirror those pure modules directly (skipping Vulkan/SPIR-V driver FFI) so the extracted
    // `no_std` library stays dependency-free and differential parity builds warning-free.
    let accel_src = core_src
        .join("../../qsag-accel/src")
        .canonicalize()
        .expect("locate qsag-accel for production parity");
    let accel_mirror = out_dir.join("qsag_accel_mirror");
    fs::create_dir_all(&accel_mirror).expect("create qsag-accel mirror");
    for accel_rel in ["ct.rs", "goldilocks.rs", "keccak.rs", "poseidon2.rs", "sha2.rs"] {
        let entry_path = accel_src.join(accel_rel);
        println!("cargo:rerun-if-changed={}", entry_path.display());
        let raw = fs::read_to_string(&entry_path).expect("read qsag-accel source");
        let adapted = raw
            .replace("#![no_std]", "")
            .replace("crate::", "crate::qsag_accel::")
            .replace("feature = \"alloc\"", "all()")
            + "\n#[allow(unused_imports)]\nuse crate::qsag_asm;\n";
        fs::write(accel_mirror.join(accel_rel), adapted).expect("write accel mirror");
    }
    let accel_mod = r#"extern crate alloc;
pub mod ct;
pub mod goldilocks;
pub mod keccak;
pub mod poseidon2;
pub mod sha2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AccelError {
    LengthMismatch { what: &'static str, expected: usize, actual: usize },
    NotPowerOfTwo { what: &'static str, len: usize },
    DomainTooLarge { log2_len: u32 },
    LengthOverflow,
    InvalidTwiddles,
    BackendFailure,
}

fn cpu_workers(len: usize, min_chunk: usize) -> usize {
    if len / min_chunk < 2 {
        return 1;
    }
    std::thread::available_parallelism()
        .map_or(1, usize::from)
        .min(len / min_chunk)
}

fn cpu_drain<J: Send>(workers: usize, jobs: impl Iterator<Item = J> + Send, run: impl Fn(J) + Sync) {
    let jobs = std::sync::Mutex::new(jobs);
    let drain = || {
        while let Some(job) = jobs
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .next()
        {
            run(job);
        }
    };
    std::thread::scope(|scope| {
        for _ in 1..workers {
            if std::thread::Builder::new().spawn_scoped(scope, drain).is_err() {
                break;
            }
        }
        drain();
    });
}

fn cpu_chunks_mut<T: Send>(items: &mut [T], min_chunk: usize, run: impl Fn(usize, &mut [T]) + Sync) {
    let workers = cpu_workers(items.len(), min_chunk);
    if workers > 1 {
        let chunk_len = items.len().div_ceil(workers);
        cpu_drain(
            workers,
            items.chunks_mut(chunk_len).enumerate(),
            |(i, chunk)| run(i * chunk_len, chunk),
        );
        return;
    }
    run(0, items);
}
"#;
    fs::write(accel_mirror.join("mod.rs"), accel_mod).expect("write accel mirror mod.rs");
    modules.push_str(&format!(
        "#[allow(dead_code, unused_imports, clippy::all)]\n#[path = {:?}]\nmod qsag_accel;\n",
        accel_mirror.join("mod.rs")
    ));

    let mirror_root = out_dir.join("qsag_core_mirror");
    for relative_path in [
        "wipe.rs",
        "field/mod.rs",
        "field/goldilocks.rs",
        "field/tower.rs",
        "sponge/mod.rs",
        "sponge/keccak.rs",
        "sponge/poseidon2.rs",
        "fips205.rs",
        "tsw_baggy.rs",
        "belt_latch.rs",
    ] {
        let src_file = core_src.join(relative_path);
        println!("cargo:rerun-if-changed={}", src_file.display());
        assert!(
            src_file.is_file(),
            "missing parity source: {}",
            src_file.display()
        );
        {
            let dst_file = mirror_root.join(relative_path);
            if let Some(parent) = dst_file.parent() {
                fs::create_dir_all(parent).expect("create mirror subdir");
            }
            let raw = fs::read_to_string(&src_file).expect("read qsag-core source file");
            let patched = if raw.contains("qsag_asm::") {
                inject_qsag_asm_import(&raw)
            } else {
                raw
            };
            let patched = if patched.contains("qsag_accel::") {
                patched + "\n#[allow(unused_imports)]\nuse crate::qsag_accel;\n"
            } else {
                patched
            };
            fs::write(&dst_file, patched).expect("write mirrored qsag-core source file");
        }
    }

    // Mount production source modules directly for differential tests: this crate's
    // standalone [workspace] isolates `charon cargo` from inline-ASM workspace crates.
    for (name, relative_path) in [
        ("wipe", "wipe.rs"),
        ("field", "field/mod.rs"),
        ("sponge", "sponge/mod.rs"),
        ("fips205", "fips205.rs"),
        ("tsw_baggy", "tsw_baggy.rs"),
        ("belt_latch", "belt_latch.rs"),
    ] {
        let path = mirror_root.join(relative_path);
        modules.push_str(&format!(
            "#[allow(clippy::all)]\n#[path = {:?}]\nmod {};\n",
            path, name
        ));
    }
    fs::write(out_dir.join("qsag_core_mods.rs"), modules).expect("write core module declarations");
}

fn inject_qsag_asm_import(src: &str) -> String {
    let mut insert_offset = 0usize;
    for line in src.split_inclusive('\n') {
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("#![") {
            insert_offset += line.len();
        } else {
            break;
        }
    }
    let mut out = String::with_capacity(src.len() + 64);
    out.push_str(&src[..insert_offset]);
    out.push_str("#[allow(unused_imports)]\nuse crate::qsag_asm;\n");
    out.push_str(&src[insert_offset..]);
    out
}
