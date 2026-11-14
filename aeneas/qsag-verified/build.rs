use std::{env, fs, path::PathBuf, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(qsag_nightly_const_option)");
    let rustc_bin = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let rustc_str = rustc_bin.to_string_lossy();
    let compiler = Command::new(&rustc_bin)
        .arg("-vV")
        .output()
        .expect("query compiler version");
    if String::from_utf8_lossy(&compiler.stdout).contains("-nightly") {
        println!("cargo:rustc-cfg=qsag_nightly_const_option");
    }
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
        for asm_rel in [
            "lib.rs",
            "cpuid.rs",
            "bitslice.rs",
            "portable.rs",
            "x86_64_asm.rs",
            "aarch64_asm.rs",
        ] {
            let p = asm_src.join(asm_rel);
            if p.is_file() {
                println!("cargo:rerun-if-changed={}", p.display());
                let raw = fs::read_to_string(&p).expect("read qsag-asm file");
                let mut adapted = String::with_capacity(raw.len() + 64);
                for line in raw.lines() {
                    if line.trim().starts_with("#![") || line.trim().starts_with("//!") {
                        continue;
                    }
                    adapted.push_str(&line.replace("crate::", "crate::qsag_asm::"));
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
                fs::copy(entry.path(), asm_dst.join(entry.file_name())).expect("mirror assembly source");
            }
        }
        modules.push_str(&format!(
            "#[allow(dead_code, unused_imports, clippy::all)]\n#[path = {:?}]\nmod qsag_asm;\n",
            asm_mirror.join("lib.rs")
        ));
    }

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
    ] {
        let src_file = core_src.join(relative_path);
        println!("cargo:rerun-if-changed={}", src_file.display());
        assert!(src_file.is_file(), "missing parity source: {}", src_file.display());
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
    ] {
        let path = mirror_root.join(relative_path);
        modules.push_str(&format!("#[allow(clippy::all)]\n#[path = {:?}]\nmod {};\n", path, name));
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
