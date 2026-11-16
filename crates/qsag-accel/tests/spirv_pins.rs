//! SHA-256 pins of the ten embedded SPIR-V modules.
//!
//! `test_spirv_shaders_reproducible_from_comp_sources` (in `vulkan_rdna2_differential.rs`)
//! checks that the embedded words are what `glslangValidator 14.3.0` produces from
//! `shaders/*.comp`; it needs the compiler. These pins need nothing: any change to a shader
//! or to `spirv_kernels.rs` has to arrive together with a deliberate edit of this table.
//! Regenerate the modules with `tools/regenerate_spirv.py` and take the new digests from
//! `sha256sum` of the compiler's `.spv` output.

use qsag_accel::sha2::sha256;
use qsag_accel::spirv_kernels::{
    prover_shader_source_filename, prover_spirv_kernel_bytes, prover_spirv_kernel_words,
    shader_source_filename, spirv_kernel_bytes, spirv_kernel_words,
};
use qsag_accel::{KernelSlot, ProverKernelSlot};

const PINS: [(&str, &str); 10] = [
    (
        "keccak_f1600.comp",
        "7bf1c70e4c21de7e75140d4b9fe40f4309fcd4a53407ed4cd5093d3c9157244f",
    ),
    (
        "poseidon2_perm12.comp",
        "06f5ee14f9d2bf3e353d049b96e121ee0ea656e31e978d735fdacf7cde9837f5",
    ),
    (
        "goldilocks_ntt.comp",
        "f0a593ae773214a66bc937dc4cf13f68ec4c8c75be177c567c3b546c0007add4",
    ),
    (
        "coset_lde_ext2.comp",
        "71aee0355d7745f26ffc2f534e83e89650224ee211318931ccfddf5932923d1c",
    ),
    (
        "merkle_layer_poseidon2.comp",
        "92e0593a7f25939313497b3b8c392d2dafb10a5897adf4fc736c05840cac9ae0",
    ),
    (
        "bdoz_gf2_128_dot.comp",
        "16430babdf5008c5f824152a1d2fbef2963c8b056b89f6cccfba1860639eda64",
    ),
    (
        "whir_lde_merkle.comp",
        "fe24dd768ebc637b1d3c14ee96aab5b9472cd355aca8535744238fbb6e6bb602",
    ),
    (
        "whir_fold_sumcheck.comp",
        "70cb40c582f8205a0998853a23998b809282340a3ef3f60196d4ffb438456387",
    ),
    (
        "air_row_group_a.comp",
        "8e1739147f4b401dbfbe867cf8ff286a81c92eebe7906c78dacb2f6fdd531940",
    ),
    (
        "air_row_group_b.comp",
        "26f9c47d538371ccf738f08ef036a305a73fcfc0218e83554f0c62be205ee05e",
    ),
];

fn hex(digest: &[u8; 32]) -> String {
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn embedded_spirv_modules_match_their_sha256_pins() {
    let kernels = KernelSlot::ALL.map(|slot| {
        (
            shader_source_filename(slot),
            spirv_kernel_bytes(slot),
            spirv_kernel_words(slot),
        )
    });
    let prover = ProverKernelSlot::ALL.map(|slot| {
        (
            prover_shader_source_filename(slot),
            prover_spirv_kernel_bytes(slot),
            prover_spirv_kernel_words(slot),
        )
    });
    let mut seen = 0usize;
    for (name, bytes, words) in kernels.into_iter().chain(prover) {
        // SPIR-V magic, and the byte view is the little-endian image of the word view.
        assert_eq!(words[0], 0x0723_0203, "{name}");
        assert_eq!(bytes.len(), words.len() * 4, "{name}");
        assert!(
            words
                .iter()
                .zip(bytes.as_chunks::<4>().0)
                .all(|(w, b)| w.to_le_bytes() == *b),
            "{name}"
        );
        let pinned = PINS
            .iter()
            .find(|(pin_name, _)| *pin_name == name)
            .unwrap_or_else(|| panic!("no SHA-256 pin for {name}"))
            .1;
        assert_eq!(
            hex(&sha256(bytes)),
            pinned,
            "embedded SPIR-V for {name} differs from its pin"
        );
        seen += 1;
    }
    assert_eq!(seen, PINS.len());
}
