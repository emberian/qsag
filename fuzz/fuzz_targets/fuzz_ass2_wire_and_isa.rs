// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided adversarial wire-frame, WOTS+C capability, ISA codec, assembler, and
//! constant-time DIT VM fuzzer for `qsag-ass2`.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_ass2::wire::{
    OwnerOp, capability_commit_code, encode_owner_lifecycle_frame, load_code_frame,
    load_code_open_frame, load_code_wotsc_frame, owner_wotsc_pubkey,
    parse_and_verify_load_code_wotsc_frame, parse_and_verify_owner_lifecycle_frame,
    parse_load_code_frame, parse_load_code_open_frame,
};
use qsag_ass2::{
    Ass2Vm, DitMode, LcState, assemble, decode_insn_le, disassemble_insn, encode_insn_le,
};

struct Ass2Fixtures {
    owner_pk: [u8; 32],
    enclave_id: [u8; 32],
    nonce: [u8; 16],
    record: u64,
    lease_frame: [u8; 329],
    fast_load_frame: Vec<u8>,
    wotsc_load_frame: Vec<u8>,
}

fn fixtures() -> &'static Ass2Fixtures {
    static FX: OnceLock<Ass2Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let sk0 = [0x42u8; 32];
        let sk1 = [0x99u8; 32];
        let owner_pk = owner_wotsc_pubkey(&sk0);
        let next_pk = owner_wotsc_pubkey(&sk1);
        let enclave_id = [0xA5u8; 32];
        let nonce: [u8; 16] = core::array::from_fn(|i| (i + 1) as u8);
        let record = (3u64 << 32) | 1;
        let words = [0x0006_0000u32, 0x0005_0000u32]; // ZEROIZE; HALT
        let sib = [0x7Bu8; 16];
        let cap = capability_commit_code(
            &qsag_ass2::wire::compute_image_id(&enclave_id, &words),
            &sib,
        );

        let lease_frame = encode_owner_lifecycle_frame(
            0x80,
            &sk0,
            &enclave_id,
            OwnerOp::Lease {
                expected_record: record,
            },
            &nonce,
            record,
            &cap,
            &next_pk,
        )
        .expect("lease frame");
        assert!(
            parse_and_verify_owner_lifecycle_frame(
                &lease_frame,
                &owner_pk,
                &enclave_id,
                &nonce,
                record
            )
            .is_ok()
        );

        let fast_load_frame = load_code_frame(0x40, &sib, &words).expect("fast load");
        assert!(parse_load_code_frame(&fast_load_frame).is_ok());

        let wotsc_load_frame =
            load_code_wotsc_frame(0x80, &sk0, &enclave_id, &nonce, record, &next_pk, &words)
                .expect("wotsc load");
        assert!(
            parse_and_verify_load_code_wotsc_frame(
                &wotsc_load_frame,
                &owner_pk,
                &enclave_id,
                &nonce,
                record
            )
            .is_ok()
        );

        Ass2Fixtures {
            owner_pk,
            enclave_id,
            nonce,
            record,
            lease_frame,
            fast_load_frame,
            wotsc_load_frame,
        }
    })
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    // 1. Untrusted wire frames
    if let Ok((prefix, words)) = parse_load_code_open_frame(data) {
        let reencoded = load_code_open_frame(prefix, &words).expect("canonical open re-encode");
        assert_eq!(reencoded, data);
    }
    if let Ok((prefix, words, sib)) = parse_load_code_frame(data) {
        let reencoded = load_code_frame(prefix, &sib, &words).expect("canonical re-encode");
        assert_eq!(reencoded, data);
    }
    let _ = parse_and_verify_owner_lifecycle_frame(
        data,
        &fx.owner_pk,
        &fx.enclave_id,
        &fx.nonce,
        fx.record,
    );
    let _ = parse_and_verify_load_code_wotsc_frame(
        data,
        &fx.owner_pk,
        &fx.enclave_id,
        &fx.nonce,
        fx.record,
    );

    // 2. Seeded mutations over valid signed lifecycle & load_code frames
    if let Some((&sel, rest)) = data.split_first() {
        match sel % 3 {
            0 => {
                let mut f = fx.lease_frame.to_vec();
                for e in rest.chunks_exact(3).take(6) {
                    let i = (u16::from_le_bytes([e[0], e[1]]) as usize) % f.len();
                    f[i] ^= e[2];
                }
                // Byte 0 is the unauthenticated SPI link-width prefix (`0x00`, `0x40`, `0x80`);
                // any mutation inside `header[8B] || payload[320B]` (`f[1..]`) MUST be rejected!
                if f[1..] != fx.lease_frame[1..] {
                    let res = parse_and_verify_owner_lifecycle_frame(
                        &f,
                        &fx.owner_pk,
                        &fx.enclave_id,
                        &fx.nonce,
                        fx.record,
                    );
                    assert!(res.is_err(), "mutated owner lifecycle frame forged WOTS+C!");
                }
            }
            1 => {
                let mut f = fx.fast_load_frame.clone();
                for e in rest.chunks_exact(3).take(6) {
                    let i = (u16::from_le_bytes([e[0], e[1]]) as usize) % f.len();
                    f[i] ^= e[2];
                }
                if let Ok((p, ws, sib)) = parse_load_code_frame(&f) {
                    assert_eq!(load_code_frame(p, &sib, &ws).unwrap(), f);
                }
            }
            _ => {
                let mut f = fx.wotsc_load_frame.clone();
                for e in rest.chunks_exact(3).take(6) {
                    let i = (u16::from_le_bytes([e[0], e[1]]) as usize) % f.len();
                    f[i] ^= e[2];
                }
                if f[1..] != fx.wotsc_load_frame[1..] {
                    let res = parse_and_verify_load_code_wotsc_frame(
                        &f,
                        &fx.owner_pk,
                        &fx.enclave_id,
                        &fx.nonce,
                        fx.record,
                    );
                    assert!(res.is_err(), "mutated WOTS+C load_code frame forged signature!");
                }
            }
        }
    }

    // 3. Total 32-bit ISA codec bijection + disassembler roundtrip
    for chunk in data.chunks_exact(4).take(64) {
        let word: [u8; 4] = chunk.try_into().unwrap();
        if let Some(insn) = decode_insn_le(word) {
            let reencoded = encode_insn_le(&insn).expect("decoded insn must re-encode");
            assert_eq!(reencoded, word, "non-bijective ASS2 instruction encoding");
            let text = disassemble_insn(&insn);
            let asm = assemble(&text).expect("disassembled insn must assemble");
            assert_eq!(asm, word);
        }
    }

    // 4. Bounded UTF-8 assembler + bounded `Ass2Vm` execution with trap-latch check
    if data.len() <= 512
        && let Ok(src) = core::str::from_utf8(data)
    {
        let _ = assemble(src);
    }
    if data.len() >= 4 {
        let code_len = (data.len() & !3).min(256);
        let mut vm = Ass2Vm::new(4096);
        vm.dit_mode = DitMode::Trap;
        if vm.load_image(0, &data[..code_len]).is_ok() {
            let exit1 = vm.run(32);
            if let qsag_ass2::RunExit::Trap(cause) = exit1 {
                assert_eq!(vm.step(), qsag_ass2::StepOutcome::Trap(cause));
                assert_eq!(vm.run(4), qsag_ass2::RunExit::Trap(cause));
            }
        }
        // Also exercise the Two-Ring W^X hardware enclave MPU in Ring 3 (`<= 64` words).
        let words: Vec<u32> = data[..code_len]
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
            .collect();
        let mut enc_vm = Ass2Vm::new_enclave([0x55; 32], LcState::Blank);
        enc_vm.dit_mode = DitMode::Trap;
        if enc_vm.load_open_applet(&words).is_ok() {
            let _ = enc_vm.run(32);
        }
    }
});
