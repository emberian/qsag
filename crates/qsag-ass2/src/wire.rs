//! Zero-Factory-Trust Post-Quantum Owner Authority (`WOTS+C`) & `QSAG-Wire` Host Encoder
//! for `ASS2-0P5 / Dregg-64` Rev. 2.0.
//!
//! Security properties:
//! * **Zero Factory Trust:** `CMD_ENROL` (`0x11`) accepts only the Owner's 32-byte post-quantum
//!   `WOTS+C` public root `owner_auth_root` (`pk_0`), seals `(bch_helpers, pk_0)` in private FRAM
//!   under the enclave's internal 144-bit-entropy PUF `root_secret`, and exports the public
//!   `enclave_id = TurboSHAKE256("AS2PUBID" || root_secret || owner_auth_root)`. Neither the
//!   factory nor the host ever learns `root_secret`!
//! * **128-Bit Post-Quantum `WOTS+C` Signatures:** `CMD_COMMIT` (`0x12`), `CMD_LEASE` (`0x15`),
//!   `CMD_GATE` (`0x16`), and inline `CMD_LOAD_CODE` (`0x30`, `flags = 2`) verify a 16-chain
//!   base-256 constant-sum (`sum == 2040`, zero checksum chains) `TurboSHAKE256` `WOTS+C` proof
//!   (`296 B`) against `cur_wots_root` and atomically roll `(gen + 1, state, next_wots_root)` in
//!   Dual-Slot FRAM.
//! * **Fast Capability-Committed Code & CTH Signing:** `CMD_LEASE` / `CMD_GATE` also install an
//!   Owner-signed 16-byte Merkle capability root `cap_commit` into `SYS_MMIO`, allowing fast
//!   `20 + 4*n`-byte `CMD_LOAD_CODE` (`flags = 1`) and `120`-byte `CMD_CTH_SIGN` (`0x20`) frames
//!   without any shared symmetric secret on the SPI bus.

use alloc::vec::Vec;
use qsag_accel::gf2_128::gf2_128_mul_const;
use qsag_accel::keccak::KECCAK_RC;
use qsag_core::sponge::keccak::KECCAK_ROTATION_OFFSETS;

pub const WOTSC_CHAINS: usize = 16;
pub const WOTSC_BASE: usize = 256;
pub const WOTSC_TARGET_SUM: u32 = 2040;
pub const WOTSC_PROOF_BYTES: usize = 8 + 32 + WOTSC_CHAINS * 16; // 296 B

/// Single 12-round `Keccak-p[1600, 12]` (`TurboSHAKE256`, RFC 9861) matching `KECCAK.F1600 12`.
pub fn keccak_p1600_12(state: &mut [u64; 25]) {
    for &rc in &KECCAK_RC[12..24] {
        let parity: [u64; 5] = core::array::from_fn(|x| {
            state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
        });
        let mut b = [0u64; 25];
        for (i, &lane) in state.iter().enumerate() {
            let (x, y) = (i % 5, i / 5);
            let d = parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
            b[y + 5 * ((2 * x + 3 * y) % 5)] = (lane ^ d).rotate_left(KECCAK_ROTATION_OFFSETS[i]);
        }
        for (row, input) in state.chunks_exact_mut(5).zip(b.chunks_exact(5)) {
            for x in 0..5 {
                row[x] = input[x] ^ (!input[(x + 1) % 5] & input[(x + 2) % 5]);
            }
        }
        state[0] ^= rc;
    }
}

/// Absorb up to 136-byte rate block(s) with domain separator `0x1F` (`TurboSHAKE256`).
pub fn turboshake256(msg: &[u8], out: &mut [u8]) {
    let mut st = [0u64; 25];
    let mut pos = 0;
    while pos + 136 <= msg.len() {
        for i in 0..17 {
            st[i] ^= u64::from_le_bytes(msg[pos + 8 * i..pos + 8 * i + 8].try_into().unwrap());
        }
        keccak_p1600_12(&mut st);
        pos += 136;
    }
    let mut last = [0u8; 136];
    let rem = msg.len() - pos;
    last[..rem].copy_from_slice(&msg[pos..]);
    last[rem] ^= 0x1F;
    last[135] ^= 0x80;
    for i in 0..17 {
        st[i] ^= u64::from_le_bytes(last[8 * i..8 * i + 8].try_into().unwrap());
    }
    keccak_p1600_12(&mut st);

    let mut written = 0;
    while written < out.len() {
        for i in 0..17 {
            if written >= out.len() {
                break;
            }
            let bytes = st[i].to_le_bytes();
            let take = (out.len() - written).min(8);
            out[written..written + take].copy_from_slice(&bytes[..take]);
            written += take;
        }
        if written < out.len() {
            keccak_p1600_12(&mut st);
        }
    }
}

fn wotsc_secret_start(sk_seed: &[u8; 32], chain_idx: usize) -> [u8; 16] {
    let mut buf = [0u8; 48];
    buf[..8].copy_from_slice(b"AS2WSK01");
    buf[8..40].copy_from_slice(sk_seed);
    buf[40..48].copy_from_slice(&(chain_idx as u64).to_le_bytes());
    let mut out = [0u8; 16];
    turboshake256(&buf, &mut out);
    out
}

fn wotsc_step(node: &[u8; 16], chain_idx: usize, step: usize) -> [u8; 16] {
    let mut st = [0u64; 25];
    st[0] = 0x57531;
    st[1] = u64::from_le_bytes(node[..8].try_into().unwrap());
    st[2] = u64::from_le_bytes(node[8..16].try_into().unwrap());
    st[3] = ((chain_idx as u64) << 8) | (step as u64);
    st[4] = 0x1F;
    st[16] = 0x80u64 << 56;
    keccak_p1600_12(&mut st);
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&st[0].to_le_bytes());
    out[8..16].copy_from_slice(&st[1].to_le_bytes());
    out
}

/// Compute the 32-byte `WOTS+C` public key root `pk` from a 32-byte secret key seed.
pub fn owner_wotsc_pubkey(sk_seed: &[u8; 32]) -> [u8; 32] {
    let mut msg = [0u8; WOTSC_CHAINS * 16 + 8];
    for i in 0..WOTSC_CHAINS {
        let mut cur = wotsc_secret_start(sk_seed, i);
        for s in 0..(WOTSC_BASE - 1) {
            cur = wotsc_step(&cur, i, s);
        }
        msg[16 * i..16 * (i + 1)].copy_from_slice(&cur);
    }
    msg[WOTSC_CHAINS * 16..].copy_from_slice(&0x57501u64.to_le_bytes());
    let mut pk = [0u8; 32];
    turboshake256(&msg, &mut pk);
    pk
}

/// Owner-authorized operations verified by the enclave's `I-ROM` `WOTS+C` engine.
#[derive(Clone, Copy, Debug)]
pub enum OwnerOp {
    Commit,
    Lease { expected_record: u64 },
    Gate { from: u32, to: u32 },
    LoadCode { word_count: u32, img_id: [u8; 16] },
}

fn wotsc_challenge_digest(
    enclave_id: &[u8; 32],
    opcode: u64,
    op_value: u64,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
    salt: u64,
) -> [u8; 16] {
    let mut msg = [0u8; 128];
    msg[0..8].copy_from_slice(&0x574d1u64.to_le_bytes());
    msg[8..32].copy_from_slice(&enclave_id[..24]);
    msg[32..40].copy_from_slice(&opcode.to_le_bytes());
    msg[40..48].copy_from_slice(&record.to_le_bytes());
    msg[48..64].copy_from_slice(nonce);
    msg[64..80].copy_from_slice(cap_commit);
    msg[80..88].copy_from_slice(&op_value.to_le_bytes());
    msg[88..96].copy_from_slice(&salt.to_le_bytes());
    msg[96..128].copy_from_slice(next_wots_root);
    let mut digest = [0u8; 16];
    turboshake256(&msg, &mut digest);
    digest
}

/// Produce the `296`-byte `WOTS+C` proof (`wots_salt[8B] || next_wots_root[32B] || chains[256B]`).
pub fn sign_wotsc_proof(
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
) -> [u8; WOTSC_PROOF_BYTES] {
    let (opcode, op_value, eff_cap): (u64, u64, [u8; 16]) = match op {
        OwnerOp::Commit => (0x12, 0, *cap_commit),
        OwnerOp::Lease { expected_record } => (0x15, expected_record, *cap_commit),
        OwnerOp::Gate { from, to } => (0x16, (u64::from(from) << 32) | u64::from(to), *cap_commit),
        OwnerOp::LoadCode { word_count, img_id } => (0x30, u64::from(word_count), img_id),
    };

    let mut salt = 0u64;
    let digits = loop {
        let d = wotsc_challenge_digest(
            enclave_id,
            opcode,
            op_value,
            nonce,
            record,
            &eff_cap,
            next_wots_root,
            salt,
        );
        let sum: u32 = d.iter().map(|&b| u32::from(b)).sum();
        if sum == WOTSC_TARGET_SUM {
            break d;
        }
        salt = salt.wrapping_add(1);
    };

    let mut proof = [0u8; WOTSC_PROOF_BYTES];
    proof[0..8].copy_from_slice(&salt.to_le_bytes());
    proof[8..40].copy_from_slice(next_wots_root);
    for (i, &d_i) in digits.iter().enumerate() {
        let mut cur = wotsc_secret_start(sk_seed, i);
        for s in 0..usize::from(d_i) {
            cur = wotsc_step(&cur, i, s);
        }
        proof[40 + 16 * i..40 + 16 * (i + 1)].copy_from_slice(&cur);
    }
    proof
}

/// Build the `320`-byte request payload for `CMD_COMMIT` (`0x12`), `CMD_LEASE` (`0x15`),
/// or `CMD_GATE` (`0x16`).
pub fn encode_owner_lifecycle_payload(
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
) -> [u8; 320] {
    let op_field: u64 = match op {
        OwnerOp::Commit => 0,
        OwnerOp::Lease { expected_record } => expected_record,
        OwnerOp::Gate { from, to } => (u64::from(from) << 32) | u64::from(to),
        OwnerOp::LoadCode { .. } => 0,
    };
    let proof = sign_wotsc_proof(
        sk_seed,
        enclave_id,
        op,
        nonce,
        record,
        cap_commit,
        next_wots_root,
    );
    let mut payload = [0u8; 320];
    payload[0..16].copy_from_slice(cap_commit);
    payload[16..24].copy_from_slice(&op_field.to_le_bytes());
    payload[24..320].copy_from_slice(&proof);
    payload
}

/// Compute the public `GF(2^128) + TurboSHAKE256` applet `img_id` bound to `enclave_id`.
pub fn compute_image_id(enclave_id: &[u8; 32], words: &[u32]) -> [u8; 16] {
    let mut key_in = [0u8; 40];
    key_in[0..32].copy_from_slice(enclave_id);
    key_in[32..40].copy_from_slice(&0x47461u64.to_le_bytes());
    let mut h_bytes = [0u8; 16];
    turboshake256(&key_in, &mut h_bytes);
    let h = u128::from_le_bytes(h_bytes);

    let mut d = words.len() as u128;
    for &w in words {
        d = gf2_128_mul_const(d, h) ^ u128::from(w);
    }

    let mut fin = [0u8; 56];
    fin[0..32].copy_from_slice(enclave_id);
    fin[32..48].copy_from_slice(&d.to_le_bytes());
    fin[48..56].copy_from_slice(&0x494d1u64.to_le_bytes());
    let mut img_id = [0u8; 16];
    turboshake256(&fin, &mut img_id);
    img_id
}

/// Compute a 2-leaf Owner Merkle capability root `cap_commit` authorizing an applet `img_id`
/// (domain `0x43500`) and/or a CTH signing `req_id` (domain `0x43501`).
pub fn capability_commit_code(img_id: &[u8; 16], sibling_token: &[u8; 16]) -> [u8; 16] {
    let mut buf = [0u8; 40];
    buf[0..8].copy_from_slice(&0x43500u64.to_le_bytes());
    buf[8..24].copy_from_slice(img_id);
    buf[24..40].copy_from_slice(sibling_token);
    let mut out = [0u8; 16];
    turboshake256(&buf, &mut out);
    out
}

pub fn capability_commit_cth(sibling_token: &[u8; 16], req_id: &[u8; 16]) -> [u8; 16] {
    let mut buf = [0u8; 40];
    buf[0..8].copy_from_slice(&0x43501u64.to_le_bytes());
    buf[8..24].copy_from_slice(req_id);
    buf[24..40].copy_from_slice(sibling_token);
    let mut out = [0u8; 16];
    turboshake256(&buf, &mut out);
    out
}

/// Encode a `flags = 1` (`20 + 4*n` B) capability-committed `CMD_LOAD_CODE` write transaction.
pub fn load_code_frame(prefix: u8, sibling_token: &[u8; 16], words: &[u32]) -> Option<Vec<u8>> {
    if !matches!(prefix, 0 | 0x40 | 0x80) || !(1..=128).contains(&words.len()) {
        return None;
    }
    let length = 20 + 4 * words.len();
    let header = 0x013051u64 | ((length as u64) << 24);
    let mut frame = Vec::with_capacity(9 + length.next_multiple_of(8));
    frame.push(prefix);
    frame.extend_from_slice(&header.to_le_bytes());
    frame.extend_from_slice(&(words.len() as u32).to_le_bytes());
    for word in words {
        frame.extend_from_slice(&word.to_le_bytes());
    }
    frame.extend_from_slice(sibling_token);
    frame.resize(9 + length.next_multiple_of(8), 0);
    Some(frame)
}

/// Encode a `flags = 2` (`300 + 4*n` B) inline `WOTS+C` Owner-signed `CMD_LOAD_CODE` transaction.
pub fn load_code_wotsc_frame(
    prefix: u8,
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    nonce: &[u8; 16],
    record: u64,
    next_wots_root: &[u8; 32],
    words: &[u32],
) -> Option<Vec<u8>> {
    if !matches!(prefix, 0 | 0x40 | 0x80) || !(1..=128).contains(&words.len()) {
        return None;
    }
    let img_id = compute_image_id(enclave_id, words);
    let proof = sign_wotsc_proof(
        sk_seed,
        enclave_id,
        OwnerOp::LoadCode {
            word_count: words.len() as u32,
            img_id,
        },
        nonce,
        record,
        &img_id,
        next_wots_root,
    );
    let length = 300 + 4 * words.len();
    let header = 0x023051u64 | ((length as u64) << 24);
    let mut frame = Vec::with_capacity(9 + length.next_multiple_of(8));
    frame.push(prefix);
    frame.extend_from_slice(&header.to_le_bytes());
    frame.extend_from_slice(&(words.len() as u32).to_le_bytes());
    for word in words {
        frame.extend_from_slice(&word.to_le_bytes());
    }
    frame.extend_from_slice(&proof);
    frame.resize(9 + length.next_multiple_of(8), 0);
    Some(frame)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_factory_trust_wotsc_roundtrip_verifies_exact_root() {
        let sk0 = [0x42u8; 32];
        let sk1 = [0x99u8; 32];
        let pk0 = owner_wotsc_pubkey(&sk0);
        let pk1 = owner_wotsc_pubkey(&sk1);
        let enclave_id = [0xA5u8; 32];
        let nonce = core::array::from_fn(|i| (i as u8) + 1);
        let cap = [0x33u8; 16];

        let proof = sign_wotsc_proof(
            &sk0,
            &enclave_id,
            OwnerOp::Commit,
            &nonce,
            0,
            &cap,
            &pk1,
        );
        let salt = u64::from_le_bytes(proof[0..8].try_into().unwrap());
        let digits = wotsc_challenge_digest(&enclave_id, 0x12, 0, &nonce, 0, &cap, &pk1, salt);
        let sum: u32 = digits.iter().map(|&b| u32::from(b)).sum();
        assert_eq!(sum, WOTSC_TARGET_SUM);

        let mut msg = [0u8; WOTSC_CHAINS * 16 + 8];
        for (i, &d_i) in digits.iter().enumerate() {
            let mut cur: [u8; 16] = proof[40 + 16 * i..40 + 16 * (i + 1)].try_into().unwrap();
            for s in usize::from(d_i)..255 {
                cur = wotsc_step(&cur, i, s);
            }
            msg[16 * i..16 * (i + 1)].copy_from_slice(&cur);
        }
        msg[WOTSC_CHAINS * 16..].copy_from_slice(&0x57501u64.to_le_bytes());
        let mut recovered_pk = [0u8; 32];
        turboshake256(&msg, &mut recovered_pk);
        assert_eq!(recovered_pk, pk0);
    }

    #[test]
    fn capability_and_wotsc_load_code_frames_enforce_bounds() {
        let tok = core::array::from_fn(|i| i as u8);
        let odd = load_code_frame(0x80, &tok, &[0x50000]).unwrap();
        assert_eq!(
            &odd[..17],
            &[128, 81, 48, 1, 24, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 5, 0]
        );
        assert_eq!(&odd[17..], &tok);

        let even = load_code_frame(0x40, &tok, &[0x60000, 0x50000]).unwrap();
        assert_eq!(even[4], 28);
        assert_eq!(&even[21..37], &tok);
        assert_eq!(&even[37..], &[0; 4]);
        assert_eq!(load_code_frame(0, &tok, &[0; 128]).unwrap().len(), 545);
        assert!(load_code_frame(0, &tok, &[0; 129]).is_none());
        assert!(load_code_frame(0, &tok, &[]).is_none());

        let sk = [0x11u8; 32];
        let pk_next = [0x22u8; 32];
        let eid = [0x77u8; 32];
        let nonce = [0x55u8; 16];
        let w_frame =
            load_code_wotsc_frame(0x80, &sk, &eid, &nonce, 1u64 << 32, &pk_next, &[0x50000])
                .unwrap();
        assert_eq!(w_frame.len(), 9 + 304);
    }
}
