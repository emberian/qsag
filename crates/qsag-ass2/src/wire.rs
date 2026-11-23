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

use crate::isa::mem_map::MAX_APPLET_WORDS;
use alloc::vec::Vec;
use core::fmt;
use qsag_accel::ct::ct_eq_u64;
use qsag_accel::gf2_128::gf2_128_mul_const;
use qsag_accel::keccak::KECCAK_RC;
use qsag_core::sponge::keccak::{KECCAK_ROTATION_OFFSETS, cshake256_32};

pub const WOTSC_CHAINS: usize = 16;
pub const WOTSC_BASE: usize = 256;
pub const WOTSC_TARGET_SUM: u32 = 2040;
pub const WOTSC_PROOF_BYTES: usize = 8 + 32 + WOTSC_CHAINS * 16; // 296 B
pub const OWNER_LIFECYCLE_PAYLOAD_BYTES: usize = 320;
pub const OWNER_LIFECYCLE_FRAME_BYTES: usize = 9 + OWNER_LIFECYCLE_PAYLOAD_BYTES;
/// NIST SP 800-185 customization tag for Ring-3 applet code hashing (`<= 64` 32-bit words).
pub const CODE_HASH_DOMAIN: &[u8] = b"ASS2.CODE";
/// NIST SP 800-185 customization & domain-separation tag for per-applet key derivation into `r1..r2`.
pub const APPLET_KEY_DOMAIN: &[u8] = b"ASS2.APPLET";

/// Typed wire framing, canonicality, monotone-generation, and `WOTS+C` verification errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ass2WireError {
    InvalidPrefix,
    InvalidHeader,
    UnsupportedLifecycleOp,
    LifecycleRecordMismatch,
    GenerationOverflow,
    WordCountOutOfRange,
    LengthMismatch,
    NonZeroPadding,
    GrindBudgetExhausted,
    InvalidWotscSum,
    InvalidWotscSignature,
}

impl fmt::Display for Ass2WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::InvalidPrefix => "invalid serial width prefix byte",
            Self::InvalidHeader => "non-canonical ASS2 wire command header",
            Self::UnsupportedLifecycleOp => "OwnerOp::LoadCode requires load_code_wotsc_frame",
            Self::LifecycleRecordMismatch => "lifecycle op_field disagrees with monotone record",
            Self::GenerationOverflow => "32-bit enclave monotone generation exhausted (u32::MAX)",
            Self::WordCountOutOfRange => "applet word count outside 1..=64",
            Self::LengthMismatch => "frame byte length disagrees with canonical padded length",
            Self::NonZeroPadding => "non-zero 64-bit alignment padding bytes in wire frame",
            Self::GrindBudgetExhausted => "WOTS+C salt grinding budget exhausted before target sum",
            Self::InvalidWotscSum => "WOTS+C challenge digest digit sum != 2040",
            Self::InvalidWotscSignature => "WOTS+C chain root does not match owner public key",
        };
        f.write_str(msg)
    }
}

impl core::error::Error for Ass2WireError {}

fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut diff = 0u64;
    for i in 0..4 {
        let wa = u64::from_le_bytes(a[8 * i..8 * (i + 1)].try_into().unwrap());
        let wb = u64::from_le_bytes(b[8 * i..8 * (i + 1)].try_into().unwrap());
        diff |= wa ^ wb;
    }
    ct_eq_u64(diff, 0)
}

fn valid_prefix(prefix: u8) -> bool {
    matches!(prefix, 0 | 0x40 | 0x80)
}

fn check_generation_advanceable(record: u64) -> Result<(), Ass2WireError> {
    if (record >> 32) >= u64::from(u32::MAX) {
        Err(Ass2WireError::GenerationOverflow)
    } else {
        Ok(())
    }
}

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

/// Advance one 16-byte `WOTS+C` chain node at `(chain_idx, step)` via 12-round `Keccak-p[1600, 12]`.
pub fn wotsc_step(node: &[u8; 16], chain_idx: usize, step: usize) -> [u8; 16] {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnerOp {
    Commit,
    Lease { expected_record: u64 },
    Gate { from: u32, to: u32 },
    LoadCode { word_count: u32, code_hash: [u8; 32] },
}

/// Compute the canonical 32-byte `code_hash` of a Ring-3 applet image (`cSHAKE256("ASS2.CODE", words_le)`).
pub fn compute_code_hash(words: &[u32]) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(4 * words.len());
    for &w in words {
        bytes.extend_from_slice(&w.to_le_bytes());
    }
    cshake256_32(CODE_HASH_DOMAIN, &bytes)
}

/// Derive the domain-separated 32-byte (`256`-bit; lower `128` bits injected into `r1..r2`)
/// Ring-3 applet secret `cSHAKE256(K_root, "ASS2.APPLET" || code_hash)`.
pub fn derive_applet_key(k_root: &[u8; 32], code_hash: &[u8; 32]) -> [u8; 32] {
    let mut input = [0u8; 32 + APPLET_KEY_DOMAIN.len() + 32];
    input[..32].copy_from_slice(k_root);
    input[32..32 + APPLET_KEY_DOMAIN.len()].copy_from_slice(APPLET_KEY_DOMAIN);
    input[32 + APPLET_KEY_DOMAIN.len()..].copy_from_slice(code_hash);
    cshake256_32(APPLET_KEY_DOMAIN, &input)
}

fn op_descriptor(op: OwnerOp, cap_commit: &[u8; 16]) -> (u64, u64, [u8; 16]) {
    match op {
        OwnerOp::Commit => (0x12, 0, *cap_commit),
        OwnerOp::Lease { expected_record } => (0x15, expected_record, *cap_commit),
        OwnerOp::Gate { from, to } => (0x16, (u64::from(from) << 32) | u64::from(to), *cap_commit),
        OwnerOp::LoadCode {
            word_count,
            code_hash,
        } => {
            let mut prefix16 = [0u8; 16];
            prefix16.copy_from_slice(&code_hash[..16]);
            (0x30, u64::from(word_count), prefix16)
        }
    }
}

fn wotsc_applet_challenge_digest(
    enclave_id: &[u8; 32],
    word_count: u32,
    code_hash: &[u8; 32],
    nonce: &[u8; 16],
    record: u64,
    next_wots_root: &[u8; 32],
    salt: u64,
) -> [u8; 16] {
    let mut msg = [0u8; 144];
    msg[0..8].copy_from_slice(&0x574d2u64.to_le_bytes());
    msg[8..40].copy_from_slice(enclave_id);
    msg[40..48].copy_from_slice(&u64::from(word_count).to_le_bytes());
    msg[48..56].copy_from_slice(&record.to_le_bytes());
    msg[56..72].copy_from_slice(nonce);
    msg[72..104].copy_from_slice(code_hash);
    msg[104..112].copy_from_slice(&salt.to_le_bytes());
    msg[112..144].copy_from_slice(next_wots_root);
    let mut digest = [0u8; 16];
    turboshake256(&msg, &mut digest);
    digest
}

fn op_challenge_digest(
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
    salt: u64,
) -> [u8; 16] {
    match op {
        OwnerOp::LoadCode {
            word_count,
            code_hash,
        } => wotsc_applet_challenge_digest(
            enclave_id,
            word_count,
            &code_hash,
            nonce,
            record,
            next_wots_root,
            salt,
        ),
        _ => {
            let (opcode, op_value, eff_cap) = op_descriptor(op, cap_commit);
            wotsc_challenge_digest(
                enclave_id,
                opcode,
                op_value,
                nonce,
                record,
                &eff_cap,
                next_wots_root,
                salt,
            )
        }
    }
}

fn validate_lifecycle_op_against_record(op: OwnerOp, record: u64) -> Result<(u8, u64), Ass2WireError> {
    check_generation_advanceable(record)?;
    match op {
        OwnerOp::Commit => Ok((0x12, 0)),
        OwnerOp::Lease { expected_record } => {
            if expected_record != record {
                return Err(Ass2WireError::LifecycleRecordMismatch);
            }
            Ok((0x15, expected_record))
        }
        OwnerOp::Gate { from, to } => {
            if (record as u32) != from {
                return Err(Ass2WireError::LifecycleRecordMismatch);
            }
            Ok((0x16, (u64::from(from) << 32) | u64::from(to)))
        }
        OwnerOp::LoadCode { .. } => Err(Ass2WireError::UnsupportedLifecycleOp),
    }
}

/// Derive the 16-byte `WOTS+C` base-256 challenge digest for `(enclave_id, opcode, op_value, nonce, record, cap_commit, next_wots_root, salt)`.
#[allow(clippy::too_many_arguments)]
pub fn wotsc_challenge_digest(
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

/// Bounded-effort `WOTS+C` proof generator (`max_attempts` salt candidates).
#[allow(clippy::too_many_arguments)]
pub fn try_sign_wotsc_proof_bounded(
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
    max_attempts: u64,
) -> Result<[u8; WOTSC_PROOF_BYTES], Ass2WireError> {
    check_generation_advanceable(record)?;
    if let OwnerOp::LoadCode { word_count, .. } = op {
        if !(1..=MAX_APPLET_WORDS as u32).contains(&word_count) {
            return Err(Ass2WireError::WordCountOutOfRange);
        }
    } else {
        let _ = validate_lifecycle_op_against_record(op, record)?;
    }
    let mut found = None;
    for salt in 0..max_attempts {
        let d = op_challenge_digest(
            enclave_id,
            op,
            nonce,
            record,
            cap_commit,
            next_wots_root,
            salt,
        );
        let sum: u32 = d.iter().map(|&b| u32::from(b)).sum();
        if sum == WOTSC_TARGET_SUM {
            found = Some((salt, d));
            break;
        }
    }
    let Some((salt, digits)) = found else {
        return Err(Ass2WireError::GrindBudgetExhausted);
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
    Ok(proof)
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
    let mut salt = 0u64;
    let digits = loop {
        let d = op_challenge_digest(
            enclave_id,
            op,
            nonce,
            record,
            cap_commit,
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

/// Verify a `296`-byte `WOTS+C` proof in constant time against `owner_pk` and `record`,
/// returning the authenticated `next_wots_root` on success.
pub fn verify_wotsc_proof(
    owner_pk: &[u8; 32],
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    proof: &[u8; WOTSC_PROOF_BYTES],
) -> Result<[u8; 32], Ass2WireError> {
    check_generation_advanceable(record)?;
    if let OwnerOp::LoadCode { word_count, .. } = op {
        if !(1..=MAX_APPLET_WORDS as u32).contains(&word_count) {
            return Err(Ass2WireError::WordCountOutOfRange);
        }
    } else {
        let _ = validate_lifecycle_op_against_record(op, record)?;
    }

    let salt = u64::from_le_bytes(proof[0..8].try_into().unwrap());
    let next_wots_root: [u8; 32] = proof[8..40].try_into().unwrap();
    let digits = op_challenge_digest(
        enclave_id,
        op,
        nonce,
        record,
        cap_commit,
        &next_wots_root,
        salt,
    );
    let sum: u32 = digits.iter().map(|&b| u32::from(b)).sum();
    if sum != WOTSC_TARGET_SUM {
        return Err(Ass2WireError::InvalidWotscSum);
    }

    let mut msg = [0u8; WOTSC_CHAINS * 16 + 8];
    for (i, &d_i) in digits.iter().enumerate() {
        let mut cur: [u8; 16] = proof[40 + 16 * i..40 + 16 * (i + 1)].try_into().unwrap();
        for s in usize::from(d_i)..(WOTSC_BASE - 1) {
            cur = wotsc_step(&cur, i, s);
        }
        msg[16 * i..16 * (i + 1)].copy_from_slice(&cur);
    }
    msg[WOTSC_CHAINS * 16..].copy_from_slice(&0x57501u64.to_le_bytes());
    let mut recovered_pk = [0u8; 32];
    turboshake256(&msg, &mut recovered_pk);
    if !ct_eq_bytes32(&recovered_pk, owner_pk) {
        return Err(Ass2WireError::InvalidWotscSignature);
    }
    Ok(next_wots_root)
}

/// Build the `320`-byte request payload for `CMD_COMMIT` (`0x12`), `CMD_LEASE` (`0x15`),
/// or `CMD_GATE` (`0x16`), rejecting `OwnerOp::LoadCode`, mismatched `record` fields, and
/// `u32::MAX` generation wraparound BEFORE touching the one-time `sk_seed`.
pub fn encode_owner_lifecycle_payload(
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
) -> Result<[u8; OWNER_LIFECYCLE_PAYLOAD_BYTES], Ass2WireError> {
    let (_opcode, op_field) = validate_lifecycle_op_against_record(op, record)?;
    let proof = sign_wotsc_proof(
        sk_seed,
        enclave_id,
        op,
        nonce,
        record,
        cap_commit,
        next_wots_root,
    );
    let mut payload = [0u8; OWNER_LIFECYCLE_PAYLOAD_BYTES];
    payload[0..16].copy_from_slice(cap_commit);
    payload[16..24].copy_from_slice(&op_field.to_le_bytes());
    payload[24..320].copy_from_slice(&proof);
    Ok(payload)
}

/// Encode a full `329`-byte (`prefix[1B] || header[8B] || payload[320B]`) canonical Owner lifecycle
/// transaction for `CMD_COMMIT` (`0x12`), `CMD_LEASE` (`0x15`), or `CMD_GATE` (`0x16`).
#[allow(clippy::too_many_arguments)]
pub fn encode_owner_lifecycle_frame(
    prefix: u8,
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    op: OwnerOp,
    nonce: &[u8; 16],
    record: u64,
    cap_commit: &[u8; 16],
    next_wots_root: &[u8; 32],
) -> Result<[u8; OWNER_LIFECYCLE_FRAME_BYTES], Ass2WireError> {
    if !valid_prefix(prefix) {
        return Err(Ass2WireError::InvalidPrefix);
    }
    let (opcode, _) = validate_lifecycle_op_against_record(op, record)?;
    let payload = encode_owner_lifecycle_payload(
        sk_seed,
        enclave_id,
        op,
        nonce,
        record,
        cap_commit,
        next_wots_root,
    )?;
    let header = 0x51u64
        | (u64::from(opcode) << 8)
        | ((OWNER_LIFECYCLE_PAYLOAD_BYTES as u64) << 24);
    let mut frame = [0u8; OWNER_LIFECYCLE_FRAME_BYTES];
    frame[0] = prefix;
    frame[1..9].copy_from_slice(&header.to_le_bytes());
    frame[9..].copy_from_slice(&payload);
    Ok(frame)
}

/// Parse and cryptographically verify a `329`-byte Owner lifecycle frame (`CMD_COMMIT` / `CMD_LEASE` / `CMD_GATE`).
pub fn parse_and_verify_owner_lifecycle_frame(
    frame: &[u8],
    owner_pk: &[u8; 32],
    enclave_id: &[u8; 32],
    nonce: &[u8; 16],
    expected_record: u64,
) -> Result<(u8, OwnerOp, [u8; 16], [u8; 32]), Ass2WireError> {
    if frame.len() != OWNER_LIFECYCLE_FRAME_BYTES {
        return Err(Ass2WireError::LengthMismatch);
    }
    let prefix = frame[0];
    if !valid_prefix(prefix) {
        return Err(Ass2WireError::InvalidPrefix);
    }
    check_generation_advanceable(expected_record)?;

    let header = u64::from_le_bytes(frame[1..9].try_into().unwrap());
    let magic = (header & 0xFF) as u8;
    let opcode = ((header >> 8) & 0xFF) as u8;
    let flags = ((header >> 16) & 0xFF) as u8;
    let len = ((header >> 24) & 0xFF_FFFF) as usize;
    let arg = (header >> 48) as u16;
    if magic != 0x51 || flags != 0 || len != OWNER_LIFECYCLE_PAYLOAD_BYTES || arg != 0 {
        return Err(Ass2WireError::InvalidHeader);
    }

    let cap_commit: [u8; 16] = frame[9..25].try_into().unwrap();
    let op_field = u64::from_le_bytes(frame[25..33].try_into().unwrap());
    let op = match opcode {
        0x12 => {
            if op_field != 0 {
                return Err(Ass2WireError::InvalidHeader);
            }
            OwnerOp::Commit
        }
        0x15 => {
            if op_field != expected_record {
                return Err(Ass2WireError::LifecycleRecordMismatch);
            }
            OwnerOp::Lease {
                expected_record: op_field,
            }
        }
        0x16 => {
            let from = (op_field >> 32) as u32;
            let to = op_field as u32;
            if from != (expected_record as u32) {
                return Err(Ass2WireError::LifecycleRecordMismatch);
            }
            OwnerOp::Gate { from, to }
        }
        _ => return Err(Ass2WireError::InvalidHeader),
    };

    let proof: [u8; WOTSC_PROOF_BYTES] = frame[33..329].try_into().unwrap();
    let next_root = verify_wotsc_proof(
        owner_pk,
        enclave_id,
        op,
        nonce,
        expected_record,
        &cap_commit,
        &proof,
    )?;
    Ok((prefix, op, cap_commit, next_root))
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

/// Encode a `flags = 0` (`4 + 4*n` B) open `CMD_LOAD_CODE` (`0x30`) write transaction
/// accepted only in `LcState::Blank` (`1..=64` 32-bit `ASS-2` words).
pub fn load_code_open_frame(prefix: u8, words: &[u32]) -> Option<Vec<u8>> {
    if !valid_prefix(prefix) || !(1..=MAX_APPLET_WORDS).contains(&words.len()) {
        return None;
    }
    let length = 4 + 4 * words.len();
    let header = 0x003051u64 | ((length as u64) << 24);
    let mut frame = Vec::with_capacity(9 + length.next_multiple_of(8));
    frame.push(prefix);
    frame.extend_from_slice(&header.to_le_bytes());
    frame.extend_from_slice(&(words.len() as u32).to_le_bytes());
    for word in words {
        frame.extend_from_slice(&word.to_le_bytes());
    }
    frame.resize(9 + length.next_multiple_of(8), 0);
    Some(frame)
}

/// Parse a canonical `flags = 0` open `CMD_LOAD_CODE` (`0x30`) wire frame (`1..=64` words).
pub fn parse_load_code_open_frame(frame: &[u8]) -> Result<(u8, Vec<u32>), Ass2WireError> {
    if frame.len() < 9 + 8 {
        return Err(Ass2WireError::LengthMismatch);
    }
    let prefix = frame[0];
    if !valid_prefix(prefix) {
        return Err(Ass2WireError::InvalidPrefix);
    }
    let header = u64::from_le_bytes(frame[1..9].try_into().unwrap());
    let magic = (header & 0xFF) as u8;
    let opcode = ((header >> 8) & 0xFF) as u8;
    let flags = ((header >> 16) & 0xFF) as u8;
    let length = ((header >> 24) & 0xFF_FFFF) as usize;
    let arg = (header >> 48) as u16;
    if magic != 0x51 || opcode != 0x30 || flags != 0 || arg != 0 {
        return Err(Ass2WireError::InvalidHeader);
    }
    let count = u32::from_le_bytes(frame[9..13].try_into().unwrap()) as usize;
    if !(1..=MAX_APPLET_WORDS).contains(&count) {
        return Err(Ass2WireError::WordCountOutOfRange);
    }
    let expected_len = 4 + 4 * count;
    if length != expected_len {
        return Err(Ass2WireError::InvalidHeader);
    }
    let total_bytes = 9 + expected_len.next_multiple_of(8);
    if frame.len() != total_bytes {
        return Err(Ass2WireError::LengthMismatch);
    }
    if frame[9 + expected_len..].iter().any(|&b| b != 0) {
        return Err(Ass2WireError::NonZeroPadding);
    }
    let words: Vec<u32> = frame[13..9 + expected_len]
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect();
    Ok((prefix, words))
}

/// Encode a `flags = 1` (`20 + 4*n` B) capability-committed `CMD_LOAD_CODE` write transaction (`1..=64` words).
pub fn load_code_frame(prefix: u8, sibling_token: &[u8; 16], words: &[u32]) -> Option<Vec<u8>> {
    if !valid_prefix(prefix) || !(1..=MAX_APPLET_WORDS).contains(&words.len()) {
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

/// Encode a `flags = 2` (`300 + 4*n` B) inline `WOTS+C` Owner-signed `CMD_LOAD_CODE` transaction
/// over `code_hash = compute_code_hash(words)` (`1..=64` words).
pub fn load_code_wotsc_frame(
    prefix: u8,
    sk_seed: &[u8; 32],
    enclave_id: &[u8; 32],
    nonce: &[u8; 16],
    record: u64,
    next_wots_root: &[u8; 32],
    words: &[u32],
) -> Option<Vec<u8>> {
    if !valid_prefix(prefix)
        || !(1..=MAX_APPLET_WORDS).contains(&words.len())
        || check_generation_advanceable(record).is_err()
    {
        return None;
    }
    let code_hash = compute_code_hash(words);
    let mut cap_prefix = [0u8; 16];
    cap_prefix.copy_from_slice(&code_hash[..16]);
    let proof = sign_wotsc_proof(
        sk_seed,
        enclave_id,
        OwnerOp::LoadCode {
            word_count: words.len() as u32,
            code_hash,
        },
        nonce,
        record,
        &cap_prefix,
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

/// Parse a canonical `flags = 1` capability-committed `CMD_LOAD_CODE` wire frame, enforcing exact
/// header fields, `1..=64` word count, 64-bit padded length, and all-zero alignment pad bytes.
pub fn parse_load_code_frame(frame: &[u8]) -> Result<(u8, Vec<u32>, [u8; 16]), Ass2WireError> {
    if frame.len() < 9 + 24 {
        return Err(Ass2WireError::LengthMismatch);
    }
    let prefix = frame[0];
    if !valid_prefix(prefix) {
        return Err(Ass2WireError::InvalidPrefix);
    }
    let header = u64::from_le_bytes(frame[1..9].try_into().unwrap());
    let magic = (header & 0xFF) as u8;
    let opcode = ((header >> 8) & 0xFF) as u8;
    let flags = ((header >> 16) & 0xFF) as u8;
    let length = ((header >> 24) & 0xFF_FFFF) as usize;
    let arg = (header >> 48) as u16;
    if magic != 0x51 || opcode != 0x30 || flags != 1 || arg != 0 {
        return Err(Ass2WireError::InvalidHeader);
    }
    let count = u32::from_le_bytes(frame[9..13].try_into().unwrap()) as usize;
    if !(1..=MAX_APPLET_WORDS).contains(&count) {
        return Err(Ass2WireError::WordCountOutOfRange);
    }
    let expected_len = 20 + 4 * count;
    if length != expected_len {
        return Err(Ass2WireError::InvalidHeader);
    }
    let total_bytes = 9 + expected_len.next_multiple_of(8);
    if frame.len() != total_bytes {
        return Err(Ass2WireError::LengthMismatch);
    }
    if frame[9 + expected_len..].iter().any(|&b| b != 0) {
        return Err(Ass2WireError::NonZeroPadding);
    }
    let words_end = 13 + 4 * count;
    let words: Vec<u32> = frame[13..words_end]
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect();
    let sibling_token: [u8; 16] = frame[words_end..words_end + 16].try_into().unwrap();
    Ok((prefix, words, sibling_token))
}

/// Parse and cryptographically verify a canonical `flags = 2` inline `WOTS+C` `CMD_LOAD_CODE` frame,
/// authenticating `code_hash = compute_code_hash(&words)` (`1..=64` words).
pub fn parse_and_verify_load_code_wotsc_frame(
    frame: &[u8],
    owner_pk: &[u8; 32],
    enclave_id: &[u8; 32],
    nonce: &[u8; 16],
    expected_record: u64,
) -> Result<(u8, Vec<u32>, [u8; 32], [u8; 32]), Ass2WireError> {
    if frame.len() < 9 + 304 {
        return Err(Ass2WireError::LengthMismatch);
    }
    let prefix = frame[0];
    if !valid_prefix(prefix) {
        return Err(Ass2WireError::InvalidPrefix);
    }
    check_generation_advanceable(expected_record)?;

    let header = u64::from_le_bytes(frame[1..9].try_into().unwrap());
    let magic = (header & 0xFF) as u8;
    let opcode = ((header >> 8) & 0xFF) as u8;
    let flags = ((header >> 16) & 0xFF) as u8;
    let length = ((header >> 24) & 0xFF_FFFF) as usize;
    let arg = (header >> 48) as u16;
    if magic != 0x51 || opcode != 0x30 || flags != 2 || arg != 0 {
        return Err(Ass2WireError::InvalidHeader);
    }
    let count = u32::from_le_bytes(frame[9..13].try_into().unwrap()) as usize;
    if !(1..=MAX_APPLET_WORDS).contains(&count) {
        return Err(Ass2WireError::WordCountOutOfRange);
    }
    let expected_len = 300 + 4 * count;
    if length != expected_len {
        return Err(Ass2WireError::InvalidHeader);
    }
    let total_bytes = 9 + expected_len.next_multiple_of(8);
    if frame.len() != total_bytes {
        return Err(Ass2WireError::LengthMismatch);
    }
    if frame[9 + expected_len..].iter().any(|&b| b != 0) {
        return Err(Ass2WireError::NonZeroPadding);
    }
    let words_end = 13 + 4 * count;
    let words: Vec<u32> = frame[13..words_end]
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect();
    let proof: [u8; WOTSC_PROOF_BYTES] = frame[words_end..words_end + WOTSC_PROOF_BYTES]
        .try_into()
        .unwrap();
    let code_hash = compute_code_hash(&words);
    let mut cap_prefix = [0u8; 16];
    cap_prefix.copy_from_slice(&code_hash[..16]);
    let next_root = verify_wotsc_proof(
        owner_pk,
        enclave_id,
        OwnerOp::LoadCode {
            word_count: count as u32,
            code_hash,
        },
        nonce,
        expected_record,
        &cap_prefix,
        &proof,
    )?;
    Ok((prefix, words, code_hash, next_root))
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
        assert_eq!(load_code_frame(0, &tok, &[0; 64]).unwrap().len(), 9 + 280);
        assert!(load_code_frame(0, &tok, &[0; 65]).is_none());
        assert!(load_code_frame(0, &tok, &[]).is_none());
        assert_eq!(load_code_open_frame(0x80, &[0; 64]).unwrap().len(), 9 + 264);
        assert!(load_code_open_frame(0x80, &[0; 65]).is_none());
        assert!(load_code_open_frame(0x80, &[]).is_none());

        let sk = [0x11u8; 32];
        let pk_next = [0x22u8; 32];
        let eid = [0x77u8; 32];
        let nonce = [0x55u8; 16];
        let w_frame =
            load_code_wotsc_frame(0x80, &sk, &eid, &nonce, 1u64 << 32, &pk_next, &[0x50000])
                .unwrap();
        assert_eq!(w_frame.len(), 9 + 304);
        assert!(
            load_code_wotsc_frame(0x80, &sk, &eid, &nonce, 1u64 << 32, &pk_next, &[0; 65])
                .is_none()
        );
    }

    #[test]
    fn tooth_ass2_wire_lifecycle_rejects_load_code_gen_overflow_and_noncanonical_padding() {
        let sk0 = [0x24u8; 32];
        let sk1 = [0x7Bu8; 32];
        let pk0 = owner_wotsc_pubkey(&sk0);
        let pk1 = owner_wotsc_pubkey(&sk1);
        let eid = [0xC3u8; 32];
        let nonce = [0x19u8; 16];
        let cap = [0x6Eu8; 16];

        assert_eq!(
            encode_owner_lifecycle_payload(
                &sk0,
                &eid,
                OwnerOp::LoadCode {
                    word_count: 1,
                    code_hash: [0xAB; 32],
                },
                &nonce,
                0,
                &cap,
                &pk1,
            ),
            Err(Ass2WireError::UnsupportedLifecycleOp)
        );
        let max_gen_record = (u64::from(u32::MAX) << 32) | 1;
        assert_eq!(
            encode_owner_lifecycle_payload(
                &sk0,
                &eid,
                OwnerOp::Commit,
                &nonce,
                max_gen_record,
                &cap,
                &pk1,
            ),
            Err(Ass2WireError::GenerationOverflow)
        );
        assert!(
            load_code_wotsc_frame(0x80, &sk0, &eid, &nonce, max_gen_record, &pk1, &[0x50000])
                .is_none()
        );
        assert_eq!(
            encode_owner_lifecycle_payload(
                &sk0,
                &eid,
                OwnerOp::Lease {
                    expected_record: 99,
                },
                &nonce,
                100,
                &cap,
                &pk1,
            ),
            Err(Ass2WireError::LifecycleRecordMismatch)
        );
        assert_eq!(
            encode_owner_lifecycle_payload(
                &sk0,
                &eid,
                OwnerOp::Gate { from: 3, to: 4 },
                &nonce,
                (5u64 << 32) | 2,
                &cap,
                &pk1,
            ),
            Err(Ass2WireError::LifecycleRecordMismatch)
        );

        let record = (7u64 << 32) | 2;
        let gate_op = OwnerOp::Gate { from: 2, to: 3 };
        let frame = encode_owner_lifecycle_frame(
            0x80, &sk0, &eid, gate_op, &nonce, record, &cap, &pk1,
        )
        .unwrap();
        assert_eq!(
            parse_and_verify_owner_lifecycle_frame(&frame, &pk0, &eid, &nonce, record),
            Ok((0x80, gate_op, cap, pk1))
        );
        // Replay at next generation (`record + (1 << 32)`) MUST fail verification!
        assert!(
            parse_and_verify_owner_lifecycle_frame(
                &frame,
                &pk0,
                &eid,
                &nonce,
                record + (1u64 << 32)
            )
            .is_err()
        );
        let mut tampered_sig = frame;
        tampered_sig[100] ^= 0x01;
        assert_eq!(
            parse_and_verify_owner_lifecycle_frame(&tampered_sig, &pk0, &eid, &nonce, record),
            Err(Ass2WireError::InvalidWotscSignature)
        );

        // Capability-committed & inline WOTS+C LOAD_CODE frames with 2 words have 4 alignment pad bytes.
        let words = [0x0006_0000u32, 0x0005_0000u32];
        let mut cap_frame = load_code_frame(0x40, &cap, &words).unwrap();
        assert_eq!(
            parse_load_code_frame(&cap_frame).unwrap(),
            (0x40, alloc::vec![words[0], words[1]], cap)
        );
        *cap_frame.last_mut().unwrap() = 1;
        assert_eq!(
            parse_load_code_frame(&cap_frame),
            Err(Ass2WireError::NonZeroPadding)
        );

        let mut wotsc_load =
            load_code_wotsc_frame(0x80, &sk0, &eid, &nonce, record, &pk1, &words).unwrap();
        let expected_hash = compute_code_hash(&words);
        assert_eq!(
            parse_and_verify_load_code_wotsc_frame(&wotsc_load, &pk0, &eid, &nonce, record)
                .unwrap(),
            (0x80, alloc::vec![words[0], words[1]], expected_hash, pk1)
        );
        *wotsc_load.last_mut().unwrap() = 0x80;
        assert_eq!(
            parse_and_verify_load_code_wotsc_frame(&wotsc_load, &pk0, &eid, &nonce, record),
            Err(Ass2WireError::NonZeroPadding)
        );
    }

    #[test]
    fn tooth_lean_cross_kat_ass2_wotsc_golden_anchors() {
        // Golden parity anchors generated directly by the Lean `qsag-kat --cross-kat` oracle
        // (`ass2wotsc` family), ensuring standalone workspace exports enforce identical bit-level
        // TurboSHAKE256, `Keccak-p[1600,12]`, `WOTS+C`, and capability commitments.
        let unhex = |s: &str| -> alloc::vec::Vec<u8> {
            (0..s.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
                .collect()
        };
        let mut s = [0u64; 25];
        keccak_p1600_12(&mut s);
        assert_eq!(s[0], 10258729603806234135);
        assert_eq!(s[24], 14987149935989530652);

        let mut ts_empty = [0u8; 32];
        turboshake256(&[], &mut ts_empty);
        assert_eq!(
            ts_empty.as_slice(),
            unhex("367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db")
        );

        let seq16: [u8; 16] = core::array::from_fn(|i| i as u8);
        let hi16: [u8; 16] = core::array::from_fn(|i| (0xa0 + i) as u8);
        assert_eq!(
            wotsc_step(&seq16, 0, 0).as_slice(),
            unhex("865f894b0af8fe4272f0d9a22eec4419")
        );
        assert_eq!(
            owner_wotsc_pubkey(&[0x42; 32]).as_slice(),
            unhex("cad91194bfdb183aef64a294f8e40ca4150771a2a0a9e9e85a340f72bb3df467")
        );
        assert_eq!(
            capability_commit_code(&seq16, &hi16).as_slice(),
            unhex("ca25977d035d29406d9ec1ac174f5655")
        );
        assert_eq!(
            capability_commit_cth(&hi16, &seq16).as_slice(),
            unhex("827e7cde0e26e855a46f747f212a8252")
        );
        assert_eq!(
            compute_image_id(&[0xa5; 32], &[327680, 393216, 3735928559]).as_slice(),
            unhex("2eb6f050a3dcf308d5fed686f3428b0a")
        );

        let nonce: [u8; 16] = core::array::from_fn(|i| (i + 1) as u8);
        let d0 = wotsc_challenge_digest(&[0xa5; 32], 0x12, 0, &nonce, 0, &[0x33; 16], &[0x77; 32], 0);
        assert_eq!(d0.as_slice(), unhex("1b4eefb76e92ef7e92e79bdf427e35d5"));
        assert_ne!(
            d0.iter().map(|&b| u32::from(b)).sum::<u32>(),
            WOTSC_TARGET_SUM
        );
        let d_valid =
            wotsc_challenge_digest(&[0xa5; 32], 0x12, 0, &nonce, 0, &[0x33; 16], &[0x77; 32], 729);
        assert_eq!(
            d_valid.iter().map(|&b| u32::from(b)).sum::<u32>(),
            WOTSC_TARGET_SUM
        );
    }
}
