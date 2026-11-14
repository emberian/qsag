//! Cryptographic sponges (`Keccak-f[1600]` / `SHAKE256` / `cSHAKE256` and Width-12 Goldilocks
//! `Poseidon2`), self-delimiting LEB128 multi-field framing, and compile-time typestate
//! Fiat–Shamir transcripts.

pub mod keccak;
pub mod poseidon2;

pub use keccak::{
    Cshake256Xof, FiatShamirTranscript, InstanceBound, KECCAK_ROUND_CONSTANTS, RelationBound,
    SHAKE256_RATE_BYTES, SHAKE256_RATE_LANES, Shake256Xof, TranscriptPhase, Unbound,
    cshake256_32, cshake256_customization_prefix, cshake256_xof, encode_frame, encode_list_field,
    encode_multi_frame, keccak_f1600, leb128, leb128_u64, shake256_32, shake256_xof,
    sp800_185_bytepad, sp800_185_encode_string, sp800_185_left_encode,
};
pub use poseidon2::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INIT_STATE,
    POSEIDON2_INTERNAL_ROUNDS, Poseidon2State12, bytes_to_limbs56, poseidon2_apply_me,
    poseidon2_apply_mi, poseidon2_const_at, poseidon2_hash32, poseidon2_pad, poseidon2_perm12,
    poseidon2_rc_bijection, poseidon2_sbox7,
};
