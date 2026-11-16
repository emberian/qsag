#![no_main]
//! Hostile framing and canonical re-encoding, plus valid-frame payload coverage.
use libfuzzer_sys::fuzz_target;
use qsag_quorum::wire_channel::{decode_frame, decode_header, encode_frame, FrameHeader};
fuzz_target!(|data: &[u8]| {
    let _ = decode_header(data);
    if let Ok((header, payload)) = decode_frame(data) {
        assert_eq!(encode_frame(&header, payload).unwrap(), data);
    }
    let header = FrameHeader { session_id: [0x51; 32], from: 0, to: 1,
        round_tag: 3, seq: data.first().copied().unwrap_or(0) as u64 };
    if let Ok(encoded) = encode_frame(&header, data) {
        let (decoded, payload) = decode_frame(&encoded).unwrap();
        assert_eq!(decoded, header);
        assert_eq!(payload, data);
        let mut invalid = encoded;
        invalid.push(0);
        assert!(decode_frame(&invalid).is_err());
    }
});
