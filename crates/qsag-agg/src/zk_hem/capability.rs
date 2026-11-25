//! Wire identifiers for the presentation relation implemented in `qsag_cred::capability`.

pub const CAPABILITY_WIRE_MAGIC: &[u8; 8] = b"QSAGCAP1";
pub const CONTEXT_DOMAIN: &[u8] = b"QSAG.ZKHEM.CAP.CTX/v1";
pub const BATCH_DOMAIN: &[u8] = b"QSAG.ZKHEM.CAPABILITY.BATCH/v1";
pub const UNLINKABLE_DOMAIN: &[u8] = b"QSAG.CAPABILITY.UNLINKABLE/v1";
pub const UNLINKABLE_WIRE_MAGIC: &[u8; 8] = b"QSAGCAU1";
