use super::*;

#[inline]
pub(super) fn init_rss_state_from_public_midstate(
    midstate: &[u64; 25],
    active_mask: u64,
    st_p: &mut [[u64; 1600]; 3],
    st_s: &mut [[u64; 1600]; 3],
) {
    for lane in 0..25 {
        let w = midstate[lane];
        for z in 0..64 {
            if ((w >> z) & 1) == 1 {
                st_p[0][64 * lane + z] = active_mask;
                st_s[2][64 * lane + z] = active_mask;
            }
        }
    }
}

/// Bitsliced theta, rho and pi on one share of 64 parallel states (`lane * 64 + bit`).
fn rss_keccak_linear_layer(st: &[u64; 1600], out: &mut [u64; 1600]) {
    let mut c = [[0u64; 64]; 5];
    for x in 0..5 {
        for z in 0..64 {
            c[x][z] = st[x * 64 + z]
                ^ st[(x + 5) * 64 + z]
                ^ st[(x + 10) * 64 + z]
                ^ st[(x + 15) * 64 + z]
                ^ st[(x + 20) * 64 + z];
        }
    }
    let mut d = [[0u64; 64]; 5];
    for x in 0..5 {
        let prev = &c[(x + 4) % 5];
        let next = &c[(x + 1) % 5];
        d[x][0] = prev[0] ^ next[63];
        for z in 1..64 {
            d[x][z] = prev[z] ^ next[z - 1];
        }
    }
    for source in 0..25 {
        let x = source % 5;
        let y = source / 5;
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        let rot = KECCAK_ROTATION_OFFSETS[source] as usize;
        for z in 0..64 {
            let src_z = (z + 64 - rot) & 63;
            out[target * 64 + z] = st[source * 64 + src_z] ^ d[x][src_z];
        }
    }
    qsag_asm::volatile_fill(&mut c, [0; 64]);
    qsag_asm::volatile_fill(&mut d, [0; 64]);
}

/// Run the 24 replicated rounds on 64 bitsliced states and append every AND relation to
/// `pending_dzk` without verifying it.
pub(super) fn eval_rss_keccak_f1600_batch64_record(
    session_id: &[u8; 32],
    batch_ctr: u64,
    batch_len: usize,
    states_prim: &mut [[u64; 1600]; 3],
    states_sec: &mut [[u64; 1600]; 3],
    mask: &RssMaskSession,
    pending_dzk: &mut RssPendingDzkTriples,
) -> Result<(), KeccakMpcError> {
    if pending_dzk.poison.is_set() {
        return Err(KeccakMpcError::Poisoned);
    }
    if batch_len == 0 || batch_len > 64 {
        return Err(KeccakMpcError::InvalidBatchSize(batch_len));
    }
    let active_mask = batch_active_mask(batch_len);
    pending_dzk.lane_perms += batch_len as u64;
    for (p, secondary) in states_sec.iter().enumerate() {
        let next = (p + 1) % 3;
        if secondary
            .iter()
            .zip(&states_prim[next])
            .any(|(a, b)| black_box((a ^ b) & active_mask) != 0)
        {
            return pending_dzk
                .poison
                .fail(KeccakMpcError::RssShareEqualityFailed(RssSlashingReceipt {
                    share_slot: next,
                    primary_party: next,
                    secondary_party: p,
                }));
        }
    }
    // Replica equality holds, so slot `s` is `states_prim[s]`; party `p` holds slots `p`, `p + 1`.
    let mut st = [[0u64; 1600]; 3];
    for s in 0..3 {
        for idx in 0..1600 {
            st[s][idx] = states_prim[s][idx] & active_mask;
        }
    }

    // One masked product share per AND and party. Pairwise streams provide cancelling masks;
    // the complete gate witnesses are checked before any cut.
    let (mut mask_prim, mut mask_sec) = mask.chi_streams(session_id, batch_ctr);
    let mut b = [[0u64; 1600]; 3];
    let mut mp = [[0u64; 1600]; 3];
    let mut ms = [[0u64; 1600]; 3];
    let mut prod = [[0u64; 1600]; 3];

    for &rc in &KECCAK_ROUND_CONSTANTS {
        for s in 0..3 {
            rss_keccak_linear_layer(&st[s], &mut b[s]);
            mask_prim[s].fill_words(&mut mp[s]);
        }
        match &mut mask_sec {
            Some(streams) => {
                for p in 0..3 {
                    streams[p].fill_words(&mut ms[p]);
                }
            }
            None => {
                for p in 0..3 {
                    ms[p] = mp[(p + 1) % 3];
                }
            }
        }
        // Chi: (~b[x+1]) & b[x+2] == b[x+2] ^ (b[x+1] & b[x+2]), so out[x] = b[x] ^ b[x+2] ^ (b[x+1] & b[x+2]).
        // Every party evaluates the uncomplemented product of a = b[x+1] and b = b[x+2]
        // (`a_p & (b_p ^ b_q) ^ a_q & b_p ^ mask`) and XORs `b_p = b[p][x+2]` locally, matching
        // `RssParticipantKeccak.lean` (`productGate` on uncomplemented operands; note `ThresholdMpc.lean`
        // instead complements share 0 of `b[x+1]` before the AND gate, which reconstructs identically
        // while differing on raw per-share gate transcripts under the same mask stream).
        for p in 0..3 {
            let q = (p + 1) % 3;
            for lane in 0..25 {
                let row = 5 * (lane / 5);
                let l1 = (row + (lane + 1) % 5) * 64;
                let l2 = (row + (lane + 2) % 5) * 64;
                let l0 = lane * 64;
                for z in 0..64 {
                    let ap = b[p][l1 + z];
                    let aq = b[q][l1 + z];
                    let bp = b[p][l2 + z];
                    let bq = b[q][l2 + z];
                    let t = qsag_verified::rss_party_and_local(
                        ap,
                        aq,
                        bp,
                        bq,
                        mp[p][l0 + z],
                        ms[p][l0 + z],
                    ) & active_mask;
                    prod[p][l0 + z] = t;
                    st[p][l0 + z] = b[p][l0 + z] ^ bp ^ t;
                }
            }
        }
        for s in 0..3 {
            for lane in 0..25 {
                let row = 5 * (lane / 5);
                let l1 = (row + (lane + 1) % 5) * 64;
                let l2 = (row + (lane + 2) % 5) * 64;
                secret_vec_extend_from_slice(&mut pending_dzk.a[s], &b[s][l1..l1 + 64]);
                secret_vec_extend_from_slice(&mut pending_dzk.b[s], &b[s][l2..l2 + 64]);
            }
            secret_vec_extend_from_slice(&mut pending_dzk.c[s], &prod[s]);
        }
        // Iota: the public round constant enters slot 0.
        for (z, word) in st[0][..64].iter_mut().enumerate() {
            if ((rc >> z) & 1) == 1 {
                *word ^= active_mask;
            }
        }
    }

    for p in 0..3 {
        states_prim[p] = st[p];
        states_sec[p] = st[(p + 1) % 3];
    }
    for s in 0..3 {
        wipe_u64s(&mut st[s]);
        wipe_u64s(&mut b[s]);
        wipe_u64s(&mut mp[s]);
        wipe_u64s(&mut ms[s]);
        wipe_u64s(&mut prod[s]);
    }
    Ok(())
}

/// Evaluate 64 parallel `Keccak-f[1600]` permutations using direct replicated chi and the
/// batched AND-relation proof:
/// - `states_prim[p]` and `states_sec[p]` have length `1600` (`lane * 64 + bit_pos`), where bit `b` of each
///   `u64` belongs to sponge instance `b in 0..batch_len`.
/// - Records `24 * 1600 = 38,400` packed AND relation words (`1,600` per round), verifies
///   replicated input equality, and runs both passes of `verify_rss_boolean_triples_bbcggi19`
///   before returning.
/// - Mask and proof streams are hedged by a fresh joint coin from `party_rngs` on every call.
///
/// This is a one-shot evaluation: the mask session and the relation accumulator live only
/// for this call, and nothing is opened here. There is therefore no engine state in which
/// a failed proof could later be taken for a passed one. If the proof fails, both state
/// arrays are zeroed before the error is returned, so no unverified output share is left
/// for the caller to open. Argument and replica-equality errors are detected before the
/// states are touched and leave them unchanged.
pub fn eval_rss_keccak_f1600_batch64(
    session_id: &[u8; 32],
    batch_ctr: u64,
    batch_len: usize,
    states_prim: &mut [[u64; 1600]; 3],
    states_sec: &mut [[u64; 1600]; 3],
    keys: &[RssKeyShare256; 3],
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    if batch_len == 0 || batch_len > 64 {
        return Err(KeccakMpcError::InvalidBatchSize(batch_len));
    }
    let mask = RssMaskSession::derive(session_id, keys, party_rngs)?;
    let mut pending = RssPendingDzkTriples::new();
    eval_rss_keccak_f1600_batch64_record(
        session_id,
        batch_ctr,
        batch_len,
        states_prim,
        states_sec,
        &mask,
        &mut pending,
    )?;
    let verified =
        verify_rss_boolean_triples_bbcggi19(session_id, batch_ctr, &mut pending, &mask, party_rngs);
    if verified.is_err() {
        wipe_rss_states(states_prim, states_sec);
    }
    verified
}

pub(super) fn wipe_rss_states<const N: usize>(prim: &mut [[u64; N]; 3], sec: &mut [[u64; N]; 3]) {
    for p in 0..3 {
        wipe_u64s(&mut prim[p]);
        wipe_u64s(&mut sec[p]);
    }
}

/// Cut-boundary share words of the three parties, collected across batches until the cut
/// is verified and opened. Wiped on `Drop`, so an error return clears them as well.
pub(super) struct RssCutBuffer {
    pub(super) prim: [Vec<u64>; 3],
    pub(super) sec: [Vec<u64>; 3],
}

impl RssCutBuffer {
    pub(super) fn new() -> Self {
        Self {
            prim: [Vec::new(), Vec::new(), Vec::new()],
            sec: [Vec::new(), Vec::new(), Vec::new()],
        }
    }

    #[inline]
    pub(super) fn push_party_slices(
        &mut self,
        party: usize,
        prim_slice: &[u64],
        sec_slice: &[u64],
    ) {
        secret_vec_extend_from_slice(&mut self.prim[party], prim_slice);
        secret_vec_extend_from_slice(&mut self.sec[party], sec_slice);
    }
}

impl Drop for RssCutBuffer {
    fn drop(&mut self) {
        for p in 0..3 {
            wipe_u64s(&mut self.prim[p]);
            wipe_u64s(&mut self.sec[p]);
        }
    }
}

/// Active 2-of-3 RSS distributed `SLH-DSA` cluster implementing sealed [`SlhMpcOracles`].
