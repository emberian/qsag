//! Adaptive bucket combining of checked, authenticated raw triples.

use super::*;

/// Statistical security of one combine pass, in bits.
pub(super) const COMBINE_SECURITY_BITS: u32 = 40;

/// Bucket size of a combine pass that outputs `out_bits` bits: the least `f >= 2` with
/// `out_bits / C(f (out_bits + 1), f) <= 2^-40`.
///
/// **Leakage model.** Before the bucket coin is drawn, a deviating party can make the sacrifice
/// succeed only if linear functionals of its choice over the honest parties' raw bits of one
/// factor take values it guessed: a wrong OT correction on bit `k` is caught unless the
/// receiver's bit is the guess, and one error spread over a set of corrections tests the parity
/// of that set. `j` independent functionals survive with probability `2^-j` and tell the
/// adversary the subspace `L` they span, nothing else, about uniformly random raw bits.
///
/// **Combine.** A public uniform permutation of the raw bit positions, drawn after every such
/// transfer, cuts `f (out_bits + 1)` positions into buckets of `f` and discards the rest,
/// including one whole bucket. An output bit is the XOR of the folded factor over its bucket;
/// nothing else about the folded factor is ever opened. The outputs are uniform in the
/// adversary's view unless some non-zero `l` in `L` is a sum of output functionals, that is,
/// unless the support of `l` is a union of `g >= 1` kept buckets.
///
/// **Bound.** For a fixed support of size `f g` that happens with probability
/// `R(g) = C(n, g) / C(f m, f g)` with `n = out_bits`, `m = n + 1`. `R(n) = R(1) / n`, and for
/// `2 <= g < n`, `C(f m, f g) >= C(m, g)^f` (Vandermonde) gives
/// `R(g) <= C(m, g)^(1 - f) <= (m (m - 1) / 2)^(1 - f) < R(1)` once `n >= 15`. So every `l`
/// is bad with probability at most `R(1) = n / C(f m, f)`, and by a union bound over the
/// `2^j - 1` non-zero elements of `L` the adversary survives and learns anything about the
/// outputs with probability below `2^-j (2^j - 1) R(1) < R(1)`, whatever `j` it chose. The
/// discarded bucket is what rules out the parity of all raw bits, which without it is the
/// parity of all outputs. `combine_arity_meets_its_bound` checks the maximum over `g`
/// numerically.
pub(super) fn combine_arity(out_bits: usize) -> usize {
    debug_assert!(out_bits >= 64);
    let n = out_bits as u128;
    let target = n << COMBINE_SECURITY_BITS;
    let mut f = 2u128;
    loop {
        // `C(f (n + 1), f)`, exact while it fits; an overflow is above every target.
        let mut binom = Some(1u128);
        for i in 0..f {
            binom = binom
                .and_then(|c| c.checked_mul(f * (n + 1) - i))
                .map(|c| c / (i + 1));
        }
        if binom.is_none_or(|c| c >= target) {
            return f as usize;
        }
        f += 1;
    }
}

/// Raw words a combine pass with bucket size `arity` needs for `out_words` outputs.
pub(super) fn combine_input_words(out_words: usize, arity: usize) -> usize {
    (arity * (64 * out_words + 1)).div_ceil(64)
}

/// Which raw factors a deviating party can aim a selective failure at.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Leak {
    /// Only `b`. With KOS-backed raw triples every OT choice is a raw `b` row, a share of the
    /// folded `b` that [`bind_choice`] ties to those rows, or the mask `v` of the folded `b`;
    /// `a` and its mask are only ever payloads, and a receiver has no freedom in its choices.
    ChoiceSide,
    /// Both. Raw triples from a PCG are claimed, not computed: a party that misreports its
    /// share of one factor is caught exactly when the other factor's bit is set.
    BothFactors,
}

/// `(raw words, bucket size folding b, bucket size folding a)` for `out_words` final words.
pub(super) fn combine_shape(
    out_words: usize,
    leak: Leak,
) -> (usize, usize, Option<(usize, usize)>) {
    match leak {
        Leak::ChoiceSide => {
            let fold_b = combine_arity(64 * out_words);
            (combine_input_words(out_words, fold_b), fold_b, None)
        }
        Leak::BothFactors => {
            let fold_a = combine_arity(64 * out_words);
            let mid_words = combine_input_words(out_words, fold_a);
            let fold_b = combine_arity(64 * mid_words);
            (
                combine_input_words(mid_words, fold_b),
                fold_b,
                Some((mid_words, fold_a)),
            )
        }
    }
}

/// Equally sized batches addressed as one array of bit triples.
struct PoolView<'a> {
    batches: &'a [&'a BitTriples],
    batch_bits: PublicDivisor,
}

impl PoolView<'_> {
    #[inline]
    fn bit(&self, which: usize, party: usize, idx: usize) -> u64 {
        let (batch, bit) = self.batch_bits.split(idx);
        word_bit(&self.batches[batch].bits[which][party], bit)
    }

    #[inline]
    fn mac(&self, which: usize, party: usize, lane: usize, idx: usize) -> u128 {
        let (batch, bit) = self.batch_bits.split(idx);
        self.batches[batch].macs[which][party][lane][bit]
    }
}

/// One pass of the bucket combine. With `fold = 1` an output triple is
/// `(a_0, b_0 ^ .. ^ b_{f-1}, c_0 ^ .. ^ c_{f-1} ^ e_1 b_1 ^ .. ^ e_{f-1} b_{f-1})` over the
/// `f = arity` members of its bucket, where `e_i = a_0 ^ a_i` is opened with a MAC check;
/// `fold = 0` swaps the roles of `a` and `b`. The bucket permutation is drawn here, bound to
/// `transcript`, and every opening is absorbed into it.
#[expect(
    clippy::too_many_arguments,
    reason = "Pool, shape, key shares and private randomness of one pass are separate inputs"
)]
pub(super) fn combine_pass(
    session_id: &[u8; 32],
    phase: &'static str,
    fold: usize,
    arity: usize,
    out_words: usize,
    batches: &[&BitTriples],
    delta: &[Row],
    transcript: &mut [u8; 32],
    mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<BitTriples, PreprocessError> {
    let n = delta.len();
    let keep = 1 - fold;
    let pool = PoolView {
        batches,
        batch_bits: PublicDivisor::new(64 * batches[0].words()),
    };
    let total = pool.batch_bits.size * batches.len();
    let out_bits = 64 * out_words;
    if batches
        .iter()
        .any(|b| 64 * b.words() != pool.batch_bits.size)
        || arity < 2
        || arity * (out_bits + 1) > total
    {
        return Err(PreprocessError::VaultExhausted {
            kind: "raw triples of a combine pool",
        });
    }

    // Every raw share is authenticated and every sacrifice has finished, so no transfer that
    // depends on a raw bit is still to come. Only now is the bucket coin drawn.
    let coin = run_commit_and_open_coin(session_id, phase.as_bytes(), transcript, party_rngs)?;
    absorb_transcript(transcript, b"bucket", &coin);
    let perm = derive_coin_permutation(&coin, phase.as_bytes(), total);
    let member = |bit: usize, i: usize| perm[bit * arity + i] as usize;

    // Openings `e = keep_0 ^ keep_i`, 128 to a field element.
    let opens = out_bits * (arity - 1);
    let elems = opens.div_ceil(128);
    struct PartyOpen {
        party: usize,
        shares: Vec<u128>,
        macs: Vec<Row>,
    }
    let mut parts: Vec<PartyOpen> = (0..n)
        .map(|party| PartyOpen {
            party,
            shares: vec![0u128; elems],
            macs: vec![[0u128; 2]; elems],
        })
        .collect();
    {
        let (pool, member) = (&pool, &member);
        let bucket = PublicDivisor::new(arity - 1);
        par_for_each(&mut parts, |part| {
            let p = part.party;
            let mut rows = [[0u128; 128]; 2];
            for elem in 0..elems {
                let mut share = 0u128;
                for j in 0..128.min(opens - 128 * elem) {
                    let open = 128 * elem + j;
                    let (bit, offset) = bucket.split(open);
                    let i = offset + 1;
                    let (m0, mi) = (member(bit, 0), member(bit, i));
                    share |= u128::from(pool.bit(keep, p, m0) ^ pool.bit(keep, p, mi)) << j;
                    for lane in 0..2 {
                        rows[lane][j] = pool.mac(keep, p, lane, m0) ^ pool.mac(keep, p, lane, mi);
                    }
                }
                part.shares[elem] = share;
                part.macs[elem] = core::array::from_fn(|lane| gf_dot(&rows[lane], &POWERS));
                rows = [[0u128; 128]; 2];
            }
        });
    }
    let mut shares = SecretBuffer(Vec::with_capacity(n));
    let mut macs = SecretBuffer(Vec::with_capacity(n));
    for mut part in parts {
        if let Some(hook) = faults.combine_shares.as_mut() {
            hook(part.party, &mut part.shares);
        }
        shares.push(core::mem::take(&mut part.shares));
        macs.push(core::mem::take(&mut part.macs));
    }
    let opened =
        open_additive_authenticated(session_id, phase, &shares, &macs, delta, mesh, party_rngs)?;
    absorb_transcript(transcript, b"mac-blind", &mesh.transcript_digest());
    drop((shares, macs));
    let opened_bytes: Vec<u8> = opened.iter().flat_map(|e| e.to_le_bytes()).collect();
    absorb_transcript(transcript, b"open", &opened_bytes);
    let opened_bit = |bit: usize, i: usize| {
        let open = bit * (arity - 1) + (i - 1);
        ((opened[open / 128] >> (open % 128)) & 1) as u64
    };

    struct PartyOut {
        party: usize,
        bits: [Vec<u64>; 3],
        macs: [[Vec<u128>; 2]; 3],
    }
    let mut outs: Vec<PartyOut> = (0..n)
        .map(|party| PartyOut {
            party,
            bits: core::array::from_fn(|_| vec![0u64; out_words]),
            macs: core::array::from_fn(|_| core::array::from_fn(|_| vec![0u128; out_bits])),
        })
        .collect();
    {
        let (pool, member, opened_bit) = (&pool, &member, &opened_bit);
        par_for_each(&mut outs, |out| {
            let p = out.party;
            for bit in 0..out_bits {
                let m0 = member(bit, 0);
                let kept = pool.bit(keep, p, m0);
                let mut folded = 0u64;
                let mut product = 0u64;
                let mut folded_mac = [0u128; 2];
                let mut product_mac = [0u128; 2];
                for i in 0..arity {
                    let mi = member(bit, i);
                    let e = if i == 0 { 0 } else { opened_bit(bit, i) };
                    let y = pool.bit(fold, p, mi);
                    folded ^= y;
                    product ^= pool.bit(2, p, mi) ^ (e & y);
                    for lane in 0..2 {
                        let y_mac = pool.mac(fold, p, lane, mi);
                        folded_mac[lane] ^= y_mac;
                        product_mac[lane] ^= pool.mac(2, p, lane, mi) ^ (bit_mask(e) & y_mac);
                    }
                }
                out.bits[keep][bit / 64] |= kept << (bit % 64);
                out.bits[fold][bit / 64] |= folded << (bit % 64);
                out.bits[2][bit / 64] |= product << (bit % 64);
                for lane in 0..2 {
                    out.macs[keep][lane][bit] = pool.mac(keep, p, lane, m0);
                    out.macs[fold][lane][bit] = folded_mac[lane];
                    out.macs[2][lane][bit] = product_mac[lane];
                }
            }
        });
    }
    let mut combined = BitTriples {
        bits: core::array::from_fn(|_| SecretBuffer(Vec::with_capacity(n))),
        macs: core::array::from_fn(|_| SecretBuffer(Vec::with_capacity(n))),
    };
    for mut out in outs {
        for which in 0..3 {
            combined.bits[which].push(core::mem::take(&mut out.bits[which]));
            combined.macs[which].push(core::mem::take(&mut out.macs[which]));
        }
    }
    Ok(combined)
}

/// Combine the raw triples of `batches` into `out_words` final words: fold `b`, and where both
/// factors can leak fold `a` in a second pass under a fresh permutation of the intermediate
/// triples. Each pass is one application of the bound of [`combine_arity`]; in the second, the
/// first pass's openings turn any functional of the raw `a` bits into one of the intermediate
/// `a` bits, fixed before the second coin.
#[expect(
    clippy::too_many_arguments,
    reason = "Pool, shape, key shares and private randomness of one combine are separate inputs"
)]
pub(super) fn combine_raw(
    session_id: &[u8; 32],
    leak: Leak,
    out_words: usize,
    batches: &[&BitTriples],
    delta: &[Row],
    transcript: &mut [u8; 32],
    mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    faults: &mut PiTripleF2Faults<'_>,
) -> Result<BitTriples, PreprocessError> {
    let (_, fold_b, second) = combine_shape(out_words, leak);
    let first_words = second.map_or(out_words, |(mid_words, _)| mid_words);
    let first = combine_pass(
        session_id,
        "pi_triple_f2_comb_b",
        1,
        fold_b,
        first_words,
        batches,
        delta,
        transcript,
        mesh,
        party_rngs,
        faults,
    )?;
    let Some((_, fold_a)) = second else {
        return Ok(first);
    };
    combine_pass(
        session_id,
        "pi_triple_f2_comb_a",
        0,
        fold_a,
        out_words,
        &[&first],
        delta,
        transcript,
        mesh,
        party_rngs,
        faults,
    )
}
