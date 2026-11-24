//! Blinded additive openings and conversion to authenticated Shamir shares.

use super::*;
use crate::preprocessing::gf256_auth::{
    shamir_share_bits64_gf256_mats, shamir_share_tower128x64_mats, unpack_bs_gf256x16_to_u128x64,
};

// ---------------------------------------------------------------------------
// Additive opening with MAC check.
// ---------------------------------------------------------------------------

#[cfg(test)]
std::thread_local! {
    pub(super) static ADDITIVE_CHECK_WEIGHTS: core::cell::RefCell<Vec<u128>> = const {
        core::cell::RefCell::new(Vec::new())
    };
    pub(super) static ADDITIVE_CHECK_OPENINGS: core::cell::RefCell<Vec<Tower128>> = const {
        core::cell::RefCell::new(Vec::new())
    };
}

/// Open additively shared field elements `shares[party][j]` and check their two-lane MACs
/// `macs[party][j]` against the parties' key shares. Commit value shares before opening them,
/// and commit MAC residual shares while keeping them private. Only independently randomized
/// MAC residuals are revealed; a failing residual must never expose a multiple of the key.
#[inline(never)]
pub(super) fn open_additive_authenticated(
    session_id: &[u8; 32],
    phase: &'static str,
    shares: &[Vec<u128>],
    macs: &[Vec<Row>],
    delta: &[Row],
    mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<u128>, PreprocessError> {
    let n = shares.len();
    let count = shares[0].len();
    let commit = |tag: &[u8], party: usize, words: &[u128], salt: &[u8; 32]| -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.TRIPLE.F2.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(phase.as_bytes());
        xof.absorb(tag);
        xof.absorb(&(party as u64).to_be_bytes());
        for w in words {
            xof.absorb(&w.to_le_bytes());
        }
        xof.absorb(salt);
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    };

    let mut opened = vec![0u128; count];
    let mut salts = Vec::with_capacity(n);
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        let salt = party_rngs[p].next_bytes32();
        coms.push(commit(b"value", p, &shares[p], &salt));
        salts.push(salt);
    }
    for p in 0..n {
        if !ct_eq_bytes32(&commit(b"value", p, &shares[p], &salts[p]), &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
        wipe_bytes32(&mut salts[p]);
        for (dst, share) in opened.iter_mut().zip(&shares[p]) {
            *dst ^= *share;
        }
    }

    let mut sigma = SecretBuffer(vec![vec![0u128; 2 * count]; n]);
    coms.clear();
    for p in 0..n {
        for j in 0..count {
            for lane in 0..2 {
                sigma[p][2 * j + lane] = macs[p][j][lane] ^ gf_mul(opened[j], delta[p][lane]);
            }
        }
        salts[p] = party_rngs[p].next_bytes32();
        coms.push(commit(b"sigma", p, &sigma[p], &salts[p]));
    }
    for p in 0..n {
        if !ct_eq_bytes32(&commit(b"sigma", p, &sigma[p], &salts[p]), &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
        wipe_bytes32(&mut salts[p]);
    }
    if count == 0 {
        return Ok(opened);
    }
    // Fix the WHOLE residual vector before drawing any projection coefficient.
    // For a nonzero vector over q = 2^128, a uniform linear projection is zero
    // with probability 1/q. Conditional on a nonzero projection, the existing
    // two-round blinding accepts with probability 1/q^2. Three independent
    // projections therefore accept with probability
    // (1/q + (1 - 1/q)/q^2)^3 < 1/q^2, even for a fault in only ONE MAC lane.
    // No projection is ever reconstructed without a fresh private multiplier.
    let mut binding = Cshake256Xof::new(b"QSAG.TRIPLE.F2.MAC.PROJECTIONS.COM/v1");
    binding.absorb(session_id);
    binding.absorb(phase.as_bytes());
    binding.absorb(&(n as u64).to_be_bytes());
    binding.absorb(&(count as u64).to_be_bytes());
    for commitment in &coms {
        binding.absorb(commitment);
    }
    let mut committed = [0u8; 32];
    binding.squeeze(&mut committed);
    for projection in 0..3u64 {
        let sid = cshake256_32_multi_frame(
            b"QSAG.TRIPLE.F2.MAC.PROJECTION/v1",
            &[session_id, phase.as_bytes(), &projection.to_be_bytes()],
        );
        let coin_binding = cshake256_32_multi_frame(
            b"QSAG.TRIPLE.F2.MAC.PROJECTION.COIN/v1",
            &[&committed, &mesh.transcript_digest()],
        );
        let coin = run_commit_and_open_coin(
            &sid,
            b"PI_TRIPLE_F2_MAC_PROJECTION",
            &coin_binding,
            party_rngs,
        )?;
        for lane in 0..2 {
            let mut xof = Cshake256Xof::new(b"QSAG.TRIPLE.F2.MAC.PROJECTION.COEFF/v1");
            xof.absorb(&coin);
            xof.absorb(&[lane as u8]);
            let weights = (0..count)
                .map(|_| {
                    let mut bytes = [0u8; 16];
                    xof.squeeze(&mut bytes);
                    u128::from_le_bytes(bytes)
                })
                .collect::<Vec<_>>();
            let residual = SecretBuffer(
                sigma
                    .iter()
                    .map(|row| {
                        let values = SecretBuffer(
                            row.as_chunks::<2>()
                                .0
                                .iter()
                                .map(|pair| pair[lane])
                                .collect::<Vec<_>>(),
                        );
                        // Projection uses the MAC's polynomial field. The final coordinate
                        // map into the tower field is XOR-linear and zero-preserving;
                        // its blinding zero test needs no multiplicative isomorphism.
                        Tower128(gf_dot(&weights, &values))
                    })
                    .collect::<Vec<_>>(),
            );
            let blind_sid =
                cshake256_32_multi_frame(b"QSAG.TRIPLE.F2.MAC.BLIND/v1", &[&sid, &[lane as u8]]);
            let blinded = mac_blind::blind_open_tower128(
                &blind_sid,
                phase,
                &residual,
                Some(&mut *mesh),
                party_rngs,
            )?;
            #[cfg(test)]
            {
                ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().push(blinded));
                ADDITIVE_CHECK_WEIGHTS
                    .with(|weights_seen| weights_seen.borrow_mut().push(weights[0]));
            }
            if !blinded.ct_eq(Tower128::ZERO) {
                return Err(PreprocessError::MacCheckFailed {
                    phase,
                    accused_party: None,
                });
            }
        }
    }
    Ok(opened)
}

// ---------------------------------------------------------------------------
// Shamir conversion.
// ---------------------------------------------------------------------------

/// Degree-`< t` shares of a full `GF(256)^64` word.
fn shamir_share_planes(
    t: usize,
    eval_mats: &[PublicGf256Matrix],
    secret: &BitslicedGf256x64,
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let mut coeffs: Vec<BitslicedGf256x64> = Vec::with_capacity(t);
    coeffs.push(*secret);
    for _ in 1..t {
        coeffs.push(core::array::from_fn(|_| rng.next_u64()));
    }
    let out = eval_mats
        .iter()
        .map(|mat| {
            let mut acc = [0u64; 8];
            for c in coeffs.iter().rev() {
                acc = bs_gf256_xor(&mat.scale_planes(&acc), c);
            }
            acc
        })
        .collect();
    for c in &mut coeffs {
        wipe_u64s(c);
    }
    out
}

/// Deal degree-`< t` shares of every party's XOR share `bit_words[party][word]` and of its
/// additive MAC share `mac_bits[party][lane][64 * word + bit]`, then run the `Π_MAC`
/// consistency and degree check over all `n` parties. `tamper` sees the dealt shares before
/// the check.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub(super) fn convert_to_shamir_and_check(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    alpha_shamir: &[[Tower128; 2]],
    mask: CheckMask,
    bit_words: &[Vec<u64>],
    mac_bits: &[[Vec<u128>; 2]],
    transcript: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    tamper: &mut ShamirTamper<'_>,
) -> Result<ShamirAuthenticatedWords, PreprocessError> {
    let n = eval_points.len();
    let num_words = bit_words[0].len();
    let eval_mats: Vec<PublicGf256Matrix> = eval_points
        .iter()
        .map(|&pt| PublicGf256Matrix::from_public_scalar(pt))
        .collect();

    // The disposable mask word of the check is read as 64 `GF(256)` lanes.
    struct Dealer {
        party: usize,
        rng: PartyPrivateRng,
        /// `[receiver][word]`, the mask word last.
        dealt: SecretBuffer<Vec<Vec<BitslicedGf256x64>>>,
        additive: SecretBuffer<Vec<[[u128; 64]; 2]>>,
    }
    let mut dealers: Vec<Dealer> = (0..n)
        .map(|party| Dealer {
            party,
            rng: PartyPrivateRng::from_seed(
                party_rngs[party].next_bytes32(),
                b"QSAG.TRIPLE.F2.DEAL/v1",
            ),
            dealt: SecretBuffer(vec![vec![[0u64; 8]; num_words + 1]; n]),
            additive: SecretBuffer(vec![[[0u128; 64]; 2]; num_words + 1]),
        })
        .collect();
    {
        let mask_ref = &mask;
        let eval_mats_ref = &eval_mats;
        par_for_each(&mut dealers, |dealer| {
            let p = dealer.party;
            for (k, word) in bit_words[p].iter().enumerate() {
                let dealt = SecretBuffer(shamir_share_bits64_gf256_mats(
                    t,
                    eval_mats_ref,
                    *word,
                    &mut dealer.rng,
                ));
                for q in 0..n {
                    dealer.dealt[q][k] = dealt[q];
                }
                for lane in 0..2 {
                    dealer.additive[k][lane]
                        .copy_from_slice(&mac_bits[p][lane][64 * k..64 * k + 64]);
                }
            }
            let dealt = SecretBuffer(shamir_share_planes(
                t,
                eval_mats_ref,
                &mask_ref.planes[p],
                &mut dealer.rng,
            ));
            for q in 0..n {
                dealer.dealt[q][num_words] = dealt[q];
            }
            dealer.additive[num_words] = mask_ref.macs[p];
        });
    }
    let mut words_sh = SecretBuffer(vec![vec![[0u64; 8]; num_words]; n]);
    let mut r_chk_sh = SecretBuffer(vec![[0u64; 8]; n]);
    for dealer in &dealers {
        for q in 0..n {
            for k in 0..num_words {
                bs_gf256_xor_assign(&mut words_sh[q][k], &dealer.dealt[q][k]);
            }
            bs_gf256_xor_assign(&mut r_chk_sh[q], &dealer.dealt[q][num_words]);
        }
    }
    let additive: Vec<SecretBuffer<Vec<[[u128; 64]; 2]>>> = dealers
        .into_iter()
        .map(|mut dealer| SecretBuffer(core::mem::take(&mut dealer.additive.0)))
        .collect();

    // Shamir-share every additive MAC word. Each block of words draws from per-party
    // substreams keyed by the block index, so blocks are independent of scheduling.
    let seeds: SecretBuffer<Vec<[u8; 32]>> =
        SecretBuffer((0..n).map(|p| party_rngs[p].next_bytes32()).collect());
    let mut macs_sh = vec![vec![[[Tower128::ZERO; 64]; 2]; num_words + 1]; n];
    {
        struct MacBlock<'a> {
            index: usize,
            dst: Vec<&'a mut [[[Tower128; 64]; 2]]>,
        }
        let mut iters: Vec<_> = macs_sh
            .iter_mut()
            .map(|v| v.chunks_mut(SHAMIR_BLOCK_WORDS))
            .collect();
        let mut blocks = Vec::new();
        loop {
            let dst: Vec<_> = iters.iter_mut().filter_map(Iterator::next).collect();
            if dst.is_empty() {
                break;
            }
            blocks.push(MacBlock {
                index: blocks.len(),
                dst,
            });
        }
        let additive_ref = &additive;
        let seeds_ref = &seeds;
        let eval_mats_ref = &eval_mats;
        par_for_each(&mut blocks, |block| {
            let first = block.index * SHAMIR_BLOCK_WORDS;
            let block_le = (block.index as u64).to_le_bytes();
            for p in 0..n {
                let mut rng = PartyPrivateRng::from_seed(seeds_ref[p], &block_le);
                for k_off in 0..block.dst[0].len() {
                    for lane in 0..2 {
                        let dealt = SecretBuffer(shamir_share_tower128x64_mats(
                            t,
                            eval_mats_ref,
                            &additive_ref[p][first + k_off][lane],
                            &mut rng,
                        ));
                        for (q, dst_q) in block.dst.iter_mut().enumerate() {
                            let mut unpacked = unpack_bs_gf256x16_to_u128x64(&dealt[q]);
                            for bit in 0..64 {
                                dst_q[k_off][lane][bit] =
                                    dst_q[k_off][lane][bit].add(Tower128(unpacked[bit]));
                            }
                            wipe_u128s(&mut unpacked);
                        }
                    }
                }
            }
        });
    }
    drop((additive, seeds, mask));

    tamper(&mut words_sh, &mut macs_sh);

    let checked = spdz_pimac_check_bs_gf256_words(
        session_id,
        t,
        eval_points,
        alpha_shamir,
        &words_sh,
        &macs_sh,
        &mut r_chk_sh,
        transcript,
        party_rngs,
    );
    for party in &mut macs_sh {
        if let Some(mut chk) = party.pop() {
            wipe_tower128(&mut chk[0]);
            wipe_tower128(&mut chk[1]);
        }
    }
    if let Err(e) = checked {
        for party in &mut macs_sh {
            for word in party.iter_mut() {
                wipe_tower128(&mut word[0]);
                wipe_tower128(&mut word[1]);
            }
        }
        return Err(e);
    }
    Ok((core::mem::take(&mut words_sh.0), macs_sh))
}

/// Authenticate XOR-shared Boolean words under the two-lane SPDZ key and return consistent
/// degree-`< t` Shamir shares of the bits and of their MACs.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, key shares, value shares and private randomness are separate protocol inputs"
)]
pub(in crate::preprocessing) fn authenticate_xor_shared_words(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    bit_words: &[Vec<u64>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<ShamirAuthenticatedWords, PreprocessError> {
    let n = eval_points.len();
    let num_words = bit_words[0].len();
    let nbits = 64 * num_words;
    let mut pool = DeltaCotPool::establish(
        session_id,
        ot_mesh,
        alpha_contribs,
        nbits + CHECK_MASK_BITS,
        0,
        party_rngs,
    )?;
    let off = pool.alloc(nbits)?;
    let mut transcript = *session_id;
    let mut d_total = vec![0u64; num_words];
    for p in 0..n {
        for (k, word) in bit_words[p].iter().enumerate() {
            let d = *word ^ pool.rho[p][off / 64 + k];
            absorb_transcript(&mut transcript, b"bits", &d.to_le_bytes());
            d_total[k] ^= d;
        }
    }
    let mac_bits: SecretBuffer<Vec<[Vec<u128>; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| pool.mac_bits(p, off, nbits, &d_total))
            .collect(),
    );
    let mask = pool.take_check_mask()?;
    drop(pool);
    convert_to_shamir_and_check(
        session_id,
        t,
        eval_points,
        alpha_shamir,
        mask,
        bit_words,
        &mac_bits,
        &transcript,
        party_rngs,
        &mut |_, _| {},
    )
}
