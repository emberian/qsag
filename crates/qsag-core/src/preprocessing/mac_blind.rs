//! Multiplicatively blinded MAC residual openings at every threshold and committee size.
//!
//! These helpers consume additive residuals that remain private throughout multiplication.
//! A fresh joint randomizer is the OLE receiver input; the residual is ALWAYS the sender
//! input. Both OLE backends use disposable random choice tapes and a post-OT entropy
//! amplifier, rather than choice bits of a MAC residual. No authenticated triple or MAC
//! opening is used to bootstrap this multiplication, so there is no circular check.
//!
//! In the ideal OLE hybrid, fixing every corrupt input leaves an honest party's uniform
//! randomizer uniform over the field. For nonzero d, w = r*d is a field permutation:
//! its distribution is independent of d (including alpha), with false acceptance 1/|F|.
//! The concrete OLE adds its documented statistical selective-failure bound; raw Gilboa
//! on residual bits would NOT provide this property. Commit all final shares before any
//! are revealed, preventing a last speaker from cancelling the honest check share.
use super::*;

/// Check every degree syndrome privately before opening the blinded constant.
/// Each constraint uses an independent joint randomizer: opening pointwise
/// products with one common r would expose r through a corrupt party's known share.
pub(super) fn blind_open_degree_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let tables = GoldilocksOpeningTables::new(t, points)?;
    for (offset, row) in tables.extra.iter().enumerate() {
        let residual = SecretBuffer(
            shares
                .iter()
                .enumerate()
                .map(|(p, &d)| {
                    let coefficient = if p < t {
                        -row[p]
                    } else if p == t + offset {
                        Goldilocks::ONE
                    } else {
                        Goldilocks::ZERO
                    };
                    d.mul_base(coefficient)
                })
                .collect::<Vec<_>>(),
        );
        let sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.EXT2.DEG/v1",
            &[session_id, phase.as_bytes(), &(offset as u64).to_be_bytes()],
        );
        let w = blind_open_ext2(&sid, phase, &residual, Some(&mut *mesh), rngs)?;
        if !w.ct_eq(GoldilocksExt2::ZERO) {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    let residual = SecretBuffer(
        shares
            .iter()
            .enumerate()
            .map(|(p, &d)| {
                if p < t {
                    d.mul_base(tables.zero[p])
                } else {
                    GoldilocksExt2::ZERO
                }
            })
            .collect::<Vec<_>>(),
    );
    blind_open_ext2(session_id, phase, &residual, Some(mesh), rngs)
}

pub(super) fn blind_open_degree_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    points: &[TowerGf256],
    shares: &[Tower128],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    let tables = Gf256OpeningTables::new(t, points)?;
    for (offset, row) in tables.extra.iter().enumerate() {
        let residual = SecretBuffer(
            shares
                .iter()
                .enumerate()
                .map(|(p, &d)| {
                    let coefficient = if p < t {
                        row[p]
                    } else if p == t + offset {
                        TowerGf256::ONE
                    } else {
                        TowerGf256::ZERO
                    };
                    d.mul_gf256(coefficient)
                })
                .collect::<Vec<_>>(),
        );
        let sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.T128.DEG/v1",
            &[session_id, phase.as_bytes(), &(offset as u64).to_be_bytes()],
        );
        let w = blind_open_tower128(&sid, phase, &residual, Some(&mut *mesh), rngs)?;
        if !w.ct_eq(Tower128::ZERO) {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    let residual = SecretBuffer(
        shares
            .iter()
            .enumerate()
            .map(|(p, &d)| {
                if p < t {
                    d.mul_gf256(tables.zero[p])
                } else {
                    Tower128::ZERO
                }
            })
            .collect::<Vec<_>>(),
    );
    blind_open_tower128(session_id, phase, &residual, Some(mesh), rngs)
}

fn blinding_mesh(
    session_id: &[u8; 32],
    phase: &'static str,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<OtMesh, PreprocessError> {
    let sid = cshake256_32_multi_frame(b"QSAG.SPDZ.BLIND.OT/v1", &[session_id, phase.as_bytes()]);
    OtMesh::establish(sid, party_rngs)
}

///Multiplicatively blind and open an additive `GoldilocksExt2` MAC residual (`1 / p^2 \approx 2^{-128}`
/// soundness, `0` choice-bit leakage).
///
/// When `mesh` is `Some`, consumes one single-use `(r, a, c = r * a)` triple from the mesh's
/// pre-staged `GoldilocksExt2` blinding pool (auto-refilling if empty); when `None`, establishes
/// a dedicated one-shot Ring-LWE OT mesh and multiplies directly.
pub fn blind_open_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    residual: &[GoldilocksExt2],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    if residual.is_empty()
        || residual.len() != party_rngs.len()
        || mesh.as_ref().is_some_and(|m| m.n != residual.len())
    {
        return Err(PreprocessError::InvalidThreshold {
            t: residual.len(),
            n: party_rngs.len(),
        });
    }
    let mut owned_mesh;
    let mesh = match mesh {
        Some(mesh) => return mesh.blind_open_ext2_pooled(session_id, phase, residual, party_rngs),
        None => {
            owned_mesh = blinding_mesh(session_id, phase, party_rngs)?;
            &mut owned_mesh
        }
    };
    // Multiply in the EXTENSION field directly. Splitting into four base-field
    // OLEs would let a malicious peer use inconsistent correlations in the four
    // columns, weakening the extension-field soundness to a base-field event.
    let randomizers = SecretBuffer(
        party_rngs
            .iter_mut()
            .map(|rng| vec![rng.next_ext2()])
            .collect::<Vec<_>>(),
    );
    let senders = SecretBuffer(residual.iter().map(|&d| vec![d]).collect::<Vec<_>>());
    let products = SecretBuffer(ole_blind_ext2_batch(
        session_id,
        mesh,
        &randomizers,
        &senders,
        party_rngs,
    )?);
    let w = SecretBuffer(products.iter().map(|row| row[0]).collect::<Vec<_>>());
    commit_and_open_additive_ext2(session_id, phase, &w, party_rngs)
}

fn commit_and_open_additive_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let n = shares.len();
    if n == 0 || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: n, n });
    }
    // Represent additive shares as n-of-n Shamir shares using PUBLIC inverse weights.
    let points = (1..=n)
        .map(|p| Goldilocks::from_u64_reduced(p as u64))
        .collect::<Vec<_>>();
    let lambdas = lagrange_weights_zero_goldilocks(&points)
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let shamir = SecretBuffer(
        (0..n)
            .map(|p| shares[p].mul_base(lambdas[p].inv()))
            .collect::<Vec<_>>(),
    );
    commit_and_open_degree_ext2(session_id, phase, n, &points, &shamir, party_rngs)
}

/// Native-field batched `GoldilocksExt2` OLE. The only receiver choices are `640 * count`
/// disposable random bits; neither the sender payload nor its coordinates ever supply a choice bit.
/// Each item retains a 384-bit post-OT LHL entropy budget after a field-sized error observation
/// and the 128-bit extracted randomizer. Sender errors therefore cannot turn the final opening
/// into probes of secret bits. The public correction derandomizes each extracted mask to the
/// fresh receiver randomizer; it never opens a sender input.
fn ole_blind_ext2_batch(
    session_id: &[u8; 32],
    mesh: &mut OtMesh,
    randomizers: &[Vec<GoldilocksExt2>],
    senders: &[Vec<GoldilocksExt2>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<GoldilocksExt2>>, PreprocessError> {
    const WORDS_PER_ITEM: usize = 10;
    const BITS_PER_ITEM: usize = 64 * WORDS_PER_ITEM;
    let n = senders.len();
    let count = senders[0].len();
    if count == 0 {
        return Ok(vec![Vec::new(); n]);
    }
    let total_words = count
        .checked_mul(WORDS_PER_ITEM)
        .ok_or(BLIND_POOL_EXHAUSTED)?;
    let total_bits = count
        .checked_mul(BITS_PER_ITEM)
        .ok_or(BLIND_POOL_EXHAUSTED)?;
    let choices = SecretBuffer(
        party_rngs
            .iter_mut()
            .map(|rng| (0..total_words).map(|_| rng.next_u64()).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
    );
    let mut raw = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; total_bits]; n]);
    let mut bind = Cshake256Xof::new(b"QSAG.SPDZ.BLIND.EXT2.CT/v1");
    for receiver in 0..n {
        for sender in 0..n {
            if sender == receiver {
                continue;
            }
            let (send, recv) =
                mesh.run_correlated_ot_words(sender, receiver, &choices[receiver], party_rngs)?;
            for (k, &s_val) in senders[sender].iter().enumerate().take(count) {
                let base_bit = k * BITS_PER_ITEM;
                for b in 0..BITS_PER_ITEM {
                    let bit = base_bit + b;
                    let decode = |pad: &[u8; 48]| {
                        GoldilocksExt2::new(
                            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| pad[i])),
                            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| {
                                pad[24 + i]
                            })),
                        )
                    };
                    let mask = party_rngs[sender].next_ext2();
                    let ct0 = decode(&send[bit].0) - mask;
                    let ct1 = decode(&send[bit].1) + s_val - mask;
                    bind.absorb(&ct0.to_be_bytes());
                    bind.absorb(&ct1.to_be_bytes());
                    let choice = (choices[receiver][bit / 64] >> (bit % 64)) & 1;
                    let select = 0u64.wrapping_sub(black_box(choice));
                    let selected = GoldilocksExt2::new(
                        Goldilocks::from_u64_reduced(
                            ct0.c0.to_canonical_u64()
                                ^ (select & (ct0.c0.to_canonical_u64() ^ ct1.c0.to_canonical_u64())),
                        ),
                        Goldilocks::from_u64_reduced(
                            ct0.c1.to_canonical_u64()
                                ^ (select & (ct0.c1.to_canonical_u64() ^ ct1.c1.to_canonical_u64())),
                        ),
                    );
                    raw[sender][bit] += mask;
                    raw[receiver][bit] += selected - decode(&recv[bit]);
                }
            }
        }
    }
    bind.absorb(&mesh.transcript_digest());
    let mut digest = [0u8; 32];
    bind.squeeze(&mut digest);
    let coin = run_commit_and_open_coin(session_id, b"SPDZ_BLIND_EXT2_LHL", &digest, party_rngs)?;
    let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BLIND.EXT2.H/v1");
    xof.absorb(&coin);
    let mut extracted = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; count]; n]);
    let mut w = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; count]; n]);
    for k in 0..count {
        let base_bit = k * BITS_PER_ITEM;
        for b in 0..BITS_PER_ITEM {
            let bit = base_bit + b;
            let mut bytes = [0u8; 48];
            xof.squeeze(&mut bytes);
            let g = GoldilocksExt2::new(
                Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| bytes[i])),
                Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| bytes[24 + i])),
            );
            for party in 0..n {
                let select =
                    0u64.wrapping_sub(black_box((choices[party][bit / 64] >> (bit % 64)) & 1));
                extracted[party][k] += GoldilocksExt2::new(
                    Goldilocks::from_u64_reduced(select & g.c0.to_canonical_u64()),
                    Goldilocks::from_u64_reduced(select & g.c1.to_canonical_u64()),
                );
                w[party][k] += g * raw[party][bit];
            }
        }
    }
    for k in 0..count {
        let diffs = SecretBuffer(
            (0..n)
                .map(|p| randomizers[p][k] - extracted[p][k])
                .collect::<Vec<_>>(),
        );
        let sum_diff = diffs
            .iter()
            .copied()
            .fold(GoldilocksExt2::ZERO, |a, b| a + b);
        for party in 0..n {
            w[party][k] += senders[party][k] * (randomizers[party][k] + sum_diff - diffs[party]);
        }
    }
    Ok(w.into_inner())
}

fn commit_and_open_additive_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    shares: &[Tower128],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    let n = shares.len();
    if n == 0 || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: n, n });
    }
    let mut salts = SecretBuffer(vec![[0u8; 32]; n]);
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        salts[p] = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].0.to_le_bytes();
        coms.push(cshake256_32_multi_frame(
            b"QSAG.SPDZ.T128.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salts[p]],
        ));
    }
    let mut sum = Tower128::ZERO;
    for p in 0..n {
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].0.to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.T128.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salts[p]],
        );
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
        sum = sum.add(shares[p]);
    }
    Ok(sum)
}

pub(crate) fn blind_open_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    residual: &[Tower128],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    if residual.is_empty()
        || residual.len() != party_rngs.len()
        || mesh.as_ref().is_some_and(|m| m.n != residual.len())
    {
        return Err(PreprocessError::InvalidThreshold {
            t: residual.len(),
            n: party_rngs.len(),
        });
    }
    // A retained mesh answers from its pre-staged single-use triple pool. A mesh that
    // exists only for this one opening has nothing to amortize and multiplies directly.
    let mut owned_mesh;
    let mesh = match mesh {
        Some(mesh) => return mesh.blind_open_pooled(session_id, phase, residual, party_rngs),
        None => {
            owned_mesh = blinding_mesh(session_id, phase, party_rngs)?;
            &mut owned_mesh
        }
    };
    let sender = SecretBuffer(residual.iter().map(|&d| vec![d]).collect::<Vec<_>>());
    // Repeat independently so even a fault confined to ONE MAC lane retains
    // 2^-256 rejection soundness, rather than accepting when one randomizer is zero.
    for round in 0u64..2 {
        let round_sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.T128.ROUND/v1",
            &[session_id, phase.as_bytes(), &round.to_be_bytes()],
        );
        let receiver = SecretBuffer(
            party_rngs
                .iter_mut()
                .map(|rng| vec![rng.next_tower128()])
                .collect::<Vec<_>>(),
        );
        // Tower OLE's FIRST input is the sender, its SECOND input is the receiver.
        let products = SecretBuffer(pairwise_ole_tower128(
            &round_sid, mesh, &sender, &receiver, party_rngs,
        )?);
        let shares = SecretBuffer(products.iter().map(|w| w[0]).collect::<Vec<_>>());
        let opened = commit_and_open_additive_tower128(&round_sid, phase, &shares, party_rngs)?;
        if !opened.ct_eq(Tower128::ZERO) {
            return Ok(opened);
        }
    }
    Ok(Tower128::ZERO)
}

/// Multiplicatively blind and open additive `GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)` MAC residuals
/// by mapping into `Tower128` via the exact field isomorphism `poly128_to_tower128_ct` and running
/// two independent `pairwise_ole_tower128` rounds (`2^-256` rejection soundness, `0` key-bit leakage).
pub fn blind_open_additive_gf128_poly(
    session_id: &[u8; 32],
    phase: &'static str,
    poly_residuals: &[u128],
    mesh: Option<&mut OtMesh>,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<u128, PreprocessError> {
    let tower_residuals = SecretBuffer(
        poly_residuals
            .iter()
            .map(|&r| Tower128(qsag_asm::poly128_to_tower128_ct(r)))
            .collect::<Vec<_>>(),
    );
    let opened = blind_open_tower128(session_id, phase, &tower_residuals, mesh, party_rngs)?;
    let mut flat = SecretBuffer([0u128; 64]);
    flat.0[0] = opened.0;
    qsag_asm::tower128_to_poly128_x64_ct(&mut flat.0);
    Ok(flat.0[0])
}

/// One single-use multiplicative blinding triple: per-party additive shares of a joint
/// randomizer `r`, a one-time mask `a`, and `c = r * a`. Not `Clone`; wiped on drop.
struct BlindTriple {
    /// Position in the mesh's lifetime triple sequence, bound into both openings that use it.
    serial: u64,
    r: SecretBuffer<Vec<Tower128>>,
    a: SecretBuffer<Vec<Tower128>>,
    c: SecretBuffer<Vec<Tower128>>,
}

/// One single-use multiplicative `GoldilocksExt2` blinding triple: per-party additive shares
/// of a joint randomizer `r`, a one-time mask `a`, and `c = r * a` in $\mathbb{F}_{p^2}$.
/// Not `Clone`; wiped on drop.
struct Ext2BlindTriple {
    serial: u64,
    r: SecretBuffer<Vec<GoldilocksExt2>>,
    a: SecretBuffer<Vec<GoldilocksExt2>>,
    c: SecretBuffer<Vec<GoldilocksExt2>>,
}

/// Single-use blinding triples staged on a retained [`OtMesh`].
#[derive(Default)]
pub(super) struct BlindPool {
    triples: Vec<BlindTriple>,
    /// Number of triples ever staged; the next refill starts its serials here.
    staged: u64,
    refills: u64,
    /// Set by a failed refill or a rejected opening commitment. Never cleared.
    poisoned: bool,
    #[cfg(test)]
    fail_next_refill: bool,
    ext2_triples: Vec<Ext2BlindTriple>,
    ext2_staged: u64,
    ext2_refills: u64,
    ext2_poisoned: bool,
    #[cfg(test)]
    fail_next_ext2_refill: bool,
}

const BLIND_POOL_POISONED: PreprocessError = PreprocessError::VaultPoisoned {
    kind: "blinding_pool",
};
const BLIND_POOL_EXHAUSTED: PreprocessError = PreprocessError::VaultExhausted {
    kind: "blinding_pool",
};
const EXT2_BLIND_POOL_POISONED: PreprocessError = PreprocessError::VaultPoisoned {
    kind: "ext2_blinding_pool",
};
const EXT2_BLIND_POOL_EXHAUSTED: PreprocessError = PreprocessError::VaultExhausted {
    kind: "ext2_blinding_pool",
};

/// Independent blinding rounds per check; see [`blind_open_tower128`].
const BLIND_ROUNDS: usize = 2;
/// Checks staged by an automatic refill when a check finds the pool empty.
const BLIND_AUTO_REFILL_CHECKS: usize = 8;

impl OtMesh {
    /// Number of blinded MAC checks the staged pool can answer without a refill.
    pub fn staged_blinded_checks(&self) -> usize {
        self.blind_pool.triples.len() / BLIND_ROUNDS
    }

    /// Number of `GoldilocksExt2` blinded MAC checks the staged pool can answer without a refill.
    pub fn staged_ext2_blinded_checks(&self) -> usize {
        self.blind_pool.ext2_triples.len()
    }

    /// Make the next refill fail before it stages anything.
    #[cfg(test)]
    pub(crate) fn fail_next_blinding_refill(&mut self) {
        self.blind_pool.fail_next_refill = true;
    }

    /// Make the next `GoldilocksExt2` refill fail before it stages anything.
    #[cfg(test)]
    pub(crate) fn fail_next_ext2_blinding_refill(&mut self) {
        self.blind_pool.fail_next_ext2_refill = true;
    }

    /// Joint randomizer of the triple the next pooled round will consume.
    #[cfg(test)]
    pub(super) fn next_blinding_randomizer(&self) -> Option<Tower128> {
        self.blind_pool
            .triples
            .last()
            .map(|t| t.r.iter().fold(Tower128::ZERO, |sum, &r| sum.add(r)))
    }

    /// Joint randomizer of the `GoldilocksExt2` triple the next pooled check will consume.
    #[cfg(test)]
    pub(super) fn next_ext2_blinding_randomizer(&self) -> Option<GoldilocksExt2> {
        self.blind_pool
            .ext2_triples
            .last()
            .map(|t| t.r.iter().copied().fold(GoldilocksExt2::ZERO, |s, r| s + r))
    }

    /// Serials of the staged triples, oldest first.
    #[cfg(test)]
    pub(crate) fn staged_blinding_serials(&self) -> Vec<u64> {
        self.blind_pool.triples.iter().map(|t| t.serial).collect()
    }

    /// Serials of the staged `GoldilocksExt2` triples, oldest first.
    #[cfg(test)]
    pub(crate) fn staged_ext2_blinding_serials(&self) -> Vec<u64> {
        self.blind_pool
            .ext2_triples
            .iter()
            .map(|t| t.serial)
            .collect()
    }

    /// Whether a failed refill or opening has permanently disabled pooled checks on this mesh.
    pub fn blinding_poisoned(&self) -> bool {
        self.blind_pool.poisoned
    }

    /// Whether a failed refill or opening has permanently disabled pooled `GoldilocksExt2` checks.
    pub fn ext2_blinding_poisoned(&self) -> bool {
        self.blind_pool.ext2_poisoned
    }

    /// Stage single-use `GoldilocksExt2` blinding material for `checks` further MAC checks.
    ///
    /// Runs one batched LHL-amplified native-field `GoldilocksExt2` OLE over the mesh with fresh
    /// per-party randomizers and masks. Each refill batch is bound to the mesh session, party
    /// count, refill index, first triple serial and running OT transcript. A failure permanently
    /// poisons and wipes the `GoldilocksExt2` pool.
    pub fn prestage_ext2_blinded_checks(
        &mut self,
        checks: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), PreprocessError> {
        if self.blind_pool.ext2_poisoned {
            return Err(EXT2_BLIND_POOL_POISONED);
        }
        let n = self.n;
        if party_rngs.len() != n {
            return Err(PreprocessError::InvalidThreshold {
                t: n,
                n: party_rngs.len(),
            });
        }
        if checks == 0 {
            return Ok(());
        }
        let staged = self.refill_ext2_blind_pool(checks, party_rngs);
        if staged.is_err() {
            self.poison_ext2_blind_pool();
        }
        staged
    }

    fn poison_ext2_blind_pool(&mut self) {
        self.blind_pool.ext2_poisoned = true;
        self.blind_pool.ext2_triples.clear();
    }

    fn refill_ext2_blind_pool(
        &mut self,
        checks: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), PreprocessError> {
        let n = self.n;
        let first_serial = self.blind_pool.ext2_staged;
        let next_staged = first_serial
            .checked_add(checks as u64)
            .ok_or(EXT2_BLIND_POOL_EXHAUSTED)?;
        let refill = self.blind_pool.ext2_refills;
        self.blind_pool.ext2_refills = refill.checked_add(1).ok_or(EXT2_BLIND_POOL_EXHAUSTED)?;
        #[cfg(test)]
        if core::mem::take(&mut self.blind_pool.fail_next_ext2_refill) {
            return Err(EXT2_BLIND_POOL_POISONED);
        }
        // Seven frames vs three in `blind_open_degree_ext2` and five in `blind_open_ext2_pooled`,
        // so frame-count length prefixing guarantees complete domain disjointness with zero new labels.
        let refill_sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.EXT2.DEG/v1",
            &[
                &self.session_id,
                b"ext2_blind_pool_refill",
                &(n as u64).to_be_bytes(),
                &refill.to_be_bytes(),
                &first_serial.to_be_bytes(),
                &(checks as u64).to_be_bytes(),
                &self.transcript,
            ],
        );
        let draw = |rngs: &mut [PartyPrivateRng]| {
            SecretBuffer(
                rngs.iter_mut()
                    .map(|rng| (0..checks).map(|_| rng.next_ext2()).collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
            )
        };
        let masks = draw(party_rngs);
        let randomizers = draw(party_rngs);
        let products = SecretBuffer(ole_blind_ext2_batch(
            &refill_sid,
            self,
            &randomizers,
            &masks,
            party_rngs,
        )?);
        self.blind_pool.ext2_triples.reserve(checks);
        for k in 0..checks {
            let column = |rows: &[Vec<GoldilocksExt2>]| {
                SecretBuffer(rows.iter().map(|row| row[k]).collect::<Vec<_>>())
            };
            self.blind_pool.ext2_triples.push(Ext2BlindTriple {
                serial: first_serial + k as u64,
                r: column(&randomizers),
                a: column(&masks),
                c: column(&products),
            });
        }
        self.blind_pool.ext2_staged = next_staged;
        Ok(())
    }

    /// Pooled multiplicative blinding of an additive `GoldilocksExt2` residual `d`.
    ///
    /// Pops one single-use triple `(r, a, c = r * a)`, commit-opens `e = d + a`, and then
    /// commit-opens `w = r * e - c = r * d`. An empty pool refills itself; any failed refill or
    /// rejected commitment permanently poisons and wipes the pool.
    fn blind_open_ext2_pooled(
        &mut self,
        session_id: &[u8; 32],
        phase: &'static str,
        residual: &[GoldilocksExt2],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<GoldilocksExt2, PreprocessError> {
        if self.blind_pool.ext2_poisoned {
            return Err(EXT2_BLIND_POOL_POISONED);
        }
        if self.blind_pool.ext2_triples.is_empty() {
            self.prestage_ext2_blinded_checks(BLIND_AUTO_REFILL_CHECKS, party_rngs)?;
        }
        let Some(triple) = self.blind_pool.ext2_triples.pop() else {
            self.poison_ext2_blind_pool();
            return Err(EXT2_BLIND_POOL_POISONED);
        };
        let n = self.n;
        let serial = triple.serial.to_be_bytes();
        let opening_sid = |stage: &[u8]| {
            cshake256_32_multi_frame(
                b"QSAG.SPDZ.BLIND.EXT2.DEG/v1",
                &[
                    session_id,
                    phase.as_bytes(),
                    &self.session_id,
                    &serial,
                    stage,
                ],
            )
        };
        let (mask_sid, product_sid) = (opening_sid(b"mask"), opening_sid(b"product"));
        let masked = SecretBuffer(
            (0..n)
                .map(|p| residual[p] + triple.a[p])
                .collect::<Vec<_>>(),
        );
        let e = match commit_and_open_additive_ext2(&mask_sid, phase, &masked, party_rngs) {
            Ok(e) => e,
            Err(err) => {
                self.poison_ext2_blind_pool();
                return Err(err);
            }
        };
        let shares = SecretBuffer(
            (0..n)
                .map(|p| blinding_ext2_product(triple.r[p], e) - triple.c[p])
                .collect::<Vec<_>>(),
        );
        match commit_and_open_additive_ext2(&product_sid, phase, &shares, party_rngs) {
            Ok(w) => Ok(w),
            Err(err) => {
                self.poison_ext2_blind_pool();
                Err(err)
            }
        }
    }

    /// Stage single-use blinding material for `checks` further MAC checks.
    ///
    /// Runs one batched entropy-amplified Tower OLE over the mesh with fresh per-party
    /// randomizers and masks. Each refill batch is bound to the mesh session, the party
    /// count, its refill index and the first triple serial it produces. A failure poisons
    /// the pool: staged triples are wiped and every later pooled check is refused.
    pub fn prestage_blinded_checks(
        &mut self,
        checks: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), PreprocessError> {
        if self.blind_pool.poisoned {
            return Err(BLIND_POOL_POISONED);
        }
        let n = self.n;
        if party_rngs.len() != n {
            return Err(PreprocessError::InvalidThreshold {
                t: n,
                n: party_rngs.len(),
            });
        }
        if checks == 0 {
            return Ok(());
        }
        let staged = self.refill_blind_pool(checks, party_rngs);
        if staged.is_err() {
            self.poison_blind_pool();
        }
        staged
    }

    fn poison_blind_pool(&mut self) {
        self.blind_pool.poisoned = true;
        // Dropping each triple wipes its shares.
        self.blind_pool.triples.clear();
    }

    fn refill_blind_pool(
        &mut self,
        checks: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), PreprocessError> {
        let n = self.n;
        let count = checks
            .checked_mul(BLIND_ROUNDS)
            .ok_or(BLIND_POOL_EXHAUSTED)?;
        let first_serial = self.blind_pool.staged;
        let next_staged = first_serial
            .checked_add(count as u64)
            .ok_or(BLIND_POOL_EXHAUSTED)?;
        let refill = self.blind_pool.refills;
        self.blind_pool.refills = refill.checked_add(1).ok_or(BLIND_POOL_EXHAUSTED)?;
        #[cfg(test)]
        if core::mem::take(&mut self.blind_pool.fail_next_refill) {
            return Err(BLIND_POOL_POISONED);
        }
        // Four more frames than any per-check round label, so a refill batch can never
        // share a session with an opening whatever phase string a caller supplies.
        let refill_sid = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BLIND.T128.ROUND/v1",
            &[
                &self.session_id,
                b"blind_pool_refill",
                &(n as u64).to_be_bytes(),
                &refill.to_be_bytes(),
                &first_serial.to_be_bytes(),
                &(count as u64).to_be_bytes(),
                &self.transcript,
            ],
        );
        let draw = |rngs: &mut [PartyPrivateRng]| {
            SecretBuffer(
                rngs.iter_mut()
                    .map(|rng| (0..count).map(|_| rng.next_tower128()).collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
            )
        };
        let masks = draw(party_rngs);
        let randomizers = draw(party_rngs);
        // The mask is the OLE sender input and the randomizer the receiver input, exactly
        // the roles the residual and the randomizer take in the direct multiplication.
        let products = SecretBuffer(pairwise_ole_tower128(
            &refill_sid,
            self,
            &masks,
            &randomizers,
            party_rngs,
        )?);
        self.blind_pool.triples.reserve(count);
        for k in 0..count {
            let column = |rows: &[Vec<Tower128>]| {
                SecretBuffer(rows.iter().map(|row| row[k]).collect::<Vec<_>>())
            };
            self.blind_pool.triples.push(BlindTriple {
                serial: first_serial + k as u64,
                r: column(&randomizers),
                a: column(&masks),
                c: column(&products),
            });
        }
        self.blind_pool.staged = next_staged;
        Ok(())
    }

    /// Pooled multiplicative blinding of an additive residual `d`.
    ///
    /// Each of the two rounds pops one triple `(r, a, c = r * a)` that no other round or
    /// check ever sees, opens the one-time-padded `e = d + a` behind commitments, and then
    /// opens `w = r * e + c = r * d` behind commitments. The residual shares never leave a
    /// party except under the uniform mask `a`, and `w` is a field permutation of `d` under
    /// the uniform `r`, as in the direct multiplication. An empty pool refills itself; if
    /// that fails, or an opening commitment is rejected, the pool is poisoned.
    fn blind_open_pooled(
        &mut self,
        session_id: &[u8; 32],
        phase: &'static str,
        residual: &[Tower128],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Tower128, PreprocessError> {
        if self.blind_pool.poisoned {
            return Err(BLIND_POOL_POISONED);
        }
        let n = self.n;
        for round in 0..BLIND_ROUNDS as u64 {
            if self.blind_pool.triples.is_empty() {
                self.prestage_blinded_checks(BLIND_AUTO_REFILL_CHECKS, party_rngs)?;
            }
            // Moved out of the pool before anything is sent; wiped when this round ends,
            // whether it returns, fails or continues.
            let Some(triple) = self.blind_pool.triples.pop() else {
                self.poison_blind_pool();
                return Err(BLIND_POOL_POISONED);
            };
            let serial = triple.serial.to_be_bytes();
            let round_be = round.to_be_bytes();
            let opening_sid = |stage: &[u8]| {
                cshake256_32_multi_frame(
                    b"QSAG.SPDZ.BLIND.T128.ROUND/v1",
                    &[
                        session_id,
                        phase.as_bytes(),
                        &round_be,
                        &self.session_id,
                        &serial,
                        stage,
                    ],
                )
            };
            let (mask_sid, product_sid) = (opening_sid(b"mask"), opening_sid(b"product"));
            let masked = SecretBuffer(
                (0..n)
                    .map(|p| residual[p].add(triple.a[p]))
                    .collect::<Vec<_>>(),
            );
            let e = match commit_and_open_additive_tower128(&mask_sid, phase, &masked, party_rngs) {
                Ok(e) => e,
                Err(err) => {
                    self.poison_blind_pool();
                    return Err(err);
                }
            };
            let shares = SecretBuffer(
                (0..n)
                    .map(|p| blinding_tower_product(triple.r[p], e).add(triple.c[p]))
                    .collect::<Vec<_>>(),
            );
            let opened =
                match commit_and_open_additive_tower128(&product_sid, phase, &shares, party_rngs) {
                    Ok(w) => w,
                    Err(err) => {
                        self.poison_blind_pool();
                        return Err(err);
                    }
                };
            if !opened.ct_eq(Tower128::ZERO) {
                return Ok(opened);
            }
        }
        Ok(Tower128::ZERO)
    }
}

// Keep the large portable field circuit out of the basis-table loop's
// vectorization, just as for the regression's independent product oracle.
#[inline(never)]
fn blinding_tower_product(a: Tower128, b: Tower128) -> Tower128 {
    a.mul(b)
}

#[inline(never)]
fn blinding_ext2_product(a: GoldilocksExt2, b: GoldilocksExt2) -> GoldilocksExt2 {
    a * b
}

/// Entropy-amplified native-field Tower OLE with six independent 128-bit receiver masks.
/// Correlations and ciphertexts are fixed before the field-valued hash coin. The masks
/// supply 128-bit statistical privacy under affine bit errors, up to field-sized
/// MAC-key guessing events; see the module's committed blinding construction.
/// Computes additive shares of `(sum u) * (sum v)` without reconstructing either input.
pub(super) fn pairwise_ole_tower128(
    session_id: &[u8; 32],
    ot_mesh: &mut OtMesh,
    u_per_party: &[Vec<Tower128>],
    v_per_party: &[Vec<Tower128>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<Tower128>>, PreprocessError> {
    let n = ot_mesh.n;
    let count = u_per_party[0].len();
    let mut w_per_party = SecretBuffer(
        (0..n)
            .map(|i| {
                (0..count)
                    .map(|k| u_per_party[i][k].mul(v_per_party[i][k]))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
    );
    if count == 0 {
        return Ok(core::mem::take(&mut w_per_party.0));
    }

    // Each sender payload is multiplied by the same public basis elements in
    // every mask and receiver transfer. Compute those products once, preserving
    // the exact ciphertexts and RNG stream. Only PUBLIC (sender, column, bit)
    // indices address this secret table, which is wiped on every return path.
    let mut sender_basis = SecretBuffer(vec![vec![[Tower128::ZERO; 128]; count]; n]);
    for sender in 0..n {
        for k in 0..count {
            for bit in 0..128 {
                sender_basis[sender][k][bit] =
                    blinding_tower_product(u_per_party[sender][k], Tower128(1u128 << bit));
            }
        }
    }

    // Each party `i` samples `6 * count` uniform `Tower128` OT masks (`12 * count` u64 choice words)
    let mut r_masks = SecretBuffer(vec![vec![[Tower128::ZERO; 6]; count]; n]);
    let mut choice_words = crate::wipe::secret_vecs_with_capacity(n, 12 * count);
    for i in 0..n {
        for k in 0..count {
            for m in 0..6 {
                let r = party_rngs[i].next_tower128();
                r_masks[i][k][m] = r;
                choice_words[i].push(r.0 as u64);
                choice_words[i].push((r.0 >> 64) as u64);
            }
        }
    }

    let mut raw_s = SecretBuffer(vec![vec![vec![[Tower128::ZERO; 6]; count]; n]; n]);
    let mut raw_r = SecretBuffer(vec![vec![vec![[Tower128::ZERO; 6]; count]; n]; n]);
    let mut bind = Cshake256Xof::new(b"QSAG.SPDZ.BLIND.T128.CT/v1");
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            // Sender `j` inputs `u_j[k]`; Receiver `i` inputs uniform random `r_masks[i][k][0..6]`
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(j, i, &choice_words[i], party_rngs)?;
            for k in 0..count {
                for m in 0..6 {
                    let rm_raw = black_box(r_masks[i][k][m].0);
                    let mut s_sum = Tower128::ZERO;
                    let mut r_sum = Tower128::ZERO;
                    let base_off = (6 * k + m) * 128;
                    for bit in 0..128 {
                        let (p0, p1) = &send_pads[base_off + bit];
                        let pad0 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p0[0..16])[array_index]
                            })));
                        let pad1 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p1[0..16])[array_index]
                            })));
                        let mask = party_rngs[j].next_tower128();
                        s_sum = s_sum.add(mask);
                        let ct0 = mask.add(pad0);
                        let ct1 = mask.add(sender_basis[j][k][bit]).add(pad1);
                        bind.absorb(&ct0.0.to_le_bytes());
                        bind.absorb(&ct1.0.to_le_bytes());

                        let pad_c =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (recv_pads[base_off + bit][0..16])[array_index]
                            })));
                        let choice = ((rm_raw >> bit) & 1) == 1;
                        let cmask = 0u128.wrapping_sub(black_box(choice as u128));
                        let sel = Tower128(ct0.0 ^ (cmask & (ct0.0 ^ ct1.0)));
                        r_sum = r_sum.add(sel.add(pad_c));
                    }
                    raw_s[j][i][k][m] = s_sum;
                    raw_r[j][i][k][m] = r_sum;
                }
            }
        }
    }

    // Post-OT `Π_coin` 2-universal LHL combiner (`768 -> 128` bits) + MASCOT input derandomization
    bind.absorb(&ot_mesh.transcript_digest());
    let mut digest = [0u8; 32];
    bind.squeeze(&mut digest);
    let coin = run_commit_and_open_coin(session_id, b"PCG_OLE_T128_LHL", &digest, party_rngs)?;
    let mut xof = Cshake256Xof::new(b"QSAG.PCG.OLE.T128.LHL/v1");
    xof.absorb(&coin);
    let mut g_weights = vec![[Tower128::ONE; 6]; count];
    for g_weights_k_item in g_weights[..count].iter_mut() {
        for m in 1..6 {
            let mut gb = [0u8; 16];
            xof.squeeze(&mut gb);
            (*g_weights_k_item)[m] = Tower128(u128::from_le_bytes(gb));
        }
    }

    let mut diffs = SecretBuffer(vec![vec![Tower128::ZERO; count]; n]);
    for i in 0..n {
        for k in 0..count {
            let mut r_comb = r_masks[i][k][0];
            for m in 1..6 {
                r_comb = r_comb.add(g_weights[k][m].mul(r_masks[i][k][m]));
            }
            diffs[i][k] = v_per_party[i][k].add(r_comb);
            wipe_tower128(&mut r_masks[i][k]);
        }
        wipe_u64s(&mut choice_words[i]);
    }

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..count {
                let mut s_comb = raw_s[j][i][k][0];
                let mut r_comb = raw_r[j][i][k][0];
                for m in 1..6 {
                    let g = g_weights[k][m];
                    s_comb = s_comb.add(g.mul(raw_s[j][i][k][m]));
                    r_comb = r_comb.add(g.mul(raw_r[j][i][k][m]));
                }
                // `s_comb + r_comb == u_j * r_comb_i`; add `u_j * (v_i + r_comb_i)` to Sender `j`!
                s_comb = s_comb.add(u_per_party[j][k].mul(diffs[i][k]));
                w_per_party[j][k] = w_per_party[j][k].add(s_comb);
                w_per_party[i][k] = w_per_party[i][k].add(r_comb);
                wipe_tower128(&mut raw_s[j][i][k]);
                wipe_tower128(&mut raw_r[j][i][k]);
            }
        }
    }
    Ok(w_per_party.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rngs(tape: u8) -> Vec<PartyPrivateRng> {
        [tape, 200]
            .into_iter()
            .map(|seed| PartyPrivateRng::from_seed([seed; 32], b"mac-blind-regression"))
            .collect()
    }

    fn tower_rngs(n: usize, tape: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|p| PartyPrivateRng::from_seed([tape ^ (p as u8); 32], b"mac-blind-pool"))
            .collect()
    }

    #[test]
    fn pooled_blinding_consumes_each_triple_once_and_blinds_nonzero_residuals() {
        let n = 3;
        let sid = [0x4c; 32];
        let mut rngs = tower_rngs(n, 0x71);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        assert_eq!(mesh.staged_blinded_checks(), 0);
        mesh.prestage_blinded_checks(3, &mut rngs).unwrap();
        assert_eq!(mesh.staged_blinded_checks(), 3);
        let serials = mesh.staged_blinding_serials();
        assert_eq!(serials, (0..6).collect::<Vec<u64>>());

        // Every staged triple is a correct product of independent, nonzero values.
        let sum = |v: &[Tower128]| v.iter().fold(Tower128::ZERO, |a, &b| a.add(b));
        let mut seen = Vec::new();
        for triple in &mesh.blind_pool.triples {
            let (r, a, c) = (sum(&triple.r), sum(&triple.a), sum(&triple.c));
            assert!(c.ct_eq(r.mul(a)));
            assert!(!seen.contains(&r.0) && !seen.contains(&a.0));
            seen.push(r.0);
            seen.push(a.0);
        }

        // A zero residual, split additively, opens to zero and spends exactly two triples.
        let zero = [Tower128(0x55), Tower128(0x11), Tower128(0x44)];
        let w = blind_open_tower128(&sid, "pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
        assert!(w.ct_eq(Tower128::ZERO));
        assert_eq!(mesh.staged_blinding_serials(), (0..4).collect::<Vec<u64>>());

        // A nonzero residual stops at its first round, spending one more triple, and the
        // same residual opens to a different nonzero value under the next triple.
        let d = Tower128(0x1234_5678_9abc_def0_0fed_cba9_8765_4321);
        let bad = [d.add(Tower128(7)), Tower128(7), Tower128::ZERO];
        let w1 = blind_open_tower128(&sid, "pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
        assert_eq!(mesh.staged_blinding_serials(), (0..3).collect::<Vec<u64>>());
        let w2 = blind_open_tower128(&sid, "pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
        assert_eq!(mesh.staged_blinding_serials(), (0..2).collect::<Vec<u64>>());
        assert!(!w1.ct_eq(Tower128::ZERO) && !w2.ct_eq(Tower128::ZERO));
        assert!(!w1.ct_eq(w2) && !w1.ct_eq(d) && !w2.ct_eq(d));

        // An empty pool refills itself with serials that were never issued before.
        let w = blind_open_tower128(&sid, "pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
        assert!(w.ct_eq(Tower128::ZERO));
        assert!(mesh.staged_blinding_serials().is_empty());
        let w = blind_open_tower128(&sid, "pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
        assert!(w.ct_eq(Tower128::ZERO));
        let refilled = mesh.staged_blinding_serials();
        assert_eq!(
            refilled.len(),
            BLIND_ROUNDS * BLIND_AUTO_REFILL_CHECKS - BLIND_ROUNDS
        );
        assert!(refilled.iter().all(|&s| s >= 6));
    }

    #[test]
    fn pooled_blinding_matches_direct_verdict_and_fails_closed_on_refill_failure() {
        let n = 3;
        let sid = [0x4d; 32];
        let mut rngs = tower_rngs(n, 0x72);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        let zero = [Tower128(9), Tower128(8), Tower128(1)];
        let bad = [Tower128(9), Tower128(8), Tower128(3)];
        for (residual, expect_zero) in [(&zero, true), (&bad, false)] {
            let pooled =
                blind_open_tower128(&sid, "pool_cmp", residual, Some(&mut mesh), &mut rngs)
                    .unwrap();
            let direct = blind_open_tower128(&sid, "pool_cmp", residual, None, &mut rngs).unwrap();
            assert_eq!(pooled.ct_eq(Tower128::ZERO), expect_zero);
            assert_eq!(direct.ct_eq(Tower128::ZERO), expect_zero);
        }

        // Wrong shapes are refused before any triple is spent.
        let before = mesh.staged_blinding_serials();
        assert!(
            blind_open_tower128(&sid, "pool_shape", &zero[..2], Some(&mut mesh), &mut rngs)
                .is_err()
        );
        assert_eq!(mesh.staged_blinding_serials(), before);

        // Drain the pool, then make the automatic refill fail: the check is refused, the
        // pool is poisoned, and neither a later check nor a later refill is served.
        while mesh.staged_blinded_checks() > 0 {
            blind_open_tower128(&sid, "pool_drain", &zero, Some(&mut mesh), &mut rngs).unwrap();
        }
        mesh.fail_next_blinding_refill();
        assert_eq!(
            blind_open_tower128(&sid, "pool_fail", &zero, Some(&mut mesh), &mut rngs),
            Err(BLIND_POOL_POISONED)
        );
        assert!(mesh.blinding_poisoned());
        assert_eq!(
            blind_open_tower128(&sid, "pool_fail", &zero, Some(&mut mesh), &mut rngs),
            Err(BLIND_POOL_POISONED)
        );
        assert_eq!(
            mesh.prestage_blinded_checks(1, &mut rngs),
            Err(BLIND_POOL_POISONED)
        );
        assert_eq!(mesh.staged_blinded_checks(), 0);

        // A failed explicit refill discards what was already staged.
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        mesh.prestage_blinded_checks(2, &mut rngs).unwrap();
        mesh.fail_next_blinding_refill();
        assert!(mesh.prestage_blinded_checks(1, &mut rngs).is_err());
        assert!(mesh.blinding_poisoned() && mesh.staged_blinded_checks() == 0);
    }

    #[test]
    fn unanimous_opening_share_shift_aborts_without_releasing_alpha() {
        let sid = [0x9d; 32];
        let points = [Goldilocks::ONE, Goldilocks::from_u64_reduced(2)];
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let x = Goldilocks::from_u64_reduced(41);
        let mut private = rngs(31);
        let alpha_shares = shamir_share_ext2(2, &points, alpha, &mut private[0]);
        let shares = shamir_share_goldilocks(2, &points, x, &mut private[0]);
        let macs = shamir_share_ext2(2, &points, alpha.mul_base(x), &mut private[0]);
        let mut shifted = shares.clone();
        shifted[0] += Goldilocks::ONE;
        assert!(matches!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "unanimous_shift",
                2,
                &points,
                &shifted,
                &macs,
                &alpha_shares,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
        assert_eq!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "unanimous_honest",
                2,
                &points,
                &shares,
                &macs,
                &alpha_shares,
                &mut private,
            )
            .unwrap(),
            x
        );
    }

    #[test]
    fn degree_consistent_dealer_shift_with_full_redundancy_aborts() {
        let sid = [0x8d; 32];
        let points = (1..=3)
            .map(Goldilocks::from_u64_reduced)
            .collect::<Vec<_>>();
        let mut private = (0..3)
            .map(|p| PartyPrivateRng::from_seed([p + 60; 32], b"dealer-shift"))
            .collect::<Vec<_>>();
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let x = Goldilocks::from_u64_reduced(41);
        let keys = shamir_share_ext2(2, &points, alpha, &mut private[0]);
        let macs = shamir_share_ext2(2, &points, alpha.mul_base(x), &mut private[0]);
        let mut shares = shamir_share_goldilocks(2, &points, x, &mut private[0]);
        for share in &mut shares {
            *share += Goldilocks::ONE;
        }
        assert_eq!(
            open_and_check_degree_goldilocks(2, &points, &shares, "dealer_shift").unwrap(),
            x + Goldilocks::ONE
        );
        assert!(matches!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "dealer_shift",
                2,
                &points,
                &shares,
                &macs,
                &keys,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    #[test]
    fn degree_consistent_three_of_four_shift_aborts() {
        let sid = [0x8e; 32];
        let points = (1..=4)
            .map(Goldilocks::from_u64_reduced)
            .collect::<Vec<_>>();
        let mut private = (0..4)
            .map(|p| PartyPrivateRng::from_seed([p + 70; 32], b"three-of-four"))
            .collect::<Vec<_>>();
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let x = Goldilocks::from_u64_reduced(41);
        let keys = shamir_share_ext2(3, &points, alpha, &mut private[0]);
        let macs = shamir_share_ext2(3, &points, alpha.mul_base(x), &mut private[0]);
        let mut shares = shamir_share_goldilocks(3, &points, x, &mut private[0]);
        // The two corrupt points shift by a quadratic that vanishes at both
        // honest points. All four values STILL have degree <3, but x moves by 12.
        for p in 0..2 {
            shares[p] += (points[p] - points[2]) * (points[p] - points[3]);
        }
        assert_eq!(
            open_and_check_degree_goldilocks(3, &points, &shares, "coalition").unwrap(),
            x + Goldilocks::from_u64_reduced(12)
        );
        assert!(matches!(
            commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "three_of_four_shift",
                3,
                &points,
                &shares,
                &macs,
                &keys,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    #[test]
    fn private_degree_checks_reject_mac_tampering_at_an_extra_recipient() {
        let sid = [0x81; 32];
        let mut private = (0..4)
            .map(|p| PartyPrivateRng::from_seed([p + 80; 32], b"private-degree"))
            .collect::<Vec<_>>();
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        let points = (1..=4)
            .map(Goldilocks::from_u64_reduced)
            .collect::<Vec<_>>();
        let mut shares = shamir_share_ext2(3, &points, GoldilocksExt2::ZERO, &mut private[0]);
        assert_eq!(
            blind_open_degree_ext2(
                &sid,
                "private_degree_honest",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            )
            .unwrap(),
            GoldilocksExt2::ZERO
        );
        shares[3] += GoldilocksExt2::ONE;
        assert!(matches!(
            blind_open_degree_ext2(
                &sid,
                "private_degree",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::DegreeCheckFailed { .. })
        ));
        let points = (1..=4).map(TowerGf256).collect::<Vec<_>>();
        let mut shares = shamir_share_tower128(3, &points, Tower128::ZERO, &mut private[0]);
        assert_eq!(
            blind_open_degree_tower128(
                &sid,
                "private_degree_honest",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            )
            .unwrap(),
            Tower128::ZERO
        );
        shares[3] = shares[3].add(Tower128::ONE);
        assert!(matches!(
            blind_open_degree_tower128(
                &sid,
                "private_degree",
                3,
                &points,
                &shares,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::DegreeCheckFailed { .. })
        ));
    }

    #[test]
    fn unanimous_boolean_share_shift_aborts() {
        let sid = [0x7e; 32];
        let points = [TowerGf256(1), TowerGf256(2)];
        let mats = points
            .iter()
            .map(|&p| PublicGf256Matrix::from_public_scalar(p))
            .collect::<Vec<_>>();
        let alpha = [Tower128(0x123456), Tower128(0x987654)];
        let mut private = rngs(51);
        let mut alpha_shares = vec![[Tower128::ZERO; 2]; 2];
        let mut macs = vec![[[Tower128::ZERO; 64]; 2]; 2];
        for lane in 0..2 {
            let key = shamir_share_tower128(2, &points, alpha[lane], &mut private[0]);
            for p in 0..2 {
                alpha_shares[p][lane] = key[p];
            }
            #[expect(
                clippy::needless_range_loop,
                reason = "Each bit indexes the same lane in both parties' MAC arrays"
            )]
            for bit in 0..64 {
                let mac = shamir_share_tower128(
                    2,
                    &points,
                    alpha[lane].mul_gf256(TowerGf256(((42u64 >> bit) & 1) as u8)),
                    &mut private[0],
                );
                for p in 0..2 {
                    macs[p][lane][bit] = mac[p];
                }
            }
        }
        let mut shares = shamir_share_bits64_gf256_mats(2, &mats, 42, &mut private[0]);
        shares[0][0] ^= 1;
        assert!(matches!(
            commit_and_open_spdz_bs_gf256_quorum(
                &sid,
                "unanimous_boolean_shift",
                2,
                &points,
                &shares,
                &macs,
                &alpha_shares,
                &mut private,
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    #[test]
    fn pooled_ext2_blinding_consumes_each_triple_once_and_fails_closed() {
        let n = 3;
        let sid = [0x4e; 32];
        let mut rngs = tower_rngs(n, 0x73);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        assert_eq!(mesh.staged_ext2_blinded_checks(), 0);
        mesh.prestage_ext2_blinded_checks(3, &mut rngs).unwrap();
        assert_eq!(mesh.staged_ext2_blinded_checks(), 3);
        assert_eq!(
            mesh.staged_ext2_blinding_serials(),
            (0..3).collect::<Vec<u64>>()
        );

        let sum = |v: &[GoldilocksExt2]| v.iter().copied().fold(GoldilocksExt2::ZERO, |a, b| a + b);
        let mut seen = Vec::new();
        for triple in &mesh.blind_pool.ext2_triples {
            let (r, a, c) = (sum(&triple.r), sum(&triple.a), sum(&triple.c));
            assert!(c.ct_eq(r * a));
            assert!(!seen.contains(&r) && !seen.contains(&a));
            seen.push(r);
            seen.push(a);
        }

        let g1 = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(55),
            Goldilocks::from_u64_reduced(11),
        );
        let g2 = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(23),
            Goldilocks::from_u64_reduced(99),
        );
        let zero = [g1, g2, -(g1 + g2)];
        let w = blind_open_ext2(&sid, "ext2_pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
        assert!(w.ct_eq(GoldilocksExt2::ZERO));
        assert_eq!(
            mesh.staged_ext2_blinding_serials(),
            (0..2).collect::<Vec<u64>>()
        );

        let d = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(0x1234_5678),
            Goldilocks::from_u64_reduced(0x9abc_def0),
        );
        let bad = [d + g1, -g1, GoldilocksExt2::ZERO];
        let w1 = blind_open_ext2(&sid, "ext2_pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
        assert_eq!(mesh.staged_ext2_blinding_serials(), vec![0]);
        let w2 = blind_open_ext2(&sid, "ext2_pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
        assert!(mesh.staged_ext2_blinding_serials().is_empty());
        assert!(!w1.ct_eq(GoldilocksExt2::ZERO) && !w2.ct_eq(GoldilocksExt2::ZERO));
        assert!(!w1.ct_eq(w2) && !w1.ct_eq(d) && !w2.ct_eq(d));

        // Automatic refill issues strictly fresh monotone serials >= 3.
        let w = blind_open_ext2(&sid, "ext2_pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
        assert!(w.ct_eq(GoldilocksExt2::ZERO));
        let refilled = mesh.staged_ext2_blinding_serials();
        assert_eq!(refilled.len(), BLIND_AUTO_REFILL_CHECKS - 1);
        assert!(refilled.iter().all(|&s| s >= 3));

        // Wrong shapes are refused before spending a triple.
        let before = mesh.staged_ext2_blinding_serials();
        assert!(
            blind_open_ext2(
                &sid,
                "ext2_pool_shape",
                &zero[..2],
                Some(&mut mesh),
                &mut rngs
            )
            .is_err()
        );
        assert_eq!(mesh.staged_ext2_blinding_serials(), before);

        // Failed refill poisons permanently and wipes all staged triples.
        while mesh.staged_ext2_blinded_checks() > 0 {
            blind_open_ext2(&sid, "ext2_drain", &zero, Some(&mut mesh), &mut rngs).unwrap();
        }
        mesh.fail_next_ext2_blinding_refill();
        assert_eq!(
            blind_open_ext2(&sid, "ext2_fail", &zero, Some(&mut mesh), &mut rngs),
            Err(EXT2_BLIND_POOL_POISONED)
        );
        assert!(mesh.ext2_blinding_poisoned());
        assert_eq!(
            blind_open_ext2(&sid, "ext2_fail", &zero, Some(&mut mesh), &mut rngs),
            Err(EXT2_BLIND_POOL_POISONED)
        );
        assert_eq!(
            mesh.prestage_ext2_blinded_checks(1, &mut rngs),
            Err(EXT2_BLIND_POOL_POISONED)
        );
    }

    #[test]
    fn repeated_aborts_with_fixed_alpha_open_fresh_field_permutations() {
        let sid = [0x4b; 32];
        let alpha = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(19),
            Goldilocks::from_u64_reduced(23),
        );
        let d = -alpha.mul_base(Goldilocks::from_u64_reduced(17));
        let residual = [d - GoldilocksExt2::ONE, GoldilocksExt2::ONE];
        let mut seen = Vec::new();
        for tape in 1..=16 {
            let mut private = rngs(tape);
            let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
            mesh.prestage_ext2_blinded_checks(1, &mut private).unwrap();
            let r = mesh.next_ext2_blinding_randomizer().unwrap();
            assert_eq!(mesh.staged_ext2_blinding_serials(), vec![0]);
            let w = blind_open_ext2(
                &sid,
                "fixed_alpha_abort",
                &residual,
                Some(&mut mesh),
                &mut private,
            )
            .unwrap();
            assert!(mesh.staged_ext2_blinding_serials().is_empty());
            assert_eq!(w, r * d, "pooled OLE must open exactly r * d");
            assert!(!w.ct_eq(GoldilocksExt2::ZERO));
            assert!(!w.ct_eq(d), "raw -delta*alpha residual escaped");
            assert!(!seen.contains(&w), "random tapes reused a check value");
            seen.push(w);
        }
        // Algebraic distribution check, beyond a sampling assertion: multiplication
        // by either nonzero residual is bijective. For a fixed corrupt contribution,
        // the honest randomizer that yields any target w exists and is unique.
        let other = d + GoldilocksExt2::ONE;
        let corrupt_r = GoldilocksExt2::new(Goldilocks::ONE, Goldilocks::from_u64_reduced(7));
        for target in seen {
            for residual in [d, other] {
                let honest_r = target * residual.inv().unwrap() - corrupt_r;
                assert_eq!((honest_r + corrupt_r) * residual, target);
            }
        }
    }

    #[test]
    #[ignore = "retained OtMesh GoldilocksExt2 pooled vs direct blinding latency"]
    fn bench_ext2_retained_mesh_mac_latency() {
        let n = 3;
        let sid = [0x4f; 32];
        let mut rngs = tower_rngs(n, 0x81);
        let t_setup = std::time::Instant::now();
        let mut mesh = OtMesh::establish(sid, &mut rngs).unwrap();
        let setup_ms = t_setup.elapsed().as_secs_f64() * 1e3;

        let checks = 64usize;
        let t_refill = std::time::Instant::now();
        mesh.prestage_ext2_blinded_checks(checks, &mut rngs)
            .unwrap();
        let refill_ms = t_refill.elapsed().as_secs_f64() * 1e3;

        let g1 = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(101),
            Goldilocks::from_u64_reduced(202),
        );
        let g2 = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(303),
            Goldilocks::from_u64_reduced(404),
        );
        let zero = [g1, g2, -(g1 + g2)];
        let mut samples = Vec::with_capacity(checks);
        for i in 0..checks {
            let call_sid = [i as u8; 32];
            let t0 = std::time::Instant::now();
            let w = blind_open_ext2(
                &call_sid,
                "bench_ext2_pool",
                &zero,
                Some(&mut mesh),
                &mut rngs,
            )
            .unwrap();
            samples.push(t0.elapsed().as_secs_f64() * 1e3);
            assert!(w.ct_eq(GoldilocksExt2::ZERO));
        }
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        std::eprintln!(
            "GoldilocksExt2 retained mesh (n={n}): setup={setup_ms:.2} ms, \
             refill({checks})={refill_ms:.2} ms ({:.3} ms/check), \
             online min={:.3} / median={:.3} / max={:.3} ms",
            refill_ms / checks as f64,
            samples[0],
            samples[checks / 2],
            samples[checks - 1],
        );
    }

    #[test]
    fn tower_blinding_is_multiplication_with_receiver_randomness() {
        let sid = [0x3c; 32];
        let mut seen = Vec::new();
        for tape in 1..=8 {
            let mut private = rngs(tape);
            let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
            let w = blind_open_tower128(
                &sid,
                "tower_abort",
                &[Tower128(0x1234), Tower128(0x9876)],
                Some(&mut mesh),
                &mut private,
            )
            .unwrap();
            assert_ne!(w, Tower128::ZERO);
            assert!(!seen.contains(&w));
            seen.push(w);
        }
        let mut private = rngs(42);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        assert_eq!(
            blind_open_tower128(
                &sid,
                "tower_zero",
                &[Tower128(7), Tower128(7)],
                Some(&mut mesh),
                &mut private
            )
            .unwrap(),
            Tower128::ZERO
        );
    }
}
