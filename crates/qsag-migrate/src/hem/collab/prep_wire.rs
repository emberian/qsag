//! A custodian's local state in the distributed preprocessing ceremony.
use super::*;
use crate::hem::collab::net::{self, NetError, Transport};
use qsag_core::preprocessing::{PartyCoinCommitState, verify_and_combine_coin_openings};

#[path = "prep_ot.rs"]
mod ot;
use ot::{Channels, PairIo};

impl From<NetError> for PrepError {
    fn from(error: NetError) -> Self {
        Self::Transport(error)
    }
}

// All preprocessing broadcasts have equal, publicly known lengths.
fn exchange<T: Transport>(net: &mut T, bytes: &[u8]) -> Result<Secret<Vec<Vec<u8>>>, PrepError> {
    Ok(net::exchange(net, Secret(bytes.to_vec()), bytes.len())?)
}

struct Party<'a, T> {
    net: &'a mut T,
    rng: &'a mut PartyPrivateRng,
    session: [u8; 32],
    me: usize,
    n: usize,
    key: Secret<Mac>,
    channels: Channels,
    // One chain per link, identical at its two endpoints.
    chains: Vec<[u8; 32]>,
    pads: Vec<Pair>,
    transcript: Transcript,
    coins: u64,
    commits: u64,
}

fn decode(raw: &[u8], count: usize) -> Result<SecretVec<F>, PrepError> {
    if count.checked_mul(8) != Some(raw.len()) {
        return Err(Check::Commitment.into());
    }
    raw.chunks_exact(8)
        .map(|b| {
            F::from_canonical(u64::from_le_bytes(b.try_into().unwrap()))
                .map_err(|_| Check::Commitment.into())
        })
        .collect()
}

fn encode(values: &[F]) -> SecretVec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}

impl<T: Transport> Party<'_, T> {
    fn sample(&mut self) -> F {
        element_from(|b| self.rng.fill_bytes(b))
    }

    // Confirm every party saw the same commitments before releasing openings.
    fn agree(&mut self, digest: &[u8; 32]) -> Result<(), PrepError> {
        if exchange(self.net, digest)?
            .iter()
            .any(|d| d.as_slice() != digest)
        {
            return Err(Check::Commitment.into());
        }
        Ok(())
    }

    fn coin(&mut self, label: &[u8]) -> Result<Challenges, PrepError> {
        let row: Vec<u8> = self.chains.iter().flatten().copied().collect();
        let rows = exchange(self.net, &row)?;
        if rows.iter().any(|r| r.len() != row.len()) {
            return Err(Check::Coin.into());
        }
        self.transcript.label(b"pair traffic");
        for (a, row_a) in rows.iter().enumerate() {
            for (b, row_b) in rows.iter().enumerate().skip(a + 1) {
                let hash = &row_a[b * 32..(b + 1) * 32];
                if hash != &row_b[a * 32..(a + 1) * 32] {
                    return Err(Check::Coin.into());
                }
                self.transcript.bytes(hash);
            }
        }
        let digest = self.transcript.digest();
        let mut phase = label.to_vec();
        phase.extend_from_slice(&self.coins.to_le_bytes());
        self.coins = self.coins.checked_add(1).ok_or(Check::Coin)?;
        let state = PartyCoinCommitState::commit(self.me, &self.session, &phase, &digest, self.rng);
        let commits: Vec<[u8; 32]> = exchange(self.net, &[state.commitment(), digest].concat())?
            .iter()
            .map(|b| {
                if b.get(32..) != Some(digest.as_slice()) {
                    return Err(Check::Coin);
                }
                b[..32].try_into().map_err(|_| Check::Coin)
            })
            .collect::<Result<_, _>>()?;
        self.agree(&cshake256_framed_32(
            b"QSAG.COLLAB.PREP.COIN.COMMITMENTS/v1",
            &[commits.as_flattened()],
        ))?;
        let mine = state.open_share(&commits).map_err(|_| Check::Coin)?;
        let openings: Vec<[u8; 32]> = exchange(self.net, &mine)?
            .iter()
            .map(|b| b.as_slice().try_into().map_err(|_| Check::Coin))
            .collect::<Result<_, _>>()?;
        let coin =
            verify_and_combine_coin_openings(&self.session, &phase, &digest, &commits, &openings)
                .map_err(|_| Check::Coin)?;
        self.transcript.label(b"coin");
        self.transcript.bytes(&coin);
        Ok(Challenges(xof(
            b"QSAG.COLLAB.PREP.CHALLENGE/v1",
            &[&self.session, &phase, &coin],
        )))
    }

    fn commit_then_open(
        &mut self,
        label: &[u8],
        payload: &[F],
    ) -> Result<Vec<SecretVec<F>>, PrepError> {
        let invocation = self.commits;
        self.commits = invocation.checked_add(1).ok_or(Check::Commitment)?;
        let nonce = Secret(self.rng.next_bytes32());
        let words: SecretVec<u64> = payload.iter().map(|v| v.to_canonical_u64()).collect();
        let mine = commitment(&self.session, label, invocation, self.me, &words, &nonce);
        let commits = exchange(self.net, &mine)?;
        self.transcript.label(label);
        self.transcript.bytes(&invocation.to_le_bytes());
        for c in commits.iter() {
            if c.len() != 32 {
                return Err(Check::Commitment.into());
            }
            self.transcript.bytes(c);
        }
        let digest = self.transcript.digest();
        self.agree(&digest)?;
        let mut opening = encode(payload);
        opening.extend_from_slice(&*nonce);
        let mut all = Vec::with_capacity(self.n);
        for (p, raw) in exchange(self.net, &opening)?.iter().enumerate() {
            if raw.len() != opening.len() {
                return Err(Check::Commitment.into());
            }
            let (bytes, nonce) = raw.split_at(raw.len() - 32);
            let values = decode(bytes, payload.len())?;
            let words: SecretVec<u64> = values.iter().map(|v| v.to_canonical_u64()).collect();
            let got = commitment(
                &self.session,
                label,
                invocation,
                p,
                &words,
                nonce.try_into().unwrap(),
            );
            if !qsag_asm::ct_eq_32(&got, commits[p].as_slice().try_into().unwrap()) {
                return Err(Check::Commitment.into());
            }
            self.transcript.bytes(bytes);
            all.push(values);
        }
        Ok(all)
    }

    fn open_sums(&mut self, label: &[u8], values: &[F]) -> Result<SecretVec<F>, PrepError> {
        let mut sums = SecretVec::from(vec![F::ZERO; values.len()]);
        for row in self.commit_then_open(label, values)? {
            for (sum, v) in sums.iter_mut().zip(&row) {
                *sum += *v;
            }
        }
        Ok(sums)
    }

    fn check_zero(&mut self, label: &[u8], sigmas: &[F], site: Check) -> Result<(), PrepError> {
        if self.open_sums(label, sigmas)?.iter().any(|v| *v != F::ZERO) {
            return Err(site.into());
        }
        Ok(())
    }

    fn establish_pairs(&mut self) -> Result<(), PrepError> {
        for owner in 0..self.n {
            for holder in (0..self.n).filter(|&h| h != owner) {
                if self.me != owner && self.me != holder {
                    continue;
                }
                let peer = if self.me == owner { holder } else { owner };
                let mut io = PairIo::new(self.net, peer, &mut self.chains[peer]);
                if self.me == owner {
                    let chan =
                        ot::establish_sender(&mut io, self.session, owner, holder, self.rng)?;
                    self.channels.send[peer] = Some(chan);
                    let pads = self.channels.send(&mut io, BASE_WORDS, self.rng)?;
                    self.pads[peer].send = pads
                        .iter()
                        .enumerate()
                        .map(|(i, (a, b))| {
                            [
                                Prg::new(&self.session, owner, holder, i, a),
                                Prg::new(&self.session, owner, holder, i, b),
                            ]
                        })
                        .collect();
                } else {
                    let chan =
                        ot::establish_receiver(&mut io, self.session, owner, holder, self.rng)?;
                    self.channels.recv[peer] = Some(chan);
                    let [a, b] = mac_words(*self.key);
                    let pads = self.channels.receive(&mut io, &[a, b, 0], self.rng)?;
                    self.pads[peer].receive = pads
                        .iter()
                        .enumerate()
                        .map(|(i, p)| Prg::new(&self.session, owner, holder, i, p))
                        .collect();
                }
            }
        }
        Ok(())
    }

    fn cope(
        &mut self,
        owner: usize,
        holder: usize,
        key: usize,
        values: &[F],
    ) -> Result<SecretVec<F>, PrepError> {
        let count = values.len();
        let sender = owner == self.me;
        let peer = if sender { holder } else { owner };
        let mut io = PairIo::new(self.net, peer, &mut self.chains[peer]);
        let zeros = || SecretVec::from(vec![F::ZERO; count]);
        let (mut result, mut pad, mut other) = (zeros(), zeros(), zeros());
        // One message for each bit keeps the working set proportional to the batch size.
        for bit in (0..64).rev() {
            let index = 64 * key + bit;
            if sender {
                let pair = &mut self.pads[peer].send[index];
                pair[0].elements(&mut pad);
                pair[1].elements(&mut other);
                for k in 0..count {
                    other[k] = pad[k] - other[k] + values[k];
                }
                io.send(&encode(&other))?;
            } else {
                self.pads[peer].receive[index].elements(&mut pad);
                let corrections = decode(&io.recv(8 * count)?, count)?;
                let select = 0u64.wrapping_sub((self.key[key].to_canonical_u64() >> bit) & 1);
                for k in 0..count {
                    pad[k] += F::from_u64_reduced(corrections[k].to_canonical_u64() & select);
                }
            }
            for (acc, v) in result.iter_mut().zip(&pad) {
                *acc = *acc + *acc + *v;
            }
        }
        Ok(result)
    }

    /// Keep this party's MAC contribution for each owner through the two masked
    /// input checks. Only then sum the owners into one local authenticated share.
    fn authenticate(&mut self, mut mine: SecretVec<F>) -> Result<SecretVec<Share>, PrepError> {
        let count = mine.len();
        for _ in 0..KEYS {
            mine.push(self.sample());
        }
        let mut owners = Vec::with_capacity(self.n);
        for owner in 0..self.n {
            let mut macs: SecretVec<Mac> = mine
                .iter()
                .map(|v| {
                    if self.me == owner {
                        mac_scale(*self.key, *v)
                    } else {
                        [F::ZERO; KEYS]
                    }
                })
                .collect();
            for holder in (0..self.n).filter(|&h| h != owner) {
                if self.me != owner && self.me != holder {
                    continue;
                }
                for key in 0..KEYS {
                    let part = self.cope(owner, holder, key, &mine)?;
                    for (mac, v) in macs.iter_mut().zip(&part) {
                        if self.me == owner {
                            mac[key] -= *v;
                        } else {
                            mac[key] = *v;
                        }
                    }
                }
            }
            owners.push(macs);
        }
        let mut coin = self.coin(b"authenticate")?;
        let mut sigma = SecretVec::with_capacity(self.n * KEYS * KEYS);
        for (owner, macs) in owners.iter().enumerate() {
            for instance in 0..KEYS {
                let mut value = mine[count + instance];
                let mut mac = macs[count + instance];
                for k in 0..count {
                    let r = coin.element();
                    value += r * mine[k];
                    mac = mac_add(mac, mac_scale(macs[k], r));
                }
                let opened = if owner == self.me {
                    for peer in (0..self.n).filter(|&p| p != owner) {
                        self.net.send(peer, &value.to_le_bytes())?;
                    }
                    value
                } else {
                    decode(&self.net.recv_bounded(owner, 8)?, 1)?[0]
                };
                self.transcript.element(opened);
                sigma.extend_from_slice(&mac_sub(mac, mac_scale(*self.key, opened)));
            }
        }
        self.check_zero(b"input check sigma", &sigma, Check::InputConsistency)?;
        let mut out = SecretVec::with_capacity(count);
        for k in 0..count {
            let mac = owners
                .iter()
                .fold([F::ZERO; KEYS], |acc, row| mac_add(acc, row[k]));
            out.push([mine[k], mac[0], mac[1]]);
        }
        Ok(out)
    }

    fn multiply(&mut self, count: usize) -> Result<SecretVec<F>, PrepError> {
        let mut out = SecretVec::with_capacity(count * TRIPLE_INPUTS);
        if count == 0 {
            return Ok(out);
        }
        let a: SecretVec<F> = (0..count * TAU).map(|_| self.sample()).collect();
        let b: SecretVec<F> = (0..count).map(|_| self.sample()).collect();
        let mut c: SecretVec<F> = a.iter().enumerate().map(|(i, v)| *v * b[i / TAU]).collect();
        let choices: SecretVec<u64> = a.iter().map(|v| v.to_canonical_u64()).collect();
        for sender in 0..self.n {
            for receiver in (0..self.n).filter(|&r| r != sender) {
                if sender != self.me && receiver != self.me {
                    continue;
                }
                let peer = if sender == self.me { receiver } else { sender };
                let mut io = PairIo::new(self.net, peer, &mut self.chains[peer]);
                // A smaller OT frame also bounds the much larger expanded pad arrays.
                let words = (MAX_FRAME_BUDGET / (128 * 8) - 4).min(256);
                for (frame, chunk) in choices.chunks(words).enumerate() {
                    let offset = frame * words;
                    if sender == self.me {
                        let pads = self.channels.send(&mut io, chunk.len(), self.rng)?;
                        let mut corrections = SecretVec::with_capacity(64 * chunk.len());
                        for (j, word) in pads.chunks_exact(64).enumerate() {
                            let mut sum = F::ZERO;
                            for (zero, one) in word.iter().rev() {
                                let z = pad_element(zero);
                                corrections.push(z - pad_element(one) + b[(offset + j) / TAU]);
                                sum = sum + sum + z;
                            }
                            c[offset + j] -= sum;
                        }
                        io.send(&encode(&corrections))?;
                    } else {
                        let pads = self.channels.receive(&mut io, chunk, self.rng)?;
                        let corrections =
                            decode(&io.recv(8 * 64 * chunk.len())?, 64 * chunk.len())?;
                        for (j, word) in pads.chunks_exact(64).enumerate() {
                            let mut sum = F::ZERO;
                            for (i, pad) in word.iter().rev().enumerate() {
                                let mask = 0u64.wrapping_sub((chunk[j] >> (63 - i)) & 1);
                                sum = sum
                                    + sum
                                    + pad_element(pad)
                                    + F::from_u64_reduced(
                                        corrections[j * 64 + i].to_canonical_u64() & mask,
                                    );
                            }
                            c[offset + j] += sum;
                        }
                    }
                }
            }
        }
        let mut coin = self.coin(b"combine")?;
        for (t, bt) in b.iter().enumerate() {
            for combo in 0..=SACRIFICES {
                let (mut av, mut cv) = (F::ZERO, F::ZERO);
                for k in t * TAU..(t + 1) * TAU {
                    let r = coin.element();
                    av += r * a[k];
                    cv += r * c[k];
                }
                out.push(av);
                if combo == 0 {
                    out.push(*bt);
                }
                out.push(cv);
            }
        }
        Ok(out)
    }

    fn key_consistency(&mut self, shares: &[Share]) -> Result<(), PrepError> {
        let mut values: SecretVec<F> = shares.iter().map(|v| v[0]).collect();
        let mut masks = Secret([F::ZERO; KEYS]);
        for (p, pair) in self.pads.iter_mut().enumerate() {
            if p == self.me {
                continue;
            }
            if p > self.me {
                pair.send[SHARED_BASE][0].elements(&mut *masks);
            } else {
                pair.receive[SHARED_BASE].elements(&mut *masks);
            }
            for (v, m) in values.iter_mut().zip(masks.iter()) {
                if p > self.me {
                    *v += *m;
                } else {
                    *v -= *m;
                }
            }
        }
        let opened = self.open_sums(b"key consistency", &values)?;
        let sigmas: SecretVec<F> = shares
            .iter()
            .zip(&opened)
            .flat_map(|(s, v)| mac_sub(mac_of(*s), mac_scale(*self.key, *v)))
            .collect();
        self.check_zero(b"key consistency sigma", &sigmas, Check::KeyConsistency)
    }

    /// Open all sacrificial differences in a batch, then check the queued opening
    /// MACs and the two zero equations under independent field challenges.
    fn sacrifice(&mut self, triples: &[Share]) -> Result<(), PrepError> {
        if triples.is_empty() {
            return Ok(());
        }
        let mut coin = self.coin(b"sacrifice")?;
        let mut rhos = SecretVec::new();
        let mut queue = SecretVec::new();
        for triple in triples.chunks_exact(TRIPLE_INPUTS) {
            for pair in 0..SACRIFICES {
                let s = coin.element();
                let hat = 3 + 2 * pair;
                let rho = share_sub(share_scale(triple[0], s), triple[hat]);
                rhos.push(rho[0]);
                queue.push((
                    mac_of(rho),
                    mac_sub(mac_scale(mac_of(triple[2]), s), mac_of(triple[hat + 1])),
                    mac_of(triple[1]),
                ));
            }
        }
        let opened = self.open_sums(b"sacrifice", &rhos)?;
        let mut coin = self.coin(b"field mac check")?;
        let mut sigma = Secret([F::ZERO; KEYS]);
        for key in 0..KEYS {
            for ((mac, left, b), rho) in queue.iter().zip(&opened) {
                sigma[key] += coin.element() * (mac[key] - self.key[key] * *rho);
                sigma[key] += coin.element() * (left[key] - b[key] * *rho);
            }
        }
        self.check_zero(b"field sigma", &*sigma, Check::TripleSacrifice)
    }

    fn batch(&mut self, t: usize, r: usize, store: &mut Preprocessing) -> Result<(), PrepError> {
        let mut inputs = self.multiply(t)?;
        for _ in 0..r + KEYS {
            inputs.push(self.sample());
        }
        let shares = self.authenticate(inputs)?;
        let at = t * TRIPLE_INPUTS;
        self.key_consistency(&shares[at + r..])?;
        self.sacrifice(&shares[..at])?;
        store.triples.extend(
            shares[..at]
                .chunks_exact(TRIPLE_INPUTS)
                .map(|s| [to_engine(s[0]), to_engine(s[1]), to_engine(s[2])]),
        );
        store
            .randoms
            .extend(shares[at..at + r].iter().copied().map(to_engine));
        Ok(())
    }
}

/// Produce exactly one custodian's authenticated field material over its private links.
pub fn run_party_preprocessing<T: Transport>(
    session: [u8; 32],
    demand: &PrepDemand,
    net: &mut T,
    rng: &mut PartyPrivateRng,
) -> Result<Preprocessing, PrepError> {
    let (me, n) = (net.me(), net.parties());
    if !(2..=64).contains(&n) || me >= n {
        return Err(PrepError::InvalidConfiguration);
    }
    let mut store = Preprocessing {
        key: [F::ZERO; KEYS],
        triples: Vec::new(),
        randoms: Vec::new(),
    };
    store
        .triples
        .try_reserve_exact(demand.triples)
        .and_then(|()| store.randoms.try_reserve_exact(demand.randoms))
        .map_err(|_| PrepError::InvalidConfiguration)?;
    let mut party = Party {
        net,
        rng,
        me,
        n,
        session,
        key: Secret([F::ZERO; KEYS]),
        channels: Channels::new(n),
        chains: vec![session; n],
        pads: (0..n)
            .map(|_| Pair {
                send: Vec::new(),
                receive: Vec::new(),
            })
            .collect(),
        transcript: Transcript::new(&session),
        coins: 0,
        commits: 0,
    };
    let config = cshake256_framed_32(
        b"QSAG.COLLAB.PREP.CONFIG/v1",
        &[
            &session,
            &[n as u8],
            &(demand.triples as u64).to_le_bytes(),
            &(demand.randoms as u64).to_le_bytes(),
        ],
    );
    party.agree(&config)?;
    party.transcript.bytes(&config);
    party.key = Secret([party.sample(), party.sample()]);
    store.key = *party.key;
    party.establish_pairs()?;
    while store.triples.len() != demand.triples || store.randoms.len() != demand.randoms {
        let t = (demand.triples - store.triples.len()).min(BATCH_TRIPLES);
        let r = (demand.randoms - store.randoms.len()).min((BATCH_TRIPLES - t) * TRIPLE_INPUTS);
        party.batch(t, r, &mut store)?;
    }
    party.coin(b"finish")?;
    Ok(store)
}
