//! Replicated arithmetic for the five-server TOPRF. Each additive component i
//! is held by every server except i.
//!
//! Multiplication. For z = x*y the diagonal terms x_c*y_c are added locally to
//! component c by its four holders. Every ordered cross term x_i*y_j (i != j)
//! is known to the three servers outside {i, j}. It is placed in the output as
//! component i += r, component j += x_i*y_j - r, where the mask r is expanded
//! from the subset seed shared by all servers except i, under a domain unique to
//! the session, counter, layer, gate and pair. Server j and the three term
//! holders derive r; the term holders also compute the masked term. Server i
//! holds component j yet knows neither the term nor r, so the three holders send
//! it the masked term over private channels and it decodes by majority. With one
//! corrupt server two of the three senders are honest and agree, so the decoded
//! value is the honest one. Nothing else is transmitted: per gate each server
//! receives four masked field elements, each with threefold redundancy.
//!
//! Privacy against server p: the only values p receives are x_p*y_j - r_(p,j),
//! each masked by a fresh pseudorandom element of a seed p does not hold, and
//! each of the four output components p holds contains exactly one such mask.
//! Its view is therefore simulated by four uniform elements per gate.
//!
//! When a layer carries more than `DIGEST_THRESHOLD` gates, one designated
//! holder per pair sends a 32-byte digest of its vector instead of the vector.
//! The recipient accepts a received vector only if it equals the other vector
//! or matches that digest. Two of the three contributions are honest, so an
//! accepted vector is the honest one unless the hash collides.
use crate::voprf::{Error, SERVERS, Transport};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::ct_zeroize_u64s,
    goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub},
    keccak::{Shake256, cshake256_framed_32},
    poseidon2::{poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at},
};
/// Layers with at most this many gates send three plain vectors: a digest would
/// not be shorter than the vector it replaces.
pub(crate) const DIGEST_THRESHOLD: usize = 4;
pub(crate) type Wire = [u64; SERVERS];

pub(crate) fn hash(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    cshake256_framed_32(domain, parts)
}
pub(crate) fn fields(seed: &[u8; 32], domain: &[u8], context: &[u8], n: usize) -> Vec<u64> {
    let mut xof = Shake256::new();
    xof.absorb(&hash(domain, &[seed, context]));
    xof.finalize(0x1f);
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let mut b = [0; 8];
        xof.squeeze(&mut b);
        let v = u64::from_le_bytes(b);
        if v < GOLDILOCKS_PRIME {
            out.push(v);
        }
    }
    out
}
pub(crate) fn subset(i: usize, j: usize) -> usize {
    let (a, b) = if i <= j { (i, j) } else { (j, i) };
    a * SERVERS + b
}
pub(crate) fn put(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}
pub(crate) fn read(bytes: &[u8], cursor: &mut usize) -> Result<u64, Error> {
    let end = cursor.checked_add(8).ok_or(Error::Encoding)?;
    let b = bytes.get(*cursor..end).ok_or(Error::Encoding)?;
    *cursor = end;
    let v = u64::from_le_bytes(b.try_into().map_err(|_| Error::Encoding)?);
    if v >= GOLDILOCKS_PRIME {
        return Err(Error::Encoding);
    }
    Ok(v)
}
pub(crate) fn majority(values: &[(usize, u64)], needed: usize) -> Result<u64, Error> {
    values
        .iter()
        .find_map(|&(_, v)| {
            (values.iter().filter(|&&(_, w)| w == v).count() >= needed).then_some(v)
        })
        .ok_or(Error::InconsistentShares)
}
pub(crate) fn linear(st: &mut [Wire; 12], me: bool) {
    for component in 0..SERVERS {
        let mut column: [u64; 12] = core::array::from_fn(|lane| st[lane][component]);
        if me {
            poseidon2_apply_me(&mut column)
        } else {
            poseidon2_apply_mi(&mut column)
        }
        for (wire, value) in st.iter_mut().zip(column) {
            wire[component] = value;
        }
    }
}
pub(crate) fn public(st: &mut Wire, party: usize, v: u64) {
    if party != 0 {
        st[0] = gl_add(st[0], v);
    }
}

/// The three holders of the cross term (i, j), ascending.
pub(crate) fn holders(i: usize, j: usize) -> [usize; 3] {
    let mut out = [0; 3];
    let mut next = 0;
    for party in 0..SERVERS {
        if party != i && party != j {
            out[next] = party;
            next += 1;
        }
    }
    out
}
/// The holder that sends a digest for pair (i, j), if the layer is large enough.
pub(crate) fn digest_holder(i: usize, j: usize, gates: usize) -> Option<usize> {
    (gates > DIGEST_THRESHOLD).then(|| holders(i, j)[(i + j) % 3])
}
fn group_digest(context: &[u8; 32], layer: u64, i: usize, j: usize, values: &[u64]) -> [u8; 32] {
    let mut payload = Vec::with_capacity(values.len() * 8);
    for &v in values {
        put(&mut payload, v)
    }
    hash(
        b"QSAG.TOPRF.RESHARE.DIGEST.V2",
        &[context, &layer.to_le_bytes(), &[i as u8, j as u8], &payload],
    )
}
/// Bytes server `sender` owes recipient `i` for partner `j` in a layer of `gates`.
fn group_len(i: usize, j: usize, sender: usize, gates: usize) -> usize {
    if digest_holder(i, j, gates) == Some(sender) {
        32
    } else {
        8 * gates
    }
}
/// Decode what `recipient` receives for partner `j`. A malformed or mis-sized
/// message is an erasure, never a field zero.
pub(crate) fn decode_group(
    context: &[u8; 32],
    layer: u64,
    recipient: usize,
    j: usize,
    gates: usize,
    incoming: &[Vec<u8>; SERVERS],
) -> Result<Vec<u64>, Error> {
    let digest_sender = digest_holder(recipient, j, gates);
    let mut vectors: Vec<(usize, Vec<u64>)> = Vec::with_capacity(3);
    let mut digest: Option<&[u8]> = None;
    for sender in holders(recipient, j) {
        let message = &incoming[sender];
        let mut offset = 0;
        let mut expected = 0;
        for partner in 0..SERVERS {
            if partner != recipient && partner != sender {
                let len = group_len(recipient, partner, sender, gates);
                if partner < j {
                    offset += len;
                }
                expected += len;
            }
        }
        if message.len() != expected {
            continue;
        }
        if digest_sender == Some(sender) {
            digest = message.get(offset..offset + 32);
            continue;
        }
        let mut cursor = offset;
        let mut values = Vec::with_capacity(gates);
        while values.len() < gates {
            match read(message, &mut cursor) {
                Ok(v) => values.push(v),
                Err(_) => break,
            }
        }
        if values.len() == gates {
            vectors.push((sender, values));
        } else {
            ct_zeroize_u64s(&mut values);
        }
    }
    if digest_sender.is_none() {
        let mut out = Vec::with_capacity(gates);
        for gate in 0..gates {
            let candidates: Vec<(usize, u64)> =
                vectors.iter().map(|(sender, v)| (*sender, v[gate])).collect();
            out.push(majority(&candidates, 2)?);
        }
        for (_, v) in &mut vectors {
            ct_zeroize_u64s(v)
        }
        return Ok(out);
    }
    let agree = vectors.len() == 2 && vectors[0].1 == vectors[1].1;
    let chosen = if agree {
        Some(0)
    } else {
        digest.and_then(|d| {
            vectors
                .iter()
                .position(|(_, v)| group_digest(context, layer, recipient, j, v) == d)
        })
    };
    let mut result = Err(Error::InconsistentShares);
    for (index, (_, v)) in vectors.iter_mut().enumerate() {
        if chosen == Some(index) {
            result = Ok(core::mem::take(v));
        } else {
            ct_zeroize_u64s(v)
        }
    }
    result
}

pub(crate) struct Engine<'a, T> {
    pub party: usize,
    pub seeds: &'a [[u8; 32]; 25],
    pub context: [u8; 32],
    pub layer: u64,
    pub transport: &'a mut T,
}
impl<T: Transport> Engine<'_, T> {
    /// Mask vector for the ordered pair (i, j); requires `self.party != i`.
    fn masks(&self, i: usize, j: usize, gates: usize) -> Vec<u64> {
        let mut context = Vec::from(self.context);
        context.extend_from_slice(&self.layer.to_le_bytes());
        context.extend_from_slice(&[i as u8, j as u8]);
        fields(
            &self.seeds[subset(i, i)],
            b"QSAG.TOPRF.RESHARE.V2",
            &context,
            gates,
        )
    }
    fn multiply(&mut self, xs: &[Wire], ys: &[Wire]) -> Result<Vec<Wire>, Error> {
        if xs.len() != ys.len() {
            return Err(Error::Encoding);
        }
        let gates = xs.len();
        let me = self.party;
        let mut out = vec![[0; SERVERS]; gates];
        for ((z, x), y) in out.iter_mut().zip(xs).zip(ys) {
            for (c, slot) in z.iter_mut().enumerate() {
                if c != me {
                    *slot = gl_mul(x[c], y[c]);
                }
            }
        }
        let mut messages: [Vec<u8>; SERVERS] = core::array::from_fn(|_| Vec::new());
        for (i, message) in messages.iter_mut().enumerate() {
            if i == me {
                continue;
            }
            for j in 0..SERVERS {
                if j == i {
                    continue;
                }
                let mut mask = self.masks(i, j, gates);
                for (z, &r) in out.iter_mut().zip(&mask) {
                    z[i] = gl_add(z[i], r);
                }
                if j != me {
                    // Term holder: component j receives the masked term.
                    for (((z, x), y), r) in out.iter_mut().zip(xs).zip(ys).zip(mask.iter_mut()) {
                        *r = gl_sub(gl_mul(x[i], y[j]), *r);
                        z[j] = gl_add(z[j], *r);
                    }
                    if digest_holder(i, j, gates) == Some(me) {
                        message.extend_from_slice(&group_digest(
                            &self.context,
                            self.layer,
                            i,
                            j,
                            &mask,
                        ));
                    } else {
                        for &v in &mask {
                            put(message, v)
                        }
                    }
                }
                ct_zeroize_u64s(&mut mask);
            }
        }
        let phase = hash(
            b"QSAG.TOPRF.LAYER.V2",
            &[&self.context, &self.layer.to_le_bytes()],
        );
        let layer = self.layer;
        self.layer = self.layer.checked_add(1).ok_or(Error::Counter)?;
        let incoming = self.transport.exchange(phase, messages)?;
        for j in 0..SERVERS {
            if j == me {
                continue;
            }
            let mut masked = decode_group(&self.context, layer, me, j, gates, &incoming)?;
            for (z, &v) in out.iter_mut().zip(&masked) {
                z[j] = gl_add(z[j], v);
            }
            ct_zeroize_u64s(&mut masked);
        }
        Ok(out)
    }
    fn sbox(&mut self, x: &[Wire]) -> Result<Vec<Wire>, Error> {
        let x2 = self.multiply(x, x)?;
        let mut a = x2.clone();
        a.extend_from_slice(&x2);
        let mut b = x.to_vec();
        b.extend_from_slice(&x2);
        let middle = self.multiply(&a, &b)?;
        self.multiply(&middle[..x.len()], &middle[x.len()..])
    }
    pub fn permute(&mut self, states: &mut [[Wire; 12]]) -> Result<(), Error> {
        for st in states.iter_mut() {
            linear(st, true)
        }
        for (tag, rounds) in [(0, 4), (1, 22), (2, 4)] {
            for round in 0..rounds {
                let width = if tag == 1 { 1 } else { 12 };
                let mut inputs = Vec::new();
                for st in states.iter_mut() {
                    for (lane, wire) in st.iter_mut().enumerate().take(width) {
                        public(
                            wire,
                            self.party,
                            poseidon2_const_at(tag, round, lane as u64),
                        );
                        inputs.push(*wire);
                    }
                }
                let outputs = self.sbox(&inputs)?;
                for (st, chunk) in states.iter_mut().zip(outputs.chunks_exact(width)) {
                    st[..width].copy_from_slice(chunk);
                    linear(st, tag != 1);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn honest(recipient: usize, gates: usize, value: impl Fn(usize, usize) -> u64) -> [Vec<u8>; 5] {
        let context = [7; 32];
        core::array::from_fn(|sender| {
            let mut message = Vec::new();
            if sender == recipient {
                return message;
            }
            for j in 0..SERVERS {
                if j == recipient || j == sender {
                    continue;
                }
                let values: Vec<u64> = (0..gates).map(|gate| value(j, gate)).collect();
                if digest_holder(recipient, j, gates) == Some(sender) {
                    message.extend_from_slice(&group_digest(&context, 3, recipient, j, &values));
                } else {
                    values.iter().for_each(|&v| put(&mut message, v));
                }
            }
            message
        })
    }
    #[test]
    fn decoding_corrects_one_fault_and_rejects_two() {
        let context = [7; 32];
        let value = |j: usize, gate: usize| (j as u64) << 32 | gate as u64;
        for gates in [1, DIGEST_THRESHOLD, DIGEST_THRESHOLD + 1, 24] {
            for recipient in 0..SERVERS {
                let clean = honest(recipient, gates, value);
                let expect = |j: usize| (0..gates).map(|g| value(j, g)).collect::<Vec<_>>();
                for j in (0..SERVERS).filter(|&j| j != recipient) {
                    assert_eq!(
                        decode_group(&context, 3, recipient, j, gates, &clean).unwrap(),
                        expect(j)
                    );
                    // A digest is bound to its layer, pair and session.
                    if gates > DIGEST_THRESHOLD {
                        let mut one_vector = clean.clone();
                        let holders = holders(recipient, j);
                        let digest = digest_holder(recipient, j, gates).unwrap();
                        let dropped = holders.into_iter().find(|&h| h != digest).unwrap();
                        one_vector[dropped].clear();
                        assert!(decode_group(&context, 3, recipient, j, gates, &one_vector).is_ok());
                        assert!(decode_group(&context, 4, recipient, j, gates, &one_vector).is_err());
                        assert!(decode_group(&[8; 32], 3, recipient, j, gates, &one_vector).is_err());
                    }
                }
                for bad in (0..SERVERS).filter(|&s| s != recipient) {
                    // Every byte position of the faulty message, one at a time,
                    // then truncation, extension and omission.
                    let mut faults: Vec<Vec<u8>> = (0..clean[bad].len())
                        .map(|at| {
                            let mut m = clean[bad].clone();
                            m[at] ^= 0x80;
                            m
                        })
                        .collect();
                    faults.push(clean[bad][..clean[bad].len() - 1].to_vec());
                    faults.push([clean[bad].as_slice(), &[0]].concat());
                    faults.push(Vec::new());
                    for fault in faults {
                        let mut incoming = clean.clone();
                        incoming[bad] = fault;
                        for j in (0..SERVERS).filter(|&j| j != recipient) {
                            assert_eq!(
                                decode_group(&context, 3, recipient, j, gates, &incoming).unwrap(),
                                expect(j)
                            );
                        }
                    }
                    // A second, differently lying holder is outside the model:
                    // decoding must fail closed, not pick either lie.
                    for second in (0..SERVERS).filter(|&s| s != recipient && s != bad) {
                        let mut incoming = clean.clone();
                        incoming[bad][0] ^= 1;
                        incoming[second][0] ^= 2;
                        let j = (0..SERVERS)
                            .find(|&j| j != recipient && j != bad && j != second)
                            .unwrap();
                        let first_group = (0..SERVERS).find(|&p| p != recipient && p != bad);
                        let second_group = (0..SERVERS).find(|&p| p != recipient && p != second);
                        if first_group == Some(j) && second_group == Some(j) {
                            assert_eq!(
                                decode_group(&context, 3, recipient, j, gates, &incoming),
                                Err(Error::InconsistentShares)
                            );
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn masks_are_unique_per_pair_and_layer_and_roles_are_balanced() {
        struct Never;
        impl Transport for Never {
            fn exchange(&mut self, _: [u8; 32], _: [Vec<u8>; 5]) -> Result<[Vec<u8>; 5], Error> {
                Err(Error::Transport)
            }
            fn broadcast(&mut self, _: [u8; 32], _: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
                Err(Error::Transport)
            }
        }
        let seeds: [[u8; 32]; 25] = core::array::from_fn(|i| [i as u8 + 1; 32]);
        let mut seen = Vec::new();
        for layer in 0..3 {
            let engine = Engine { party: 4, seeds: &seeds, context: [9; 32], layer, transport: &mut Never };
            for i in 0..4 {
                for j in (0..SERVERS).filter(|&j| j != i) {
                    seen.push(engine.masks(i, j, 2));
                }
            }
        }
        for (a, x) in seen.iter().enumerate() {
            assert!(seen[..a].iter().all(|y| x[0] != y[0] && x[1] != y[1] && x[0] != y[1]));
        }
        let mut digests = [0usize; SERVERS];
        for i in 0..SERVERS {
            for j in (0..SERVERS).filter(|&j| j != i) {
                assert_eq!(digest_holder(i, j, DIGEST_THRESHOLD), None);
                let holder = digest_holder(i, j, DIGEST_THRESHOLD + 1).unwrap();
                assert!(holder != i && holder != j);
                digests[holder] += 1;
            }
        }
        assert_eq!(digests, [4; SERVERS]);
    }
}
