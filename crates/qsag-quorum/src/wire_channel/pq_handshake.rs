//! Pairwise ephemeral X25519 and ML-KEM-768 with PSK authentication and bilateral
//! transcript confirmation. Only the lower-numbered endpoint stores a decapsulation key.
#![forbid(unsafe_code)]

mod mlkem;
mod x25519;

use super::{FrameSequencer, MacSealedWireChannel, TransportError, WireTransport};
use crate::hash::{h32, mac32};
use alloc::{vec, vec::Vec};
use qsag_core::sponge::keccak::Cshake256Xof;
use qsag_core::wipe::{SecretBuffer, SecretBytes, ct_eq_bytes};

use super::{ROUND_PQ_HS_CONFIRM, ROUND_PQ_HS_INIT, ROUND_PQ_HS_RESP};
const AUTH: &[u8] = b"QSAG.QUORUM.WIRE_PQ_AUTH/v1";
const TRANSCRIPT: &[u8] = b"QSAG.QUORUM.WIRE_PQ_TRANSCRIPT/v1";

struct Initiator {
    scalar: SecretBytes<32>,
    dk: mlkem::DecapsulationKey,
    init_hash: [u8; 32],
}

struct Context {
    deployment: [u8; 32],
    session: [u8; 32],
    lo: [u8; 2],
    hi: [u8; 2],
    encrypted: bool,
}

impl Context {
    fn header(&self, round: u32) -> [u8; 32] {
        h32(
            b"QSAG.QUORUM.WIRE_PQ_HEADER/v1",
            &[
                &self.deployment,
                &self.session,
                &self.lo,
                &self.hi,
                &[u8::from(self.encrypted)],
                &round.to_be_bytes(),
            ],
        )
    }
    fn coins(&self, seed: &[u8; 32], sender: usize) -> Result<Cshake256Xof, TransportError> {
        let mut x = Cshake256Xof::new(b"QSAG.QUORUM.WIRE_PQ_COINS/v1");
        x.absorb(seed);
        #[cfg(feature = "std")]
        {
            let mut entropy = SecretBuffer([0; 32]);
            qsag_asm::fill_os_random(&mut entropy[..])
                .map_err(|_| TransportError::AuthenticationFailed)?;
            x.absorb(&entropy[..]);
        }
        x.absorb(&self.header(ROUND_PQ_HS_INIT));
        x.absorb(&(sender as u16).to_be_bytes());
        Ok(x)
    }
    fn keys(
        &self,
        psk: &[u8; 32],
        dh: &[u8; 32],
        kem: &[u8; 32],
        transcript: &[u8; 32],
    ) -> SecretBuffer<[[u8; 32]; 4]> {
        let mut x = Cshake256Xof::new(b"QSAG.QUORUM.WIRE_PQ_HYBRID_KDF/v1");
        for part in [
            psk.as_slice(),
            dh,
            kem,
            &self.deployment,
            &self.session,
            &self.lo,
            &self.hi,
            transcript,
        ] {
            x.absorb(part);
        }
        SecretBuffer(core::array::from_fn(|_| *draw(&mut x)))
    }
}

fn draw(x: &mut Cshake256Xof) -> SecretBytes<32> {
    let mut out = SecretBuffer([0; 32]);
    x.squeeze(&mut out[..]);
    out
}

fn receive<T: WireTransport>(
    t: &mut T,
    peer: usize,
    ctx: &Context,
    round: u32,
    len: usize,
) -> Result<Vec<u8>, TransportError> {
    let bytes = t.recv_authenticated_envelope(peer, round)?;
    if bytes.len() != len || !ct_eq_bytes(&bytes[..32], &ctx.header(round)) {
        return Err(TransportError::AuthenticationFailed);
    }
    Ok(bytes)
}

pub(super) fn establish<T: WireTransport>(
    transport: T,
    deployment: [u8; 32],
    session: [u8; 32],
    psks: Vec<[u8; 32]>,
    seed: &[u8; 32],
    encrypted: bool,
) -> Result<MacSealedWireChannel<T>, TransportError> {
    let psks = SecretBuffer(psks);
    let me = transport.party();
    let n = transport.parties();
    if me >= n || n > 65536 || psks.len() != n {
        return Err(TransportError::Malformed);
    }
    let invalid = psks
        .iter()
        .enumerate()
        .filter(|(peer, _)| *peer != me)
        .fold(false, |invalid, (_, key)| {
            invalid | ct_eq_bytes(key, &[0; 32])
        });
    if invalid {
        return Err(TransportError::AuthenticationFailed);
    }
    // The partially populated channel owns the traffic keys on every error path.
    let mut channel = MacSealedWireChannel {
        deployment_id: deployment,
        transport,
        sequencer: FrameSequencer::new(session, me, n),
        keys: vec![[0; 32]; n],
        recv_keys: vec![[0; 32]; n],
        failed_links: vec![false; n],
        encrypted,
    };
    let context = |peer: usize| Context {
        deployment,
        session,
        lo: (me.min(peer) as u16).to_be_bytes(),
        hi: (me.max(peer) as u16).to_be_bytes(),
        encrypted,
    };
    let mut pending = Vec::with_capacity(n - me - 1);
    for hi in me + 1..n {
        let ctx = context(hi);
        let mut coins = ctx.coins(seed, me)?;
        let scalar = draw(&mut coins);
        let dk = mlkem::keygen(&draw(&mut coins), draw(&mut coins));
        let mut pkt = ctx.header(ROUND_PQ_HS_INIT).to_vec();
        pkt.extend_from_slice(&x25519::exchange(&scalar, &x25519::BASE)?[..]);
        pkt.extend_from_slice(&dk.ek);
        pkt.extend_from_slice(&mac32(&psks[hi], AUTH, &[&pkt]));
        channel.transport.send_frame(hi, ROUND_PQ_HS_INIT, &pkt)?;
        pending.push(alloc::boxed::Box::new(Initiator {
            scalar,
            dk,
            init_hash: h32(TRANSCRIPT, &[&pkt]),
        }));
    }
    let mut confirmations = Vec::with_capacity(me);
    for lo in 0..me {
        let ctx = context(lo);
        let pkt = receive(
            &mut channel.transport,
            lo,
            &ctx,
            ROUND_PQ_HS_INIT,
            96 + mlkem::EK_BYTES,
        )?;
        let (body, tag) = pkt.split_at(pkt.len() - 32);
        if !ct_eq_bytes(tag, &mac32(&psks[lo], AUTH, &[body])) {
            return Err(TransportError::AuthenticationFailed);
        }
        let mut resp = ctx.header(ROUND_PQ_HS_RESP).to_vec();
        let (transcript, keys) = {
            let mut coins = ctx.coins(seed, me)?;
            let scalar = draw(&mut coins);
            let dh = x25519::exchange(
                &scalar,
                body[32..64]
                    .try_into()
                    .map_err(|_| TransportError::AuthenticationFailed)?,
            )?;
            let (ct, kem) = mlkem::encapsulate(
                body[64..]
                    .try_into()
                    .map_err(|_| TransportError::AuthenticationFailed)?,
                &draw(&mut coins),
            )?;
            resp.extend_from_slice(&x25519::exchange(&scalar, &x25519::BASE)?[..]);
            resp.extend_from_slice(&ct);
            let transcript = h32(TRANSCRIPT, &[&h32(TRANSCRIPT, &[&pkt]), &resp]);
            (transcript, ctx.keys(&psks[lo], &dh, &kem, &transcript))
        };
        channel.keys[lo] = keys[1];
        channel.recv_keys[lo] = keys[0];
        resp.extend_from_slice(&mac32(&keys[2], AUTH, &[&transcript]));
        confirmations.push((transcript, SecretBuffer(keys[3])));
        channel.transport.send_frame(lo, ROUND_PQ_HS_RESP, &resp)?;
    }
    for (hi, init) in (me + 1..n).zip(pending) {
        let ctx = context(hi);
        let pkt = receive(
            &mut channel.transport,
            hi,
            &ctx,
            ROUND_PQ_HS_RESP,
            96 + mlkem::CT_BYTES,
        )?;
        let (body, tag) = pkt.split_at(pkt.len() - 32);
        let transcript = h32(TRANSCRIPT, &[&init.init_hash, body]);
        let keys = {
            let dh = x25519::exchange(
                &init.scalar,
                body[32..64]
                    .try_into()
                    .map_err(|_| TransportError::AuthenticationFailed)?,
            )?;
            let kem = init.dk.decapsulate(
                body[64..]
                    .try_into()
                    .map_err(|_| TransportError::AuthenticationFailed)?,
            )?;
            ctx.keys(&psks[hi], &dh, &kem, &transcript)
        };
        drop(init);
        if !ct_eq_bytes(tag, &mac32(&keys[2], AUTH, &[&transcript])) {
            return Err(TransportError::AuthenticationFailed);
        }
        channel.keys[hi] = keys[0];
        channel.recv_keys[hi] = keys[1];
        let mut confirm = ctx.header(ROUND_PQ_HS_CONFIRM).to_vec();
        confirm.extend_from_slice(&transcript);
        confirm.extend_from_slice(&mac32(
            &keys[3],
            b"QSAG.QUORUM.WIRE_PQ_CONFIRM_NONCE/v1",
            &[&transcript],
        ));
        confirm.extend_from_slice(&mac32(&keys[3], AUTH, &[&confirm]));
        channel
            .transport
            .send_frame(hi, ROUND_PQ_HS_CONFIRM, &confirm)?;
    }
    for (lo, (transcript, key)) in confirmations.iter_mut().enumerate() {
        let pkt = receive(
            &mut channel.transport,
            lo,
            &context(lo),
            ROUND_PQ_HS_CONFIRM,
            128,
        )?;
        if !(ct_eq_bytes(&pkt[32..64], transcript)
            & ct_eq_bytes(&pkt[96..], &mac32(key, AUTH, &[&pkt[..96]])))
        {
            return Err(TransportError::AuthenticationFailed);
        }
        qsag_asm::ct_memzero(&mut key[..]);
    }
    Ok(channel)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire_channel::{
        ConfidentialWireChannel, InMemoryEndpoint, InMemoryWireMesh, SEALED_FRAME_OVERHEAD,
    };
    use std::sync::{Arc, Mutex};

    #[cfg(feature = "std")]
    #[test]
    fn repeated_context_and_seed_draw_independent_ephemeral_coins() {
        let ctx = Context {
            deployment: [1; 32],
            session: [2; 32],
            lo: [0, 0],
            hi: [0, 1],
            encrypted: true,
        };
        let a = draw(&mut ctx.coins(&[3; 32], 0).unwrap());
        let b = draw(&mut ctx.coins(&[3; 32], 0).unwrap());
        assert_ne!(&a[..], &b[..]);
    }

    #[derive(Clone, Copy)]
    enum Change {
        None,
        Psk,
        Ciphertext,
        LowOrder,
        Confirm,
    }
    type Trace = Arc<Mutex<Vec<(u32, Vec<u8>)>>>;
    struct Recorder {
        inner: InMemoryEndpoint,
        trace: Trace,
        change: Change,
    }
    impl WireTransport for Recorder {
        fn party(&self) -> usize {
            self.inner.party()
        }
        fn parties(&self) -> usize {
            self.inner.parties()
        }
        fn send_frame(&mut self, p: usize, r: u32, bytes: &[u8]) -> Result<(), TransportError> {
            let mut raw = bytes.to_vec();
            match (r, self.change) {
                (ROUND_PQ_HS_RESP, Change::Ciphertext) => raw[64] ^= 1,
                (ROUND_PQ_HS_RESP, Change::LowOrder) => raw[32..64].fill(0),
                (ROUND_PQ_HS_CONFIRM, Change::Confirm) => *raw.last_mut().unwrap() ^= 1,
                _ => (),
            }
            assert!(raw.len() >= SEALED_FRAME_OVERHEAD);
            self.trace.lock().unwrap().push((r, raw.clone()));
            self.inner.send_frame(p, r, &raw)
        }
        fn recv_frame(&mut self, _: usize, _: u32) -> Result<Vec<u8>, TransportError> {
            panic!("handshake must receive an authenticated envelope")
        }
        fn recv_authenticated_envelope(
            &mut self,
            p: usize,
            r: u32,
        ) -> Result<Vec<u8>, TransportError> {
            self.inner.recv_authenticated_envelope(p, r)
        }
    }
    type TrafficKeys = ([u8; 32], [u8; 32]);
    fn run(change: Change, tape: u8) -> (Vec<Result<TrafficKeys, TransportError>>, Trace) {
        let (endpoints, _) = InMemoryWireMesh::connect(2, [3; 32]);
        let trace = Trace::default();
        let out = std::thread::scope(|s| {
            let mut tasks = vec![];
            for (p, inner) in endpoints.into_iter().enumerate() {
                let transport = Recorder {
                    inner,
                    trace: trace.clone(),
                    change,
                };
                tasks.push(s.spawn(move || {
                    let link = if matches!(change, Change::Psk) && p == 1 {
                        2
                    } else {
                        1
                    };
                    let mut c = ConfidentialWireChannel::establish_pq_hybrid(
                        transport,
                        [4; 32],
                        [3; 32],
                        vec![[link; 32]; 2],
                        [tape + p as u8; 32],
                    )?;
                    let keys = (c.inner.keys[1 - p], c.inner.recv_keys[1 - p]);
                    if p == 0 {
                        c.send_frame(1, 42, b"custody material")?;
                    } else {
                        assert_eq!(c.recv_frame(0, 42)?, b"custody material");
                    }
                    Ok(keys)
                }));
            }
            tasks.into_iter().map(|t| t.join().unwrap()).collect()
        });
        (out, trace)
    }

    #[test]
    fn tooth_recording_and_compromised_psks_do_not_recover_traffic() {
        let (ends, a) = run(Change::None, 10);
        let (fresh, b) = run(Change::None, 20);
        let send = ends[0].unwrap();
        assert_eq!(send.0, ends[1].unwrap().1);
        assert_eq!(send.1, ends[1].unwrap().0);
        assert_ne!(send.0, send.1);
        assert_ne!(send.0, fresh[0].unwrap().0);
        assert_ne!(send.1, fresh[0].unwrap().1);
        let a = a.lock().unwrap();
        let b = b.lock().unwrap();
        assert_eq!(a.len(), 4);
        assert_eq!(
            a.iter().map(|i| i.0).collect::<Vec<_>>(),
            [ROUND_PQ_HS_INIT, ROUND_PQ_HS_RESP, ROUND_PQ_HS_CONFIRM, 42]
        );
        assert_ne!(a[3].1, b[3].1);
        let (mut endpoints, _) = InMemoryWireMesh::connect(2, [3; 32]);
        let mut legacy = MacSealedWireChannel::new_encrypted(
            endpoints.pop().unwrap(),
            [4; 32],
            [3; 32],
            vec![[1; 32]; 2],
        )
        .unwrap();
        assert_eq!(
            legacy.open(0, 42, &a[3].1),
            Err(TransportError::AuthenticationFailed)
        );
    }

    #[test]
    fn tooth_invalid_credentials_and_modified_exchanges_fail_authentication() {
        for (change, verifier) in [
            (Change::Psk, 1),
            (Change::Ciphertext, 0),
            (Change::LowOrder, 0),
            (Change::Confirm, 1),
        ] {
            assert_eq!(
                run(change, 8).0[verifier],
                Err(TransportError::AuthenticationFailed)
            );
        }
    }
}
