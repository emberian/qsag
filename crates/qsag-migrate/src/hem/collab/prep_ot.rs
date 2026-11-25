//! Directed Ring-LWE base OT and checked OT extension on a single link.
use super::*;
use qsag_core::preprocessing::{
    BaseOtCrsCommitMsg, BaseOtCrsOpenMsg, BaseOtCrsReceiverRound0, BaseOtCrsSenderRound0,
    BaseOtCrsShareMsg, BaseOtExtReceiverRound2, BaseOtExtSenderRound1, BaseOtRound1Msg,
    BaseOtRound2Msg, BaseOtRound3Msg, BaseOtRound4Msg, KosOtChallengeMsg, KosOtUColsMsg,
    OtExtProofMsg, OtExtReceiverChannel, OtExtSenderChannel, OtPadPair,
};

pub(super) struct PairIo<'a, T> {
    net: &'a mut T,
    peer: usize,
    digest: &'a mut [u8; 32],
}

impl<'a, T: Transport> PairIo<'a, T> {
    pub(super) fn new(net: &'a mut T, peer: usize, digest: &'a mut [u8; 32]) -> Self {
        Self { net, peer, digest }
    }
    fn record(&mut self, sender: usize, bytes: &[u8]) {
        *self.digest = cshake256_framed_32(
            b"QSAG.COLLAB.PREP.LINK/v1",
            &[self.digest, &[sender as u8], bytes],
        );
    }
    pub(super) fn send(&mut self, bytes: &[u8]) -> Result<(), PrepError> {
        self.net.send(self.peer, bytes)?;
        self.record(self.net.me(), bytes);
        Ok(())
    }
    pub(super) fn recv(&mut self, limit: usize) -> Result<Secret<Vec<u8>>, PrepError> {
        let bytes = Secret(self.net.recv_bounded(self.peer, limit)?);
        self.record(self.peer, &bytes);
        Ok(bytes)
    }
}

pub(super) fn establish_sender<T: Transport>(
    io: &mut PairIo<T>,
    session: [u8; 32],
    sender: usize,
    receiver: usize,
    rng: &mut PartyPrivateRng,
) -> Result<OtExtSenderChannel, PrepError> {
    let com = BaseOtCrsCommitMsg::from_bytes(&io.recv(32)?).ok_or(Check::Ot)?;
    let (state, share) = BaseOtCrsSenderRound0::respond(session, sender, receiver, &com, rng);
    io.send(&share.to_bytes())?;
    let open = BaseOtCrsOpenMsg::from_bytes(&io.recv(32)?).ok_or(Check::Ot)?;
    let crs = state
        .verify_and_derive_crs_coin(&open)
        .map_err(|_| Check::Ot)?;
    let (state, msg) = BaseOtExtSenderRound1::start_with_crs(crs, session, sender, receiver, rng);
    io.send(&msg.to_bytes())?;
    let msg = BaseOtRound2Msg::from_bytes(&io.recv(MAX_FRAME_BUDGET)?).ok_or(Check::Ot)?;
    let (state, msg) = state
        .verify_fo_and_respond_coin(&msg, rng)
        .map_err(|_| Check::Ot)?;
    io.send(&msg.to_bytes())?;
    let msg = BaseOtRound4Msg::from_bytes(&io.recv(MAX_FRAME_BUDGET)?).ok_or(Check::Ot)?;
    state.finalize(&msg).map_err(|_| Check::Ot.into())
}

pub(super) fn establish_receiver<T: Transport>(
    io: &mut PairIo<T>,
    session: [u8; 32],
    sender: usize,
    receiver: usize,
    rng: &mut PartyPrivateRng,
) -> Result<OtExtReceiverChannel, PrepError> {
    let (state, com) = BaseOtCrsReceiverRound0::commit(session, sender, receiver, rng);
    io.send(&com.to_bytes())?;
    let share = BaseOtCrsShareMsg::from_bytes(&io.recv(32)?).ok_or(Check::Ot)?;
    let (crs, open) = state.open_and_derive_crs_coin(&share);
    io.send(&open.to_bytes())?;
    let msg = BaseOtRound1Msg::from_bytes(&io.recv(MAX_FRAME_BUDGET)?).ok_or(Check::Ot)?;
    let (state, msg) =
        BaseOtExtReceiverRound2::respond_with_crs(crs, session, sender, receiver, &msg, rng)
            .map_err(|_| Check::Ot)?;
    io.send(&msg.to_bytes())?;
    let msg = BaseOtRound3Msg::from_bytes(&io.recv(32)?).ok_or(Check::Ot)?;
    let (chan, msg) = state.finalize(&msg);
    io.send(&msg.to_bytes())?;
    Ok(chan)
}

pub(super) struct Channels {
    pub(super) send: Vec<Option<OtExtSenderChannel>>,
    pub(super) recv: Vec<Option<OtExtReceiverChannel>>,
}

impl Channels {
    pub(super) fn new(n: usize) -> Self {
        Self {
            send: (0..n).map(|_| None).collect(),
            recv: (0..n).map(|_| None).collect(),
        }
    }
    pub(super) fn send<T: Transport>(
        &mut self,
        io: &mut PairIo<T>,
        words: usize,
        rng: &mut PartyPrivateRng,
    ) -> Result<Secret<Vec<OtPadPair>>, PrepError> {
        let chan = self.send[io.peer].as_mut().ok_or(Check::Ot)?;
        let length = 4 + 128 * 8 * (words + 4);
        let raw = io.recv(length)?;
        if raw.len() != length {
            return Err(Check::Ot.into());
        }
        let u = KosOtUColsMsg::from_bytes(&raw).ok_or(Check::Ot)?;
        let (pending, chal) = chan
            .round2_sample_challenge(&u, rng)
            .map_err(|_| Check::Ot)?;
        io.send(&chal.to_bytes())?;
        let proof = OtExtProofMsg::from_bytes(&io.recv(MAX_FRAME_BUDGET)?).ok_or(Check::Ot)?;
        let pads = Secret(
            chan.round4_verify_and_finish(pending, &proof)
                .map_err(|_| Check::Ot)?,
        );
        if pads.len() != 64 * words {
            return Err(Check::Ot.into());
        }
        Ok(pads)
    }
    pub(super) fn receive<T: Transport>(
        &mut self,
        io: &mut PairIo<T>,
        choices: &[u64],
        rng: &mut PartyPrivateRng,
    ) -> Result<Secret<Vec<[u8; 48]>>, PrepError> {
        let chan = self.recv[io.peer].as_mut().ok_or(Check::Ot)?;
        let (pending, u) = chan.round1_send_u_cols(choices, rng);
        io.send(&u.to_bytes())?;
        let chal = KosOtChallengeMsg::from_bytes(&io.recv(32)?).ok_or(Check::Ot)?;
        let (proof, pads) = chan.round3_prove_and_finish(pending, &chal);
        let pads = Secret(pads);
        io.send(&proof.to_bytes())?;
        Ok(pads)
    }
}
