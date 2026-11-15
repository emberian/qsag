//! Attenuated bearer capabilities with 256-bit cSHAKE256 chained tags.
//!
//! Every caveat is conjunctive: adding one can only restrict authorization. The
//! verifier supplies trusted request facts and discharge keys; token contents
//! never select an authority key. A discharge must be explicitly bound to the
//! final parent tag, so it cannot be transplanted to another capability.
//! Tags are 256 bits; this is not a claim of 256-bit quantum forgery resistance.
extern crate alloc;
use alloc::vec::Vec;
use qsag_accel::{ct::ct_eq_bytes, keccak::cshake256_framed_32};

pub const CAV_BIND_TO_PARENT: u8 = 6;
const MAX_CAVEATS: usize = 64;
const MAGIC: &[u8; 8] = b"QSMAC001";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Caveat {
    ExpiresAt(u64),
    NotBefore(u64),
    Resource([u8; 32]),
    Actions(u64),
    MaxAmount(u128),
    BindToParent([u8; 32]),
    ThirdParty([u8; 32]),
}
impl Caveat {
    fn encoded(&self) -> ([u8; 34], usize) {
        let mut out = [0; 34];
        let (kind, len) = match self {
            Self::ExpiresAt(v) | Self::NotBefore(v) | Self::Actions(v) => {
                out[2..10].copy_from_slice(&v.to_be_bytes());
                (match self { Self::ExpiresAt(_) => 1, Self::NotBefore(_) => 2, _ => 4 }, 8)
            }
            Self::Resource(v) | Self::BindToParent(v) | Self::ThirdParty(v) => {
                out[2..34].copy_from_slice(v);
                (match self { Self::Resource(_) => 3, Self::BindToParent(_) => CAV_BIND_TO_PARENT, _ => 7 }, 32)
            }
            Self::MaxAmount(v) => { out[2..18].copy_from_slice(&v.to_be_bytes()); (5, 16) }
        };
        out[0] = kind;
        out[1] = len as u8;
        (out, len + 2)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityError { Malformed, TooManyCaveats, InvalidTag, Denied, MissingDischarge, UnboundDischarge }

/// Request facts derived by the service, never accepted from untrusted token claims.
pub struct CapabilityRequest {
    pub audience: [u8; 32],
    pub resource: [u8; 32],
    /// All requested action bits must be allowed by every Actions caveat.
    pub actions: u64,
    pub amount: u128,
    pub now: u64,
}

/// A discharge paired with a key selected by the verifier's trusted authority registry.
pub struct Discharge<'a> {
    pub token: &'a SpongeMacaroon,
    pub root_key: &'a [u8; 32],
}

/// Bearer secret: deliberately no Debug implementation exposing its chaining tag.
#[derive(Clone, PartialEq, Eq)]
pub struct SpongeMacaroon {
    discharge: bool,
    identifier: [u8; 32],
    audience: [u8; 32],
    caveats: Vec<Caveat>,
    tag: [u8; 32],
}
impl Drop for SpongeMacaroon {
    fn drop(&mut self) { qsag_accel::ct::ct_zeroize_bytes(&mut self.tag); }
}
impl SpongeMacaroon {
    pub fn issue(root_key: &[u8; 32], identifier: [u8; 32], audience: [u8; 32]) -> Self {
        Self::new(root_key, identifier, audience, false)
    }
    fn new(key: &[u8; 32], identifier: [u8; 32], audience: [u8; 32], discharge: bool) -> Self {
        let tag = Self::root_tag(key, &identifier, &audience, discharge);
        Self { discharge, identifier, audience, caveats: Vec::new(), tag }
    }
    fn root_tag(key: &[u8; 32], id: &[u8; 32], audience: &[u8; 32], discharge: bool) -> [u8; 32] {
        cshake256_framed_32(b"QSAG.MACAROON.ROOT.V1", &[key, &[u8::from(discharge)], id, audience])
    }
    fn chained(tag: &[u8; 32], caveat: &Caveat) -> [u8; 32] {
        let (bytes, len) = caveat.encoded();
        cshake256_framed_32(b"QSAG.MACAROON.CAVEAT.V1", &[tag, &bytes[..len]])
    }
    /// Attenuate without the issuer's key. No API removes or replaces caveats.
    pub fn attenuate(&mut self, caveat: Caveat) -> Result<(), CapabilityError> {
        if self.caveats.len() >= MAX_CAVEATS { return Err(CapabilityError::TooManyCaveats); }
        if (!self.discharge && matches!(caveat, Caveat::BindToParent(_)))
            || (self.discharge && matches!(caveat, Caveat::ThirdParty(_))) {
            return Err(CapabilityError::Denied);
        }
        self.tag = Self::chained(&self.tag, &caveat);
        self.caveats.push(caveat);
        Ok(())
    }
    /// Issue after the third party has authorized the obligation identified by `identifier`.
    pub fn issue_discharge(key: &[u8; 32], identifier: [u8; 32], parent: &Self) -> Self {
        let mut token = Self::new(key, identifier, parent.audience, true);
        let binding = Caveat::BindToParent(parent.tag);
        token.tag = Self::chained(&token.tag, &binding);
        token.caveats.push(binding);
        token
    }
    pub fn identifier(&self) -> &[u8; 32] { &self.identifier }
    pub fn caveats(&self) -> &[Caveat] { &self.caveats }

    fn authenticate(&self, key: &[u8; 32]) -> Result<(), CapabilityError> {
        let mut expected = Self::root_tag(key, &self.identifier, &self.audience, self.discharge);
        for caveat in &self.caveats { expected = Self::chained(&expected, caveat); }
        let ok = ct_eq_bytes(&expected, &self.tag);
        qsag_accel::ct::ct_zeroize_bytes(&mut expected);
        if ok { Ok(()) } else { Err(CapabilityError::InvalidTag) }
    }
    pub fn verify(&self, key: &[u8; 32], request: &CapabilityRequest, discharges: &[Discharge<'_>])
        -> Result<(), CapabilityError>
    {
        if self.discharge { return Err(CapabilityError::Denied); }
        self.authenticate(key)?;
        self.check(request, discharges, None)
    }
    fn check(&self, r: &CapabilityRequest, discharges: &[Discharge<'_>], parent: Option<&[u8; 32]>)
        -> Result<(), CapabilityError>
    {
        if !ct_eq_bytes(&self.audience, &r.audience) { return Err(CapabilityError::Denied); }
        let mut bound = false;
        for caveat in &self.caveats {
            let allowed = match caveat {
                Caveat::ExpiresAt(t) => r.now < *t,
                Caveat::NotBefore(t) => r.now >= *t,
                Caveat::Resource(v) => ct_eq_bytes(v, &r.resource),
                Caveat::Actions(mask) => r.actions & !mask == 0,
                Caveat::MaxAmount(max) => r.amount <= *max,
                Caveat::BindToParent(tag) => {
                    let matches = parent.is_some_and(|p| ct_eq_bytes(p, tag));
                    bound |= matches;
                    matches
                }
                Caveat::ThirdParty(id) => {
                    if parent.is_some() { return Err(CapabilityError::Denied); }
                    let mut matching = discharges.iter().filter(|d| ct_eq_bytes(&d.token.identifier, id));
                    let d = matching.next().ok_or(CapabilityError::MissingDischarge)?;
                    if matching.next().is_some() || !d.token.discharge { return Err(CapabilityError::Denied); }
                    d.token.authenticate(d.root_key)?;
                    d.token.check(r, &[], Some(&self.tag))?;
                    true
                }
            };
            if !allowed { return Err(CapabilityError::Denied); }
        }
        if self.discharge && !bound { return Err(CapabilityError::UnboundDischarge); }
        Ok(())
    }
    /// Canonical bounded wire format; common two-to-six caveat tokens occupy 127–311 bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(107 + self.caveats.len() * 34);
        out.extend_from_slice(MAGIC);
        out.push(u8::from(self.discharge));
        out.extend_from_slice(&(self.caveats.len() as u16).to_be_bytes());
        out.extend_from_slice(&self.identifier);
        out.extend_from_slice(&self.audience);
        for caveat in &self.caveats { let (b, n) = caveat.encoded(); out.extend_from_slice(&b[..n]); }
        out.extend_from_slice(&self.tag);
        out
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CapabilityError> {
        let bad = CapabilityError::Malformed;
        if bytes.len() < 107 || bytes.len() > 107 + MAX_CAVEATS * 34 || &bytes[..8] != MAGIC || bytes[8] > 1 {
            return Err(bad);
        }
        let count = u16::from_be_bytes([bytes[9], bytes[10]]) as usize;
        if count > MAX_CAVEATS { return Err(CapabilityError::TooManyCaveats); }
        let identifier = bytes[11..43].try_into().map_err(|_| bad)?;
        let audience = bytes[43..75].try_into().map_err(|_| bad)?;
        let end = bytes.len() - 32;
        let tag = bytes[end..].try_into().map_err(|_| bad)?;
        let mut pos = 75;
        let mut caveats = Vec::with_capacity(count);
        for _ in 0..count {
            let header = bytes.get(pos..pos + 2).filter(|_| pos + 2 <= end).ok_or(bad)?;
            let len = usize::from(header[1]);
            pos += 2;
            let value = bytes.get(pos..pos + len).filter(|_| pos + len <= end).ok_or(bad)?;
            let caveat = match (header[0], len) {
                (1, 8) => Caveat::ExpiresAt(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (2, 8) => Caveat::NotBefore(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (3, 32) => Caveat::Resource(value.try_into().map_err(|_| bad)?),
                (4, 8) => Caveat::Actions(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (5, 16) => Caveat::MaxAmount(u128::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (CAV_BIND_TO_PARENT, 32) if bytes[8] == 1 => Caveat::BindToParent(value.try_into().map_err(|_| bad)?),
                (7, 32) if bytes[8] == 0 => Caveat::ThirdParty(value.try_into().map_err(|_| bad)?),
                _ => return Err(bad),
            };
            caveats.push(caveat);
            pos += len;
        }
        if pos != end { return Err(bad); }
        Ok(Self { discharge: bytes[8] == 1, identifier, audience, caveats, tag })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn request() -> CapabilityRequest {
        CapabilityRequest { audience: [2; 32], resource: [3; 32], actions: 1, amount: 5, now: 10 }
    }
    #[test]
    fn verification_latency_sample() {
        let mut m = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        for c in [Caveat::Resource([3; 32]), Caveat::Actions(1), Caveat::ExpiresAt(20)] {
            m.attenuate(c).unwrap();
        }
        let r = request();
        let start = std::time::Instant::now();
        for _ in 0..20_000 { core::hint::black_box(m.verify(&[1; 32], &r, &[])).unwrap(); }
        std::eprintln!("SpongeMacaroon: {} bytes; {} ns/verify (three caveats)",
            m.to_bytes().len(), start.elapsed().as_nanos() / 20_000);
    }
    #[test]
    fn attenuation_is_conjunctive_and_wire_is_canonical() {
        let mut m = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        for caveat in [Caveat::ExpiresAt(20), Caveat::Resource([3; 32]), Caveat::Actions(3), Caveat::MaxAmount(10)] {
            m.attenuate(caveat).unwrap();
        }
        let bytes = m.to_bytes();
        assert!((160..=320).contains(&bytes.len()));
        let decoded = SpongeMacaroon::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.to_bytes(), bytes);
        assert_eq!(decoded.verify(&[1; 32], &request(), &[]), Ok(()));
        for pos in 0..bytes.len() {
            let mut tampered = bytes.clone(); tampered[pos] ^= 1;
            assert!(SpongeMacaroon::from_bytes(&tampered).map_or(true, |t| t.verify(&[1; 32], &request(), &[]).is_err()));
        }
        m.attenuate(Caveat::MaxAmount(4)).unwrap();
        m.attenuate(Caveat::MaxAmount(100)).unwrap(); // later permissive caveat cannot undo the earlier one
        assert_eq!(m.verify(&[1; 32], &request(), &[]), Err(CapabilityError::Denied));
        for len in 0..bytes.len() { assert!(SpongeMacaroon::from_bytes(&bytes[..len]).is_err()); }
        let mut extra = bytes; extra.push(0); assert!(SpongeMacaroon::from_bytes(&extra).is_err());
    }
    #[test]
    fn discharge_is_required_and_bound_to_exact_parent() {
        let mut parent = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        parent.attenuate(Caveat::ThirdParty([5; 32])).unwrap();
        assert_eq!(parent.verify(&[1; 32], &request(), &[]), Err(CapabilityError::MissingDischarge));
        let discharge = SpongeMacaroon::issue_discharge(&[6; 32], [5; 32], &parent);
        let d = [Discharge { token: &discharge, root_key: &[6; 32] }];
        assert_eq!(parent.verify(&[1; 32], &request(), &d), Ok(()));
        parent.attenuate(Caveat::ExpiresAt(30)).unwrap();
        assert_eq!(parent.verify(&[1; 32], &request(), &d), Err(CapabilityError::Denied));
        let unbound = SpongeMacaroon::new(&[6; 32], [5; 32], [2; 32], true);
        assert_eq!(parent.verify(&[1; 32], &request(), &[Discharge { token: &unbound, root_key: &[6; 32] }]), Err(CapabilityError::UnboundDischarge));
        assert_eq!(discharge.verify(&[6; 32], &request(), &[]), Err(CapabilityError::Denied));
    }
    #[test]
    fn repeated_constraints_cannot_expand_authority() {
        let mut m = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        m.attenuate(Caveat::Actions(0)).unwrap();
        m.attenuate(Caveat::Actions(u64::MAX)).unwrap();
        assert!(m.verify(&[1; 32], &request(), &[]).is_err());
        let mut m = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        m.attenuate(Caveat::ExpiresAt(10)).unwrap();
        m.attenuate(Caveat::ExpiresAt(u64::MAX)).unwrap();
        assert!(m.verify(&[1; 32], &request(), &[]).is_err());
    }
}
