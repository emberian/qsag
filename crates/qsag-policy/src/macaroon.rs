//! Attenuated bearer capabilities with 256-bit cSHAKE256 chained tags.
//!
//! Every caveat is conjunctive: adding one can only restrict authorization. The
//! verifier supplies trusted request facts and discharge keys; token contents
//! never select an authority key. A third party issues a discharge without ever
//! seeing the parent capability; the holder then binds it to a one-way commitment
//! of the parent's final tag, so it cannot be transplanted to another capability
//! and neither the third party nor the discharge bytes reveal the parent's tag.
//! These are reusable bearer grants, not request-bound proofs of possession.
//! Verification checks predicates only; it does not consume an intent or a token.
//! PolicyEngine passes the full intent through the signing barrier, whose guards
//! enforce nonce/session replay rules and whose release tokens bind its canonical
//! digest. Standalone services must enforce their own transaction replay policy.
//! Tags are 256 bits; this is not a claim of 256-bit quantum forgery resistance.
extern crate alloc;
use alloc::vec::Vec;
use qsag_accel::{
    ct::ct_eq_bytes,
    keccak::{Shake256, cshake256_framed_32, finalize_cshake256, init_cshake256},
};
use qsag_asm::wipe::{SecretBuffer, SecretBytes};

const ROOT_DOMAIN: &[u8] = b"QSAG.MACAROON.ROOT.V1";
const CAVEAT_DOMAIN: &[u8] = b"QSAG.MACAROON.CAVEAT.V1";
const BIND_DOMAIN: &[u8] = b"QSAG.MACAROON.BIND.V1";

/// What a bound discharge carries in place of the parent's bearer tag.
fn parent_binding(parent_tag: &[u8; 32]) -> [u8; 32] {
    cshake256_framed_32(BIND_DOMAIN, &[parent_tag])
}

/// Only the public domain prefix is cached. Keys and bearer tags never enter shared state.
fn prefix(root: bool) -> Shake256 {
    #[cfg(any(test, feature = "std"))]
    {
        static ROOT: std::sync::OnceLock<Shake256> = std::sync::OnceLock::new();
        static CAVEAT: std::sync::OnceLock<Shake256> = std::sync::OnceLock::new();
        let (cell, domain) = if root {
            (&ROOT, ROOT_DOMAIN)
        } else {
            (&CAVEAT, CAVEAT_DOMAIN)
        };
        cell.get_or_init(|| init_cshake256(b"", domain)).clone()
    }
    #[cfg(not(any(test, feature = "std")))]
    {
        init_cshake256(b"", if root { ROOT_DOMAIN } else { CAVEAT_DOMAIN })
    }
}
fn mac_hash(root: bool, fields: &[&[u8]]) -> [u8; 32] {
    let mut sponge = prefix(root);
    sponge.absorb(&(fields.len() as u64).to_le_bytes());
    for field in fields {
        sponge.absorb(&(field.len() as u64).to_le_bytes());
        sponge.absorb(field);
    }
    finalize_cshake256(&mut sponge, true);
    let mut out = [0; 32];
    sponge.squeeze(&mut out);
    out
}

pub const CAV_BIND_TO_PARENT: u8 = 6;
pub(crate) const MAX_CAVEATS: usize = 64;
const MAGIC: &[u8; 8] = b"QSMAC001";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Caveat {
    ExpiresAt(u64),
    NotBefore(u64),
    Resource([u8; 32]),
    Actions(u64),
    MaxAmount(u128),
    /// One-way commitment to the final tag of the capability this discharge serves.
    BindToParent([u8; 32]),
    ThirdParty([u8; 32]),
}
impl Caveat {
    pub(crate) fn encoded(&self) -> ([u8; 34], usize) {
        let mut out = [0; 34];
        let (kind, len) = match self {
            Self::ExpiresAt(v) | Self::NotBefore(v) | Self::Actions(v) => {
                out[2..10].copy_from_slice(&v.to_be_bytes());
                (
                    match self {
                        Self::ExpiresAt(_) => 1,
                        Self::NotBefore(_) => 2,
                        _ => 4,
                    },
                    8,
                )
            }
            Self::Resource(v) | Self::BindToParent(v) | Self::ThirdParty(v) => {
                out[2..34].copy_from_slice(v);
                (
                    match self {
                        Self::Resource(_) => 3,
                        Self::BindToParent(_) => CAV_BIND_TO_PARENT,
                        _ => 7,
                    },
                    32,
                )
            }
            Self::MaxAmount(v) => {
                out[2..18].copy_from_slice(&v.to_be_bytes());
                (5, 16)
            }
        };
        out[0] = kind;
        out[1] = len as u8;
        (out, len + 2)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityError {
    Malformed,
    /// This seal has already authorized a request.
    Replay,
    /// Consumption could not be durably recorded (including capacity exhaustion).
    ConsumptionFailed,
    TooManyCaveats,
    InvalidTag,
    Denied,
    MissingDischarge,
    UnboundDischarge,
    /// A supplied discharge answers no third-party caveat of the capability.
    UnusedDischarge,
}

/// Request facts derived by the service, never accepted from untrusted token claims.
pub struct CapabilityRequest {
    /// Complete application intent digest, derived by the verifier. For policy
    /// requests this is `TransactionIntent::canonical_digest()`. Macaroon bearer
    /// predicates do not bind this value; Biscuit request-bound seals do.
    pub intent_digest: [u8; 32],
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

/// Server-side verifier for one issued session. Caches the authenticated root tag, not
/// an authorization decision: every caveat and discharge is checked on every request.
/// Treat this handle as a secret capable of minting unrestricted tokens for that session.
pub struct MacaroonVerifier {
    identifier: [u8; 32],
    audience: [u8; 32],
    root_tag: SecretBytes<32>,
}
impl MacaroonVerifier {
    pub fn new(key: &[u8; 32], identifier: [u8; 32], audience: [u8; 32]) -> Self {
        Self {
            identifier,
            audience,
            root_tag: SpongeMacaroon::root_tag(key, &identifier, &audience, false),
        }
    }
    pub fn verify(
        &self,
        token: &SpongeMacaroon,
        request: &CapabilityRequest,
        discharges: &[Discharge<'_>],
    ) -> Result<(), CapabilityError> {
        if token.discharge
            || !ct_eq_bytes(&self.identifier, &token.identifier)
            || !ct_eq_bytes(&self.audience, &token.audience)
        {
            return Err(CapabilityError::Denied);
        }
        token.authenticate_from(&self.root_tag)?;
        token.check_primary(request, discharges)
    }
}

/// Bearer secret: deliberately no Debug implementation exposing its chaining tag.
#[derive(Clone)]
pub struct SpongeMacaroon {
    discharge: bool,
    identifier: [u8; 32],
    audience: [u8; 32],
    caveats: Vec<Caveat>,
    tag: [u8; 32],
}
impl Drop for SpongeMacaroon {
    fn drop(&mut self) {
        qsag_asm::wipe::wipe(&mut self.tag);
    }
}
impl SpongeMacaroon {
    pub fn issue(root_key: &[u8; 32], identifier: [u8; 32], audience: [u8; 32]) -> Self {
        Self::new(root_key, identifier, audience, false)
    }
    fn new(key: &[u8; 32], identifier: [u8; 32], audience: [u8; 32], discharge: bool) -> Self {
        let tag = *Self::root_tag(key, &identifier, &audience, discharge);
        Self {
            discharge,
            identifier,
            audience,
            caveats: Vec::new(),
            tag,
        }
    }
    fn root_tag(
        key: &[u8; 32],
        id: &[u8; 32],
        audience: &[u8; 32],
        discharge: bool,
    ) -> SecretBytes<32> {
        let mut identity = [0u8; 33];
        identity[0] = u8::from(discharge);
        identity[1..].copy_from_slice(id);
        SecretBuffer(mac_hash(true, &[key, &identity, audience]))
    }
    fn chained(tag: &[u8; 32], caveat: &Caveat) -> [u8; 32] {
        let (bytes, len) = caveat.encoded();
        mac_hash(false, &[tag, &bytes[..len]])
    }
    /// Attenuate without the issuer's key. No API removes or replaces caveats.
    pub fn attenuate(&mut self, caveat: Caveat) -> Result<(), CapabilityError> {
        if self.caveats.len() >= MAX_CAVEATS {
            return Err(CapabilityError::TooManyCaveats);
        }
        if (!self.discharge && matches!(caveat, Caveat::BindToParent(_)))
            || (self.discharge && matches!(caveat, Caveat::ThirdParty(_)))
        {
            return Err(CapabilityError::Denied);
        }
        self.tag = Self::chained(&self.tag, &caveat);
        self.caveats.push(caveat);
        Ok(())
    }
    /// Third-party side: issue after authorizing the obligation identified by `identifier`.
    /// The result is unbound and must reach only the holder, who binds it with
    /// [`Self::bind_discharge`] before presenting it. The third party never needs the parent.
    pub fn issue_discharge(key: &[u8; 32], identifier: [u8; 32], audience: [u8; 32]) -> Self {
        Self::new(key, identifier, audience, true)
    }
    /// Holder side: bind `discharge` to this capability as it stands now. Attenuating this
    /// capability afterwards invalidates the binding.
    pub fn bind_discharge(&self, discharge: &mut Self) -> Result<(), CapabilityError> {
        if self.discharge
            || !discharge.discharge
            || !ct_eq_bytes(&self.audience, &discharge.audience)
        {
            return Err(CapabilityError::Denied);
        }
        discharge.attenuate(Caveat::BindToParent(parent_binding(&self.tag)))
    }
    pub fn identifier(&self) -> &[u8; 32] {
        &self.identifier
    }
    pub const fn audience(&self) -> &[u8; 32] {
        &self.audience
    }
    pub const fn is_discharge(&self) -> bool {
        self.discharge
    }
    pub fn caveats(&self) -> &[Caveat] {
        &self.caveats
    }

    fn authenticate(&self, key: &[u8; 32]) -> Result<(), CapabilityError> {
        self.authenticate_from(&Self::root_tag(
            key,
            &self.identifier,
            &self.audience,
            self.discharge,
        ))
    }
    fn authenticate_from(&self, root_tag: &[u8; 32]) -> Result<(), CapabilityError> {
        let mut expected = SecretBuffer(*root_tag);
        for caveat in &self.caveats {
            *expected = Self::chained(&expected, caveat);
        }
        if ct_eq_bytes(&*expected, &self.tag) {
            Ok(())
        } else {
            Err(CapabilityError::InvalidTag)
        }
    }
    pub fn verify(
        &self,
        key: &[u8; 32],
        request: &CapabilityRequest,
        discharges: &[Discharge<'_>],
    ) -> Result<(), CapabilityError> {
        if self.discharge {
            return Err(CapabilityError::Denied);
        }
        self.authenticate(key)?;
        self.check_primary(request, discharges)
    }
    fn check_primary(
        &self,
        request: &CapabilityRequest,
        discharges: &[Discharge<'_>],
    ) -> Result<(), CapabilityError> {
        // Every discharge must answer a third-party caveat, so more than that many cannot.
        if discharges.len() > self.caveats.len() {
            return Err(CapabilityError::UnusedDischarge);
        }
        self.check(request, discharges, None)?;
        let unused = discharges.iter().any(|d| {
            !self.caveats.iter().any(
                |c| matches!(c, Caveat::ThirdParty(id) if ct_eq_bytes(id, &d.token.identifier)),
            )
        });
        if unused {
            return Err(CapabilityError::UnusedDischarge);
        }
        Ok(())
    }
    /// `parent` is the binding commitment of the capability a discharge is presented with.
    fn check(
        &self,
        r: &CapabilityRequest,
        discharges: &[Discharge<'_>],
        parent: Option<&[u8; 32]>,
    ) -> Result<(), CapabilityError> {
        if !ct_eq_bytes(&self.audience, &r.audience) {
            return Err(CapabilityError::Denied);
        }
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
                    if parent.is_some() {
                        return Err(CapabilityError::Denied);
                    }
                    let mut matching = discharges
                        .iter()
                        .filter(|d| ct_eq_bytes(&d.token.identifier, id));
                    let d = matching.next().ok_or(CapabilityError::MissingDischarge)?;
                    if matching.next().is_some() || !d.token.discharge {
                        return Err(CapabilityError::Denied);
                    }
                    d.token.authenticate(d.root_key)?;
                    d.token.check(r, &[], Some(&parent_binding(&self.tag)))?;
                    true
                }
            };
            if !allowed {
                return Err(CapabilityError::Denied);
            }
        }
        if self.discharge && !bound {
            return Err(CapabilityError::UnboundDischarge);
        }
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
        for caveat in &self.caveats {
            let (b, n) = caveat.encoded();
            out.extend_from_slice(&b[..n]);
        }
        out.extend_from_slice(&self.tag);
        out
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CapabilityError> {
        let bad = CapabilityError::Malformed;
        if bytes.len() < 107
            || bytes.len() > 107 + MAX_CAVEATS * 34
            || &bytes[..8] != MAGIC
            || bytes[8] > 1
        {
            return Err(bad);
        }
        let count = u16::from_be_bytes([bytes[9], bytes[10]]) as usize;
        if count > MAX_CAVEATS {
            return Err(CapabilityError::TooManyCaveats);
        }
        let identifier = bytes[11..43].try_into().map_err(|_| bad)?;
        let audience = bytes[43..75].try_into().map_err(|_| bad)?;
        let end = bytes.len() - 32;
        let mut pos = 75;
        let mut caveats = Vec::with_capacity(count);
        for _ in 0..count {
            let header = bytes
                .get(pos..pos + 2)
                .filter(|_| pos + 2 <= end)
                .ok_or(bad)?;
            let len = usize::from(header[1]);
            pos += 2;
            let value = bytes
                .get(pos..pos + len)
                .filter(|_| pos + len <= end)
                .ok_or(bad)?;
            let caveat = match (header[0], len) {
                (1, 8) => Caveat::ExpiresAt(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (2, 8) => Caveat::NotBefore(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (3, 32) => Caveat::Resource(value.try_into().map_err(|_| bad)?),
                (4, 8) => Caveat::Actions(u64::from_be_bytes(value.try_into().map_err(|_| bad)?)),
                (5, 16) => {
                    Caveat::MaxAmount(u128::from_be_bytes(value.try_into().map_err(|_| bad)?))
                }
                (CAV_BIND_TO_PARENT, 32) if bytes[8] == 1 => {
                    Caveat::BindToParent(value.try_into().map_err(|_| bad)?)
                }
                (7, 32) if bytes[8] == 0 => Caveat::ThirdParty(value.try_into().map_err(|_| bad)?),
                _ => return Err(bad),
            };
            caveats.push(caveat);
            pos += len;
        }
        if pos != end {
            return Err(bad);
        }
        Ok(Self {
            discharge: bytes[8] == 1,
            identifier,
            audience,
            caveats,
            tag: bytes[end..].try_into().map_err(|_| bad)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn request() -> CapabilityRequest {
        CapabilityRequest {
            intent_digest: [0x55; 32],
            audience: [2; 32],
            resource: [3; 32],
            actions: 1,
            amount: 5,
            now: 10,
        }
    }
    #[test]
    fn cached_public_prefix_matches_cshake_framing() {
        for (root, domain) in [(true, ROOT_DOMAIN), (false, CAVEAT_DOMAIN)] {
            for length in [0, 8, 32, 128, 136, 250] {
                let value = alloc::vec![0xa5; length];
                let fields: &[&[u8]] = &[&[1; 32], &value];
                assert_eq!(
                    mac_hash(root, fields),
                    qsag_accel::keccak::cshake256_framed_32(domain, fields)
                );
            }
        }
    }
    #[test]
    fn verification_latency_sample() {
        let mut m = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        for c in [
            Caveat::Resource([3; 32]),
            Caveat::Actions(1),
            Caveat::ExpiresAt(20),
        ] {
            m.attenuate(c).unwrap();
        }
        let r = request();
        let verifier = MacaroonVerifier::new(&[1; 32], [4; 32], [2; 32]);
        let start = std::time::Instant::now();
        for _ in 0..20_000 {
            verifier
                .verify(core::hint::black_box(&m), core::hint::black_box(&r), &[])
                .unwrap();
        }
        std::eprintln!(
            "SpongeMacaroon: {} bytes; {} ns/verify (prepared session, three caveats)",
            m.to_bytes().len(),
            start.elapsed().as_nanos() / 20_000
        );
        assert!(
            MacaroonVerifier::new(&[1; 32], [9; 32], [2; 32])
                .verify(&m, &r, &[])
                .is_err()
        );
        assert!(
            MacaroonVerifier::new(&[9; 32], [4; 32], [2; 32])
                .verify(&m, &r, &[])
                .is_err()
        );
    }
    #[test]
    fn attenuation_is_conjunctive_and_wire_is_canonical() {
        let mut m = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        for caveat in [
            Caveat::ExpiresAt(20),
            Caveat::Resource([3; 32]),
            Caveat::Actions(3),
            Caveat::MaxAmount(10),
        ] {
            m.attenuate(caveat).unwrap();
        }
        let bytes = m.to_bytes();
        assert!((160..=320).contains(&bytes.len()));
        let decoded = SpongeMacaroon::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.to_bytes(), bytes);
        assert_eq!(decoded.verify(&[1; 32], &request(), &[]), Ok(()));
        for pos in 0..bytes.len() {
            let mut tampered = bytes.clone();
            tampered[pos] ^= 1;
            assert!(
                SpongeMacaroon::from_bytes(&tampered)
                    .map_or(true, |t| t.verify(&[1; 32], &request(), &[]).is_err())
            );
        }
        m.attenuate(Caveat::MaxAmount(4)).unwrap();
        m.attenuate(Caveat::MaxAmount(100)).unwrap(); // later permissive caveat cannot undo the earlier one
        assert_eq!(
            m.verify(&[1; 32], &request(), &[]),
            Err(CapabilityError::Denied)
        );
        for len in 0..bytes.len() {
            assert!(SpongeMacaroon::from_bytes(&bytes[..len]).is_err());
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(SpongeMacaroon::from_bytes(&extra).is_err());
    }
    #[test]
    fn discharge_is_required_and_bound_to_exact_parent() {
        let mut parent = SpongeMacaroon::issue(&[1; 32], [4; 32], [2; 32]);
        parent.attenuate(Caveat::ThirdParty([5; 32])).unwrap();
        assert_eq!(
            parent.verify(&[1; 32], &request(), &[]),
            Err(CapabilityError::MissingDischarge)
        );
        let mut discharge = SpongeMacaroon::issue_discharge(&[6; 32], [5; 32], [2; 32]);
        parent.bind_discharge(&mut discharge).unwrap();
        let d = [Discharge {
            token: &discharge,
            root_key: &[6; 32],
        }];
        assert_eq!(parent.verify(&[1; 32], &request(), &d), Ok(()));
        parent.attenuate(Caveat::ExpiresAt(30)).unwrap();
        assert_eq!(
            parent.verify(&[1; 32], &request(), &d),
            Err(CapabilityError::Denied)
        );
        let unbound = SpongeMacaroon::issue_discharge(&[6; 32], [5; 32], [2; 32]);
        assert_eq!(
            parent.verify(
                &[1; 32],
                &request(),
                &[Discharge {
                    token: &unbound,
                    root_key: &[6; 32]
                }]
            ),
            Err(CapabilityError::UnboundDischarge)
        );
        assert_eq!(
            discharge.verify(&[6; 32], &request(), &[]),
            Err(CapabilityError::Denied)
        );
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

    const ROOT: [u8; 32] = [1; 32];
    const THIRD: [u8; 32] = [6; 32];
    fn parent_with_third_party(id: [u8; 32]) -> SpongeMacaroon {
        let mut parent = SpongeMacaroon::issue(&ROOT, [4; 32], [2; 32]);
        parent.attenuate(Caveat::Resource([3; 32])).unwrap();
        parent.attenuate(Caveat::ThirdParty(id)).unwrap();
        parent
    }
    fn bound_discharge(parent: &SpongeMacaroon, id: [u8; 32]) -> SpongeMacaroon {
        let mut discharge = SpongeMacaroon::issue_discharge(&THIRD, id, [2; 32]);
        parent.bind_discharge(&mut discharge).unwrap();
        discharge
    }
    fn contains(haystack: &[u8], needle: &[u8]) -> bool {
        haystack.windows(needle.len()).any(|w| w == needle)
    }
    #[test]
    fn bound_discharge_never_carries_the_parent_bearer_tag() {
        let parent = parent_with_third_party([5; 32]);
        let discharge = bound_discharge(&parent, [5; 32]);
        assert!(!contains(&discharge.to_bytes(), &parent.tag));
        for caveat in discharge.caveats() {
            if let Caveat::BindToParent(binding) = caveat {
                assert_ne!(binding, &parent.tag);
                assert_eq!(binding, &parent_binding(&parent.tag));
            }
        }
        let d = [Discharge {
            token: &discharge,
            root_key: &THIRD,
        }];
        assert_eq!(parent.verify(&ROOT, &request(), &d), Ok(()));
    }
    #[test]
    fn discharge_cannot_be_transplanted_stripped_or_rebound() {
        let parent = parent_with_third_party([5; 32]);
        let discharge = bound_discharge(&parent, [5; 32]);
        // Another capability of the same issuer carrying the same third-party caveat.
        let mut other = SpongeMacaroon::issue(&ROOT, [4; 32], [2; 32]);
        other.attenuate(Caveat::ThirdParty([5; 32])).unwrap();
        let d = [Discharge {
            token: &discharge,
            root_key: &THIRD,
        }];
        assert_eq!(
            other.verify(&ROOT, &request(), &d),
            Err(CapabilityError::Denied)
        );
        // Binding it a second time to the other capability keeps the first binding in force.
        let mut twice = discharge.clone();
        other.bind_discharge(&mut twice).unwrap();
        for target in [&parent, &other] {
            assert_eq!(
                target.verify(
                    &ROOT,
                    &request(),
                    &[Discharge {
                        token: &twice,
                        root_key: &THIRD
                    }]
                ),
                Err(CapabilityError::Denied)
            );
        }
        // Dropping the binding caveat from the wire breaks the chained tag.
        let wire = discharge.to_bytes();
        let mut stripped = wire[..75].to_vec();
        stripped[9..11].copy_from_slice(&0u16.to_be_bytes());
        stripped.extend_from_slice(&wire[wire.len() - 32..]);
        let stripped = SpongeMacaroon::from_bytes(&stripped).unwrap();
        assert_eq!(
            parent.verify(
                &ROOT,
                &request(),
                &[Discharge {
                    token: &stripped,
                    root_key: &THIRD
                }]
            ),
            Err(CapabilityError::InvalidTag)
        );
        // A discharge keyed by a different authority, or for a different audience, is refused.
        assert_eq!(
            parent.verify(
                &ROOT,
                &request(),
                &[Discharge {
                    token: &discharge,
                    root_key: &[7; 32]
                }]
            ),
            Err(CapabilityError::InvalidTag)
        );
        let mut foreign = SpongeMacaroon::issue_discharge(&THIRD, [5; 32], [9; 32]);
        assert_eq!(
            parent.bind_discharge(&mut foreign),
            Err(CapabilityError::Denied)
        );
    }
    #[test]
    fn unused_duplicate_and_nested_discharges_are_rejected() {
        let parent = parent_with_third_party([5; 32]);
        let discharge = bound_discharge(&parent, [5; 32]);
        let stray = bound_discharge(&parent, [8; 32]);
        let good = Discharge {
            token: &discharge,
            root_key: &THIRD,
        };
        let extra = Discharge {
            token: &stray,
            root_key: &THIRD,
        };
        let again = Discharge {
            token: &discharge,
            root_key: &THIRD,
        };
        assert_eq!(
            parent.verify(&ROOT, &request(), &[good, extra]),
            Err(CapabilityError::UnusedDischarge)
        );
        let good = Discharge {
            token: &discharge,
            root_key: &THIRD,
        };
        assert_eq!(
            parent.verify(&ROOT, &request(), &[good, again]),
            Err(CapabilityError::Denied)
        );
        // A capability without third-party caveats accepts no discharge at all.
        let plain = SpongeMacaroon::issue(&ROOT, [4; 32], [2; 32]);
        let verifier = MacaroonVerifier::new(&ROOT, [4; 32], [2; 32]);
        for result in [
            plain.verify(
                &ROOT,
                &request(),
                &[Discharge {
                    token: &discharge,
                    root_key: &THIRD,
                }],
            ),
            verifier.verify(
                &plain,
                &request(),
                &[Discharge {
                    token: &discharge,
                    root_key: &THIRD,
                }],
            ),
        ] {
            assert_eq!(result, Err(CapabilityError::UnusedDischarge));
        }
        // Discharges cannot demand further discharges, and primaries cannot carry bindings.
        let mut nested = SpongeMacaroon::issue_discharge(&THIRD, [5; 32], [2; 32]);
        assert_eq!(
            nested.attenuate(Caveat::ThirdParty([9; 32])),
            Err(CapabilityError::Denied)
        );
        let mut primary = SpongeMacaroon::issue(&ROOT, [4; 32], [2; 32]);
        assert_eq!(
            primary.attenuate(Caveat::BindToParent([0; 32])),
            Err(CapabilityError::Denied)
        );
        assert_eq!(
            discharge.bind_discharge(&mut nested),
            Err(CapabilityError::Denied)
        );
        // A discharge's own first-party caveats restrict the request too.
        let mut expired = SpongeMacaroon::issue_discharge(&THIRD, [5; 32], [2; 32]);
        expired.attenuate(Caveat::ExpiresAt(10)).unwrap();
        parent.bind_discharge(&mut expired).unwrap();
        assert_eq!(
            parent.verify(
                &ROOT,
                &request(),
                &[Discharge {
                    token: &expired,
                    root_key: &THIRD
                }]
            ),
            Err(CapabilityError::Denied)
        );
    }
    #[test]
    fn caveat_order_kind_and_role_are_authenticated() {
        let mut m = SpongeMacaroon::issue(&ROOT, [4; 32], [2; 32]);
        m.attenuate(Caveat::Resource([3; 32])).unwrap();
        m.attenuate(Caveat::ExpiresAt(20)).unwrap();
        m.attenuate(Caveat::NotBefore(5)).unwrap();
        let wire = m.to_bytes();
        assert_eq!(
            SpongeMacaroon::from_bytes(&wire)
                .unwrap()
                .verify(&ROOT, &request(), &[]),
            Ok(())
        );
        // Swap the two eight-byte caveats (each 10 bytes on the wire, after a 34-byte one).
        let mut swapped = wire.clone();
        let (a, b) = (75 + 34, 75 + 44);
        let first: [u8; 10] = wire[a..b].try_into().unwrap();
        swapped.copy_within(b..b + 10, a);
        swapped[b..b + 10].copy_from_slice(&first);
        assert_ne!(swapped, wire);
        // Reinterpret ExpiresAt as NotBefore, and Resource as a third-party obligation.
        let mut rekind = wire.clone();
        rekind[a] = 2;
        let mut third = wire.clone();
        third[75] = 7;
        // Present the primary as a discharge.
        let mut role = wire.clone();
        role[8] = 1;
        for forged in [swapped, rekind, third, role] {
            let token = SpongeMacaroon::from_bytes(&forged).unwrap();
            assert_eq!(token.authenticate(&ROOT), Err(CapabilityError::InvalidTag));
        }
        // Dropping the last caveat cannot be repaired without the previous chaining tag.
        let mut dropped = wire[..wire.len() - 42].to_vec();
        dropped[9..11].copy_from_slice(&2u16.to_be_bytes());
        dropped.extend_from_slice(&wire[wire.len() - 32..]);
        assert_eq!(
            SpongeMacaroon::from_bytes(&dropped)
                .unwrap()
                .verify(&ROOT, &request(), &[]),
            Err(CapabilityError::InvalidTag)
        );
        // Root and caveat hashing are separate domains over identical fields.
        let fields: &[&[u8]] = &[&[1; 32], &[2; 33], &[3; 32]];
        assert_ne!(mac_hash(true, fields), mac_hash(false, fields));
        assert_ne!(parent_binding(&[1; 32]), mac_hash(false, &[&[1u8; 32][..]]));
    }
    #[test]
    fn caveat_bounds_match_on_mint_and_parse() {
        let mut m = SpongeMacaroon::issue(&ROOT, [4; 32], [2; 32]);
        for _ in 0..MAX_CAVEATS {
            m.attenuate(Caveat::Actions(1)).unwrap();
        }
        assert_eq!(
            m.attenuate(Caveat::Actions(1)),
            Err(CapabilityError::TooManyCaveats)
        );
        let wire = m.to_bytes();
        let parsed = SpongeMacaroon::from_bytes(&wire).unwrap();
        assert_eq!(parsed.verify(&ROOT, &request(), &[]), Ok(()));
        let mut over = wire.clone();
        over[9..11].copy_from_slice(&(MAX_CAVEATS as u16 + 1).to_be_bytes());
        assert_eq!(
            SpongeMacaroon::from_bytes(&over).err(),
            Some(CapabilityError::TooManyCaveats)
        );
        // A full discharge has no room left for its binding.
        let mut full = SpongeMacaroon::issue_discharge(&THIRD, [5; 32], [2; 32]);
        for _ in 0..MAX_CAVEATS {
            full.attenuate(Caveat::Actions(1)).unwrap();
        }
        let parent = parent_with_third_party([5; 32]);
        assert_eq!(
            parent.bind_discharge(&mut full),
            Err(CapabilityError::TooManyCaveats)
        );
        // Wrong value lengths and unknown kinds are malformed, whatever the count says.
        for (kind, len) in [(1u8, 16u8), (3, 8), (5, 8), (0, 8), (8, 32), (6, 32)] {
            let mut bad = wire[..75].to_vec();
            bad[9..11].copy_from_slice(&1u16.to_be_bytes());
            bad.extend_from_slice(&[kind, len]);
            bad.extend(core::iter::repeat_n(0u8, usize::from(len)));
            bad.extend_from_slice(&[0; 32]);
            assert_eq!(
                SpongeMacaroon::from_bytes(&bad).err(),
                Some(CapabilityError::Malformed)
            );
        }
    }
}
