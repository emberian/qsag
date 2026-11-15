//! Dealerless, fixed-subset WOTS+C minting directly into volatile coupon slots.
//!
//! The production binary-SPDZ staging engine evaluates all three chain steps;
//! only endpoints are reconstructed. Fresh OS entropy seeds each participant,
//! and fresh pairwise masks independently rerandomize every retained chain state.
//! The in-process orchestrator has the same trust boundary as `dealerless_staging`:
//! a separate-host deployment still needs authenticated confidential transport.
//!
//! Root certification is generic over [`BaggyEngine`]: the 2-of-3 replicated engine
//! or the `t`-of-`n` [`qsag_core::spdz_sweep::SpdzSweepEngine`], under `FORS+C`
//! (version 1) or `PORS+FP` (version 2) parameters. The root certificate carries the
//! threshold of the engine that signed it; the coupon carries the all-of-subset rule
//! of its own minting. Neither raises the other.

use super::*;
use crate::dealerless_staging::stage_volatile_subset_into;
use qsag_core::baggy::{
    BaggyEngine, BaggyKeyBinding, MemoryFirstSigned, WaistbandCache, baggy_sign_mpc,
};
use qsag_core::preprocessing::PartyPrivateRng;

/// Public mint policy. Only these members participate; no enumeration of n-choose-t.
pub struct MintPlan {
    pub parent: BaggyPublicKey,
    pub parties: usize,
    pub members: Vec<u32>,
    pub expires_at: u64,
    pub coupons: usize,
}

/// Uncertified output has no opening API. Dropping it erases every staged share.
pub struct PendingCouponBatch {
    descriptors: Vec<CouponDescriptor>,
    // [coupon][member], each table is a distinct locked mapping.
    material: Vec<Vec<LockedBytes>>,
}

/// Process-local authenticated Waistband for the Baggy root signer (any [`BaggyEngine`]).
/// It starts empty; it cannot import caller-supplied entries or first-signed records.
/// On restart BOTH the cache and its MAC key disappear, so the engine recomputes
/// roots from the long-term key. No disk state is required by this wrapper.
///
/// The memory ledger is an additional consistency check for this process, not a
/// rollback anchor. The secret MAC binds the actual Waistband contents AND the
/// records before any MPC output. Any failed ceremony poisons the wrapper.
pub struct AuthenticatedWaistband {
    parent: BaggyPublicKey,
    params: BaggyParams,
    binding: BaggyKeyBinding,
    cache: WaistbandCache,
    records: MemoryFirstSigned,
    key: InitiatorKey,
    tag: Option<Node>,
}

impl AuthenticatedWaistband {
    pub fn new(
        parent: BaggyPublicKey,
        params: BaggyParams,
        binding: BaggyKeyBinding,
        top_layers: usize,
        max_entries: usize,
    ) -> Result<Self, CouponError> {
        if !params.is_well_formed()
            || !binding.matches(&params, &parent)
            || top_layers >= params.num_layers
        {
            return Err(CouponError::InvalidParameters);
        }
        let mut out = Self {
            parent,
            params,
            binding,
            cache: WaistbandCache::new(top_layers, max_entries),
            records: MemoryFirstSigned::new(),
            key: InitiatorKey::generate()?,
            tag: None,
        };
        out.tag = Some(out.mac()?);
        Ok(out)
    }

    fn mac(&self) -> Result<Node, CouponError> {
        self.key.mac(
            b"QSAG.VOLATILE.ROOT_WAISTBAND/v1",
            &[
                &self.binding.identity(),
                &self.cache.authentication_digest(),
                &self.records.authentication_digest(),
            ],
        )
    }

    pub fn sign<E: BaggyEngine>(
        &mut self,
        protection: &ProtectedMintProcess,
        engine: &mut E,
        message: &[u8],
    ) -> Result<BaggySig, CouponError> {
        protection.check()?;
        let tag = self.tag.ok_or(CouponError::Authentication)?;
        if !self.binding.matches(&self.params, &self.parent) || !ct_eq_bytes32(&tag, &self.mac()?) {
            return Err(CouponError::Authentication);
        }
        self.tag = None;
        // Populate all covered upper-layer records from MPC-derived roots. This
        // also avoids CacheUnanchored on a later path through a different leaf of
        // a cached subtree. No caller-provided cache entry enters precomputation.
        if self.records.is_empty() && self.cache.top_layers() > 0 {
            self.cache
                .precompute(
                    engine,
                    &self.params,
                    &self.parent,
                    &self.binding,
                    &mut self.records,
                )
                .map_err(|_| CouponError::Certificate)?;
        }
        let sig = baggy_sign_mpc(
            engine,
            &self.params,
            &self.parent,
            &self.binding,
            &mut self.cache,
            &mut self.records,
            message,
        )
        .map_err(|_| CouponError::Certificate)?;
        self.tag = Some(self.mac()?);
        Ok(sig)
    }

    pub fn cached_signatures(&self) -> usize {
        self.cache.sig_entries()
    }
}

impl PendingCouponBatch {
    /// Fresh per-party entropy is sampled AFTER process protection succeeds. No
    /// deterministic seed input or share-table export exists on this mint API.
    pub fn mint(protection: &ProtectedMintProcess, plan: MintPlan) -> Result<Self, CouponError> {
        protection.check()?;
        let t = plan.members.len();
        let bytes = plan
            .coupons
            .checked_mul(t)
            .and_then(|n| n.checked_mul(SHARE_BYTES));
        if plan.coupons == 0 || bytes.is_none_or(|n| n > 256 * 1024 * 1024) {
            return Err(CouponError::InvalidParameters);
        }
        let mut descriptor = CouponDescriptor {
            parent: plan.parent,
            threshold: t,
            parties: plan.parties,
            members: plan.members,
            pk_seed: [0; 32],
            leaf: 0,
            chain_ends: vec![[0; 32]; WOTS_CHAINS],
            expires_at: plan.expires_at,
        };
        descriptor.validate()?;
        if now()? > plan.expires_at {
            return Err(CouponError::Expired);
        }
        let public_coins = LockedBytes::random(64)?;
        descriptor
            .pk_seed
            .copy_from_slice(&public_coins.as_slice()?[..32]);
        let mut session = [0; 32];
        session.copy_from_slice(&public_coins.as_slice()?[32..]);
        let mut rngs = Vec::with_capacity(t);
        for _ in 0..t {
            let seed = LockedBytes::random(32)?;
            let mut bytes = [0; 32];
            bytes.copy_from_slice(seed.as_slice()?);
            rngs.push(PartyPrivateRng::from_seed(
                bytes,
                b"QSAG.VOLATILE.MINT.RNG/v1",
            ));
            wipe_bytes(&mut bytes);
        }
        let mut material = Vec::with_capacity(plan.coupons);
        for _ in 0..plan.coupons {
            let mut members = Vec::with_capacity(t);
            for _ in 0..t {
                members.push(LockedBytes::new(SHARE_BYTES)?);
            }
            material.push(members);
        }
        let leaves: Vec<u64> = (0..plan.coupons as u64).collect();
        let ends = stage_volatile_subset_into(
            &leaves,
            &descriptor.pk_seed,
            session,
            &mut rngs,
            &mut |party, coupon, position, share| {
                let dest = material[coupon][party]
                    .as_mut_slice()
                    .map_err(|_| crate::DealerlessStagingError::OutputRejected)?;
                dest[position * 32..(position + 1) * 32].copy_from_slice(share);
                Ok(())
            },
        )
        .map_err(|_| CouponError::Staging)?;
        drop(rngs);
        // Pairwise zero-sum masks across a spanning star. Each coordinate gets
        // independent entropy, so revealing one chain position does not reveal
        // the missing member's share at any other position. Across hosts each
        // pair obtains its mask through an authenticated confidential channel.
        for members in &mut material {
            let (left, right) = members.split_at_mut(t - 1);
            for member in left {
                let mask = LockedBytes::random(SHARE_BYTES)?;
                for ((a, b), &r) in member
                    .as_mut_slice()?
                    .iter_mut()
                    .zip(right[0].as_mut_slice()?)
                    .zip(mask.as_slice()?)
                {
                    *a ^= r;
                    *b ^= r;
                }
            }
        }
        let descriptors = ends
            .into_iter()
            .map(|(leaf, chain_ends)| CouponDescriptor {
                leaf,
                chain_ends,
                ..descriptor.clone()
            })
            .collect();
        Ok(Self {
            descriptors,
            material,
        })
    }

    pub fn descriptors(&self) -> &[CouponDescriptor] {
        &self.descriptors
    }

    /// Certify through a fresh, MAC-authenticated RAM Waistband, without a WAL.
    /// The certificate remains an ordinary BaggySig accepted by baggy_verify.
    pub fn certify_with_waistband<E: BaggyEngine>(
        self,
        protection: &ProtectedMintProcess,
        engine: &mut E,
        waistband: &mut AuthenticatedWaistband,
        pools: &mut [CouponPool],
    ) -> Result<Vec<CertifiedCoupon>, CouponError> {
        self.validate_pools(pools)?;
        if self
            .descriptors
            .iter()
            .any(|d| d.parent != waistband.parent)
        {
            return Err(CouponError::Certificate);
        }
        let certificates = self
            .descriptors
            .iter()
            .map(|d| waistband.sign(protection, engine, &d.certificate_message()?))
            .collect::<Result<_, _>>()?;
        self.install(&waistband.params, certificates, pools)
    }

    /// Finish a separate offline certification ceremony. Certificates are checked
    /// concretely against the minted descriptors BEFORE any pool is modified.
    pub fn install(
        self,
        params: &BaggyParams,
        certificates: Vec<BaggySig>,
        pools: &mut [CouponPool],
    ) -> Result<Vec<CertifiedCoupon>, CouponError> {
        self.validate_pools(pools)?;
        if certificates.len() != self.descriptors.len() {
            return Err(CouponError::Certificate);
        }
        let certified: Vec<_> = self
            .descriptors
            .into_iter()
            .zip(certificates)
            .map(|(d, certificate)| {
                CertifiedCoupon::verify(&d.parent, params, d.clone(), certificate)
            })
            .collect::<Result<_, _>>()?;
        for (coupon, shares) in certified.iter().zip(self.material) {
            for (pool, share) in pools.iter_mut().zip(shares) {
                pool.install(coupon.clone(), share)?;
            }
        }
        Ok(certified)
    }

    fn validate_pools(&self, pools: &[CouponPool]) -> Result<(), CouponError> {
        for d in &self.descriptors {
            if now()? > d.expires_at {
                return Err(CouponError::Expired);
            }
            if pools.len() != d.members.len() {
                return Err(CouponError::InvalidParameters);
            }
            let id = d.id()?;
            for (pool, &party) in pools.iter().zip(&d.members) {
                if pool.party != party || pool.parent != d.parent {
                    return Err(CouponError::InvalidParameters);
                }
                if pool.slots.contains_key(&id) {
                    return Err(CouponError::AlreadyInstalled);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_core::baggy::{baggy_reference_keygen, baggy_reference_sign};
    use qsag_core::tsw_baggy::PqSecretKey;

    #[test]
    fn dealerless_baggy_waistband_root_certificate() {
        const CHILD: &str = "QSAG_VOLATILE_WAISTBAND_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "volatile_coupon::mint::tests::dealerless_baggy_waistband_root_certificate",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(CHILD, "1")
                .status()
                .unwrap();
            assert!(status.success());
            return;
        }
        let protection = ProtectedMintProcess::enable().unwrap();
        let mut rngs = core::array::from_fn(|i| {
            PartyPrivateRng::from_seed([i as u8 + 18; 32], b"volatile-root-dkg")
        });
        let (keys, _) =
            qsag_core::keccak_mpc::run_dealerless_rss_dkg_2of3([39; 32], 32, &mut rngs).unwrap();
        let mut engine = qsag_core::rss256::Rss256Engine::new([40; 32], keys, rngs).unwrap();
        // Version 2: the root certificate is a PORS+FP signature.
        let params = BaggyParams::SHA3_128F_V2;
        let (parent, binding) = qsag_core::baggy::baggy_keygen_mpc(
            &mut engine,
            &params,
            &mut WaistbandCache::disabled(),
        )
        .unwrap();
        let mut waistband = AuthenticatedWaistband::new(parent, params, binding, 2, 256).unwrap();
        let pending = PendingCouponBatch::mint(
            &protection,
            MintPlan {
                parent,
                parties: 3,
                members: vec![0, 2],
                expires_at: now().unwrap() + 600,
                coupons: 1,
            },
        )
        .unwrap();
        let mut pools: Vec<_> = [0, 2]
            .into_iter()
            .map(|party| CouponPool::new(party, parent, super::super::tests::key()).unwrap())
            .collect();
        let coupons = pending
            .certify_with_waistband(&protection, &mut engine, &mut waistband, &mut pools)
            .unwrap();
        assert!(waistband.cached_signatures() > 0);
        let req = super::super::tests::request(&coupons[0], b"real dealerless root and coupon");
        let openings: Vec<_> = pools.iter_mut().map(|p| p.open(&req).unwrap()).collect();
        let sig = combine(&coupons[0], &req, &openings).unwrap();
        assert!(verify(&parent, &params, &req.message, &sig));

        // Replacing a whole, internally consistent cache is still a MAC failure,
        // before even the deterministic root randomizer can be released.
        let old_cache = waistband.cache.clone();
        waistband.cache = WaistbandCache::disabled();
        assert!(matches!(
            waistband.sign(&protection, &mut engine, b"cache attack"),
            Err(CouponError::Authentication)
        ));
        waistband.cache = old_cache;
        let saved_tag = waistband.tag;
        waistband.tag.as_mut().unwrap()[0] ^= 1;
        assert!(matches!(
            waistband.sign(&protection, &mut engine, b"tag attack"),
            Err(CouponError::Authentication)
        ));
        waistband.tag = saved_tag;
        let cached_sig = waistband
            .sign(&protection, &mut engine, b"cached root certificate")
            .unwrap();
        assert!(baggy_verify(
            &params,
            &parent,
            b"cached root certificate",
            &cached_sig
        ));

        // Rebuilding empty RAM state is safe: roots are recomputed from the key,
        // no first-signed record or WAL is restored from disk.
        drop(waistband);
        let mut restarted = AuthenticatedWaistband::new(parent, params, binding, 2, 256).unwrap();
        let again = restarted
            .sign(&protection, &mut engine, b"cached root certificate")
            .unwrap();
        assert_eq!(cached_sig, again);
    }

    #[test]
    fn dealerless_mint_2_of_3_batch() {
        check_mint(2, 3, 2, "dealerless_mint_2_of_3_batch");
    }
    #[test]
    fn dealerless_mint_3_of_5() {
        check_mint(3, 5, 1, "dealerless_mint_3_of_5");
    }
    #[test]
    fn dealerless_mint_5_of_7() {
        check_mint(5, 7, 1, "dealerless_mint_5_of_7");
    }
    #[test]
    fn dealerless_mint_all_of_3() {
        check_mint(3, 3, 1, "dealerless_mint_all_of_3");
    }

    fn check_mint(t: usize, n: usize, count: usize, name: &str) {
        // Process-wide protection must not affect the test harness's other tests.
        const CHILD: &str = "QSAG_VOLATILE_MINT_MATRIX_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let name = format!("volatile_coupon::mint::tests::{name}");
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", &name, "--nocapture", "--test-threads=1"])
                .env(CHILD, "1")
                .status()
                .unwrap();
            assert!(status.success());
            return;
        }
        let protection = ProtectedMintProcess::enable().unwrap();
        let params = BaggyParams::SHA3_128F;
        // Reference root certificate only; every coupon secret and all chain
        // evaluation use the real production dealerless OT/SPDZ engine.
        let sk = PqSecretKey {
            sk_seed: [19; 32],
            sk_prf: [42; 32],
            pk_seed: [83; 32],
        };
        let parent = baggy_reference_keygen(&params, &sk).unwrap();
        {
            let members: Vec<_> = (n - t..n).map(|i| i as u32).collect();
            let pending = PendingCouponBatch::mint(
                &protection,
                MintPlan {
                    parent,
                    parties: n,
                    members: members.clone(),
                    expires_at: now().unwrap() + 600,
                    coupons: count,
                },
            )
            .unwrap();
            let certs = pending
                .descriptors()
                .iter()
                .map(|d| {
                    baggy_reference_sign(&params, &sk, &parent, &d.certificate_message().unwrap())
                        .unwrap()
                })
                .collect();
            let mut pools: Vec<_> = members
                .into_iter()
                .map(|party| CouponPool::new(party, parent, super::super::tests::key()).unwrap())
                .collect();
            let coupons = pending.install(&params, certs, &mut pools).unwrap();
            assert_eq!(coupons.len(), count);
            for coupon in &coupons {
                let req = super::super::tests::request(coupon, b"dealerless volatile spend");
                let openings: Vec<_> = pools.iter_mut().map(|p| p.open(&req).unwrap()).collect();
                let sig = combine(coupon, &req, &openings).unwrap();
                assert!(verify(&parent, &params, &req.message, &sig));
                assert!(combine(coupon, &req, &openings[..t - 1]).is_err());
                assert!(
                    pools
                        .iter_mut()
                        .all(|p| matches!(p.open(&req), Err(CouponError::MissingOrSpent)))
                );
            }
            eprintln!("dealerless locked coupon passed {t}-of-{n}, batch {count}");
        }
    }
}
