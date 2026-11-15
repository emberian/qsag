//! `PiHdCommitInventory` — Batch-derived post-quantum watch-only HD wallet inventory committed
//! under a `32 B` Poseidon2 + SHAKE256 Merkle/Vector-Commitment master public key (`0` online MPC rounds).
//! Child seeds are a dealerless replicated threshold PRF over the custodians' subset seeds.

use crate::seeds::CustodianSet;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_accel::AcceleratorBackend;
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes};
use qsag_accel::goldilocks::pack_bytes32_to_limbs56;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_accel::poseidon2::poseidon2_hash_limbs;
use qsag_addr::{AddrError, KeyIdentityKind, QsagAddress, WitnessSuiteTag};

use crate::seeds::{CommitteeConfig, CustodianSeeds};

/// Errors produced by `PiHdCommitInventory` or `PiHdLinearModule`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HdError {
    InvalidBatchSize,
    ChildIndexOutOfBounds,
    InvalidInventoryProof,
    AddressCodecError(AddrError),
    InvalidThresholdParameters,
    DuplicateOrZeroEvalPoint,
    DerivationBudgetExceeded {
        current: u16,
        max: u16,
    },
    NormBoundExceeded,
    MacCheckFailed,
    EvaluationBudgetExceeded,
    /// The committee is outside the supported honest-majority model.
    UnsupportedCommittee,
    /// A dealerless ceremony detected a fault and stopped before releasing output.
    RekeyAborted(RekeyFault),
    HardenedDerivationRequired,
    DurableBudgetRequired,
    BudgetStorageFailed,
    InvalidSignatureKey,
    UnauthorizedProjection,
}

/// Why a dealerless ceremony stopped. Every variant is detected from messages
/// alone; none requires a custodian to reveal secret state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RekeyFault {
    /// Wrong sender order, missing or duplicate message, wrong length, or a
    /// non-canonical field element.
    MalformedMessage,
    /// An opening does not match its frozen commitment.
    CommitmentMismatch,
    /// Holders of one subset seed derived different seeds.
    SeedConfirmationMismatch,
    /// Holders of one subset published different public images of its tweak.
    PublicShareMismatch,
    /// Broadcast shares do not lie on one polynomial of the required degree.
    InconsistentDegree,
    /// The child MAC sacrifice opened a nonzero value: a multiplication was faulted.
    SacrificeNonZero,
    /// The parent sharing does not satisfy its own MAC relation.
    ParentAuthenticationFailed,
    /// Holders of one replicated component disagree.
    ReplicatedShareMismatch,
}

impl From<AddrError> for HdError {
    fn from(e: AddrError) -> Self {
        Self::AddressCodecError(e)
    }
}

/// Compact `32 B` master root public descriptor (`master_root_pk`) plus algebraic 4-limb Poseidon2
/// commitment for `qsag-agg` recursive Merkle folding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventoryMasterPublicKey {
    /// Compact `32 B` master root PK binding `(pk_seed, batch_size, poseidon2_merkle_root)`.
    pub master_root_pk: [u8; 32],
    pub batch_size: u32,
    pub pk_seed_limbs: [u64; 4],
    pub poseidon2_root_limbs: [u64; 4],
}

/// Public watch-only table allowing a frontend/coordinator to derive deposit addresses in `0` online
/// MPC rounds and attach compact Merkle openings foldable in `qsag-agg`.
#[derive(Clone, Debug)]
pub struct WatchOnlyInventoryTable {
    pub master_pk: InventoryMasterPublicKey,
    pub child_pubkeys: Vec<[u8; 32]>,
    merkle_layers: Vec<Vec<[u64; 4]>>,
}

/// Compact algebraic Poseidon2 Merkle opening proving `child_pk` is the authentic `child_idx`-th
/// derived child under `master_pk.master_root_pk`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventoryChildProof {
    pub child_idx: u32,
    pub child_pk: [u8; 32],
    pub poseidon2_siblings: Vec<[u64; 4]>,
}

/// One custodian's hardened child-seed custody for an SLH-DSA-SHAKE-128f inventory.
///
/// Child seed `i` is the replicated threshold PRF
/// `XOR over subsets A of cSHAKE256(k_A, ceremony, A, pk_seed, i)` under the
/// dealerless subset seeds of [`crate::seeds`]. A custodian derives its components
/// locally, with no interaction and without any party evaluating the PRF on the
/// complete key. A coalition of at most `t - 1` custodians lacks one subset seed,
/// so every child seed stays pseudorandom to it under the PRF security of
/// cSHAKE256; a reconstructed child seed reveals nothing about siblings or the
/// subset seeds under the same assumption.
///
/// The custodian identity is fixed at derivation: duplicate detection during
/// reconstruction and enrollment corroboration relies on it.
/// ```compile_fail
/// fn relabel(vault: &mut qsag_hd::InventoryPartyShareVault) { vault.party_id = 9; }
/// ```
/// ```
/// fn custodian(vault: &qsag_hd::InventoryPartyShareVault) -> u16 { vault.party_id() }
/// ```
pub struct InventoryPartyShareVault {
    party_id: u16,
    config_digest: [u8; 32],
    children: Vec<Vec<(CustodianSet, RedactedSecret<32>)>>,
}

impl Drop for InventoryPartyShareVault {
    fn drop(&mut self) {
        for child in &mut self.children {
            for (_, seed) in child {
                crate::erase::ct_zeroize_bytes(seed.expose_mut());
            }
        }
    }
}

impl InventoryPartyShareVault {
    pub const fn party_id(&self) -> u16 {
        self.party_id
    }
}

impl fmt::Debug for InventoryPartyShareVault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InventoryPartyShareVault")
            .field("party_id", &self.party_id)
            .field("num_children", &self.children.len())
            .field("child_seed_components", &"<REDACTED>")
            .finish()
    }
}

fn hash_inventory_leaf_poseidon2(
    pk_seed_limbs: &[u64; 4],
    child_idx: u32,
    child_pk: &[u8; 32],
) -> [u64; 4] {
    let pk5 = pack_bytes32_to_limbs56(child_pk);
    let limbs = [
        pk_seed_limbs[0],
        pk_seed_limbs[1],
        pk_seed_limbs[2],
        pk_seed_limbs[3],
        child_idx as u64,
        pk5[0],
        pk5[1],
        pk5[2],
        pk5[3],
        pk5[4],
    ];
    poseidon2_hash_limbs(0x4844_494E_565F_4C46, &limbs) // "HDINV_LF"
}

fn compute_master_root_pk32(
    batch_size: u32,
    pk_seed_limbs: &[u64; 4],
    poseidon2_root_limbs: &[u64; 4],
) -> [u8; 32] {
    let b_be = batch_size.to_be_bytes();
    let mut seed_b = [0u8; 32];
    let mut root_b = [0u8; 32];
    for (i, (seed, root)) in pk_seed_limbs.iter().zip(poseidon2_root_limbs).enumerate() {
        seed_b[i * 8..(i + 1) * 8].copy_from_slice(&seed.to_le_bytes());
        root_b[i * 8..(i + 1) * 8].copy_from_slice(&root.to_le_bytes());
    }
    cshake256_framed_32(b"QSAG.HD.INV.SLH128F.ROOT32.V2", &[&b_be, &seed_b, &root_b])
}

fn valid_batch(batch_size: usize) -> bool {
    batch_size.is_power_of_two() && batch_size >= 2 && batch_size <= u32::MAX as usize
}

/// Derives this custodian's replicated components of `batch_size` hardened child
/// seeds. Local and non-interactive; no child seed or PRF key is assembled.
pub fn derive_inventory_vault(
    seeds: &CustodianSeeds,
    pk_seed_bytes: [u8; 32],
    batch_size: usize,
) -> Result<InventoryPartyShareVault, HdError> {
    if !valid_batch(batch_size) {
        return Err(HdError::InvalidBatchSize);
    }
    let subsets: Vec<CustodianSet> = seeds.held_subsets().collect();
    let children = (0..batch_size as u32)
        .map(|idx| {
            subsets
                .iter()
                .map(|&subset| {
                    seeds
                        .prf32(
                            subset,
                            b"QSAG.HD.INV.TPRF.CHILD.V1",
                            &[&pk_seed_bytes, &idx.to_be_bytes()],
                        )
                        .map(|component| (subset, RedactedSecret::new(component)))
                        .ok_or(HdError::InvalidThresholdParameters)
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(InventoryPartyShareVault {
        party_id: seeds.party_id(),
        config_digest: seeds.config().digest(),
        children,
    })
}

/// SLH-DSA-SHAKE-128f public key (`PK.seed || PK.root`) of a child seed.
pub fn inventory_child_public_key(child_seed: &RedactedSecret<32>) -> Result<[u8; 32], HdError> {
    let (_, pk) = qsag_core::fips205::slh_keygen_from_seed(
        &qsag_core::fips205::Fips205Params::SLH_DSA_SHAKE_128F,
        child_seed.expose(),
    )
    .map_err(|_| HdError::InvalidSignatureKey)?;
    pk.to_bytes()
        .try_into()
        .map_err(|_| HdError::InvalidSignatureKey)
}

fn reconstruct_child_seed_with_min_holders(
    config: &CommitteeConfig,
    vaults: &[&InventoryPartyShareVault],
    child_idx: u32,
    min_holders_per_subset: usize,
) -> Result<RedactedSecret<32>, HdError> {
    let digest = config.digest();
    let mut seed = RedactedSecret::new([0u8; 32]);
    for (i, vault) in vaults.iter().enumerate() {
        if vault.config_digest != digest
            || config.position(vault.party_id).is_none()
            || vaults[..i]
                .iter()
                .any(|prior| prior.party_id == vault.party_id)
        {
            return Err(HdError::InvalidThresholdParameters);
        }
    }
    for subset in config.subsets() {
        let mut found: Option<&RedactedSecret<32>> = None;
        let mut holders = 0usize;
        for vault in vaults {
            let components = vault.child_components(child_idx)?;
            let Some((_, component)) = components
                .binary_search_by_key(&subset, |entry| entry.0)
                .ok()
                .map(|i| &components[i])
            else {
                continue;
            };
            holders += 1;
            match found {
                Some(first) if first != component => {
                    return Err(HdError::RekeyAborted(RekeyFault::ReplicatedShareMismatch));
                }
                Some(_) => {}
                None => found = Some(component),
            }
        }
        if holders < min_holders_per_subset {
            return Err(HdError::InvalidThresholdParameters);
        }
        let component = found.ok_or(HdError::InvalidThresholdParameters)?;
        for (acc, &byte) in seed.expose_mut().iter_mut().zip(component.expose()) {
            *acc ^= byte;
        }
    }
    Ok(seed)
}

/// Explicit verified reconstruction of ONE child signing seed from a quorum of vaults,
/// requiring `expected_child_pk = Some(&pk)` (`None` is rejected with
/// [`HdError::InvalidSignatureKey`] so uncorroborated single-holder subsets can never bias an
/// enrollment key). Use [`enroll_child_signing_seed_quorum`] for corroborated initial
/// enrollment before `expected_child_pk` exists, or `recover_child_signing_seed_unchecked` (test builds)
/// only in explicit unchecked diagnostic views.
pub fn recover_child_signing_seed(
    config: &CommitteeConfig,
    vaults: &[&InventoryPartyShareVault],
    child_idx: u32,
    expected_child_pk: Option<&[u8; 32]>,
) -> Result<RedactedSecret<32>, HdError> {
    let expected = expected_child_pk.ok_or(HdError::InvalidSignatureKey)?;
    let seed = reconstruct_child_seed_with_min_holders(config, vaults, child_idx, 1)?;
    if !ct_eq_bytes(&inventory_child_public_key(&seed)?, expected) {
        return Err(HdError::InvalidSignatureKey);
    }
    Ok(seed)
}

/// Verified initial enrollment of ONE child signing seed and its `32 B` SLH-DSA public key
/// before `expected_child_pk` exists: requires every subset `A` to be corroborated by at least
/// `max(threshold, 2)` agreeing custodians (when `n > 1`), guaranteeing at least one honest
/// holder corroborates every subset under `<= t - 1` corruptions.
pub fn enroll_child_signing_seed_quorum(
    config: &CommitteeConfig,
    vaults: &[&InventoryPartyShareVault],
    child_idx: u32,
) -> Result<(RedactedSecret<32>, [u8; 32]), HdError> {
    let min_holders = if config.members().len() > 1 {
        usize::from(config.threshold()).max(2)
    } else {
        1
    };
    let seed = reconstruct_child_seed_with_min_holders(config, vaults, child_idx, min_holders)?;
    let pk = inventory_child_public_key(&seed)?;
    Ok((seed, pk))
}

/// Unchecked reconstruction of ONE child signing seed without verifying against an enrolled
/// `expected_child_pk`. Callers in production signing/recovery MUST use
/// [`recover_child_signing_seed`] with `Some(&expected_child_pk)` or
/// [`enroll_child_signing_seed_quorum`]. Absent from builds without `cfg(test)` or the
/// `testing-ephemeral` feature (regression on
/// [`crate::linear_module::DEALER_FREE_PUBLIC_API`]).
#[cfg(any(test, feature = "testing-ephemeral"))]
pub fn recover_child_signing_seed_unchecked(
    config: &CommitteeConfig,
    vaults: &[&InventoryPartyShareVault],
    child_idx: u32,
) -> Result<RedactedSecret<32>, HdError> {
    reconstruct_child_seed_with_min_holders(config, vaults, child_idx, 1)
}

/// Builds the watch-only table and its `32 B` master root from child PUBLIC keys
/// only. No secret enters this function.
pub fn commit_inventory_public_keys<B: AcceleratorBackend>(
    pk_seed_bytes: [u8; 32],
    child_pubkeys: Vec<[u8; 32]>,
    accel: &B,
) -> Result<WatchOnlyInventoryTable, HdError> {
    let batch_size = child_pubkeys.len();
    if !valid_batch(batch_size) {
        return Err(HdError::InvalidBatchSize);
    }
    let seed5 = pack_bytes32_to_limbs56(&pk_seed_bytes);
    let pk_seed_limbs = poseidon2_hash_limbs(0x5345_4544_3536_5633, &seed5);
    let leaves: Vec<[u64; 4]> = child_pubkeys
        .iter()
        .enumerate()
        .map(|(idx, child_pk)| hash_inventory_leaf_poseidon2(&pk_seed_limbs, idx as u32, child_pk))
        .collect();
    let log_b = batch_size.trailing_zeros() as usize;
    let mut merkle_layers = Vec::with_capacity(log_b + 1);
    merkle_layers.push(leaves);
    for layer in 0..log_b {
        let cur = &merkle_layers[layer];
        let mut parents = vec![[0u64; 4]; cur.len() / 2];
        accel
            .merkle_layer_poseidon2(cur, &pk_seed_limbs, layer as u32, &mut parents)
            .map_err(|_| HdError::InvalidInventoryProof)?;
        merkle_layers.push(parents);
    }
    let poseidon2_root_limbs = merkle_layers[log_b][0];
    let master_root_pk =
        compute_master_root_pk32(batch_size as u32, &pk_seed_limbs, &poseidon2_root_limbs);
    Ok(WatchOnlyInventoryTable {
        master_pk: InventoryMasterPublicKey {
            master_root_pk,
            batch_size: batch_size as u32,
            pk_seed_limbs,
            poseidon2_root_limbs,
        },
        child_pubkeys,
        merkle_layers,
    })
}

impl WatchOnlyInventoryTable {
    /// Derive the `child_idx`-th strict `Bech32m` address and foldable Poseidon2 Merkle proof
    /// in **`0` online MPC rounds**!
    pub fn derive_watch_only_child(
        &self,
        child_idx: u32,
        hrp: &str,
    ) -> Result<(QsagAddress, InventoryChildProof), HdError> {
        let idx = child_idx as usize;
        if idx >= self.child_pubkeys.len() || child_idx >= self.master_pk.batch_size {
            return Err(HdError::ChildIndexOutOfBounds);
        }
        let child_pk = self.child_pubkeys[idx];
        let addr = QsagAddress::from_pubkey_poseidon2(
            hrp,
            WitnessSuiteTag::PiHdCommitInventory,
            KeyIdentityKind::SingleOrThreshold,
            &child_pk,
        )?;
        let log_b = self
            .merkle_layers
            .len()
            .checked_sub(1)
            .ok_or(HdError::InvalidInventoryProof)?;
        let mut poseidon2_siblings = Vec::with_capacity(log_b);
        let mut cur = idx;
        for layer_vec in self.merkle_layers.iter().take(log_b) {
            poseidon2_siblings.push(
                *layer_vec
                    .get(cur ^ 1)
                    .ok_or(HdError::InvalidInventoryProof)?,
            );
            cur >>= 1;
        }
        Ok((
            addr,
            InventoryChildProof {
                child_idx,
                child_pk,
                poseidon2_siblings,
            },
        ))
    }
}

impl InventoryPartyShareVault {
    /// Local lookup of this custodian's `(subset, component)` list for one child.
    pub fn child_components(
        &self,
        child_idx: u32,
    ) -> Result<&[(CustodianSet, RedactedSecret<32>)], HdError> {
        self.children
            .get(child_idx as usize)
            .map(Vec::as_slice)
            .ok_or(HdError::ChildIndexOutOfBounds)
    }
}

/// Verify an [`InventoryChildProof`] against the compact `32 B` `master_pk` and derived `Bech32m` address.
pub fn verify_inventory_child_proof<B: AcceleratorBackend>(
    master_pk: &InventoryMasterPublicKey,
    proof: &InventoryChildProof,
    expected_addr: &QsagAddress,
    accel: &B,
) -> Result<(), HdError> {
    const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001;
    if !master_pk.batch_size.is_power_of_two() {
        return Err(HdError::InvalidBatchSize);
    }
    if proof.child_idx >= master_pk.batch_size {
        return Err(HdError::ChildIndexOutOfBounds);
    }
    if master_pk.pk_seed_limbs.iter().any(|&x| x >= GOLDILOCKS_P)
        || master_pk
            .poseidon2_root_limbs
            .iter()
            .any(|&x| x >= GOLDILOCKS_P)
        || proof
            .poseidon2_siblings
            .iter()
            .any(|sib| sib.iter().any(|&x| x >= GOLDILOCKS_P))
    {
        return Err(HdError::InvalidInventoryProof);
    }
    let expected_root32 = compute_master_root_pk32(
        master_pk.batch_size,
        &master_pk.pk_seed_limbs,
        &master_pk.poseidon2_root_limbs,
    );
    if !ct_eq_bytes(&expected_root32, &master_pk.master_root_pk) {
        return Err(HdError::InvalidInventoryProof);
    }

    let recomputed_addr = QsagAddress::from_pubkey_poseidon2(
        &expected_addr.hrp,
        WitnessSuiteTag::PiHdCommitInventory,
        KeyIdentityKind::SingleOrThreshold,
        &proof.child_pk,
    )?;
    if recomputed_addr != *expected_addr {
        return Err(HdError::InvalidInventoryProof);
    }

    let log_b = master_pk.batch_size.trailing_zeros() as usize;
    if proof.poseidon2_siblings.len() != log_b {
        return Err(HdError::InvalidInventoryProof);
    }

    let mut cur_hash =
        hash_inventory_leaf_poseidon2(&master_pk.pk_seed_limbs, proof.child_idx, &proof.child_pk);
    let mut idx = proof.child_idx as usize;
    for (layer, &sib) in proof.poseidon2_siblings.iter().enumerate() {
        let pair = if (idx & 1) == 0 {
            [cur_hash, sib]
        } else {
            [sib, cur_hash]
        };
        let mut out = [[0u64; 4]; 1];
        accel
            .merkle_layer_poseidon2_at(
                &pair,
                &master_pk.pk_seed_limbs,
                layer as u32,
                (idx >> 1) as u64,
                &mut out,
            )
            .map_err(|_| HdError::InvalidInventoryProof)?;
        cur_hash = out[0];
        idx >>= 1;
    }

    if cur_hash != master_pk.poseidon2_root_limbs {
        return Err(HdError::InvalidInventoryProof);
    }
    Ok(())
}

impl core::fmt::Display for HdError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for HdError {}

#[cfg(test)]
mod signature_tests {
    use super::*;
    use crate::seeds::run_seed_ceremony;
    use qsag_core::fips205::{
        Fips205Params, SlhPublicKey, slh_keygen_from_seed, slh_sign, slh_verify,
    };

    fn committee(t: u16, n: u16) -> CommitteeConfig {
        let members: Vec<_> = (0..n).map(|i| (i, u32::from(i) + 1)).collect();
        CommitteeConfig::new(t, &members, [3; 32]).unwrap()
    }

    #[test]
    fn threshold_prf_inventory_key_signs_and_rejects_placeholder_and_sibling() {
        let accel = qsag_accel::CpuReferenceBackend::new();
        let config = committee(2, 3);
        let seeds = run_seed_ceremony(&config, 0x21);
        let vaults: Vec<_> = seeds
            .iter()
            .map(|s| derive_inventory_vault(s, [2; 32], 2).unwrap())
            .collect();
        // Verified enrollment: `expected_child_pk = None` is rejected on `recover_child_signing_seed`,
        // and corroborated initial enrollment requires every subset to have >= t agreeing holders!
        assert_eq!(
            recover_child_signing_seed(&config, &[&vaults[0], &vaults[2]], 0, None).err(),
            Some(HdError::InvalidSignatureKey)
        );
        assert_eq!(
            enroll_child_signing_seed_quorum(&config, &[&vaults[0], &vaults[2]], 0).err(),
            Some(HdError::InvalidThresholdParameters)
        );
        let all_vaults: Vec<&InventoryPartyShareVault> = vaults.iter().collect();
        let pubkeys: Vec<[u8; 32]> = (0..2)
            .map(|idx| {
                enroll_child_signing_seed_quorum(&config, &all_vaults, idx)
                    .unwrap()
                    .1
            })
            .collect();
        let table = commit_inventory_public_keys([2; 32], pubkeys, &accel).unwrap();
        // A different quorum recovers the same seed and it matches the enrolled key.
        let seed = recover_child_signing_seed(
            &config,
            &[&vaults[1], &vaults[2]],
            0,
            Some(&table.child_pubkeys[0]),
        )
        .unwrap();
        let params = Fips205Params::SLH_DSA_SHAKE_128F;
        let (sk, pk) = slh_keygen_from_seed(&params, seed.expose()).unwrap();
        assert_eq!(pk.to_bytes(), table.child_pubkeys[0]);
        let signature =
            slh_sign(&params, b"inventory spend", b"hd-inventory-v2", &sk, None).unwrap();
        assert!(slh_verify(
            &params,
            b"inventory spend",
            &signature,
            b"hd-inventory-v2",
            &pk
        ));
        let sibling =
            SlhPublicKey::from_bytes_for_params(&params, &table.child_pubkeys[1]).unwrap();
        assert!(!slh_verify(
            &params,
            b"inventory spend",
            &signature,
            b"hd-inventory-v2",
            &sibling
        ));
        let placeholder = cshake256_framed_32(
            b"QSAG.HD.INV.CHILD_PK.V1",
            &[&[2; 32], &0u32.to_be_bytes(), seed.expose()],
        );
        assert_ne!(table.child_pubkeys[0], placeholder);
        let (addr, mut proof) = table.derive_watch_only_child(0, "qsp").unwrap();
        let mut noncanon_master = table.master_pk.clone();
        noncanon_master.poseidon2_root_limbs[0] = 0xFFFF_FFFF_0000_0001;
        assert_eq!(
            verify_inventory_child_proof(&noncanon_master, &proof, &addr, &accel).err(),
            Some(HdError::InvalidInventoryProof)
        );
        let mut noncanon_proof = proof.clone();
        noncanon_proof.poseidon2_siblings[0][0] = 0xFFFF_FFFF_0000_0001;
        assert_eq!(
            verify_inventory_child_proof(&table.master_pk, &noncanon_proof, &addr, &accel).err(),
            Some(HdError::InvalidInventoryProof)
        );
        proof.child_pk = placeholder;
        assert!(verify_inventory_child_proof(&table.master_pk, &proof, &addr, &accel).is_err());
    }

    #[test]
    fn threshold_prf_faults_and_single_custodian_views() {
        let config = committee(2, 3);
        let seeds = run_seed_ceremony(&config, 0x22);
        let mut vaults: Vec<_> = seeds
            .iter()
            .map(|s| derive_inventory_vault(s, [5; 32], 4).unwrap())
            .collect();
        let all_refs: Vec<&InventoryPartyShareVault> = vaults.iter().collect();
        let (honest, pk) = enroll_child_signing_seed_quorum(&config, &all_refs, 3).unwrap();
        // `recover_child_signing_seed` explicitly rejects `expected_child_pk = None`!
        assert_eq!(
            recover_child_signing_seed(&config, &[&vaults[0], &vaults[1]], 3, None).err(),
            Some(HdError::InvalidSignatureKey)
        );
        // One custodian alone does not cover every subset.
        assert_eq!(
            recover_child_signing_seed_unchecked(&config, &[&vaults[0]], 3).err(),
            Some(HdError::InvalidThresholdParameters)
        );
        // Each custodian lacks exactly the component of the subset that excludes it,
        // and that component is not a function of anything the custodian holds:
        // replacing only that subset seed changes the child seed and no held component.
        let world = |flip: bool| -> Vec<CustodianSeeds> {
            (0..3u16)
                .map(|id| {
                    CustodianSeeds::from_explicit_seeds(&config, id, [8; 32], |subset| {
                        let mut seed = [subset.to_be_bytes()[31]; 32];
                        // Subset 0b110 excludes custodian 0.
                        if flip && subset == CustodianSet::from(0b110) {
                            seed[31] ^= 1;
                        }
                        seed
                    })
                })
                .collect()
        };
        let (a, b) = (world(false), world(true));
        let va: Vec<_> = a
            .iter()
            .map(|s| derive_inventory_vault(s, [5; 32], 2).unwrap())
            .collect();
        let vb: Vec<_> = b
            .iter()
            .map(|s| derive_inventory_vault(s, [5; 32], 2).unwrap())
            .collect();
        assert_eq!(
            va[0].child_components(1).unwrap(),
            vb[0].child_components(1).unwrap()
        );
        assert!(
            va[0]
                .child_components(1)
                .unwrap()
                .iter()
                .all(|entry| entry.0 != CustodianSet::from(0b110))
        );
        let seed_a = recover_child_signing_seed_unchecked(&config, &[&va[1], &va[2]], 1).unwrap();
        let seed_b = recover_child_signing_seed_unchecked(&config, &[&vb[1], &vb[2]], 1).unwrap();
        assert_ne!(seed_a, seed_b);
        // Sibling children are unrelated values.
        let sibling =
            recover_child_signing_seed_unchecked(&config, &[&vaults[0], &vaults[1]], 2).unwrap();
        assert_ne!(sibling, honest);
        // A corrupted component is caught by a second holder ...
        let shared = vaults[2].children[3][0].0;
        vaults[2].children[3][0].1.expose_mut()[0] ^= 1;
        let other = if shared.contains(0) { 0 } else { 1 };
        assert_eq!(
            recover_child_signing_seed(&config, &[&vaults[other], &vaults[2]], 3, Some(&pk)).err(),
            Some(HdError::RekeyAborted(RekeyFault::ReplicatedShareMismatch))
        );
        // Corroborated initial enrollment also catches a single faulty custodian!
        let faulty_all: Vec<&InventoryPartyShareVault> = vaults.iter().collect();
        assert_eq!(
            enroll_child_signing_seed_quorum(&config, &faulty_all, 3).err(),
            Some(HdError::RekeyAborted(RekeyFault::ReplicatedShareMismatch))
        );
        // ... and, where the faulty custodian is a subset's only present holder,
        // by the enrolled public key.
        let alone = 1 - other;
        let solo = !vaults[2].children[3][0].0.contains(alone);
        let result =
            recover_child_signing_seed(&config, &[&vaults[alone], &vaults[2]], 3, Some(&pk));
        if solo {
            assert_eq!(result.err(), Some(HdError::InvalidSignatureKey));
        } else {
            assert_eq!(
                result.err(),
                Some(HdError::RekeyAborted(RekeyFault::ReplicatedShareMismatch))
            );
        }
        assert_eq!(
            derive_inventory_vault(&seeds[0], [5; 32], 3).err(),
            Some(HdError::InvalidBatchSize)
        );
    }
}
