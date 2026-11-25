use super::*;

// ============================================================================
// Canonical Sub-15 MiB Wire Serialization (`to_compact_wire_bytes` / `from_compact_wire_bytes`)
// ============================================================================

pub(super) const SD_COMPACT_WIRE_MAGIC: &[u8; 24] = b"QSAG.BVC.SD.LIMBO256.V2\0";

impl SelectiveDisclosurePresentation {
    /// Serialize this [`SelectiveDisclosurePresentation`] to its canonical wire format
    /// (`~9.20 MiB` at [`ZkSoundnessProfile::Quantum128`], `~4.74 MiB` at
    /// [`ZkSoundnessProfile::Classical128`]).
    pub fn to_compact_wire_bytes(&self) -> Result<Vec<u8>, BlindVcError> {
        if !(1..=MAX_VC_ATTRS).contains(&self.arity)
            || self.disclosed_attrs.len() > self.arity
            || (self.opened_reps.len() != ZkSoundnessProfile::Classical128.sd_repetitions()
                && self.opened_reps.len() != ZkSoundnessProfile::Quantum128.sd_repetitions())
        {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        for (pos, &(idx, val)) in self.disclosed_attrs.iter().enumerate() {
            if idx >= self.arity || !gl_is_canonical(val) {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            if pos > 0 && self.disclosed_attrs[pos - 1].0 >= idx {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
        }
        if self
            .accumulator_root
            .iter()
            .chain(self.verifier_scope_limbs.iter())
            .chain(self.pres_commit.iter())
            .chain(self.scope_tag.iter())
            .any(|&v| !gl_is_canonical(v))
        {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }

        let num_secret_wires = (self.arity - self.disclosed_attrs.len())
            + 4
            + 4
            + VC_ACCUMULATOR_DEPTH
            + 6 * VC_ACCUMULATOR_DEPTH;
        let base_rep_bytes = 1 + VC_SD_GGM_DEPTH * 32 + 32 + (SD_RPOLY_COEFFS + 2 * SD_GRID_L) * 40;
        let aux_bytes = (num_secret_wires + SD_TOTAL_GATES + 5) * 8;
        let mode_extra = match self.mode {
            PresentationMode::UnlinkableFresh => 1,
            PresentationMode::ScopedPseudonym(_) => 33,
        };
        let header_bytes = 24
            + 8
            + 32
            + mode_extra
            + 32
            + 8
            + 8
            + 48
            + 32
            + 32
            + 4
            + self.disclosed_attrs.len() * 12
            + 48
            + 48
            + 4;

        let mut total_bytes = header_bytes;
        for o in &self.opened_reps {
            let is_last_hidden = (o.hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1;
            if o.r_poly_without_b.len() != SD_RPOLY_COEFFS
                || o.alpha.len() != SD_GRID_L
                || o.beta.len() != SD_GRID_L
            {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            match (&o.aux, is_last_hidden) {
                (None, true) => total_bytes += base_rep_bytes,
                (Some(aux), false) => {
                    if aux.delta_w.len() != num_secret_wires
                        || aux.delta_z.len() != SD_TOTAL_GATES
                        || Fp5::from_canonical_limbs(aux.delta_c).is_none()
                        || aux.delta_w.iter().any(|&v| !gl_is_canonical(v))
                        || aux.delta_z.iter().any(|&v| !gl_is_canonical(v))
                    {
                        return Err(BlindVcError::SelectiveDisclosureProofInvalid);
                    }
                    total_bytes += base_rep_bytes + aux_bytes;
                }
                _ => return Err(BlindVcError::SelectiveDisclosureProofInvalid),
            }
            for arr in o
                .r_poly_without_b
                .iter()
                .chain(o.alpha.iter())
                .chain(o.beta.iter())
            {
                if Fp5::from_canonical_limbs(*arr).is_none() {
                    return Err(BlindVcError::SelectiveDisclosureProofInvalid);
                }
            }
        }

        let mut out = Vec::with_capacity(total_bytes);
        out.extend_from_slice(SD_COMPACT_WIRE_MAGIC);
        out.extend_from_slice(&(self.arity as u64).to_le_bytes());
        out.extend_from_slice(&self.verifier_challenge);
        match self.mode {
            PresentationMode::UnlinkableFresh => out.push(0),
            PresentationMode::ScopedPseudonym(id) => {
                out.push(1);
                out.extend_from_slice(&id);
            }
        }
        out.extend_from_slice(&self.presentation_nonce);
        out.extend_from_slice(&self.issuer_epoch.to_le_bytes());
        out.extend_from_slice(&self.schema_id.to_le_bytes());
        for &v in &self.accumulator_root {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&self.issuer_root_tag);
        for &v in &self.verifier_scope_limbs {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.disclosed_attrs.len() as u32).to_le_bytes());
        for &(idx, val) in &self.disclosed_attrs {
            out.extend_from_slice(&(idx as u32).to_le_bytes());
            out.extend_from_slice(&val.to_le_bytes());
        }
        for &v in self.pres_commit.iter().chain(self.scope_tag.iter()) {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.opened_reps.len() as u32).to_le_bytes());

        for o in &self.opened_reps {
            out.push(o.hidden_party);
            for node in &o.ggm_copath {
                out.extend_from_slice(node);
            }
            out.extend_from_slice(&o.com_1_hidden);
            if let Some(aux) = &o.aux {
                for &v in aux
                    .delta_w
                    .iter()
                    .chain(aux.delta_z.iter())
                    .chain(aux.delta_c.iter())
                {
                    out.extend_from_slice(&v.to_le_bytes());
                }
            }
            for arr in o
                .r_poly_without_b
                .iter()
                .chain(o.alpha.iter())
                .chain(o.beta.iter())
            {
                for &limb in arr {
                    out.extend_from_slice(&limb.to_le_bytes());
                }
            }
        }
        debug_assert_eq!(out.len(), total_bytes);
        Ok(out)
    }

    /// Alias for [`Self::to_compact_wire_bytes`].
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, BlindVcError> {
        self.to_compact_wire_bytes()
    }

    /// Deserialize a [`SelectiveDisclosurePresentation`] from [`Self::to_compact_wire_bytes`],
    /// validating magic, bounds, canonical Goldilocks field limbs, and exact payload length
    /// before allocating per-repetition buffers.
    pub fn from_compact_wire_bytes(bytes: &[u8]) -> Result<Self, BlindVcError> {
        fn take<'a>(cur: &mut &'a [u8], n: usize) -> Result<&'a [u8], BlindVcError> {
            if cur.len() < n {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            let (head, tail) = cur.split_at(n);
            *cur = tail;
            Ok(head)
        }
        fn take_32(cur: &mut &[u8]) -> Result<[u8; 32], BlindVcError> {
            let s = take(cur, 32)?;
            let mut out = [0u8; 32];
            out.copy_from_slice(s);
            Ok(out)
        }
        fn take_u32(cur: &mut &[u8]) -> Result<u32, BlindVcError> {
            let s = take(cur, 4)?;
            Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
        }
        fn take_u64(cur: &mut &[u8]) -> Result<u64, BlindVcError> {
            let s = take(cur, 8)?;
            let mut b = [0u8; 8];
            b.copy_from_slice(s);
            Ok(u64::from_le_bytes(b))
        }
        fn take_gl(cur: &mut &[u8]) -> Result<u64, BlindVcError> {
            let v = take_u64(cur)?;
            if !gl_is_canonical(v) {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            Ok(v)
        }
        fn take_fp5(cur: &mut &[u8]) -> Result<[u64; 5], BlindVcError> {
            Ok([
                take_gl(cur)?,
                take_gl(cur)?,
                take_gl(cur)?,
                take_gl(cur)?,
                take_gl(cur)?,
            ])
        }

        let mut cur = bytes;
        let magic = take(&mut cur, 24)?;
        if !ct_eq_bytes(magic, SD_COMPACT_WIRE_MAGIC) {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        let arity_u64 = take_u64(&mut cur)?;
        if !(1..=MAX_VC_ATTRS as u64).contains(&arity_u64) {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        let arity = arity_u64 as usize;
        let verifier_challenge = take_32(&mut cur)?;
        let mode_tag = take(&mut cur, 1)?[0];
        let mode = match mode_tag {
            0 => PresentationMode::UnlinkableFresh,
            1 => PresentationMode::ScopedPseudonym(take_32(&mut cur)?),
            _ => return Err(BlindVcError::SelectiveDisclosureProofInvalid),
        };
        let presentation_nonce = take_32(&mut cur)?;
        let issuer_epoch = take_u64(&mut cur)?;
        let schema_id = take_u64(&mut cur)?;
        let mut accumulator_root = [0u64; 6];
        for slot in &mut accumulator_root {
            *slot = take_gl(&mut cur)?;
        }
        let issuer_root_tag = take_32(&mut cur)?;
        let mut verifier_scope_limbs = [0u64; 4];
        for slot in &mut verifier_scope_limbs {
            *slot = take_gl(&mut cur)?;
        }
        let disclosed_count = take_u32(&mut cur)? as usize;
        if disclosed_count > arity {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        let mut disclosed_attrs = Vec::with_capacity(disclosed_count);
        let mut prev_idx: Option<usize> = None;
        for _ in 0..disclosed_count {
            let idx = take_u32(&mut cur)? as usize;
            let val = take_gl(&mut cur)?;
            if idx >= arity || prev_idx.is_some_and(|p| idx <= p) {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            prev_idx = Some(idx);
            disclosed_attrs.push((idx, val));
        }
        let mut pres_commit = [0u64; 6];
        for slot in &mut pres_commit {
            *slot = take_gl(&mut cur)?;
        }
        let mut scope_tag = [0u64; 6];
        for slot in &mut scope_tag {
            *slot = take_gl(&mut cur)?;
        }
        let num_reps = take_u32(&mut cur)? as usize;
        if num_reps != ZkSoundnessProfile::Classical128.sd_repetitions()
            && num_reps != ZkSoundnessProfile::Quantum128.sd_repetitions()
        {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }

        let num_secret_wires =
            (arity - disclosed_count) + 4 + 4 + VC_ACCUMULATOR_DEPTH + 6 * VC_ACCUMULATOR_DEPTH;
        let base_rep_tail = VC_SD_GGM_DEPTH * 32 + 32 + (SD_RPOLY_COEFFS + 2 * SD_GRID_L) * 40;
        let aux_bytes = (num_secret_wires + SD_TOTAL_GATES + 5) * 8;

        let mut opened_reps = Vec::with_capacity(num_reps);
        for _ in 0..num_reps {
            let hidden_party = take(&mut cur, 1)?[0];
            let is_last_hidden = (hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1;
            let needed = base_rep_tail + if is_last_hidden { 0 } else { aux_bytes };
            if cur.len() < needed {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            let mut ggm_copath = [[0u8; 32]; VC_SD_GGM_DEPTH];
            for node in &mut ggm_copath {
                *node = take_32(&mut cur)?;
            }
            let com_1_hidden = take_32(&mut cur)?;
            let aux = if is_last_hidden {
                None
            } else {
                let mut delta_w = Vec::with_capacity(num_secret_wires);
                for _ in 0..num_secret_wires {
                    delta_w.push(take_gl(&mut cur)?);
                }
                let mut delta_z = Vec::with_capacity(SD_TOTAL_GATES);
                for _ in 0..SD_TOTAL_GATES {
                    delta_z.push(take_gl(&mut cur)?);
                }
                let delta_c = take_fp5(&mut cur)?;
                Some(LimboPartyAux {
                    delta_w,
                    delta_z,
                    delta_c,
                })
            };
            let mut r_poly_without_b = Vec::with_capacity(SD_RPOLY_COEFFS);
            for _ in 0..SD_RPOLY_COEFFS {
                r_poly_without_b.push(take_fp5(&mut cur)?);
            }
            let mut alpha = Vec::with_capacity(SD_GRID_L);
            for _ in 0..SD_GRID_L {
                alpha.push(take_fp5(&mut cur)?);
            }
            let mut beta = Vec::with_capacity(SD_GRID_L);
            for _ in 0..SD_GRID_L {
                beta.push(take_fp5(&mut cur)?);
            }
            opened_reps.push(OpenedLimboRepetition {
                hidden_party,
                ggm_copath,
                com_1_hidden,
                aux,
                r_poly_without_b,
                alpha,
                beta,
            });
        }
        if !cur.is_empty() {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        Ok(Self {
            arity,
            verifier_challenge,
            mode,
            presentation_nonce,
            issuer_epoch,
            schema_id,
            accumulator_root,
            issuer_root_tag,
            verifier_scope_limbs,
            disclosed_attrs,
            pres_commit,
            scope_tag,
            opened_reps,
        })
    }

    /// Alias for [`Self::from_compact_wire_bytes`].
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, BlindVcError> {
        Self::from_compact_wire_bytes(bytes)
    }
}
