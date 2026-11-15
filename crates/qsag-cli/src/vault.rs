//! Persistent vault enrollment and reserve-before-sign state.
//!
//! A missing/replaced lock or interrupted two-file update fails closed. This is local
//! crash protection, not protection against restoring an entire vault backup.
use crate::cli::{CliError, ZeroizingBuf, replace_secret, sync_parent};
use crate::codec::Json;
use crate::persist;
use qsag_accel::keccak::cshake256_framed_32;
use std::fs::File;
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::path::Path;

pub fn corrupt() -> CliError {
    CliError::state("CorruptOrMissingVaultState")
}

pub struct Vault {
    file: File,
    path: String,
    key_material: Option<ZeroizingBuf>,
}

impl Vault {
    pub fn acquire(secret: &str, create: bool) -> Result<Self, CliError> {
        let path = format!("{secret}.vault.lock");
        let (file, _) =
            persist::acquire_lock(Path::new(&path), create).map_err(|e| match e.kind() {
                ErrorKind::WouldBlock => CliError::state("vault lock unavailable"),
                ErrorKind::InvalidData => corrupt(),
                _ if create => CliError::io("enrolling vault lock", e),
                _ => corrupt(),
            })?;
        let vault = Self {
            file,
            path,
            key_material: None,
        };
        if create {
            vault
                .file
                .sync_all()
                .map_err(|e| CliError::io("syncing lock", e))?;
            sync_parent(&vault.path)?;
        }
        Ok(vault)
    }

    fn check_path(&self) -> Result<(), CliError> {
        persist::verify_held(&self.file, Path::new(&self.path), true)
            .map(|_| ())
            .map_err(|_| corrupt())
    }

    /// Key the state MAC with the opened secret, so a sealed file's MAC needs its passphrase.
    pub fn set_key_material(&mut self, opened: &crate::envelope::OpenedSecret) {
        self.key_material = Some(opened.vault_key_material());
    }

    pub fn bind(&self, secret: &mut Json) -> Result<(), CliError> {
        #[cfg(unix)]
        {
            let (dev, ino) = persist::file_identity(&self.file.metadata().map_err(|_| corrupt())?);
            set(secret, "vault_device", Json::num(dev));
            set(secret, "vault_inode", Json::num(ino));
        }
        self.check_path()
    }

    pub fn authenticate(&mut self, secret: &Json) -> Result<(), CliError> {
        self.check_path()?;
        #[cfg(unix)]
        {
            let (dev, ino) = persist::file_identity(&self.file.metadata().map_err(|_| corrupt())?);
            if secret.field_u64("vault_device").map_err(|_| corrupt())? != dev
                || secret.field_u64("vault_inode").map_err(|_| corrupt())? != ino
            {
                return Err(corrupt());
            }
        }
        let expected = crate::cli::Secret32::new(tag(
            secret,
            self.key_material.as_deref().map(Vec::as_slice),
        )?);
        let recorded = secret.field_hex("state_mac").map_err(|_| corrupt())?;
        let mut companion = crate::cli::Secret32::new([0u8; 32]);
        if self.file.metadata().map_err(|_| corrupt())?.len() != 32 {
            return Err(corrupt());
        }
        self.file
            .seek(SeekFrom::Start(0))
            .and_then(|_| self.file.read_exact(&mut companion.0))
            .map_err(|_| corrupt())?;
        if recorded.len() != 32
            || !qsag_accel::ct::ct_eq_bytes(&recorded, &expected.0)
            || !qsag_accel::ct::ct_eq_bytes(&companion.0, &expected.0)
        {
            return Err(corrupt());
        }
        Ok(())
    }

    pub fn prepare(&self, secret: &mut Json) -> Result<(), CliError> {
        self.check_path()?;
        let mac = crate::cli::Secret32::new(tag(
            secret,
            self.key_material.as_deref().map(Vec::as_slice),
        )?);
        set(secret, "state_mac", Json::hex(&mac.0));
        Ok(())
    }

    pub fn seal(&mut self, secret: &mut Json) -> Result<(), CliError> {
        self.check_path()?;
        let mac = crate::cli::Secret32::new(tag(
            secret,
            self.key_material.as_deref().map(Vec::as_slice),
        )?);
        set(secret, "state_mac", Json::hex(&mac.0));
        self.file
            .seek(SeekFrom::Start(0))
            .and_then(|_| self.file.write_all(&mac.0))
            .and_then(|_| self.file.sync_all())
            .map_err(|e| CliError::io("syncing vault state", e))?;
        self.check_path()
    }

    pub fn reserve(&mut self, path: &str, secret: &mut Json) -> Result<(), CliError> {
        let used = secret
            .field_u64("uses_completed")?
            .checked_add(1)
            .ok_or_else(corrupt)?;
        set(secret, "uses_completed", Json::num(used));
        self.seal(secret)?;
        let bytes = ZeroizingBuf::new(secret.to_pretty().into_bytes());
        replace_secret(path, &bytes.0)?;
        self.check_path()
    }
}

pub fn set(json: &mut Json, name: &str, value: Json) {
    if let Json::Object(fields) = json {
        if let Some((_, old)) = fields.iter_mut().find(|(k, _)| k == name) {
            *old = value;
        } else {
            fields.push((name.to_owned(), value));
        }
    }
}

pub fn record_ledger_checkpoint(secret: &mut Json, ckpt: qsag_core::LedgerCheckpoint) {
    set(secret, "ledger_checkpoint_gen", Json::num(ckpt.generation));
    set(secret, "ledger_checkpoint_tag", Json::hex(&ckpt.tag));
}

pub fn read_ledger_checkpoint(secret: &Json) -> Result<qsag_core::LedgerCheckpoint, CliError> {
    read_named_checkpoint(secret, "ledger_checkpoint_gen", "ledger_checkpoint_tag")
}

pub fn record_ceremony_checkpoint(secret: &mut Json, ckpt: qsag_core::LedgerCheckpoint) {
    set(
        secret,
        "ceremony_checkpoint_gen",
        Json::num(ckpt.generation),
    );
    set(secret, "ceremony_checkpoint_tag", Json::hex(&ckpt.tag));
}

pub fn read_ceremony_checkpoint(secret: &Json) -> Result<qsag_core::LedgerCheckpoint, CliError> {
    read_named_checkpoint(secret, "ceremony_checkpoint_gen", "ceremony_checkpoint_tag")
}

pub fn record_belt_checkpoint(secret: &mut Json, ckpt: qsag_core::LedgerCheckpoint) {
    set(secret, "belt_checkpoint_gen", Json::num(ckpt.generation));
    set(secret, "belt_checkpoint_tag", Json::hex(&ckpt.tag));
}

pub fn read_belt_checkpoint(secret: &Json) -> Result<qsag_core::LedgerCheckpoint, CliError> {
    read_named_checkpoint(secret, "belt_checkpoint_gen", "belt_checkpoint_tag")
}

fn read_named_checkpoint(
    secret: &Json,
    gen_field: &str,
    tag_field: &str,
) -> Result<qsag_core::LedgerCheckpoint, CliError> {
    let generation = secret.field_u64(gen_field).map_err(|_| corrupt())?;
    let tag_str = secret.field_str(tag_field).map_err(|_| corrupt())?;
    let tag: [u8; 32] = crate::codec::from_hex_exact(tag_str, tag_field).map_err(|_| corrupt())?;
    Ok(qsag_core::LedgerCheckpoint { generation, tag })
}

fn tag(secret: &Json, key_material: Option<&[u8]>) -> Result<[u8; 32], CliError> {
    let material = secret
        .get("seed")
        .or_else(|| secret.get("secret_key"))
        .and_then(Json::as_str)
        .ok_or_else(corrupt)?;
    let material = match key_material {
        Some(key) => key,
        None if secret.get("envelope").is_some() => return Err(corrupt()),
        None => material.as_bytes(),
    };
    let nonce = secret
        .field_hex("enrollment_nonce")
        .map_err(|_| corrupt())?;
    if nonce.len() != 16 {
        return Err(corrupt());
    }
    let encoded = persist::authenticated_bytes(secret, &["state_mac"]);
    Ok(cshake256_framed_32(
        b"QSAG.CLI.VAULT.MAC.V1",
        &[material, &nonce, &encoded.0],
    ))
}
