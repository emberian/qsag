//! Persistent vault enrollment and reserve-before-sign state.
//!
//! A missing/replaced lock or interrupted two-file update fails closed. This is local
//! crash protection, not protection against restoring an entire vault backup.
use crate::cli::{CliError, ZeroizingBuf, replace_secret, sync_parent};
use crate::codec::Json;
use qsag_accel::keccak::cshake256_framed_32;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
// Independently opened descriptors contend on the same OS inode lock, including
// threads and path aliases. Unrelated vaults do not share a process-wide mutex.

pub fn corrupt() -> CliError {
    CliError::state("CorruptOrMissingVaultState")
}

pub struct Vault {
    file: File,
    path: String,
    key_material: Option<ZeroizingBuf>,
}

#[cfg(unix)]
fn identity(meta: &std::fs::Metadata) -> (u64, u64) {
    use std::os::unix::fs::MetadataExt;
    (meta.dev(), meta.ino())
}

impl Vault {
    #[cfg(not(unix))]
    pub fn acquire(_secret: &str, _create: bool) -> Result<Self, CliError> {
        Err(CliError::state(
            "vault enrollment requires Unix file identity support",
        ))
    }

    #[cfg(unix)]
    pub fn acquire(secret: &str, create: bool) -> Result<Self, CliError> {
        use std::os::unix::fs::OpenOptionsExt;
        let path = format!("{secret}.vault.lock");
        let before = if create {
            None
        } else {
            let m = std::fs::symlink_metadata(&path).map_err(|_| corrupt())?;
            if !m.is_file() {
                return Err(corrupt());
            }
            Some(m)
        };
        let mut options = OpenOptions::new();
        options
            .read(true)
            .write(true)
            .create_new(create)
            .mode(0o600);
        crate::cli::set_nofollow_nonblocking(&mut options)?;
        let file = options.open(&path).map_err(|e| {
            if create {
                CliError::io("enrolling vault lock", e)
            } else {
                corrupt()
            }
        })?;
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            match file.try_lock() {
                Ok(()) => break,
                Err(std::fs::TryLockError::WouldBlock) if std::time::Instant::now() < deadline => {
                    std::thread::sleep(std::time::Duration::from_millis(10))
                }
                Err(_) => return Err(CliError::state("vault lock unavailable")),
            }
        }
        let vault = Self {
            file,
            path,
            key_material: None,
        };
        vault.check_path()?;
        let opened = vault.file.metadata().map_err(|_| corrupt())?;
        if before.is_some_and(|m| identity(&m) != identity(&opened)) {
            return Err(corrupt());
        }
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
        #[cfg(unix)]
        {
            let named = std::fs::symlink_metadata(&self.path).map_err(|_| corrupt())?;
            let opened = self.file.metadata().map_err(|_| corrupt())?;
            if !named.is_file() || identity(&named) != identity(&opened) {
                return Err(corrupt());
            }
            Ok(())
        }
        #[cfg(not(unix))]
        {
            Err(corrupt())
        }
    }

    pub fn set_key_material(&mut self, opened: &Json) -> Result<(), CliError> {
        let material = opened
            .get("seed")
            .or_else(|| opened.get("secret_key"))
            .and_then(Json::as_str)
            .ok_or_else(corrupt)?;
        self.key_material = Some(ZeroizingBuf(material.as_bytes().to_vec()));
        Ok(())
    }

    pub fn bind(&self, secret: &mut Json) -> Result<(), CliError> {
        #[cfg(unix)]
        {
            let (dev, ino) = identity(&self.file.metadata().map_err(|_| corrupt())?);
            set(secret, "vault_device", Json::num(dev));
            set(secret, "vault_inode", Json::num(ino));
        }
        self.check_path()
    }

    pub fn authenticate(&mut self, secret: &Json) -> Result<(), CliError> {
        self.check_path()?;
        #[cfg(unix)]
        {
            let (dev, ino) = identity(&self.file.metadata().map_err(|_| corrupt())?);
            if secret.field_u64("vault_device").map_err(|_| corrupt())? != dev
                || secret.field_u64("vault_inode").map_err(|_| corrupt())? != ino
            {
                return Err(corrupt());
            }
        }
        let expected = crate::cli::Secret32(tag(secret, self.key_material.as_deref())?);
        let recorded = secret.field_hex("state_mac").map_err(|_| corrupt())?;
        let mut companion = crate::cli::Secret32([0u8; 32]);
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
        set(
            secret,
            "state_mac",
            Json::hex(&tag(secret, self.key_material.as_deref())?),
        );
        Ok(())
    }

    pub fn seal(&mut self, secret: &mut Json) -> Result<(), CliError> {
        self.check_path()?;
        let mac = tag(secret, self.key_material.as_deref())?;
        set(secret, "state_mac", Json::hex(&mac));
        self.file
            .seek(SeekFrom::Start(0))
            .and_then(|_| self.file.write_all(&mac))
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
        let bytes = ZeroizingBuf(secret.to_pretty().into_bytes());
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
    let generation = secret
        .field_u64("ledger_checkpoint_gen")
        .map_err(|_| corrupt())?;
    let tag_str = secret
        .field_str("ledger_checkpoint_tag")
        .map_err(|_| corrupt())?;
    let tag: [u8; 32] =
        crate::codec::from_hex_exact(tag_str, "ledger_checkpoint_tag").map_err(|_| corrupt())?;
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
    let mut unsigned = secret.clone();
    if let Json::Object(fields) = &mut unsigned {
        fields.retain(|(name, _)| name != "state_mac");
    }
    let encoded = ZeroizingBuf(unsigned.to_pretty().into_bytes());
    Ok(cshake256_framed_32(
        b"QSAG.CLI.VAULT.MAC.V1",
        &[material, &nonce, &encoded.0],
    ))
}
