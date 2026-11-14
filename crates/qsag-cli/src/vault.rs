//! Persistent vault enrollment and reserve-before-sign state.
//!
//! A missing/replaced lock or interrupted two-file update fails closed. This is local
//! crash protection, not protection against restoring an entire vault backup.
use crate::cli::{CliError, ZeroizingBuf, replace_secret, sync_parent};
use crate::codec::Json;
use qsag_accel::keccak::cshake256_framed_32;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::sync::{Mutex, MutexGuard};

// Deliberately serialize all local vault operations, including aliases of the same
// inode. OS locks on independently opened descriptors provide cross-process exclusion.
static LOCAL_VAULTS: Mutex<()> = Mutex::new(());

pub fn corrupt() -> CliError {
    CliError::state("CorruptOrMissingVaultState")
}

pub struct Vault {
    file: File,
    path: String,
    _local: MutexGuard<'static, ()>,
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
        let local = LOCAL_VAULTS.lock().map_err(|_| corrupt())?;
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
        // Also verify descriptors and paths below, on every supported Unix.
        #[cfg(target_os = "linux")]
        options.custom_flags(0x20000); // O_NOFOLLOW
        #[cfg(target_os = "macos")]
        options.custom_flags(0x100); // O_NOFOLLOW
        let file = options.open(&path).map_err(|e| {
            if create {
                CliError::io("enrolling vault lock", e)
            } else {
                corrupt()
            }
        })?;
        file.lock().map_err(|e| CliError::io("locking vault", e))?;
        let vault = Self {
            file,
            path,
            _local: local,
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
        let expected = tag(secret)?;
        let recorded = secret.field_hex("state_mac").map_err(|_| corrupt())?;
        let mut companion = [0u8; 32];
        if self.file.metadata().map_err(|_| corrupt())?.len() != 32 {
            return Err(corrupt());
        }
        self.file
            .seek(SeekFrom::Start(0))
            .and_then(|_| self.file.read_exact(&mut companion))
            .map_err(|_| corrupt())?;
        if recorded.len() != 32
            || recorded
                .iter()
                .zip(expected)
                .fold(0u8, |d, (a, b)| d | (a ^ b))
                != 0
            || companion
                .iter()
                .zip(expected)
                .fold(0u8, |d, (a, b)| d | (a ^ b))
                != 0
        {
            return Err(corrupt());
        }
        Ok(())
    }

    pub fn seal(&mut self, secret: &mut Json) -> Result<(), CliError> {
        self.check_path()?;
        let mac = tag(secret)?;
        set(secret, "state_mac", Json::hex(&mac));
        self.file
            .seek(SeekFrom::Start(0))
            .and_then(|_| self.file.write_all(&mac))
            .and_then(|_| self.file.sync_all())
            .map_err(|e| CliError::io("syncing vault state", e))
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

fn tag(secret: &Json) -> Result<[u8; 32], CliError> {
    let material = secret
        .get("seed")
        .or_else(|| secret.get("secret_key"))
        .and_then(Json::as_str)
        .ok_or_else(corrupt)?;
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
        &[material.as_bytes(), &nonce, &encoded.0],
    ))
}
