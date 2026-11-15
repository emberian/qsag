//! `qsag quorum coupon`: a Baggy root key, volatile one-time coupons minted under it, and
//! the stateless signatures they produce (`qsag_quorum::volatile_coupon`).
//!
//! Coupon shares exist only in locked memory of the process that minted them: the library
//! has no share-table export and no deterministic remint. Minting and signing are therefore
//! one command, `session`, which mints a batch and then signs requests read from standard
//! input until it ends. Only the root key and the finished signatures touch a disk.

const COUPON_HELP: &str = "\
qsag quorum coupon <keygen|session|verify> [options]

Volatile coupons: a dealerless 2-of-3 Baggy root key certifies one-time WOTS+C coupons that
are minted into locked memory. A coupon signs one message; the result verifies against the
root public key alone, with no state, until the coupon expires. 64-bit Linux only.

subcommands:
  keygen   generate the Baggy root key shares (--vault-dir) and write --public-out
  session  mint a batch of coupons, then sign the requests arriving on standard input
  verify   verify a coupon signature against --public and --in
";

#[cfg(not(all(target_os = "linux", target_pointer_width = "64")))]
pub fn run(raw: &[String]) -> Result<(), crate::cli::CliError> {
    if matches!(
        raw.first().map(String::as_str),
        Some("--help" | "-h" | "help")
    ) {
        print!("{COUPON_HELP}");
        return Ok(());
    }
    Err(crate::cli::CliError::usage(
        "quorum coupon requires 64-bit Linux (locked, fork-wiped memory for coupon shares)",
    ))
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
pub use linux::run;

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
mod linux {
    use std::io::{BufRead, Write};
    use std::path::Path;
    use std::time::{Instant, SystemTime, UNIX_EPOCH};

    use qsag_core::baggy::{BaggyParams, BaggyPublicKey, WaistbandCache, baggy_keygen_mpc};
    use qsag_core::keccak_mpc::run_dealerless_rss_dkg_2of3;
    use qsag_core::preprocessing::PartyPrivateRng;
    use qsag_core::rss256::Rss256Engine;
    use qsag_quorum::quorum_jorts::grind;
    use qsag_quorum::volatile_coupon::mint::{
        AuthenticatedWaistband, MintPlan, PendingCouponBatch,
    };
    use qsag_quorum::volatile_coupon::{
        BaggySig, CertifiedCoupon, CouponError, CouponPool, InitiatorKey, LockedBytes,
        ProtectedMintProcess, SHARE_BYTES, SignRequest, baggy_verify, combine,
    };

    use super::COUPON_HELP;
    use crate::cli::{
        Args, CliError, MAX_MSG_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, exit,
        os_random_32, private_dir, read_bounded_file, read_input, read_text, write_new,
    };
    use crate::codec::{Json, from_hex_exact, to_hex};
    use crate::quorum::ensure_absent;

    const SCHEME_NAME: &str = "baggy-volatile-coupon";
    const ROOT_PUBLIC_FORMAT: &str = "qsag-quorum-coupon-root-v1";
    const ROOT_PARTY_FORMAT: &str = "qsag-quorum-coupon-root-party-v1";
    const SESSION_FORMAT: &str = "qsag-quorum-coupon-session-v1";
    const SIG_FORMAT: &str = "qsag-quorum-coupon-signature-v1";
    const DEFAULT_PARAMS: &str = "sha3-128f";
    const DKG_RNG_LABEL: &[u8] = b"QSAG.CLI.QUORUM.COUPON.ROOT.DKG.RNG.V1";
    const ENGINE_RNG_LABEL: &[u8] = b"QSAG.CLI.QUORUM.COUPON.ROOT.ENGINE.RNG.V1";
    /// `PendingCouponBatch::mint` refuses a batch whose share tables exceed this.
    const MAX_BATCH_SHARE_BYTES: usize = 256 * 1024 * 1024;
    const MAX_WAISTBAND_LAYERS: u64 = 4;
    const WAISTBAND_ENTRIES: usize = 1024;
    const MAX_REQUEST_LINE_BYTES: usize = 64 * 1024;

    const KEYGEN_HELP: &str = "\
qsag quorum coupon keygen --vault-dir <dir> --public-out <path> [options]

Run a dealerless 2-of-3 RSS key generation for a Baggy root key. The root key is stateless:
it certifies coupons in every later session and nothing about it is updated on disk.

  --vault-dir <dir>     private 0700 directory for coupon-root-party-{0,1,2}.sk
  --public-out <path>   destination for the root public key JSON
  --params <name>       sha3-128f (PORS+FP, default)
  --passphrase-env <VAR> / --passphrase-file <PATH>  seal each party seed
  --json                emit the public key JSON to stdout
";

    const SESSION_HELP: &str = "\
qsag quorum coupon session --vault-dir <dir> --members <i,j,..> --coupons <n> --ttl-secs <s>

Mint <n> one-time coupons into locked memory, certify each under the root key, print the
batch as one JSON object, then sign the requests read from standard input until it ends.
Coupon shares never leave this process and are gone when it exits: a coupon that was not
used is lost, not saved. Every member of --members holds a share of every coupon and all of
them open it; the root certificate is signed by the 2-of-3 root key. All custodians run
inside this one process.

  --vault-dir <dir>         directory holding coupon-root-party-{0,1,2}.sk
  --members <i,j,..>        the coupon's fixed subset: at least two increasing party indices
  --parties <n>             size of the roster the indices refer to (default 3)
  --coupons <n>             coupons to mint; each takes about a minute of MPC, more for a
                            larger subset
  --ttl-secs <s>            lifetime: coupons and their signatures expire s seconds from now;
                            the time spent minting counts against it
  --waistband-layers <0..4> top root layers to precompute and cache in memory (default 0);
                            worth its cost only for batches of a dozen coupons or more
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock sealed party seeds

Requests, one JSON object per line:
  {\"coupon\": <index in the batch>, \"message\": \"<path>\", \"out\": \"<signature path>\"}
Each gets one JSON object on stdout with \"ok\": true or false. A coupon opens once: a
second request for it is refused, whatever the message. A refused request does not end the
session; the exit code is that of the first refusal (4 for a spent or expired coupon).
";

    const VERIFY_HELP: &str = "\
qsag quorum coupon verify --public <path> --in <file|-> --sig <path> [--json]

Verify a coupon signature against the root public key: the root certificate, the expiry and
the one-time opening on the message. Exits 0 when valid and 2 when verification fails; a
signature stops verifying when its coupon expires.
";

    pub fn run(raw: &[String]) -> Result<(), CliError> {
        let Some((sub, rest)) = raw.split_first() else {
            eprint!("{COUPON_HELP}");
            return Err(CliError::usage(
                "quorum coupon expects a subcommand (keygen, session, verify)",
            ));
        };
        match sub.as_str() {
            "--help" | "-h" | "help" => {
                print!("{COUPON_HELP}");
                Ok(())
            }
            "keygen" => keygen(rest),
            "session" => session(rest),
            "verify" => verify(rest),
            other => Err(CliError::usage(format!(
                "unknown quorum coupon subcommand '{other}' (try 'qsag quorum coupon --help')"
            ))),
        }
    }

    fn params_by_name(name: &str) -> Result<BaggyParams, CliError> {
        match name {
            "sha3-128f" => Ok(BaggyParams::SHA3_128F),
            other => Err(CliError::usage(format!(
                "unknown coupon root parameters '{other}' (expected sha3-128f)"
            ))),
        }
    }

    fn coupon_error(what: &str, err: CouponError) -> CliError {
        let code = match err {
            CouponError::InvalidParameters | CouponError::InvalidCodeword => exit::USAGE,
            CouponError::MemoryProtection | CouponError::Entropy | CouponError::Clock => exit::IO,
            CouponError::Forked
            | CouponError::Authentication
            | CouponError::Certificate
            | CouponError::Expired
            | CouponError::AlreadyInstalled
            | CouponError::MissingOrSpent
            | CouponError::InvalidOpenings
            | CouponError::Staging => exit::STATE_CONFLICT,
        };
        CliError::new(code, format!("{what}: {err}"))
    }

    fn protect() -> Result<ProtectedMintProcess, CliError> {
        ProtectedMintProcess::enable().map_err(|e| {
            CliError::new(
                exit::IO,
                format!(
                    "locking process memory and disabling core dumps failed ({e}); \
                     raise RLIMIT_MEMLOCK (ulimit -l unlimited) for this command"
                ),
            )
        })
    }

    fn party_path(vault_dir: &str, party: usize) -> String {
        Path::new(vault_dir)
            .join(format!("coupon-root-party-{party}.sk"))
            .to_string_lossy()
            .into_owned()
    }

    /// The root engine over the key shares the three party seeds determine, and its
    /// `pk_seed`. The engine's own randomness is fresh.
    fn root_engine(
        dkg_session_id: [u8; 32],
        seeds: &[Secret32; 3],
    ) -> Result<(Rss256Engine, [u8; 32]), CliError> {
        let mut dkg_rngs: [PartyPrivateRng; 3] =
            std::array::from_fn(|p| PartyPrivateRng::from_seed(seeds[p].0, DKG_RNG_LABEL));
        let (shares, pk_seed) = run_dealerless_rss_dkg_2of3(dkg_session_id, 32, &mut dkg_rngs)
            .map_err(|e| CliError::state(format!("dealerless 2-of-3 root DKG failed: {e}")))?;
        let engine_rngs = [
            PartyPrivateRng::from_seed(os_random_32()?, ENGINE_RNG_LABEL),
            PartyPrivateRng::from_seed(os_random_32()?, ENGINE_RNG_LABEL),
            PartyPrivateRng::from_seed(os_random_32()?, ENGINE_RNG_LABEL),
        ];
        let engine = Rss256Engine::new(os_random_32()?, shares, engine_rngs)
            .map_err(|e| CliError::state(format!("initializing 2-of-3 MPC engine failed: {e}")))?;
        Ok((engine, pk_seed))
    }

    fn public_json(params_name: &str, pk: &BaggyPublicKey) -> Json {
        Json::object(vec![
            ("format", Json::str(ROOT_PUBLIC_FORMAT)),
            ("scheme", Json::str(SCHEME_NAME)),
            ("custody_model", Json::str("dealerless-2of3-rss-baggy-root")),
            ("params", Json::str(params_name)),
            ("pk_seed", Json::hex(&pk.pk_seed)),
            ("pk_root", Json::hex(&pk.pk_root)),
        ])
    }

    fn keygen(raw: &[String]) -> Result<(), CliError> {
        let args = Args::parse(
            raw,
            &[
                "vault-dir",
                "public-out",
                "params",
                "passphrase-env",
                "passphrase-file",
            ],
            &["json", "help"],
        )?;
        if args.flag("help") {
            print!("{KEYGEN_HELP}");
            return Ok(());
        }
        args.no_positionals()?;
        let vault_dir = args.require("vault-dir")?;
        let public_out = args.require("public-out")?;
        let params_name = args.get("params").unwrap_or(DEFAULT_PARAMS);
        let params = params_by_name(params_name)?;
        let passphrase = crate::envelope::passphrase(&args)?;

        ensure_absent(public_out)?;
        private_dir(vault_dir, true)?;
        let paths: [String; 3] = std::array::from_fn(|p| party_path(vault_dir, p));
        for path in &paths {
            ensure_absent(path)?;
        }

        let _protection = protect()?;
        let dkg_session_id = os_random_32()?;
        let seeds = [
            Secret32::new(os_random_32()?),
            Secret32::new(os_random_32()?),
            Secret32::new(os_random_32()?),
        ];
        let (mut engine, pk_seed) = root_engine(dkg_session_id, &seeds)?;
        let (pk, _binding) =
            baggy_keygen_mpc(&mut engine, &params, &mut WaistbandCache::disabled())
                .map_err(|e| CliError::state(format!("distributed Baggy keygen failed: {e}")))?;
        if pk.pk_seed != pk_seed {
            return Err(CliError::state("Baggy root pk_seed differs from the DKG"));
        }

        for (party, path) in paths.iter().enumerate() {
            let mut secret = Json::object(vec![
                ("format", Json::str(ROOT_PARTY_FORMAT)),
                ("scheme", Json::str(SCHEME_NAME)),
                ("params", Json::str(params_name)),
                ("party_id", Json::num(party)),
                ("dkg_session_id", Json::hex(&dkg_session_id)),
                ("pk_seed", Json::hex(&pk.pk_seed)),
                ("pk_root", Json::hex(&pk.pk_root)),
                ("seed", Json::hex(&seeds[party].0)),
            ]);
            if let Some(pass) = &passphrase {
                crate::envelope::seal(&mut secret, pass)?;
            }
            let encoded = ZeroizingBuf::new(secret.to_pretty().into_bytes());
            write_new(path, &encoded.0, true)?;
        }
        let public = public_json(params_name, &pk);
        write_new(public_out, public.to_pretty().as_bytes(), false)?;

        if args.flag("json") {
            print!("{}", public.to_pretty());
        } else {
            println!(
                "generated 2-of-3 Baggy coupon root ({params_name}) in {vault_dir} -> {public_out}"
            );
        }
        Ok(())
    }

    struct Root {
        params_name: String,
        params: BaggyParams,
        pk: BaggyPublicKey,
        dkg_session_id: [u8; 32],
        seeds: [Secret32; 3],
    }

    fn load_root(vault_dir: &str, passphrase: Option<&[u8]>) -> Result<Root, CliError> {
        private_dir(vault_dir, false)?;
        let mut header: Option<(String, [u8; 32], BaggyPublicKey)> = None;
        let mut seeds = [
            Secret32::new([0; 32]),
            Secret32::new([0; 32]),
            Secret32::new([0; 32]),
        ];
        for (party, seed) in seeds.iter_mut().enumerate() {
            let path = party_path(vault_dir, party);
            let text = read_text(&path)?;
            let json = Json::parse(&text)?;
            if json.field_str("format")? != ROOT_PARTY_FORMAT
                || json.field_str("scheme")? != SCHEME_NAME
                || json.field_u64("party_id")? != party as u64
            {
                return Err(CliError::input(format!(
                    "{path} is not coupon root party {party}"
                )));
            }
            let this = (
                json.field_str("params")?.to_owned(),
                from_hex_exact(json.field_str("dkg_session_id")?, "dkg_session_id")?,
                BaggyPublicKey {
                    pk_seed: from_hex_exact(json.field_str("pk_seed")?, "pk_seed")?,
                    pk_root: from_hex_exact(json.field_str("pk_root")?, "pk_root")?,
                },
            );
            match &header {
                None => header = Some(this),
                Some(first) if *first == this => {}
                Some(_) => {
                    return Err(CliError::state(format!(
                        "{path} belongs to a different coupon root than party 0"
                    )));
                }
            }
            *seed = crate::envelope::open(&json, passphrase)?.seed()?;
        }
        let (params_name, dkg_session_id, pk) =
            header.ok_or_else(|| CliError::state("no coupon root party file"))?;
        Ok(Root {
            params: params_by_name(&params_name)?,
            params_name,
            pk,
            dkg_session_id,
            seeds,
        })
    }

    fn parse_members(text: &str, parties: usize) -> Result<Vec<u32>, CliError> {
        let members = text
            .split(',')
            .map(|item| item.trim().parse::<u32>())
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| CliError::usage("--members must be comma-separated party indices"))?;
        if members.len() < 2
            || members.windows(2).any(|w| w[0] >= w[1])
            || members.iter().any(|&m| u64::from(m) >= parties as u64)
        {
            return Err(CliError::usage(
                "--members needs at least two strictly increasing indices below --parties",
            ));
        }
        Ok(members)
    }

    /// `count` handles on one fresh 32-byte request key, each in its own locked mapping.
    fn initiator_keys(count: usize) -> Result<Vec<InitiatorKey>, CouponError> {
        let master = LockedBytes::random(32)?;
        (0..count)
            .map(|_| {
                let mut copy = LockedBytes::new(32)?;
                copy.as_mut_slice()?.copy_from_slice(master.as_slice()?);
                InitiatorKey::from_locked(copy)
            })
            .collect()
    }

    fn unix_now() -> Result<u64, CliError> {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .map_err(|_| CliError::new(exit::IO, "system clock is before the Unix epoch"))
    }

    struct Session {
        params_name: String,
        params: BaggyParams,
        parent: BaggyPublicKey,
        initiator: InitiatorKey,
        pools: Vec<CouponPool>,
        coupons: Vec<CertifiedCoupon>,
    }

    /// A refused request. `signature` is set when the coupon was spent and only the write
    /// of its signature failed, so that the signature is not lost with it.
    struct Refusal {
        error: CliError,
        signature: Option<String>,
    }
    impl From<CliError> for Refusal {
        fn from(error: CliError) -> Self {
            Self {
                error,
                signature: None,
            }
        }
    }

    fn signature_json(params_name: &str, wire: &[u8]) -> Json {
        Json::object(vec![
            ("format", Json::str(SIG_FORMAT)),
            ("scheme", Json::str(SCHEME_NAME)),
            ("params", Json::str(params_name)),
            ("signature", Json::hex(wire)),
        ])
    }

    impl Session {
        fn sign(&mut self, line: &str) -> Result<Vec<(&'static str, Json)>, Refusal> {
            let request = Json::parse(line)?;
            let index = request.field_u64("coupon")?;
            let message_path = request.field_str("message")?;
            let out = request.field_str("out")?;
            let coupon = usize::try_from(index)
                .ok()
                .and_then(|i| self.coupons.get(i))
                .ok_or_else(|| {
                    CliError::usage(format!(
                        "coupon {index} is not in this batch of {}",
                        self.coupons.len()
                    ))
                })?;
            if message_path == "-" {
                return Err(CliError::usage("a session message must be a file path").into());
            }
            ensure_absent(out)?;
            let message = read_bounded_file(message_path, MAX_MSG_BYTES)?;

            let descriptor = coupon.descriptor();
            let coupon_id = descriptor
                .id()
                .map_err(|e| coupon_error("coupon descriptor", e))?;
            let (counter, _) = grind(&SignRequest::message_hash(&coupon_id, &message))
                .ok_or_else(|| CliError::state("no WOTS+C counter found for this message"))?;
            let sign_request =
                SignRequest::authorize(&self.initiator, descriptor, message.to_vec(), counter)
                    .map_err(|e| coupon_error("authorizing the request", e))?;
            let mut openings = Vec::with_capacity(self.pools.len());
            for pool in &mut self.pools {
                openings.push(
                    pool.open(&sign_request)
                        .map_err(|e| coupon_error(&format!("opening coupon {index}"), e))?,
                );
            }
            let signature = combine(coupon, &sign_request, &openings)
                .map_err(|e| coupon_error("combining the openings", e))?;
            drop(openings);
            if !baggy_verify(&self.parent, &self.params, &message, &signature) {
                return Err(
                    CliError::state("the combined coupon signature does not verify").into(),
                );
            }
            let wire = signature
                .to_wire_bytes()
                .map_err(|e| coupon_error("encoding the signature", e))?;
            let encoded = signature_json(&self.params_name, &wire).to_pretty();
            if let Err(error) = write_new(out, encoded.as_bytes(), false) {
                return Err(Refusal {
                    error,
                    signature: Some(to_hex(&wire)),
                });
            }
            Ok(vec![
                ("ok", Json::Bool(true)),
                ("coupon", Json::num(index)),
                ("coupon_id", Json::hex(&coupon_id)),
                ("counter", Json::num(counter)),
                ("signature_bytes", Json::num(wire.len())),
                ("out", Json::str(out)),
            ])
        }
    }

    fn emit(out: &mut impl Write, json: &Json) -> Result<(), CliError> {
        out.write_all(json.to_pretty().as_bytes())
            .and_then(|()| out.flush())
            .map_err(|e| CliError::io("writing to standard output", e))
    }

    fn session(raw: &[String]) -> Result<(), CliError> {
        let args = Args::parse(
            raw,
            &[
                "vault-dir",
                "members",
                "parties",
                "coupons",
                "ttl-secs",
                "waistband-layers",
                "passphrase-env",
                "passphrase-file",
            ],
            &["help"],
        )?;
        if args.flag("help") {
            print!("{SESSION_HELP}");
            return Ok(());
        }
        args.no_positionals()?;
        let vault_dir = args.require("vault-dir")?;
        let parties = usize::try_from(args.get_u64("parties")?.unwrap_or(3))
            .ok()
            .filter(|&n| (2..=usize::from(u16::MAX)).contains(&n))
            .ok_or_else(|| CliError::usage("--parties must be between 2 and 65535"))?;
        let members = parse_members(args.require("members")?, parties)?;
        let coupons = args
            .get_u64("coupons")?
            .and_then(|n| usize::try_from(n).ok())
            .filter(|&n| {
                n >= 1
                    && n.checked_mul(members.len())
                        .and_then(|n| n.checked_mul(SHARE_BYTES))
                        .is_some_and(|bytes| bytes <= MAX_BATCH_SHARE_BYTES)
            })
            .ok_or_else(|| {
                CliError::usage(format!(
                    "--coupons is required: at least 1, and at most {} for {} members",
                    MAX_BATCH_SHARE_BYTES / (SHARE_BYTES * members.len()),
                    members.len()
                ))
            })?;
        let ttl = args
            .get_u64("ttl-secs")?
            .filter(|&s| s > 0)
            .ok_or_else(|| CliError::usage("--ttl-secs is required and must be positive"))?;
        let waistband_layers = args.get_u64("waistband-layers")?.unwrap_or(0);
        if waistband_layers > MAX_WAISTBAND_LAYERS {
            return Err(CliError::usage(format!(
                "--waistband-layers must be at most {MAX_WAISTBAND_LAYERS}"
            )));
        }
        let passphrase = crate::envelope::passphrase(&args)?;

        // Before any seed is read: lock every mapping and disable core dumps for good.
        let protection = protect()?;
        let started = Instant::now();
        let root = load_root(vault_dir, passphrase.as_deref().map(Vec::as_slice))?;
        let (mut engine, _) = root_engine(root.dkg_session_id, &root.seeds)?;
        let (parent, binding) =
            baggy_keygen_mpc(&mut engine, &root.params, &mut WaistbandCache::disabled()).map_err(
                |e| CliError::state(format!("recomputing the Baggy root key failed: {e}")),
            )?;
        if parent != root.pk {
            return Err(CliError::state(
                "the party seeds do not produce the root public key recorded with them",
            ));
        }
        eprintln!(
            "qsag: coupon root ready ({:.1} s)",
            started.elapsed().as_secs_f64()
        );

        let expires_at = unix_now()?
            .checked_add(ttl)
            .ok_or_else(|| CliError::usage("--ttl-secs is too large"))?;
        let mut keys = initiator_keys(members.len() + 1)
            .map_err(|e| coupon_error("creating the request key", e))?;
        let initiator = keys
            .pop()
            .ok_or_else(|| CliError::state("no request key"))?;
        let mut pools = members
            .iter()
            .zip(keys)
            .map(|(&party, key)| CouponPool::new(party, parent, key))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| coupon_error("creating the coupon pools", e))?;

        let started = Instant::now();
        let pending = PendingCouponBatch::mint(
            &protection,
            MintPlan {
                parent,
                parties,
                members: members.clone(),
                expires_at,
                coupons,
            },
        )
        .map_err(|e| coupon_error("minting the coupon batch", e))?;
        eprintln!(
            "qsag: minted {coupons} coupon(s) ({:.1} s)",
            started.elapsed().as_secs_f64()
        );
        let started = Instant::now();
        let mut waistband = AuthenticatedWaistband::new(
            parent,
            root.params,
            binding,
            waistband_layers as usize,
            WAISTBAND_ENTRIES,
        )
        .map_err(|e| coupon_error("creating the root Waistband", e))?;
        let certified = pending
            .certify_with_waistband(&protection, &mut engine, &mut waistband, &mut pools)
            .map_err(|e| coupon_error("certifying the coupon batch under the root key", e))?;
        drop(waistband);
        drop(engine);
        eprintln!(
            "qsag: certified {coupons} coupon(s) under the root key ({:.1} s)",
            started.elapsed().as_secs_f64()
        );

        let ids = certified
            .iter()
            .map(|c| c.descriptor().id().map(|id| Json::hex(&id)))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| coupon_error("coupon descriptor", e))?;
        let mut stdout = std::io::stdout().lock();
        emit(
            &mut stdout,
            &Json::object(vec![
                ("format", Json::str(SESSION_FORMAT)),
                ("scheme", Json::str(SCHEME_NAME)),
                ("params", Json::str(root.params_name.as_str())),
                ("pk_seed", Json::hex(&parent.pk_seed)),
                ("pk_root", Json::hex(&parent.pk_root)),
                ("threshold", Json::num(members.len())),
                ("parties", Json::num(parties)),
                (
                    "members",
                    Json::Array(members.iter().map(Json::num).collect()),
                ),
                ("expires_at", Json::num(expires_at)),
                ("coupons", Json::Array(ids)),
            ]),
        )?;

        let mut session = Session {
            params_name: root.params_name,
            params: root.params,
            parent,
            initiator,
            pools,
            coupons: certified,
        };
        let mut first_refusal = None;
        let mut stdin = std::io::stdin().lock();
        let mut line = String::new();
        let mut number = 0u64;
        loop {
            line.clear();
            let read = stdin
                .read_line(&mut line)
                .map_err(|e| CliError::io("reading a request from standard input", e))?;
            if read == 0 {
                break;
            }
            if line.trim().is_empty() {
                continue;
            }
            number += 1;
            let outcome = if line.len() > MAX_REQUEST_LINE_BYTES {
                Err(CliError::usage("request line is too long").into())
            } else {
                session.sign(&line)
            };
            let mut fields = vec![("request", Json::num(number))];
            match outcome {
                Ok(done) => fields.extend(done),
                Err(refusal) => {
                    fields.push(("ok", Json::Bool(false)));
                    fields.push(("exit_code", Json::num(refusal.error.code)));
                    fields.push(("error", Json::str(refusal.error.message.as_str())));
                    if let Some(signature) = refusal.signature {
                        fields.push(("signature", Json::str(signature)));
                    }
                    first_refusal.get_or_insert(refusal.error);
                }
            }
            emit(&mut stdout, &Json::object(fields))?;
        }
        match first_refusal {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    fn verify(raw: &[String]) -> Result<(), CliError> {
        let args = Args::parse(raw, &["public", "in", "message", "sig"], &["json", "help"])?;
        if args.flag("help") {
            print!("{VERIFY_HELP}");
            return Ok(());
        }
        args.no_positionals()?;
        if args.get("in").is_some() && args.get("message").is_some() {
            return Err(CliError::usage("pass either --message or --in, not both"));
        }
        let public_path = args.require("public")?;
        let sig_path = args.require("sig")?;
        let message_arg = args
            .get("message")
            .or_else(|| args.get("in"))
            .ok_or_else(|| CliError::usage("missing required option --in (or --message)"))?;
        let message = read_input(message_arg)?;

        let public = Json::parse(&read_text(public_path)?)?;
        if public.field_str("format")? != ROOT_PUBLIC_FORMAT
            || public.field_str("scheme")? != SCHEME_NAME
        {
            return Err(CliError::input("unexpected coupon root public key format"));
        }
        let params_name = public.field_str("params")?;
        let params = params_by_name(params_name)?;
        let parent = BaggyPublicKey {
            pk_seed: from_hex_exact(public.field_str("pk_seed")?, "pk_seed")?,
            pk_root: from_hex_exact(public.field_str("pk_root")?, "pk_root")?,
        };

        let sig_raw = read_bounded_file(sig_path, MAX_SIG_PROOF_BYTES)?;
        let sig_text = std::str::from_utf8(&sig_raw)
            .map_err(|_| CliError::input(format!("{sig_path} is not UTF-8 text")))?;
        let sig_json = Json::parse(sig_text)?;
        if sig_json.field_str("format")? != SIG_FORMAT
            || sig_json.field_str("scheme")? != SCHEME_NAME
        {
            return Err(CliError::input("unexpected coupon signature format"));
        }
        if sig_json.field_str("params")? != params_name {
            return Err(CliError::verify(
                "coupon signature parameters differ from the root key",
            ));
        }
        let wire = sig_json.field_hex("signature")?;
        let signature = BaggySig::from_wire_bytes(&parent, &params, &wire).map_err(|e| {
            CliError::verify(format!(
                "coupon signature is not one this root key certified ({e})"
            ))
        })?;
        if !baggy_verify(&parent, &params, &message, &signature) {
            return Err(CliError::verify(
                "coupon signature verification failed (wrong message, or the coupon expired)",
            ));
        }

        let descriptor = signature.coupon.descriptor();
        let coupon_id = descriptor
            .id()
            .map_err(|e| coupon_error("coupon descriptor", e))?;
        if args.flag("json") {
            let report = Json::object(vec![
                ("valid", Json::Bool(true)),
                ("scheme", Json::str(SCHEME_NAME)),
                ("params", Json::str(params_name)),
                ("coupon_id", Json::hex(&coupon_id)),
                ("threshold", Json::num(descriptor.threshold)),
                ("parties", Json::num(descriptor.parties)),
                (
                    "members",
                    Json::Array(descriptor.members.iter().map(Json::num).collect()),
                ),
                ("expires_at", Json::num(descriptor.expires_at)),
            ]);
            print!("{}", report.to_pretty());
        } else {
            println!(
                "VALID ({SCHEME_NAME} {params_name}, coupon {}, expires_at {})",
                to_hex(&coupon_id),
                descriptor.expires_at
            );
        }
        Ok(())
    }
}
