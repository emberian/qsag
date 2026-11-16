# Build-host setup used for QSAG-NI-180 (persvati, 2026-11-16)

These are the commands that were run, not a tested script. The container and
`/tmp/qsag-ni-gf180mcu` were removed at the end of the lane, so `scripts/rx.sh` needs this
again before it works. hbox was not usable: its `/usr/bin/verilator` wrapper has no
`verilator_bin` behind it.

```sh
mkdir -p /tmp/qsag-ni-gf180mcu && cd /tmp/qsag-ni-gf180mcu
git clone --depth 1 https://github.com/wafer-space/gf180mcu-project-template template   # d99f6e1
docker run -d --name qsag-ni-gf180mcu --memory 16g --memory-swap 16g --cpus 12 \
    -v /tmp/qsag-ni-gf180mcu:/work -w /work/template nixos/nix:latest sleep infinity

# /tmp/qsag-ni-gf180mcu/nx.sh (chmod +x): run a command in the template's dev shell.
# The two store paths come from the `nix build` below.
cat > nx.sh <<'SH'
#!/bin/sh
d="$1"; shift
extra=/nix/store/<gcc-wrapper>/bin:/nix/store/<z3>/bin
cd /work/template
exec nix --extra-experimental-features "nix-command flakes" --accept-flake-config develop \
    --command sh -c "export PATH=\$PATH:$extra; cd $d && $*"
SH

docker exec qsag-ni-gf180mcu git config --global --add safe.directory '*'
docker exec qsag-ni-gf180mcu /work/nx.sh /work/template true          # realises LibreLane, Yosys, OpenROAD, Verilator
docker exec qsag-ni-gf180mcu nix --extra-experimental-features "nix-command flakes" \
    build --no-link --print-out-paths nixpkgs#gcc nixpkgs#z3          # C++ compiler for Verilator, Z3
docker exec qsag-ni-gf180mcu /work/nx.sh /work/template "make clone-pdk"   # gf180mcuD via ciel, about 5 GB
```

Then, from the Mac: `scripts/rsync_to_remote.sh`, `scripts/rx.sh "sh tb/lint.sh"`, and so on.

Things that cost time:

* A command cut by the 600 s limit leaves its background children running inside the
  container. `tb/run_all.sh` gives each simulation its own `timeout`; check `docker top
  qsag-ni-gf180mcu` after any cut-off.
* The container's default shell has no coreutils; run everything through `nx.sh`.
* Do not put single quotes in a command passed to `scripts/rx.sh`.
* LibreLane resumes with `--run-tag qsag --from <step> --to <step>`; a slice that is cut
  leaves a step directory without `state_out.json`, which has to be removed before resuming.
