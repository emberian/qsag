# FPGA Verification Plan

- [ ] Run `hardware/fpga/lint.sh`. Verify `0` warnings.
- [ ] Run `./scripts/remote_run.sh ./verify_fpga.sh` on `bb2`.
- [ ] Run `./scripts/remote_run.sh python3 lec/lec.py` (or whatever the LEC script is) on `bb2`.
- [ ] Run `./scripts/remote_run.sh synth/run_all.sh` on `bb2`.
- [ ] Update `hardware/fpga/RESULTS.md` and `README.md` with results from `bb2`.
