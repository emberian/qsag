#!/usr/bin/env bash
# All FPGA tool execution lives on bb2, including temporary files and compiler subprocesses.
set -euo pipefail
printf -v task '%q ' "$@"
printf -v payload '%q' "source /home/build/qsag-ni-fpga/oss-cad-suite/environment; export TMPDIR=/home/build/qsag-ni-fpga/work/astra/tmp QSAG_FIXTURE=/home/build/qsag-ni-fpga/work/astra/lean_external_oracle_vectors.json; cd /home/build/qsag-ni-fpga/work/astra/fpga; $task"
ssh bb2 "cd /home/build/qsag-ni-fpga && SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s bash -c $payload"
