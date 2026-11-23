#!/bin/sh
# Run a command for this project inside the persvati container dev shell, under the lane's
# resource envelope (16 GiB cgroup, 600 s wall clock, inner timeout so nothing outlives it).
#   scripts/rx.sh "<shell command, cwd = project root>"
exec ssh -o ConnectTimeout=25 persvati-remote "SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s docker exec qsag-ni-gf180mcu timeout -k 10 590 /work/nx.sh /work/proj '$1'"
