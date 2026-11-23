#!/bin/sh
# Run several project commands on the build host one after another, each in its own
# 16 GiB / 600 s envelope (same wrapper as scripts/rx.sh).
#   scripts/rx_seq.sh "<cmd 1>" "<cmd 2>" ...
for c in "$@"; do
    ssh -o ConnectTimeout=25 persvati-remote "SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s docker exec qsag-ni-gf180mcu timeout -k 10 590 /work/nx.sh /work/proj '$c'" || true
done
