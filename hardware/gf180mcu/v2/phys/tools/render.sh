#!/bin/sh
# Inside the container dev shell: render exp/<run>/<def> to exp/<run>/<out>.png
#   render.sh <run> <def-file> <out-name> "<title>" [congestion.json]
set -eu
run=$1; def=$2; out=$3; title=$4; cong=${5:-}
SC=/work/pdk/gf180mcuD/libs.ref/gf180mcu_fd_sc_mcu7t5v0
IO=/work/pdk/gf180mcuD/libs.ref/gf180mcu_fd_io/lef
LEFS="$SC/lef/gf180mcu_fd_sc_mcu7t5v0.lef $(ls $IO/*.lef | tr '\n' ' ') $(ls /work/proj/ip/*/lef/*.lef | tr '\n' ' ')"
cd /work/proj/v2/phys/tools
reg=/work/exp/$run/regions.json; [ -f $reg ] || reg=""
python3 render_fp.py /work/exp/$run/$out.png "$title" /work/exp/$run/$def $SC/techlef/gf180mcu_fd_sc_mcu7t5v0__nom.tlef "$LEFS" "$reg" $cong
