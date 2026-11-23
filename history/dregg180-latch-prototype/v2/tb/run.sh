#!/bin/bash
# Dregg-180 v2 RTL: build and verification entry point. Run on a Linux host with the OSS CAD Suite
# (Verilator, Yosys, SymbiYosys), from the chip directory (hardware/gf180mcu):
#
#   bash v2/tb/run.sh gen                    generated files into build/v2 (round constants, ROM, row-map variants)
#   bash v2/tb/run.sh lint                   verilator --lint-only -Wall, every configuration
#   bash v2/tb/run.sh unit                   register-file unit bench
#   bash v2/tb/run.sh cosim <rows> [params]  record the model and replay it on dregg_core (rows: 72 or 64)
#   bash v2/tb/run.sh fast <rows> <tag> [params]  the same on a trace with the owner stand-in shortened (quick runs)
#   bash v2/tb/run.sh chip                   the reference script through dregg_top over SPI
#   bash v2/tb/run.sh xprop                  cosim of the script with every storage element randomised
#
# Environment: OSS (path of oss-cad-suite), JOBS (parallel simulations, default 16),
#   DREGG_V2_REF: the v2 directory whose model/, ucode/ and tests/ are the reference (default: this tree).
#   The RTL here was verified against commit ef8564b; extract it with
#     git archive ef8564b hardware/gf180mcu/v2/model hardware/gf180mcu/v2/ucode hardware/gf180mcu/v2/tests \
#         hardware/gf180mcu/tb hardware/gf180mcu/model | tar -x -C <dir>
#   and set DREGG_V2_REF=<dir>/hardware/gf180mcu/v2 when the live model has moved on.
set -e
OSS=${OSS:-/home/build/qsag-ni-fpga/oss-cad-suite}
. "$OSS/environment"
JOBS=${JOBS:-16}
B=build/v2
mkdir -p $B
OLD="rtl/qsag_cells.sv $B/qsag_p2_rc.sv"
R=${RTLDIR:-v2/rtl}
V2RTL="$R/dregg_gf180_sim.sv $R/dregg_regfile.sv $R/dregg_keccak_serial.sv $R/dregg_word_unit.sv $R/dregg_egress.sv $R/dregg_framer.sv $R/dregg_anchor_spi.sv $R/dregg_fram.sv $R/dregg_rules.sv $R/dregg_seq.sv $R/dregg_rst.sv $R/dregg_core.sv"
TOPRTL="$R/dregg_spi_link.sv $R/dregg_top.sv"
REFS="rtl/qsag_keccak_serial.sv rtl/qsag_anchor_spi.sv"

gen() {
    python3 scripts/gen_p2_rc.py $B/qsag_p2_rc.sv > /dev/null
    python3 -B v2/rtl/gen_defs.py --scratch 20 --check v2/rtl/dregg_defs.svh
    mkdir -p $B/inc72 $B/inc64
    cp v2/rtl/dregg_defs.svh $B/inc72/
    python3 -B v2/rtl/gen_defs.py $B/inc64/dregg_defs.svh
    python3 -B v2/tb/gen_rom.py --scratch 20 S $B/inc72/dregg_urom.sv $B/inc72/rom.txt
    python3 -B v2/tb/gen_rom.py S $B/inc64/dregg_urom.sv $B/inc64/rom.txt
}

build_cosim() {   # $1 rows, $2 tag, rest: extra verilator arguments
    rows=$1; tag=$2; shift 2
    rm -rf $B/obj_$tag
    verilator --cc --exe --build -j 8 -Wall -Wno-fatal -Wno-DECLFILENAME -O3 --x-assign fast --x-initial fast \
        -DQSAG_LATCH_RF -DDREGG_TB_BACKDOOR=dregg_cosim_tb -I$B/inc$rows "$@" -CFLAGS "-O2 -std=c++17" \
        --top-module dregg_cosim_tb -Mdir $B/obj_$tag \
        $OLD $REFS $V2RTL v2/tb/dregg_urom_sim.sv v2/tb/dregg_cosim_tb.sv v2/tb/cosim.cpp -o cosim > $B/build_$tag.log 2>&1 \
        || { grep -B2 -A8 '%Error\|error:' $B/build_$tag.log | head -80; exit 1; }
    echo "build $tag: $(grep -c '^%Warning' $B/build_$tag.log) verilator warnings"
}

run_shards() {    # $1 tag, $2 trace dir, rest: extra simulator arguments
    tag=$1; tr=$2; shift 2
    bin=$B/obj_${tag%$PROPOSE}/cosim
    rm -f $B/run_$tag.*.log
    i=0
    pids=""
    while [ $i -lt $JOBS ]; do
        timeout --kill-after=10s 3000s $bin $tr --shard $i $JOBS "$@" > $B/run_$tag.$i.log 2>&1 &
        pids="$pids $!"
        i=$((i + 1))
    done
    st=0
    for p in $pids; do wait $p || st=1; done
    cat $B/run_$tag.*.log > $B/run_$tag.log
    python3 -B v2/tb/sum_cosim.py $B/run_$tag.log
    return $st
}

case "$1" in
gen) gen ;;
lint)
    gen
    st=0
    for cfg in "" "-DQSAG_ICG" "-DSYNTHESIS" "-DSYNTHESIS -DQSAG_ICG"; do
        for rows in 72 64; do
            if verilator --lint-only -Wall -Wno-DECLFILENAME -DQSAG_LATCH_RF $cfg -I$B/inc$rows --top-module dregg_top \
                v2/tb/waivers.vlt $OLD $V2RTL $TOPRTL $B/inc$rows/dregg_urom.sv > $B/lint.log 2>&1; then r=clean; else r=NOT-CLEAN; st=1; fi
            echo "lint dregg_top [$cfg] rows $rows: $(grep -c '^%Warning' $B/lint.log) warnings, $(grep -c '^%Error' $B/lint.log) errors: $r"
            grep -A4 '^%Warning\|^%Error' $B/lint.log | head -${LINT_HEAD:-12}
        done
    done
    exit $st
    ;;
unit)
    gen
    st=0
    for rows in 72 64; do
        rm -rf $B/obj_urf
        verilator --cc --exe --build -j 8 -Wall -Wno-fatal -Wno-DECLFILENAME --x-assign unique --x-initial unique \
            -DQSAG_LATCH_RF -I$B/inc$rows --top-module unit_regfile_tb -Mdir $B/obj_urf \
            rtl/qsag_cells.sv v2/rtl/dregg_gf180_sim.sv v2/rtl/dregg_regfile.sv v2/rtl/dregg_rst.sv \
            v2/tb/unit_regfile_tb.sv v2/tb/unit_regfile.cpp -o unit_regfile > $B/build_urf$rows.log 2>&1 \
            || { grep -B2 -A8 '%Error\|error:' $B/build_urf$rows.log | head -60; exit 1; }
        for seed in 1 2 3; do
            $B/obj_urf/unit_regfile +verilator+seed+$seed +verilator+rand+reset+2 || st=1
        done
    done
    exit $st
    ;;
cosim)
    rows=${2:-72}; shift; shift || true
    gen
    tag=cosim$rows$(echo "$@" | tr -d ' =-')
    sc=20; [ "$rows" = 64 ] && sc=12
    python3 -B v2/tb/record.py --scratch $sc ${PROPOSE:+--propose $PROPOSE} $B/trace$rows$PROPOSE ${SCEN:-script quick tests long extra}
    build_cosim $rows $tag "$@"
    run_shards $tag$PROPOSE $B/trace$rows$PROPOSE
    ;;
chip)
    gen
    python3 -B v2/tb/record.py --scratch 20 $B/trace_chip script
    rm -rf $B/obj_chip
    verilator --cc --exe --build -j 8 -Wall -Wno-fatal -Wno-DECLFILENAME -O3 --x-assign fast --x-initial fast \
        -DQSAG_LATCH_RF -I$B/inc72 -CFLAGS "-O2 -std=c++17" --top-module dregg_chip_tb -Mdir $B/obj_chip \
        $OLD $V2RTL $TOPRTL $B/inc72/dregg_urom.sv v2/tb/dregg_chip_tb.sv v2/tb/chip.cpp -o chip > $B/build_chip.log 2>&1 \
        || { grep -B2 -A8 '%Error\|error:' $B/build_chip.log | head -80; exit 1; }
    echo "build chip: $(grep -c '^%Warning' $B/build_chip.log) verilator warnings"
    st=0
    for half in 3 2 7; do
        $B/obj_chip/chip $B/trace_chip $half > $B/run_chip.$half.log 2>&1 || st=1
        tail -9 $B/run_chip.$half.log | grep -v '^  ERROR' ; grep -m8 ERROR $B/run_chip.$half.log || true
    done
    exit $st
    ;;
fast)   # cosim on a trace with the owner-verification stand-in shortened to 100 clocks: parameter variants, mutants
    rows=${2:-72}; tag=${3:-fast}; shift; shift || true; shift || true
    tr=$B/trace_fast$rows$PROPOSE
    if [ ! -f $tr/trace.txt ]; then
        gen; sc=20; [ "$rows" = 64 ] && sc=12
        python3 -B v2/tb/record.py --scratch $sc --auth-verify 100 ${PROPOSE:+--propose $PROPOSE} $tr ${SCEN:-script quick tests long extra} > $tr.log 2>&1
    fi
    build_cosim $rows $tag "$@"
    p=$PROPOSE
    PROPOSE= run_shards $tag $tr
    PROPOSE=$p
    ;;
xprop)
    gen
    python3 -B v2/tb/record.py --scratch 20 $B/trace_x script
    rm -rf $B/obj_xprop
    build_cosim 72 xprop --x-assign unique --x-initial unique
    st=0
    for seed in 1 2 3; do
        timeout --kill-after=10s 900s $B/obj_xprop/cosim $B/trace_x +verilator+seed+$seed +verilator+rand+reset+2 > $B/run_xprop.$seed.log 2>&1 || st=1
        echo "x-initial seed $seed: $(grep 'before the first reset' $B/run_xprop.$seed.log); $(grep RESULT $B/run_xprop.$seed.log)"
    done
    exit $st
    ;;
*) echo "see the header of v2/tb/run.sh"; exit 2 ;;
esac
