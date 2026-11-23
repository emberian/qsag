#!/bin/bash
# Synthesis with buffering and sizing, then the timing and electrical gate on every block and the top, at
# SS 125 C 4.5 V and FF -40 C 5.5 V. Run from the chip directory:
#   bash v2/lec/timing.sh <lib dir> <sta binary> [block spec ...]
# Synthesis maps against the SS liberty (sizing for the slow corner). Output: build/v2/tim/.
LIBD=$1; STA=$2; shift 2
B=build/v2
P=gf180mcu_fd_sc_mcu7t5v0__
SPECS=${*:-"dregg_regfile dregg_keccak_serial dregg_word_unit dregg_urom dregg_seq dregg_seq@IR_STAGE=1,RA_STAGE=1 dregg_egress dregg_framer dregg_fram dregg_spi_link dregg_rst dregg_top dregg_top@IR_STAGE=1,RA_STAGE=1"}
[ -n "$NOSYN" ] || SYNOUT=$B/tim/syn bash v2/lec/synth.sh $LIBD/${P}ss_125C_4v50.lib $SPECS
mkdir -p $B/tim/sta $B/tim/net
rm -f $B/tim/sta/*
pids=""
for spec in $SPECS; do
    mod=${spec%%@*}; top=$mod
    [ "$spec" != "$mod" ] && top=${mod}_$(echo ${spec#*@} | tr '=,' '__')
    python3 v2/lec/buftree.py $LIBD/${P}ss_125C_4v50.lib $B/tim/syn/$top.v $B/tim/net/$top.v ${BT_OPTS} > $B/tim/net/$top.bt.log 2>&1 || { tail -3 $B/tim/net/$top.bt.log; continue; }
    for c in ss_125C_4v50 ff_n40C_5v50; do
        bash v2/lec/sta_gate.sh $STA $LIBD/$P$c.lib $B/tim/net/$top.v $mod $B/tim/sta/${top}.$c &
        pids="$pids $!"
    done
done
for p in $pids; do wait $p; done
python3 v2/lec/sta_table.py $B/tim/sta
