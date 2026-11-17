#!/bin/bash
# Where the sequencer's area goes: dregg_seq is synthesized from copies of v2/rtl with one feature removed
# each (area experiments only; none of these copies is simulated). Run from the chip directory:
#   bash v2/lec/ablate.sh <liberty file>
# name | sed expression on dregg_seq.sv | block spec
LIB=$1
B=build/v2
mkdir -p $B/abl
cat > $B/abl/list.txt <<'EOF'
base||dregg_seq
shadow||dregg_seq@H_SHADOW=0
nonce|s/qsag_ereg #(.W(128)) u_nonce (.*/assign nonce = 128'd0;/|dregg_seq
auth|s/wire ctl_auth    = is_ctl \&\& (fa == CTL_AUTH);/wire ctl_auth    = 1'b0;/|dregg_seq
steps|s/\.runaway(steps > 25'(MAX_STEPS))/.runaway(1'b0)/|dregg_seq
taint|s/\.t_lanes(t_lanes), \.t_h(t_h), \.t_z(t_z), \.t_cy(t_cy),/.t_lanes(1'b0), .t_h(1'b0), .t_z(1'b0), .t_cy(1'b0),/|dregg_seq
ldf|s/OP_LDF:  begin wu_op = OP_LD; wu_x = ldf; end/OP_LDF:  begin wu_op = OP_LD; wu_x = 64'd0; end/|dregg_seq
operands|s/wu_x = ldf; end/wu_x = 64'd0; end/;s/wu_x = fr_din; end/wu_x = 64'd0; end/;s/wu_x = const_data; end/wu_x = 64'd0; end/;s/wu_x = fm_rx; end/wu_x = 64'd0; end/|dregg_seq
all|s/qsag_ereg #(.W(128)) u_nonce (.*/assign nonce = 128'd0;/;s/wire ctl_auth    = is_ctl \&\& (fa == CTL_AUTH);/wire ctl_auth    = 1'b0;/;s/\.runaway(steps > 25'(MAX_STEPS))/.runaway(1'b0)/;s/\.t_lanes(t_lanes), \.t_h(t_h), \.t_z(t_z), \.t_cy(t_cy),/.t_lanes(1'b0), .t_h(1'b0), .t_z(1'b0), .t_cy(1'b0),/;s/wu_x = ldf; end/wu_x = 64'd0; end/;s/wu_x = fr_din; end/wu_x = 64'd0; end/;s/wu_x = const_data; end/wu_x = 64'd0; end/;s/wu_x = fm_rx; end/wu_x = 64'd0; end/|dregg_seq@H_SHADOW=0
EOF
pids=""
while IFS='|' read -r name expr spec; do
    d=$B/abl/$name
    rm -rf $d; mkdir -p $d/rtl
    cp v2/rtl/*.sv v2/rtl/*.svh $d/rtl/
    if [ -n "$expr" ]; then
        sed -i "$expr" $d/rtl/dregg_seq.sv
        cmp -s $d/rtl/dregg_seq.sv v2/rtl/dregg_seq.sv && { echo "ablation $name: the edit did not apply"; continue; }
    fi
    RTLDIR=$d/rtl SYNOUT=$d/syn bash v2/lec/synth.sh $LIB $spec > $d/log.txt 2>&1 &
    pids="$pids $!"
done < $B/abl/list.txt
for p in $pids; do wait $p; done
base=$(awk '/Chip area for (top )?module/ {a=$NF} END {print a}' $B/abl/base/syn/dregg_seq.stat)
while IFS='|' read -r name expr spec; do
    f=$(ls $B/abl/$name/syn/*.stat 2>/dev/null | head -1)
    [ -z "$f" ] && { echo "ablation $name: no result"; continue; }
    awk -v n=$name -v b=$base '/Chip area for (top )?module/ {a=$NF} /dffrnq_1/ {for(i=1;i<=NF;i++) if ($i ~ /^[0-9]+$/) {c=$i; break}} END {printf "ablation %-9s area %8.0f  delta %8.0f  flops %s\n", n, a, a-b, c}' $f
done < $B/abl/list.txt
