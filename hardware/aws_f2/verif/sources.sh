# Source from hardware/aws_f2. Package declarations precede their users.
rtl=(design/ass2/qsag_ass2_pkg.sv)
for f in design/ass2/*.sv; do [[ $f == "${rtl[0]}" ]] || rtl+=("$f"); done
rtl+=(design/ni/qsag*.sv design/qsag_f2*.sv design/cl_qsag_f2_top.sv)
