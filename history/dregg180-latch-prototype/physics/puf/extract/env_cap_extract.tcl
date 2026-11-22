# Magic batch script: how much does the capacitance of a ring stage's nets depend on what sits next to it?
# Builds rows of abutted standard cells (no routing), extracts with coupling, writes flat SPICE with every
# capacitor (cthresh 0).  Compare the nets of the marked nand2_1 between rows (see parse_env_cap.py).
#   magic -dnull -noconsole -rcfile $PDK_ROOT/gf180mcuD/libs.tech/magic/gf180mcuD.magicrc env_cap_extract.tcl
drc off
# keep every .ext file in the working directory (by default Magic writes cell .ext files next to the PDK cells)
extract path [pwd]
proc row {name cells} {
    load $name
    set x 0.0
    set i 0
    foreach c $cells {
        set w [lindex $c 1]
        box [format "%.3fum" $x] 0um [format "%.3fum" $x] 0um
        getcell gf180mcu_fd_sc_mcu7t5v0__[lindex $c 0]
        identify u$i
        set x [expr {$x + $w}]
        incr i
    }
    select top cell
    extract do all
    extract all
    ext2spice cthresh 0
    ext2spice format ngspice
    ext2spice hierarchy off
    ext2spice subcircuit top off
    ext2spice -o $name.spice
    save $name
}
set N {nand2_1 2.8}
# A: interior of a uniform row; marked cell is u2
row envA [list $N $N $N $N $N]
# B: row end: nothing to the right of the marked cell u2
row envB [list $N $N $N]
# C: different neighbours: buffer on the left, flip-flop on the right; marked cell u1
row envC [list {buf_2 4.48} $N {dffq_1 16.24}]
# D: filler on the right; marked cell u2
row envD [list $N $N $N {fill_1 0.56} {fill_1 0.56} $N]
quit -noprompt
