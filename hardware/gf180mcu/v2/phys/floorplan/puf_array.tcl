# Dregg-180 v2 floorplan: the PUF key array, placed by the rules of
# physics/puf/placement_requirements.md (R1, R2, R4.1; R3 and R5 are not implemented here, see the report).
# Sourced after fp_common.tcl.
#
#   slot  = u_en (buf_2, 8 sites) + g_st[0..4].u_n (5 x nand2_1, 25) + u_out (buf_2, 8) + tap (2)
#         = 43 sites = 24.08 um, abutted, one row, no spacing (R1.1, R1.2)
#   row   = 2 dummy slots + 6 quads (24 slots) + 2 dummy slots = 28 slots = 674.2 um (R1.3, R1.4, R2.1)
#   array = dummy row + 42 used rows + dummy row = 44 rows = 172.5 um (R2.2)
# A quad is four consecutive slots of one row, so its four rings have the same orientation. The
# template's staggered taps inside the box are replaced by the tap at the end of every slot.
# 1008 used + 224 dummy slots: 116,300 um2 of placed cells in a 674 x 172.5 um box, 100 % full.
#
# What it buys: every used ring has the same cells left, right, above and below at the same offsets,
# which is the precondition for the 6 aF matching budget; the placer cannot do this (a region gives
# 30 to 60 % fill with arbitrary neighbours).
namespace eval puf {
    variable X0   450.0     ;# um, left edge of the array
    variable TOPGAP 3       ;# free rows between the array and the core edge
    variable SLOT 43
    variable QPR 6          ;# quads per row
    variable NROWS 42       ;# used rows
}
proc puf::slot {path ri x} {
    set e $x
    set e [fp::put [fp::inst "$path/u_en"] $ri $e]
    for {set s 0} {$s < 5} {incr s} { set e [fp::put [fp::inst "$path/g_st\[$s\].u_n"] $ri $e] }
    set e [fp::put [fp::inst "$path/u_out"] $ri $e]
    if { $e != $x + 41 * [lindex $fp::rows 0 4] } { error "puf: slot $path is not contiguous" }
}
proc puf::place {} {
    variable X0; variable TOPGAP; variable SLOT; variable QPR; variable NROWS
    set P i_chip_core/u_pufarr
    set per [expr {4 * $QPR + 4}]
    set rtop [expr {[llength $fp::rows] - $TOPGAP}]
    set rbot [expr {$rtop - $NROWS - 2}]
    lassign [lindex $fp::rows $rbot] ry rx0 nsites orient sw rh
    set s0 [expr {int(($X0 * $::dbu - $rx0) / $sw)}]
    set sites {}
    for {set c 0} {$c < $per} {incr c} { lappend sites [expr {$s0 + $c * $SLOT + 41}] }
    fp::retap PUFTAP $rbot $rtop [expr {$s0 - 2}] [expr {$s0 + $per * $SLOT + 2}] $sites
    set d 0; set n 0
    for {set r 0} {$r < $NROWS + 2} {incr r} {
        set ri [expr {$rbot + $r}]
        for {set c 0} {$c < $per} {incr c} {
            set x [expr {$rx0 + ($s0 + $c * $SLOT) * $sw}]
            if { $r == 0 || $r == $NROWS + 1 || $c < 2 || $c >= $per - 2 } {
                puf::slot "$P/g_dum\[$d\].u_s" $ri $x
                incr d
            } else {
                set q [expr {($r - 1) * $QPR + ($c - 2) / 4}]
                puf::slot "$P/g_q\[$q\].g_r\[[expr {($c - 2) % 4}]\].u_s" $ri $x
                incr n
            }
        }
    }
    set ya [fp::row_y_um $rbot]
    set yb [expr {[fp::row_y_um [expr {$rtop - 1}]] + 3.92}]
    set xa [expr {($rx0 + $s0 * $sw) / double($::dbu)}]
    set xb [expr {($rx0 + ($s0 + $per * $SLOT) * $sw) / double($::dbu)}]
    lappend fp::regions [list puf_array $xa $ya $xb $yb]
    metric puf_rings_placed $n
    metric puf_dummy_slots $d
    metric puf_array_box "$xa $ya $xb $yb"
    metric puf_array_box_um2 [format %.0f [expr {($xb - $xa) * ($yb - $ya)}]]
    set ::puf_box [list $xa $ya $xb $yb]
}
puf::place
