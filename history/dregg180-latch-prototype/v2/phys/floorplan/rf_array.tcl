# Dregg-180 v2 floorplan: the register file as a placed array (72 words x 64 bits).
# Sourced after fp_common.tcl. Every cell of proxy/px_rf.sv's array goes on a site, FIRM.
#
#   RF_Y0   (um) bottom of the band; default 1218 (just above the distance-bounding pads on the east edge)
#
# Band, bottom to top, full core width, 84 standard-cell rows = 329.3 um:
#     F3  u_or (read-port output, leaves downwards to the word unit), u_rn (column clear driver)
#     F2  u_wd (write bit-line driver, buf_8)
#     F1  u_f0 u_f1 u_f2 (nand3 over three group lines each)
#     9 x [ 4 word rows | combiner row (u_na u_nb u_gn per column, u_ckb in the centre) | 4 word rows ]
# Word row: bits 0..31, then the centre column (u_wen, u_cg = icgtp_4, u_sel = and2_4), then bits 32..63.
# A bit is u_lat (latrnq_1, 22 sites) followed by u_rd (nand2_1, 5 sites) = 27 sites (15.12 um).
#
# Tap cells. The template's taps (every 70 sites per row, staggered by 35 between rows) cannot stay
# inside the band: a 22-site latch cannot straddle a tap, so every tap would cost about 9 sites and a
# 64-bit word would not fit in one row (measured: the first attempt ran out of row at column 54).
# The band's taps are therefore removed and re-placed on the array's own grid: one tap after every
# two bit columns in every row (56 sites = 31.4 um apart, not staggered) and one on each side of the
# centre column. Every device is then within 15.7 um of a tap in its own row, which is closer than the
# template's 19.6 um; the latch-up rules of the DRC deck are the check.
#
# What it buys:
#   * word lines (`gate`, `sel`) are straight Metal3 runs of at most 520 um from a centre driver;
#   * a column's write bit line, clear line and read tree stay inside its own 15.68 um stripe, so the
#     array needs no routing whitespace: about 94 % of its sites hold cells, against the 70 to 75 % a
#     placer region needs;
#   * the resizer and CTS never see the array's nets (flow/pnr.tcl freezes them), so no repair buffer
#     has to be legalised into it.
namespace eval rf {
    variable NROW 72
    variable NGRP 9
    variable y0 [expr {[info exists ::env(RF_Y0)] ? $::env(RF_Y0) : 1218.0}]
    variable LEFT 2            ;# first site after the endcap
    variable PAIR 56           ;# two bit columns and a tap
    variable CENTRE 68         ;# tap, u_wen 8, u_cg 34, u_sel (and2_4), slack, tap
}
# site index of bit column b
proc rf::cols {b} {
    variable LEFT; variable PAIR; variable CENTRE
    set base [expr {$b < 32 ? $LEFT : $LEFT + 16 * $PAIR + $CENTRE}]
    set bb [expr {$b % 32}]
    return [expr {$base + $PAIR * ($bb / 2) + 27 * ($bb % 2)}]
}
proc rf::retap {r0 rtop} {
    variable LEFT; variable PAIR; variable CENTRE
    set sites {}
    for {set p 0} {$p < 16} {incr p} {
        lappend sites [expr {$LEFT + $PAIR * $p + 54}]
        lappend sites [expr {$LEFT + 16 * $PAIR + $CENTRE + $PAIR * $p + 54}]
    }
    lappend sites [expr {$LEFT + 16 * $PAIR}] [expr {$LEFT + 16 * $PAIR + $CENTRE - 2}]
    fp::retap RFTAP $r0 $rtop 0 100000 $sites
}

proc rf::place {} {
    variable NROW; variable NGRP; variable y0; variable LEFT; variable PAIR
    set P i_chip_core/u_rf
    set r0 [fp::row_at $y0]
    set rtop [expr {$r0 + 3 + $NGRP * 9}]
    rf::retap $r0 $rtop
    lassign [lindex $fp::rows $r0] ry rx0 nsites orient sw rh
    set xc [expr {$rx0 + ($LEFT + 16 * $PAIR + 2) * $sw}]            ;# centre column, after its tap
    proc colx {b} { upvar rx0 rx0 sw sw; return [expr {$rx0 + [rf::cols $b] * $sw}] }
    proc must {inst ri x} {
        set e [fp::put $inst $ri $x]
        if { $e != $x + [[$inst getMaster] getWidth] } { error "rf: [$inst getName] is off its grid position" }
        return $e
    }
    # physical row index of logical word row r
    proc wrow {r} { upvar r0 r0; set k [expr {$r / 8}]; set j [expr {$r % 8}]
        return [expr {$r0 + 3 + $k * 9 + $j + ($j >= 4 ? 1 : 0)}] }
    # ---- foot rows
    for {set b 0} {$b < 64} {incr b} {
        set x [colx $b]
        set e [must [fp::inst "$P/g_col\[$b\].u_or"] $r0 $x]
        must [fp::inst "$P/g_col\[$b\].u_rn"] $r0 $e
        must [fp::inst "$P/g_col\[$b\].u_wd"] [expr {$r0 + 1}] $x
        set e [must [fp::inst "$P/g_col\[$b\].u_f0"] [expr {$r0 + 2}] $x]
        set e [must [fp::inst "$P/g_col\[$b\].u_f1"] [expr {$r0 + 2}] $e]
        must [fp::inst "$P/g_col\[$b\].u_f2"] [expr {$r0 + 2}] $e
    }
    # ---- word rows
    for {set r 0} {$r < $NROW} {incr r} {
        set ri [wrow $r]
        set e [must [fp::inst "$P/g_row\[$r\].u_wen"] $ri $xc]
        set e [must [fp::inst "$P/g_row\[$r\].u_cg"] $ri $e]
        must [fp::inst "$P/g_row\[$r\].u_sel"] $ri $e
        for {set b 0} {$b < 64} {incr b} {
            set e [must [fp::inst "$P/g_row\[$r\].g_bit\[$b\].u_lat"] $ri [colx $b]]
            must [fp::inst "$P/g_row\[$r\].g_bit\[$b\].u_rd"] $ri $e
        }
    }
    # ---- combiner rows
    for {set k 0} {$k < $NGRP} {incr k} {
        set ri [expr {$r0 + 3 + $k * 9 + 4}]
        must [fp::inst "$P/g_grp\[$k\].u_ckb"] $ri $xc
        for {set b 0} {$b < 64} {incr b} {
            set e [must [fp::inst "$P/g_grp\[$k\].g_bit\[$b\].u_na"] $ri [colx $b]]
            set e [must [fp::inst "$P/g_grp\[$k\].g_bit\[$b\].u_nb"] $ri $e]
            must [fp::inst "$P/g_grp\[$k\].g_bit\[$b\].u_gn"] $ri $e
        }
    }
    set ya [fp::row_y_um $r0]; set yb [fp::row_y_um $rtop]
    lappend fp::regions [list rf_array [expr {$rx0 / double($::dbu)}] $ya [expr {($rx0 + $nsites * $sw) / double($::dbu)}] $yb]
    metric rf_band_y0_um $ya
    metric rf_band_y1_um $yb
    metric rf_band_rows [expr {$rtop - $r0}]
    set ::rf_band [list $ya $yb]
}
rf::place
