# Dregg-180 v2 floorplan: shared procedures (OpenROAD Tcl, odb API). Sourced first by every
# floorplan file. Expects ::block, ::dbu and proc `metric` from flow/pnr.tcl.
#
# All boxes are {x1 y1 x2 y2} in microns, die coordinates (core is 442.4 .. 1493.6 by 442.96 .. 2089.36).

namespace eval fp {
    variable rows {}        ;# list of {y_dbu x0_dbu nsites orient site_w row_h}, bottom to top
    variable occ            ;# row index -> list of {x1 x2} of fixed instances (dbu)
    array set occ {}
    variable regions {}     ;# for the renderer: {name x1 y1 x2 y2}
    variable groups {}      ;# {dbGroup x1 y1 x2 y2} in dbu
}

proc fp::init {} {
    variable rows; variable occ
    set l {}
    foreach r [$::block getRows] {
        set site [$r getSite]
        if { [$site getHeight] != 7840 } { continue }
        lassign [$r getOrigin] x y
        lappend l [list $y $x [$r getSiteCount] [$r getOrient] [$site getWidth] [$site getHeight]]
    }
    set rows [lsort -integer -index 0 $l]
    array unset occ
    set y0 [lindex $rows 0 0]
    set rh [lindex $rows 0 5]
    for {set i 0} {$i < [llength $rows]} {incr i} { set occ($i) {} }
    foreach inst [$::block getInsts] {
        if { ![$inst isFixed] } { continue }
        if { [[$inst getMaster] getType] ne "CORE" && ![string match "CORE*" [[$inst getMaster] getType]] && ![string match "ENDCAP*" [[$inst getMaster] getType]] } { continue }
        set bb [$inst getBBox]
        set i [expr {([$bb yMin] - $y0) / $rh}]
        if { $i < 0 || $i >= [llength $rows] } { continue }
        lappend occ($i) [list [$bb xMin] [$bb xMax]]
    }
    metric fp_rows [llength $rows]
    metric fp_row0_y_um [expr {[lindex $rows 0 0] / double($::dbu)}]
    metric fp_row_x0_um [expr {[lindex $rows 0 1] / double($::dbu)}]
    metric fp_row_sites [lindex $rows 0 2]
}

# row index of the row whose bottom is at or just above y (um)
proc fp::row_at {y_um} {
    variable rows
    set y0 [lindex $rows 0 0]; set rh [lindex $rows 0 5]
    set i [expr {int(ceil(($y_um * $::dbu - $y0) / double($rh)))}]
    if { $i < 0 } { set i 0 }
    return $i
}
proc fp::row_y_um {i} { variable rows; return [expr {[lindex $rows $i 0] / double($::dbu)}] }

# Place `inst` FIRM in row `ri` at the first legal site at or right of x (dbu) that is free of fixed
# cells. Returns the x just right of the placed cell. dir = -1 searches leftwards instead (the cell's
# right edge at or left of x) and returns the x just left of it.
proc fp::put {inst ri x {dir 1}} {
    variable rows; variable occ
    lassign [lindex $rows $ri] ry rx0 nsites orient sw rh
    set w [[$inst getMaster] getWidth]
    set xmax [expr {$rx0 + $nsites * $sw}]
    if { $dir > 0 } {
        set s [expr {($x - $rx0 + $sw - 1) / $sw}]
        if { $s < 0 } { set s 0 }
    } else {
        set s [expr {($x - $w - $rx0) / $sw}]
    }
    while { 1 } {
        set px [expr {$rx0 + $s * $sw}]
        if { $px < $rx0 || $px + $w > $xmax } { error "fp::put: no room in row $ri for [$inst getName]" }
        set hit 0
        foreach o $occ($ri) {
            lassign $o a b
            if { $px < $b && $px + $w > $a } {
                set hit 1
                if { $dir > 0 } { set s [expr {($b - $rx0 + $sw - 1) / $sw}] } else { set s [expr {($a - $w - $rx0) / $sw}] }
                break
            }
        }
        if { !$hit } { break }
    }
    $inst setOrient $orient
    $inst setLocation $px $ry
    $inst setPlacementStatus FIRM
    lappend occ($ri) [list $px [expr {$px + $w}]]
    if { $dir > 0 } { return [expr {$px + $w}] } else { return $px }
}

# odb keeps Verilog escapes in names (`g_row\[3\].g_bit\[5\].u_lat`); the floorplan files write names
# without them. fp::nn strips the backslashes for matching, fp::inst finds either spelling.
proc fp::nn {name} { return [string map [list "\\" ""] $name] }
proc fp::inst {name} {
    set i [$::block findInst $name]
    if { $i eq "NULL" } { set i [$::block findInst [string map [list "\[" "\\\[" "\]" "\\\]"] $name]] }
    if { $i eq "NULL" } { error "fp: no instance $name" }
    return $i
}

# Region for the instances whose name matches rx. The placer counts a region at about 1.25 to 1.3
# times its geometric fill, so size it for at most 70 to 75 % (basin-search finding).
proc fp::region {name box rx} {
    variable regions
    lassign $box x1 y1 x2 y2
    set region [odb::dbRegion_create $::block $name]
    odb::dbBox_create $region [expr {int($x1*$::dbu)}] [expr {int($y1*$::dbu)}] [expr {int($x2*$::dbu)}] [expr {int($y2*$::dbu)}]
    set group [odb::dbGroup_create $region g_$name]
    set n 0; set a 0.0
    foreach inst [$::block getInsts] {
        if { [$inst isFixed] } { continue }
        if { [regexp $rx [fp::nn [$inst getName]]] && [[$inst getMaster] getType] eq "CORE" } {
            $group addInst $inst
            incr n
            set m [$inst getMaster]
            set a [expr {$a + double([$m getWidth]) * [$m getHeight] / ($::dbu*$::dbu)}]
        }
    }
    lappend regions [list $name $x1 $y1 $x2 $y2]
    lappend fp::groups [list $group [expr {int($x1*$::dbu)}] [expr {int($y1*$::dbu)}] [expr {int($x2*$::dbu)}] [expr {int($y2*$::dbu)}]]
    metric region_${name}_insts $n
    metric region_${name}_cell_um2 [format %.0f $a]
    metric region_${name}_fill_pct [format %.1f [expr {100.0*$a/(($x2-$x1)*($y2-$y1))}]]
}

# Hard placement blockage (guard spacing, halo). Fixed tap cells under it make check_placement
# print "not in rows" for them; that is the halo, not a failure.
proc fp::blockage {box} {
    lassign $box x1 y1 x2 y2
    odb::dbBlockage_create $::block [expr {int($x1*$::dbu)}] [expr {int($y1*$::dbu)}] [expr {int($x2*$::dbu)}] [expr {int($y2*$::dbu)}]
}
# Soft blockage: global placement may not use it, later buffers and fill may (decap ends up here).
proc fp::soft_blockage {box} {
    set b [fp::blockage $box]
    $b setSoft
}

# Pre-place a handful of cells FIRM inside box, filling rows from one edge (E: right-most sites first,
# rows bottom to top; W, S: left-most first). For paths of a few cells; a region that small diverges.
proc fp::preplace {name box rx edge} {
    lassign $box bx1 by1 bx2 by2
    set r0 [fp::row_at $by1]
    set cells {}
    foreach inst [$::block getInsts] {
        if { [regexp $rx [fp::nn [$inst getName]]] && [[$inst getMaster] getType] eq "CORE" && ![$inst isFixed] } { lappend cells $inst }
    }
    set cells [lsort -command {apply {{a b} {string compare [$a getName] [$b getName]}}} $cells]
    set r $r0
    set x [expr {$edge eq "E" ? int($bx2*$::dbu) : int($bx1*$::dbu)}]
    set n 0
    foreach inst $cells {
        set w [[$inst getMaster] getWidth]
        if { $edge eq "E" } {
            if { $x - $w < int($bx1*$::dbu) } { incr r; set x [expr {int($bx2*$::dbu)}] }
            set x [fp::put $inst $r $x -1]
        } else {
            if { $x + $w > int($bx2*$::dbu) } { incr r; set x [expr {int($bx1*$::dbu)}] }
            set x [fp::put $inst $r $x 1]
        }
        incr n
    }
    metric preplace_${name}_cells $n
    metric preplace_${name}_rows [expr {$r - $r0 + 1}]
}

# Detailed placement keeps cells that belong to no group out of every region (measured: 1,602 repair
# buffers created inside the ROM region could not be legalised). After each step that creates cells
# (repair_design, CTS, timing repair), give every ungrouped movable cell that sits inside a region to
# that region's group, so buffers stay with the logic they serve.
proc fp::regroup {} {
    variable groups
    set n 0
    foreach inst [$::block getInsts] {
        if { [$inst isFixed] || [$inst getGroup] ne "NULL" } { continue }
        if { [[$inst getMaster] getType] ne "CORE" } { continue }
        lassign [$inst getLocation] x y
        foreach g $groups {
            lassign $g grp x1 y1 x2 y2
            if { $x >= $x1 && $x < $x2 && $y >= $y1 && $y < $y2 } { $grp addInst $inst; incr n; break }
        }
    }
    metric regrouped_insts $n
}

proc fp::dump_regions {path} {
    variable regions
    set f [open $path w]
    puts $f "\["
    set first 1
    foreach r $regions {
        lassign $r n x1 y1 x2 y2
        if { !$first } { puts $f "," }
        puts -nonewline $f "  {\"name\": \"$n\", \"box\": \[$x1, $y1, $x2, $y2\]}"
        set first 0
    }
    puts $f "\n\]"
    close $f
}

# Replace the template's tap cells in rows r0 .. rtop-1, between site indices slo and shi, by taps at
# the given site indices (same in every row). For hand-placed arrays whose cells cannot straddle the
# template's staggered taps. The new taps are LOCKED and connected like the old ones.
proc fp::retap {prefix r0 rtop slo shi sites} {
    variable rows; variable occ
    set ya [lindex $rows $r0 0]
    set rh [lindex $rows 0 5]; set sw [lindex $rows 0 4]; set rx0 [lindex $rows 0 1]
    set yb [expr {[lindex $rows [expr {$rtop - 1}] 0] + $rh}]
    set xa [expr {$rx0 + $slo * $sw}]; set xb [expr {$rx0 + $shi * $sw}]
    set n 0
    foreach inst [$::block getInsts] {
        if { [[$inst getMaster] getName] ne "gf180mcu_fd_sc_mcu7t5v0__filltie" } { continue }
        set bb [$inst getBBox]
        if { [$bb yMin] >= $ya && [$bb yMin] < $yb && [$bb xMin] >= $xa && [$bb xMin] < $xb } { odb::dbInst_destroy $inst; incr n }
    }
    metric ${prefix}_taps_removed $n
    fp::init
    set tapm [[ord::get_db] findMaster gf180mcu_fd_sc_mcu7t5v0__filltie]
    set n 0
    for {set ri $r0} {$ri < $rtop} {incr ri} {
        lassign [lindex $rows $ri] ry rx0 nsites orient sw rh
        foreach s $sites {
            set t [odb::dbInst_create $::block $tapm ${prefix}_${ri}_$s]
            $t setOrient $orient
            $t setLocation [expr {$rx0 + $s * $sw}] $ry
            $t setPlacementStatus LOCKED
            lappend occ($ri) [list [expr {$rx0 + $s * $sw}] [expr {$rx0 + ($s + 2) * $sw}]]
            incr n
        }
    }
    metric ${prefix}_taps_placed $n
    catch { global_connect }
}

fp::init
