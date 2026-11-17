# Dregg-180 v2 floorplan: block regions, organ pad affinity, guard spacing, the responder path.
# Sourced after fp_common.tcl, rf_array.tcl and puf_array.tcl. Boxes are {x1 y1 x2 y2} in um, die
# coordinates; the core is x 442.4 .. 1493.5, y 443.0 .. 2085.4. The register-file band occupies
# y 1219.1 .. 1548.4 over the full width (rf_array.tcl) and splits the core into a south part (datapath,
# control, the east and south organs) and a north part (PUF, TRNG, FRAM master).
#
#                     NORTH  an3 an2 DVSS DVDD an1 an0 | TAMPER F_MISO F_MOSI F_SCK F_CS
#        +-----------------------------------------------------------------------------+
#        | PUF ring array: 1008 rings + dummies, placed slots  |keep|   FRAM master      |
#        | 674 x 172 um                                        |out |                    |  CLKMON
#  VDD   +------------------- keep-out 20 um ------------------+----+     +--------------+
#  VSS   | PUF decoder, BCH, counters, ring select and OR tree      |     | TRNG 8 rings |  IRQ
#  strap |                                 shield / canary logic, glue    +--------------+  FAULT
#        +=============================================================================+
#        |            REGISTER FILE  72 x 64, placed array, Metal5 reserved            |  DVDD
#        |            bits 0..31 | word-line drivers | bits 32..63                     |  DVSS
#        +=============================================================================+
#        | word unit + hold register (strip under the read port)        | fast path -> |  DB_RESP
#        +-----------------------------------------------+--------------+  13 cells    |  DB_CHAL
#        | Keccak                                        |  distance registers, TDC    |
#        +---------------------------------------+-------+-----------+-----------------+
#        | microcode ROM + sequencer             |                   |  NFC front end  |  NFC_LM
#        |                                       |                   |                 |  NFC_ASK
#        +------------+--------------------------+-----+-------------+                 |  NFC_CLK
#        | clock,reset|              | SPI link        |             +-----------------+
#        +-----------------------------------------------------------------------------+
#                     SOUTH  CLK RST_N DVSS DVDD | SCK MOSI MISO CS_N
#
# Region sizing rule, measured on this OpenROAD (dcf3613). Global placement computes a region's
# utilisation as (its cells as the placer counts them) / (region area - B) and refuses above 100 %.
#   * The placer counts cells above their LEF area: +1 % for Keccak (large flops), +5 % NFC, +25 % for
#     the word unit, +35 % for the ROM (many small cells).
#   * B is the total area of all hard placement blockages in the design, charged to every region
#     whatever its position (19 k with the halos below; 29 k in a run with wider halos).
# A region therefore needs at least B + (placer-counted cells) / 0.85. Small organs end up at 30 to
# 45 % real fill; the rest of their region takes decap. Halos are kept as narrow as their purpose allows.

# ---- distance bounding: the responder path, flush against DB_CHAL (y 1024..1099) and DB_RESP
# (y 1126..1201) on the east edge. Pad -> u_mi0/u_mi1 isolation -> u_lock (capture) -> u_rapid_mux
# (select) -> pad, pre-placed FIRM and don't-touch, so synthesis repair, CTS and the placer cannot
# lengthen it. The route between the two pads is then at most about 180 um of wire.
fp::preplace db_fast {1415 1062 1492 1166} \
    {^i_chip_core/u_db/(u_rapid_mux|u_mi0|u_mi1|u_csiso|u_cs|u_lock|u_ccb|u_ehs)/} E
# the response registers, logs, coarse counter and the Vernier chain beside it
fp::region db   {1090 870 1492 1058} {^i_chip_core/u_db/}

# ---- NFC front end at NFC_CLK / NFC_ASK / NFC_LM (east, y 514..793): the recovered-carrier clock
# domain stays within 300 um of its pads and away from the register file
fp::region nfc  {1200 520 1492 856}  {^i_chip_core/u_nfc/}

# ---- datapath and control: NOT fenced by default (FP_FENCE_CORE=1 restores the fences of run g1).
# Measured: with word unit, Keccak and ROM + sequencer in their own regions the ROM region overflowed
# in global routing (9,070 tracks, all inside it, at 45 to 64 % fill), while the same netlist with no
# regions at all routed with zero overflow. The placer already puts these blocks next to the register
# file's read port; a fence only removes the whitespace the ROM's wiring needs.
if { [info exists ::env(FP_FENCE_CORE)] && $::env(FP_FENCE_CORE) } {
    fp::region wu   {445 1128 1405 1217} {^i_chip_core/(u_wu/|u_rf/(u_hold|_[0-9]+_|g_half))}
    fp::region kec  {445 870 1085 1124}  {^i_chip_core/u_kec/}
    fp::region ctl  {445 570 1195 866}   {^i_chip_core/(u_rom|u_seq)/}
}

# ---- SPI link at SCK / MOSI / MISO / CS_N (south, x 826..1214); clock, reset, tamper at CLK / RST_N
fp::region spi  {800 445 1195 566}   {^i_chip_core/u_spi/}
fp::region clk  {445 445 790 566}    {^i_chip_core/(u_clk/|u_ring/|u_oscbuf|u_clkroot)}

# ---- north part
# FRAM master under its four pads (north, x 1138..1526)
fp::region fram {1165 1975 1492 2083} {^i_chip_core/u_fram/}
# TRNG (eight rings, coherent sampling): east side of the north part, away from the register file's
# bit lines and from the SPI, FRAM and NFC clocks. No hard guard: a region admits no foreign cell, and
# it is sized for about 45 % fill, so the rings sit in decap.
fp::region trng {1240 1690 1492 1960} {^i_chip_core/u_trng/}
# PUF: 20 um keep-out (hard blockage) east and south of the placed array (physics R2.3); west and north
# are the core edge. Decoder, enable decode, output OR tree and counters below the keep-out (R4.4).
lassign $::puf_box px1 py1 px2 py2
fp::blockage [list $px2 [expr {$py1 - 20}] [expr {$px2 + 20}] 2085.4]
fp::blockage [list 443 [expr {$py1 - 20}] $px2 $py1]
fp::region pufd [list 445 1560 1120 [expr {$py1 - 24}]] {^i_chip_core/(u_puf/|u_pufcnt|u_pufarr/)}
