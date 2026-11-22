* TRNG rings of rtl/qsag_trng.sv: 7-stage (fast) and 13-stage (slow) NAND2 rings, nand2_1 cells.
* Measures period and average supply current of each ring for the analytic thermal-jitter estimate
* (see trng_jitter_estimate.py).  No noise is simulated here.
* Assumed: 5 fF wire load per stage (same as the PUF deck), no mismatch.
.include "/spice/pdk/ngspice/design.ngspice"
.param sw_stat_global=0 sw_stat_mismatch=0
* __CORNER__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.param vdd_val=5.0
.temp 27
* __END__
.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.options klu method=gear reltol=1e-4
VF VDDF 0 {vdd_val}
VS VDDS 0 {vdd_val}
VEN EN 0 PWL(0 0 0.4n 0 0.6n {vdd_val})
.subckt st a z vdd vss
X0 a a z vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C0 z vss 5.0f
.ends
* fast ring, 7 stages (first stage gated)
XF0 f7 EN f1 VDDF VDDF 0 0 gf180mcu_fd_sc_mcu7t5v0__nand2_1
CF0 f1 0 5.0f
XF1 f1 f2 VDDF 0 st
XF2 f2 f3 VDDF 0 st
XF3 f3 f4 VDDF 0 st
XF4 f4 f5 VDDF 0 st
XF5 f5 f6 VDDF 0 st
XF6 f6 f7 VDDF 0 st
* slow ring, 13 stages
XS0 s13 EN s1 VDDS VDDS 0 0 gf180mcu_fd_sc_mcu7t5v0__nand2_1
CS0 s1 0 5.0f
XS1 s1 s2 VDDS 0 st
XS2 s2 s3 VDDS 0 st
XS3 s3 s4 VDDS 0 st
XS4 s4 s5 VDDS 0 st
XS5 s5 s6 VDDS 0 st
XS6 s6 s7 VDDS 0 st
XS7 s7 s8 VDDS 0 st
XS8 s8 s9 VDDS 0 st
XS9 s9 s10 VDDS 0 st
XS10 s10 s11 VDDS 0 st
XS11 s11 s12 VDDS 0 st
XS12 s12 s13 VDDS 0 st
.param vmid='vdd_val/2'
.tran 10p 80n 0 10p
.meas tran per_fast TRIG v(f7) VAL=vmid RISE=5 TARG v(f7) VAL=vmid RISE=15
.meas tran per_slow TRIG v(s13) VAL=vmid RISE=3 TARG v(s13) VAL=vmid RISE=13
.meas tran i_fast AVG i(VF) FROM=20n TO=80n
.meas tran i_slow AVG i(VS) FROM=20n TO=80n
.meas tran tr_fast TRIG v(f7) VAL='0.2*vdd_val' RISE=5 TARG v(f7) VAL='0.8*vdd_val' RISE=5
.end
