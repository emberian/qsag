* Foundry Pelgrom mismatch: 128 physical five-stage NAND ROs (64 disjoint pairs).
* Topology follows dregg_puf_ro5; inverter-ring witnesses retain the earlier comparison.
* Independent local mismatch enabled; global process spread disabled.
* Seed is set BEFORE model parsing in .spiceinit by run_corners.py.
* No transient-noise claim: BER postprocessing uses measured frequencies and an
* explicit asynchronous counter quantization/stop-edge model (see README.md).
.include "/spice/pdk/ngspice/design.ngspice"
.param sw_stat_global=0 sw_stat_mismatch=1
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.param vdd_val=5.0
.temp 27
* __CORNER_END__
.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.options klu method=gear reltol=1e-4
VVDD VDD 0 {vdd_val}
VVSS VSS 0 0
VEN EN 0 PWL(0 0 0.4n 0 0.6n {vdd_val})
.subckt puf_ro5_inv en osc vdd vss
X0 osc en n1  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_2
C0 n1  vss 5.0f
X1 n1  n2     vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C1 n2  vss 5.0f
X2 n2  n3     vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C2 n3  vss 5.0f
X3 n3  n4     vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C3 n4  vss 5.0f
X4 n4  osc    vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C4 osc vss 5.0f
.ends puf_ro5_inv

* Topology 2: Exact dregg_puf_ro5 (buf_2 iso + 5x nand2_1, compact 14 um row -> 5.0 fF/stage)
.subckt puf_ro5_nand en osc vdd vss
XI en  eni    vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_2
X0 osc eni n1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C0 n1  vss 5.0f
X1 n1  n1  n2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C1 n2  vss 5.0f
X2 n2  n2  n3 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C2 n3  vss 5.0f
X3 n3  n3  n4 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C3 n4  vss 5.0f
X4 n4  n4  osc vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C4 osc vss 5.0f
.ends puf_ro5_nand

X_INVA EN OSC_INVA VDD VSS puf_ro5_inv
X_INVB EN OSC_INVB VDD VSS puf_ro5_inv
X_RO0 EN OSC0 VDD VSS puf_ro5_nand
X_RO1 EN OSC1 VDD VSS puf_ro5_nand
X_RO2 EN OSC2 VDD VSS puf_ro5_nand
X_RO3 EN OSC3 VDD VSS puf_ro5_nand
X_RO4 EN OSC4 VDD VSS puf_ro5_nand
X_RO5 EN OSC5 VDD VSS puf_ro5_nand
X_RO6 EN OSC6 VDD VSS puf_ro5_nand
X_RO7 EN OSC7 VDD VSS puf_ro5_nand
X_RO8 EN OSC8 VDD VSS puf_ro5_nand
X_RO9 EN OSC9 VDD VSS puf_ro5_nand
X_RO10 EN OSC10 VDD VSS puf_ro5_nand
X_RO11 EN OSC11 VDD VSS puf_ro5_nand
X_RO12 EN OSC12 VDD VSS puf_ro5_nand
X_RO13 EN OSC13 VDD VSS puf_ro5_nand
X_RO14 EN OSC14 VDD VSS puf_ro5_nand
X_RO15 EN OSC15 VDD VSS puf_ro5_nand
X_RO16 EN OSC16 VDD VSS puf_ro5_nand
X_RO17 EN OSC17 VDD VSS puf_ro5_nand
X_RO18 EN OSC18 VDD VSS puf_ro5_nand
X_RO19 EN OSC19 VDD VSS puf_ro5_nand
X_RO20 EN OSC20 VDD VSS puf_ro5_nand
X_RO21 EN OSC21 VDD VSS puf_ro5_nand
X_RO22 EN OSC22 VDD VSS puf_ro5_nand
X_RO23 EN OSC23 VDD VSS puf_ro5_nand
X_RO24 EN OSC24 VDD VSS puf_ro5_nand
X_RO25 EN OSC25 VDD VSS puf_ro5_nand
X_RO26 EN OSC26 VDD VSS puf_ro5_nand
X_RO27 EN OSC27 VDD VSS puf_ro5_nand
X_RO28 EN OSC28 VDD VSS puf_ro5_nand
X_RO29 EN OSC29 VDD VSS puf_ro5_nand
X_RO30 EN OSC30 VDD VSS puf_ro5_nand
X_RO31 EN OSC31 VDD VSS puf_ro5_nand
X_RO32 EN OSC32 VDD VSS puf_ro5_nand
X_RO33 EN OSC33 VDD VSS puf_ro5_nand
X_RO34 EN OSC34 VDD VSS puf_ro5_nand
X_RO35 EN OSC35 VDD VSS puf_ro5_nand
X_RO36 EN OSC36 VDD VSS puf_ro5_nand
X_RO37 EN OSC37 VDD VSS puf_ro5_nand
X_RO38 EN OSC38 VDD VSS puf_ro5_nand
X_RO39 EN OSC39 VDD VSS puf_ro5_nand
X_RO40 EN OSC40 VDD VSS puf_ro5_nand
X_RO41 EN OSC41 VDD VSS puf_ro5_nand
X_RO42 EN OSC42 VDD VSS puf_ro5_nand
X_RO43 EN OSC43 VDD VSS puf_ro5_nand
X_RO44 EN OSC44 VDD VSS puf_ro5_nand
X_RO45 EN OSC45 VDD VSS puf_ro5_nand
X_RO46 EN OSC46 VDD VSS puf_ro5_nand
X_RO47 EN OSC47 VDD VSS puf_ro5_nand
X_RO48 EN OSC48 VDD VSS puf_ro5_nand
X_RO49 EN OSC49 VDD VSS puf_ro5_nand
X_RO50 EN OSC50 VDD VSS puf_ro5_nand
X_RO51 EN OSC51 VDD VSS puf_ro5_nand
X_RO52 EN OSC52 VDD VSS puf_ro5_nand
X_RO53 EN OSC53 VDD VSS puf_ro5_nand
X_RO54 EN OSC54 VDD VSS puf_ro5_nand
X_RO55 EN OSC55 VDD VSS puf_ro5_nand
X_RO56 EN OSC56 VDD VSS puf_ro5_nand
X_RO57 EN OSC57 VDD VSS puf_ro5_nand
X_RO58 EN OSC58 VDD VSS puf_ro5_nand
X_RO59 EN OSC59 VDD VSS puf_ro5_nand
X_RO60 EN OSC60 VDD VSS puf_ro5_nand
X_RO61 EN OSC61 VDD VSS puf_ro5_nand
X_RO62 EN OSC62 VDD VSS puf_ro5_nand
X_RO63 EN OSC63 VDD VSS puf_ro5_nand
X_RO64 EN OSC64 VDD VSS puf_ro5_nand
X_RO65 EN OSC65 VDD VSS puf_ro5_nand
X_RO66 EN OSC66 VDD VSS puf_ro5_nand
X_RO67 EN OSC67 VDD VSS puf_ro5_nand
X_RO68 EN OSC68 VDD VSS puf_ro5_nand
X_RO69 EN OSC69 VDD VSS puf_ro5_nand
X_RO70 EN OSC70 VDD VSS puf_ro5_nand
X_RO71 EN OSC71 VDD VSS puf_ro5_nand
X_RO72 EN OSC72 VDD VSS puf_ro5_nand
X_RO73 EN OSC73 VDD VSS puf_ro5_nand
X_RO74 EN OSC74 VDD VSS puf_ro5_nand
X_RO75 EN OSC75 VDD VSS puf_ro5_nand
X_RO76 EN OSC76 VDD VSS puf_ro5_nand
X_RO77 EN OSC77 VDD VSS puf_ro5_nand
X_RO78 EN OSC78 VDD VSS puf_ro5_nand
X_RO79 EN OSC79 VDD VSS puf_ro5_nand
X_RO80 EN OSC80 VDD VSS puf_ro5_nand
X_RO81 EN OSC81 VDD VSS puf_ro5_nand
X_RO82 EN OSC82 VDD VSS puf_ro5_nand
X_RO83 EN OSC83 VDD VSS puf_ro5_nand
X_RO84 EN OSC84 VDD VSS puf_ro5_nand
X_RO85 EN OSC85 VDD VSS puf_ro5_nand
X_RO86 EN OSC86 VDD VSS puf_ro5_nand
X_RO87 EN OSC87 VDD VSS puf_ro5_nand
X_RO88 EN OSC88 VDD VSS puf_ro5_nand
X_RO89 EN OSC89 VDD VSS puf_ro5_nand
X_RO90 EN OSC90 VDD VSS puf_ro5_nand
X_RO91 EN OSC91 VDD VSS puf_ro5_nand
X_RO92 EN OSC92 VDD VSS puf_ro5_nand
X_RO93 EN OSC93 VDD VSS puf_ro5_nand
X_RO94 EN OSC94 VDD VSS puf_ro5_nand
X_RO95 EN OSC95 VDD VSS puf_ro5_nand
X_RO96 EN OSC96 VDD VSS puf_ro5_nand
X_RO97 EN OSC97 VDD VSS puf_ro5_nand
X_RO98 EN OSC98 VDD VSS puf_ro5_nand
X_RO99 EN OSC99 VDD VSS puf_ro5_nand
X_RO100 EN OSC100 VDD VSS puf_ro5_nand
X_RO101 EN OSC101 VDD VSS puf_ro5_nand
X_RO102 EN OSC102 VDD VSS puf_ro5_nand
X_RO103 EN OSC103 VDD VSS puf_ro5_nand
X_RO104 EN OSC104 VDD VSS puf_ro5_nand
X_RO105 EN OSC105 VDD VSS puf_ro5_nand
X_RO106 EN OSC106 VDD VSS puf_ro5_nand
X_RO107 EN OSC107 VDD VSS puf_ro5_nand
X_RO108 EN OSC108 VDD VSS puf_ro5_nand
X_RO109 EN OSC109 VDD VSS puf_ro5_nand
X_RO110 EN OSC110 VDD VSS puf_ro5_nand
X_RO111 EN OSC111 VDD VSS puf_ro5_nand
X_RO112 EN OSC112 VDD VSS puf_ro5_nand
X_RO113 EN OSC113 VDD VSS puf_ro5_nand
X_RO114 EN OSC114 VDD VSS puf_ro5_nand
X_RO115 EN OSC115 VDD VSS puf_ro5_nand
X_RO116 EN OSC116 VDD VSS puf_ro5_nand
X_RO117 EN OSC117 VDD VSS puf_ro5_nand
X_RO118 EN OSC118 VDD VSS puf_ro5_nand
X_RO119 EN OSC119 VDD VSS puf_ro5_nand
X_RO120 EN OSC120 VDD VSS puf_ro5_nand
X_RO121 EN OSC121 VDD VSS puf_ro5_nand
X_RO122 EN OSC122 VDD VSS puf_ro5_nand
X_RO123 EN OSC123 VDD VSS puf_ro5_nand
X_RO124 EN OSC124 VDD VSS puf_ro5_nand
X_RO125 EN OSC125 VDD VSS puf_ro5_nand
X_RO126 EN OSC126 VDD VSS puf_ro5_nand
X_RO127 EN OSC127 VDD VSS puf_ro5_nand

.save v(VDD) v(OSC_INVA) v(OSC_INVB)
.save v(OSC0)
.save v(OSC1)
.save v(OSC2)
.save v(OSC3)
.save v(OSC4)
.save v(OSC5)
.save v(OSC6)
.save v(OSC7)
.save v(OSC8)
.save v(OSC9)
.save v(OSC10)
.save v(OSC11)
.save v(OSC12)
.save v(OSC13)
.save v(OSC14)
.save v(OSC15)
.save v(OSC16)
.save v(OSC17)
.save v(OSC18)
.save v(OSC19)
.save v(OSC20)
.save v(OSC21)
.save v(OSC22)
.save v(OSC23)
.save v(OSC24)
.save v(OSC25)
.save v(OSC26)
.save v(OSC27)
.save v(OSC28)
.save v(OSC29)
.save v(OSC30)
.save v(OSC31)
.save v(OSC32)
.save v(OSC33)
.save v(OSC34)
.save v(OSC35)
.save v(OSC36)
.save v(OSC37)
.save v(OSC38)
.save v(OSC39)
.save v(OSC40)
.save v(OSC41)
.save v(OSC42)
.save v(OSC43)
.save v(OSC44)
.save v(OSC45)
.save v(OSC46)
.save v(OSC47)
.save v(OSC48)
.save v(OSC49)
.save v(OSC50)
.save v(OSC51)
.save v(OSC52)
.save v(OSC53)
.save v(OSC54)
.save v(OSC55)
.save v(OSC56)
.save v(OSC57)
.save v(OSC58)
.save v(OSC59)
.save v(OSC60)
.save v(OSC61)
.save v(OSC62)
.save v(OSC63)
.save v(OSC64)
.save v(OSC65)
.save v(OSC66)
.save v(OSC67)
.save v(OSC68)
.save v(OSC69)
.save v(OSC70)
.save v(OSC71)
.save v(OSC72)
.save v(OSC73)
.save v(OSC74)
.save v(OSC75)
.save v(OSC76)
.save v(OSC77)
.save v(OSC78)
.save v(OSC79)
.save v(OSC80)
.save v(OSC81)
.save v(OSC82)
.save v(OSC83)
.save v(OSC84)
.save v(OSC85)
.save v(OSC86)
.save v(OSC87)
.save v(OSC88)
.save v(OSC89)
.save v(OSC90)
.save v(OSC91)
.save v(OSC92)
.save v(OSC93)
.save v(OSC94)
.save v(OSC95)
.save v(OSC96)
.save v(OSC97)
.save v(OSC98)
.save v(OSC99)
.save v(OSC100)
.save v(OSC101)
.save v(OSC102)
.save v(OSC103)
.save v(OSC104)
.save v(OSC105)
.save v(OSC106)
.save v(OSC107)
.save v(OSC108)
.save v(OSC109)
.save v(OSC110)
.save v(OSC111)
.save v(OSC112)
.save v(OSC113)
.save v(OSC114)
.save v(OSC115)
.save v(OSC116)
.save v(OSC117)
.save v(OSC118)
.save v(OSC119)
.save v(OSC120)
.save v(OSC121)
.save v(OSC122)
.save v(OSC123)
.save v(OSC124)
.save v(OSC125)
.save v(OSC126)
.save v(OSC127)
.tran 20p 80n 0 20p
.param vmid=0.5*vdd_val
.meas tran period_0 TRIG v(OSC0) VAL=vmid RISE=5 TARG v(OSC0) VAL=vmid RISE=15
.meas tran freq_0 PARAM='10/period_0'
.meas tran high_0 MAX v(OSC0) FROM=20n TO=80n
.meas tran low_0 MIN v(OSC0) FROM=20n TO=80n
.meas tran pass_ro_0 PARAM='(freq_0>1e6)*(freq_0<2e9)*(high_0>0.8*vdd_val)*(low_0<0.2*vdd_val)'
.meas tran period_1 TRIG v(OSC1) VAL=vmid RISE=5 TARG v(OSC1) VAL=vmid RISE=15
.meas tran freq_1 PARAM='10/period_1'
.meas tran high_1 MAX v(OSC1) FROM=20n TO=80n
.meas tran low_1 MIN v(OSC1) FROM=20n TO=80n
.meas tran pass_ro_1 PARAM='(freq_1>1e6)*(freq_1<2e9)*(high_1>0.8*vdd_val)*(low_1<0.2*vdd_val)'
.meas tran period_2 TRIG v(OSC2) VAL=vmid RISE=5 TARG v(OSC2) VAL=vmid RISE=15
.meas tran freq_2 PARAM='10/period_2'
.meas tran high_2 MAX v(OSC2) FROM=20n TO=80n
.meas tran low_2 MIN v(OSC2) FROM=20n TO=80n
.meas tran pass_ro_2 PARAM='(freq_2>1e6)*(freq_2<2e9)*(high_2>0.8*vdd_val)*(low_2<0.2*vdd_val)'
.meas tran period_3 TRIG v(OSC3) VAL=vmid RISE=5 TARG v(OSC3) VAL=vmid RISE=15
.meas tran freq_3 PARAM='10/period_3'
.meas tran high_3 MAX v(OSC3) FROM=20n TO=80n
.meas tran low_3 MIN v(OSC3) FROM=20n TO=80n
.meas tran pass_ro_3 PARAM='(freq_3>1e6)*(freq_3<2e9)*(high_3>0.8*vdd_val)*(low_3<0.2*vdd_val)'
.meas tran period_4 TRIG v(OSC4) VAL=vmid RISE=5 TARG v(OSC4) VAL=vmid RISE=15
.meas tran freq_4 PARAM='10/period_4'
.meas tran high_4 MAX v(OSC4) FROM=20n TO=80n
.meas tran low_4 MIN v(OSC4) FROM=20n TO=80n
.meas tran pass_ro_4 PARAM='(freq_4>1e6)*(freq_4<2e9)*(high_4>0.8*vdd_val)*(low_4<0.2*vdd_val)'
.meas tran period_5 TRIG v(OSC5) VAL=vmid RISE=5 TARG v(OSC5) VAL=vmid RISE=15
.meas tran freq_5 PARAM='10/period_5'
.meas tran high_5 MAX v(OSC5) FROM=20n TO=80n
.meas tran low_5 MIN v(OSC5) FROM=20n TO=80n
.meas tran pass_ro_5 PARAM='(freq_5>1e6)*(freq_5<2e9)*(high_5>0.8*vdd_val)*(low_5<0.2*vdd_val)'
.meas tran period_6 TRIG v(OSC6) VAL=vmid RISE=5 TARG v(OSC6) VAL=vmid RISE=15
.meas tran freq_6 PARAM='10/period_6'
.meas tran high_6 MAX v(OSC6) FROM=20n TO=80n
.meas tran low_6 MIN v(OSC6) FROM=20n TO=80n
.meas tran pass_ro_6 PARAM='(freq_6>1e6)*(freq_6<2e9)*(high_6>0.8*vdd_val)*(low_6<0.2*vdd_val)'
.meas tran period_7 TRIG v(OSC7) VAL=vmid RISE=5 TARG v(OSC7) VAL=vmid RISE=15
.meas tran freq_7 PARAM='10/period_7'
.meas tran high_7 MAX v(OSC7) FROM=20n TO=80n
.meas tran low_7 MIN v(OSC7) FROM=20n TO=80n
.meas tran pass_ro_7 PARAM='(freq_7>1e6)*(freq_7<2e9)*(high_7>0.8*vdd_val)*(low_7<0.2*vdd_val)'
.meas tran period_8 TRIG v(OSC8) VAL=vmid RISE=5 TARG v(OSC8) VAL=vmid RISE=15
.meas tran freq_8 PARAM='10/period_8'
.meas tran high_8 MAX v(OSC8) FROM=20n TO=80n
.meas tran low_8 MIN v(OSC8) FROM=20n TO=80n
.meas tran pass_ro_8 PARAM='(freq_8>1e6)*(freq_8<2e9)*(high_8>0.8*vdd_val)*(low_8<0.2*vdd_val)'
.meas tran period_9 TRIG v(OSC9) VAL=vmid RISE=5 TARG v(OSC9) VAL=vmid RISE=15
.meas tran freq_9 PARAM='10/period_9'
.meas tran high_9 MAX v(OSC9) FROM=20n TO=80n
.meas tran low_9 MIN v(OSC9) FROM=20n TO=80n
.meas tran pass_ro_9 PARAM='(freq_9>1e6)*(freq_9<2e9)*(high_9>0.8*vdd_val)*(low_9<0.2*vdd_val)'
.meas tran period_10 TRIG v(OSC10) VAL=vmid RISE=5 TARG v(OSC10) VAL=vmid RISE=15
.meas tran freq_10 PARAM='10/period_10'
.meas tran high_10 MAX v(OSC10) FROM=20n TO=80n
.meas tran low_10 MIN v(OSC10) FROM=20n TO=80n
.meas tran pass_ro_10 PARAM='(freq_10>1e6)*(freq_10<2e9)*(high_10>0.8*vdd_val)*(low_10<0.2*vdd_val)'
.meas tran period_11 TRIG v(OSC11) VAL=vmid RISE=5 TARG v(OSC11) VAL=vmid RISE=15
.meas tran freq_11 PARAM='10/period_11'
.meas tran high_11 MAX v(OSC11) FROM=20n TO=80n
.meas tran low_11 MIN v(OSC11) FROM=20n TO=80n
.meas tran pass_ro_11 PARAM='(freq_11>1e6)*(freq_11<2e9)*(high_11>0.8*vdd_val)*(low_11<0.2*vdd_val)'
.meas tran period_12 TRIG v(OSC12) VAL=vmid RISE=5 TARG v(OSC12) VAL=vmid RISE=15
.meas tran freq_12 PARAM='10/period_12'
.meas tran high_12 MAX v(OSC12) FROM=20n TO=80n
.meas tran low_12 MIN v(OSC12) FROM=20n TO=80n
.meas tran pass_ro_12 PARAM='(freq_12>1e6)*(freq_12<2e9)*(high_12>0.8*vdd_val)*(low_12<0.2*vdd_val)'
.meas tran period_13 TRIG v(OSC13) VAL=vmid RISE=5 TARG v(OSC13) VAL=vmid RISE=15
.meas tran freq_13 PARAM='10/period_13'
.meas tran high_13 MAX v(OSC13) FROM=20n TO=80n
.meas tran low_13 MIN v(OSC13) FROM=20n TO=80n
.meas tran pass_ro_13 PARAM='(freq_13>1e6)*(freq_13<2e9)*(high_13>0.8*vdd_val)*(low_13<0.2*vdd_val)'
.meas tran period_14 TRIG v(OSC14) VAL=vmid RISE=5 TARG v(OSC14) VAL=vmid RISE=15
.meas tran freq_14 PARAM='10/period_14'
.meas tran high_14 MAX v(OSC14) FROM=20n TO=80n
.meas tran low_14 MIN v(OSC14) FROM=20n TO=80n
.meas tran pass_ro_14 PARAM='(freq_14>1e6)*(freq_14<2e9)*(high_14>0.8*vdd_val)*(low_14<0.2*vdd_val)'
.meas tran period_15 TRIG v(OSC15) VAL=vmid RISE=5 TARG v(OSC15) VAL=vmid RISE=15
.meas tran freq_15 PARAM='10/period_15'
.meas tran high_15 MAX v(OSC15) FROM=20n TO=80n
.meas tran low_15 MIN v(OSC15) FROM=20n TO=80n
.meas tran pass_ro_15 PARAM='(freq_15>1e6)*(freq_15<2e9)*(high_15>0.8*vdd_val)*(low_15<0.2*vdd_val)'
.meas tran period_16 TRIG v(OSC16) VAL=vmid RISE=5 TARG v(OSC16) VAL=vmid RISE=15
.meas tran freq_16 PARAM='10/period_16'
.meas tran high_16 MAX v(OSC16) FROM=20n TO=80n
.meas tran low_16 MIN v(OSC16) FROM=20n TO=80n
.meas tran pass_ro_16 PARAM='(freq_16>1e6)*(freq_16<2e9)*(high_16>0.8*vdd_val)*(low_16<0.2*vdd_val)'
.meas tran period_17 TRIG v(OSC17) VAL=vmid RISE=5 TARG v(OSC17) VAL=vmid RISE=15
.meas tran freq_17 PARAM='10/period_17'
.meas tran high_17 MAX v(OSC17) FROM=20n TO=80n
.meas tran low_17 MIN v(OSC17) FROM=20n TO=80n
.meas tran pass_ro_17 PARAM='(freq_17>1e6)*(freq_17<2e9)*(high_17>0.8*vdd_val)*(low_17<0.2*vdd_val)'
.meas tran period_18 TRIG v(OSC18) VAL=vmid RISE=5 TARG v(OSC18) VAL=vmid RISE=15
.meas tran freq_18 PARAM='10/period_18'
.meas tran high_18 MAX v(OSC18) FROM=20n TO=80n
.meas tran low_18 MIN v(OSC18) FROM=20n TO=80n
.meas tran pass_ro_18 PARAM='(freq_18>1e6)*(freq_18<2e9)*(high_18>0.8*vdd_val)*(low_18<0.2*vdd_val)'
.meas tran period_19 TRIG v(OSC19) VAL=vmid RISE=5 TARG v(OSC19) VAL=vmid RISE=15
.meas tran freq_19 PARAM='10/period_19'
.meas tran high_19 MAX v(OSC19) FROM=20n TO=80n
.meas tran low_19 MIN v(OSC19) FROM=20n TO=80n
.meas tran pass_ro_19 PARAM='(freq_19>1e6)*(freq_19<2e9)*(high_19>0.8*vdd_val)*(low_19<0.2*vdd_val)'
.meas tran period_20 TRIG v(OSC20) VAL=vmid RISE=5 TARG v(OSC20) VAL=vmid RISE=15
.meas tran freq_20 PARAM='10/period_20'
.meas tran high_20 MAX v(OSC20) FROM=20n TO=80n
.meas tran low_20 MIN v(OSC20) FROM=20n TO=80n
.meas tran pass_ro_20 PARAM='(freq_20>1e6)*(freq_20<2e9)*(high_20>0.8*vdd_val)*(low_20<0.2*vdd_val)'
.meas tran period_21 TRIG v(OSC21) VAL=vmid RISE=5 TARG v(OSC21) VAL=vmid RISE=15
.meas tran freq_21 PARAM='10/period_21'
.meas tran high_21 MAX v(OSC21) FROM=20n TO=80n
.meas tran low_21 MIN v(OSC21) FROM=20n TO=80n
.meas tran pass_ro_21 PARAM='(freq_21>1e6)*(freq_21<2e9)*(high_21>0.8*vdd_val)*(low_21<0.2*vdd_val)'
.meas tran period_22 TRIG v(OSC22) VAL=vmid RISE=5 TARG v(OSC22) VAL=vmid RISE=15
.meas tran freq_22 PARAM='10/period_22'
.meas tran high_22 MAX v(OSC22) FROM=20n TO=80n
.meas tran low_22 MIN v(OSC22) FROM=20n TO=80n
.meas tran pass_ro_22 PARAM='(freq_22>1e6)*(freq_22<2e9)*(high_22>0.8*vdd_val)*(low_22<0.2*vdd_val)'
.meas tran period_23 TRIG v(OSC23) VAL=vmid RISE=5 TARG v(OSC23) VAL=vmid RISE=15
.meas tran freq_23 PARAM='10/period_23'
.meas tran high_23 MAX v(OSC23) FROM=20n TO=80n
.meas tran low_23 MIN v(OSC23) FROM=20n TO=80n
.meas tran pass_ro_23 PARAM='(freq_23>1e6)*(freq_23<2e9)*(high_23>0.8*vdd_val)*(low_23<0.2*vdd_val)'
.meas tran period_24 TRIG v(OSC24) VAL=vmid RISE=5 TARG v(OSC24) VAL=vmid RISE=15
.meas tran freq_24 PARAM='10/period_24'
.meas tran high_24 MAX v(OSC24) FROM=20n TO=80n
.meas tran low_24 MIN v(OSC24) FROM=20n TO=80n
.meas tran pass_ro_24 PARAM='(freq_24>1e6)*(freq_24<2e9)*(high_24>0.8*vdd_val)*(low_24<0.2*vdd_val)'
.meas tran period_25 TRIG v(OSC25) VAL=vmid RISE=5 TARG v(OSC25) VAL=vmid RISE=15
.meas tran freq_25 PARAM='10/period_25'
.meas tran high_25 MAX v(OSC25) FROM=20n TO=80n
.meas tran low_25 MIN v(OSC25) FROM=20n TO=80n
.meas tran pass_ro_25 PARAM='(freq_25>1e6)*(freq_25<2e9)*(high_25>0.8*vdd_val)*(low_25<0.2*vdd_val)'
.meas tran period_26 TRIG v(OSC26) VAL=vmid RISE=5 TARG v(OSC26) VAL=vmid RISE=15
.meas tran freq_26 PARAM='10/period_26'
.meas tran high_26 MAX v(OSC26) FROM=20n TO=80n
.meas tran low_26 MIN v(OSC26) FROM=20n TO=80n
.meas tran pass_ro_26 PARAM='(freq_26>1e6)*(freq_26<2e9)*(high_26>0.8*vdd_val)*(low_26<0.2*vdd_val)'
.meas tran period_27 TRIG v(OSC27) VAL=vmid RISE=5 TARG v(OSC27) VAL=vmid RISE=15
.meas tran freq_27 PARAM='10/period_27'
.meas tran high_27 MAX v(OSC27) FROM=20n TO=80n
.meas tran low_27 MIN v(OSC27) FROM=20n TO=80n
.meas tran pass_ro_27 PARAM='(freq_27>1e6)*(freq_27<2e9)*(high_27>0.8*vdd_val)*(low_27<0.2*vdd_val)'
.meas tran period_28 TRIG v(OSC28) VAL=vmid RISE=5 TARG v(OSC28) VAL=vmid RISE=15
.meas tran freq_28 PARAM='10/period_28'
.meas tran high_28 MAX v(OSC28) FROM=20n TO=80n
.meas tran low_28 MIN v(OSC28) FROM=20n TO=80n
.meas tran pass_ro_28 PARAM='(freq_28>1e6)*(freq_28<2e9)*(high_28>0.8*vdd_val)*(low_28<0.2*vdd_val)'
.meas tran period_29 TRIG v(OSC29) VAL=vmid RISE=5 TARG v(OSC29) VAL=vmid RISE=15
.meas tran freq_29 PARAM='10/period_29'
.meas tran high_29 MAX v(OSC29) FROM=20n TO=80n
.meas tran low_29 MIN v(OSC29) FROM=20n TO=80n
.meas tran pass_ro_29 PARAM='(freq_29>1e6)*(freq_29<2e9)*(high_29>0.8*vdd_val)*(low_29<0.2*vdd_val)'
.meas tran period_30 TRIG v(OSC30) VAL=vmid RISE=5 TARG v(OSC30) VAL=vmid RISE=15
.meas tran freq_30 PARAM='10/period_30'
.meas tran high_30 MAX v(OSC30) FROM=20n TO=80n
.meas tran low_30 MIN v(OSC30) FROM=20n TO=80n
.meas tran pass_ro_30 PARAM='(freq_30>1e6)*(freq_30<2e9)*(high_30>0.8*vdd_val)*(low_30<0.2*vdd_val)'
.meas tran period_31 TRIG v(OSC31) VAL=vmid RISE=5 TARG v(OSC31) VAL=vmid RISE=15
.meas tran freq_31 PARAM='10/period_31'
.meas tran high_31 MAX v(OSC31) FROM=20n TO=80n
.meas tran low_31 MIN v(OSC31) FROM=20n TO=80n
.meas tran pass_ro_31 PARAM='(freq_31>1e6)*(freq_31<2e9)*(high_31>0.8*vdd_val)*(low_31<0.2*vdd_val)'
.meas tran period_32 TRIG v(OSC32) VAL=vmid RISE=5 TARG v(OSC32) VAL=vmid RISE=15
.meas tran freq_32 PARAM='10/period_32'
.meas tran high_32 MAX v(OSC32) FROM=20n TO=80n
.meas tran low_32 MIN v(OSC32) FROM=20n TO=80n
.meas tran pass_ro_32 PARAM='(freq_32>1e6)*(freq_32<2e9)*(high_32>0.8*vdd_val)*(low_32<0.2*vdd_val)'
.meas tran period_33 TRIG v(OSC33) VAL=vmid RISE=5 TARG v(OSC33) VAL=vmid RISE=15
.meas tran freq_33 PARAM='10/period_33'
.meas tran high_33 MAX v(OSC33) FROM=20n TO=80n
.meas tran low_33 MIN v(OSC33) FROM=20n TO=80n
.meas tran pass_ro_33 PARAM='(freq_33>1e6)*(freq_33<2e9)*(high_33>0.8*vdd_val)*(low_33<0.2*vdd_val)'
.meas tran period_34 TRIG v(OSC34) VAL=vmid RISE=5 TARG v(OSC34) VAL=vmid RISE=15
.meas tran freq_34 PARAM='10/period_34'
.meas tran high_34 MAX v(OSC34) FROM=20n TO=80n
.meas tran low_34 MIN v(OSC34) FROM=20n TO=80n
.meas tran pass_ro_34 PARAM='(freq_34>1e6)*(freq_34<2e9)*(high_34>0.8*vdd_val)*(low_34<0.2*vdd_val)'
.meas tran period_35 TRIG v(OSC35) VAL=vmid RISE=5 TARG v(OSC35) VAL=vmid RISE=15
.meas tran freq_35 PARAM='10/period_35'
.meas tran high_35 MAX v(OSC35) FROM=20n TO=80n
.meas tran low_35 MIN v(OSC35) FROM=20n TO=80n
.meas tran pass_ro_35 PARAM='(freq_35>1e6)*(freq_35<2e9)*(high_35>0.8*vdd_val)*(low_35<0.2*vdd_val)'
.meas tran period_36 TRIG v(OSC36) VAL=vmid RISE=5 TARG v(OSC36) VAL=vmid RISE=15
.meas tran freq_36 PARAM='10/period_36'
.meas tran high_36 MAX v(OSC36) FROM=20n TO=80n
.meas tran low_36 MIN v(OSC36) FROM=20n TO=80n
.meas tran pass_ro_36 PARAM='(freq_36>1e6)*(freq_36<2e9)*(high_36>0.8*vdd_val)*(low_36<0.2*vdd_val)'
.meas tran period_37 TRIG v(OSC37) VAL=vmid RISE=5 TARG v(OSC37) VAL=vmid RISE=15
.meas tran freq_37 PARAM='10/period_37'
.meas tran high_37 MAX v(OSC37) FROM=20n TO=80n
.meas tran low_37 MIN v(OSC37) FROM=20n TO=80n
.meas tran pass_ro_37 PARAM='(freq_37>1e6)*(freq_37<2e9)*(high_37>0.8*vdd_val)*(low_37<0.2*vdd_val)'
.meas tran period_38 TRIG v(OSC38) VAL=vmid RISE=5 TARG v(OSC38) VAL=vmid RISE=15
.meas tran freq_38 PARAM='10/period_38'
.meas tran high_38 MAX v(OSC38) FROM=20n TO=80n
.meas tran low_38 MIN v(OSC38) FROM=20n TO=80n
.meas tran pass_ro_38 PARAM='(freq_38>1e6)*(freq_38<2e9)*(high_38>0.8*vdd_val)*(low_38<0.2*vdd_val)'
.meas tran period_39 TRIG v(OSC39) VAL=vmid RISE=5 TARG v(OSC39) VAL=vmid RISE=15
.meas tran freq_39 PARAM='10/period_39'
.meas tran high_39 MAX v(OSC39) FROM=20n TO=80n
.meas tran low_39 MIN v(OSC39) FROM=20n TO=80n
.meas tran pass_ro_39 PARAM='(freq_39>1e6)*(freq_39<2e9)*(high_39>0.8*vdd_val)*(low_39<0.2*vdd_val)'
.meas tran period_40 TRIG v(OSC40) VAL=vmid RISE=5 TARG v(OSC40) VAL=vmid RISE=15
.meas tran freq_40 PARAM='10/period_40'
.meas tran high_40 MAX v(OSC40) FROM=20n TO=80n
.meas tran low_40 MIN v(OSC40) FROM=20n TO=80n
.meas tran pass_ro_40 PARAM='(freq_40>1e6)*(freq_40<2e9)*(high_40>0.8*vdd_val)*(low_40<0.2*vdd_val)'
.meas tran period_41 TRIG v(OSC41) VAL=vmid RISE=5 TARG v(OSC41) VAL=vmid RISE=15
.meas tran freq_41 PARAM='10/period_41'
.meas tran high_41 MAX v(OSC41) FROM=20n TO=80n
.meas tran low_41 MIN v(OSC41) FROM=20n TO=80n
.meas tran pass_ro_41 PARAM='(freq_41>1e6)*(freq_41<2e9)*(high_41>0.8*vdd_val)*(low_41<0.2*vdd_val)'
.meas tran period_42 TRIG v(OSC42) VAL=vmid RISE=5 TARG v(OSC42) VAL=vmid RISE=15
.meas tran freq_42 PARAM='10/period_42'
.meas tran high_42 MAX v(OSC42) FROM=20n TO=80n
.meas tran low_42 MIN v(OSC42) FROM=20n TO=80n
.meas tran pass_ro_42 PARAM='(freq_42>1e6)*(freq_42<2e9)*(high_42>0.8*vdd_val)*(low_42<0.2*vdd_val)'
.meas tran period_43 TRIG v(OSC43) VAL=vmid RISE=5 TARG v(OSC43) VAL=vmid RISE=15
.meas tran freq_43 PARAM='10/period_43'
.meas tran high_43 MAX v(OSC43) FROM=20n TO=80n
.meas tran low_43 MIN v(OSC43) FROM=20n TO=80n
.meas tran pass_ro_43 PARAM='(freq_43>1e6)*(freq_43<2e9)*(high_43>0.8*vdd_val)*(low_43<0.2*vdd_val)'
.meas tran period_44 TRIG v(OSC44) VAL=vmid RISE=5 TARG v(OSC44) VAL=vmid RISE=15
.meas tran freq_44 PARAM='10/period_44'
.meas tran high_44 MAX v(OSC44) FROM=20n TO=80n
.meas tran low_44 MIN v(OSC44) FROM=20n TO=80n
.meas tran pass_ro_44 PARAM='(freq_44>1e6)*(freq_44<2e9)*(high_44>0.8*vdd_val)*(low_44<0.2*vdd_val)'
.meas tran period_45 TRIG v(OSC45) VAL=vmid RISE=5 TARG v(OSC45) VAL=vmid RISE=15
.meas tran freq_45 PARAM='10/period_45'
.meas tran high_45 MAX v(OSC45) FROM=20n TO=80n
.meas tran low_45 MIN v(OSC45) FROM=20n TO=80n
.meas tran pass_ro_45 PARAM='(freq_45>1e6)*(freq_45<2e9)*(high_45>0.8*vdd_val)*(low_45<0.2*vdd_val)'
.meas tran period_46 TRIG v(OSC46) VAL=vmid RISE=5 TARG v(OSC46) VAL=vmid RISE=15
.meas tran freq_46 PARAM='10/period_46'
.meas tran high_46 MAX v(OSC46) FROM=20n TO=80n
.meas tran low_46 MIN v(OSC46) FROM=20n TO=80n
.meas tran pass_ro_46 PARAM='(freq_46>1e6)*(freq_46<2e9)*(high_46>0.8*vdd_val)*(low_46<0.2*vdd_val)'
.meas tran period_47 TRIG v(OSC47) VAL=vmid RISE=5 TARG v(OSC47) VAL=vmid RISE=15
.meas tran freq_47 PARAM='10/period_47'
.meas tran high_47 MAX v(OSC47) FROM=20n TO=80n
.meas tran low_47 MIN v(OSC47) FROM=20n TO=80n
.meas tran pass_ro_47 PARAM='(freq_47>1e6)*(freq_47<2e9)*(high_47>0.8*vdd_val)*(low_47<0.2*vdd_val)'
.meas tran period_48 TRIG v(OSC48) VAL=vmid RISE=5 TARG v(OSC48) VAL=vmid RISE=15
.meas tran freq_48 PARAM='10/period_48'
.meas tran high_48 MAX v(OSC48) FROM=20n TO=80n
.meas tran low_48 MIN v(OSC48) FROM=20n TO=80n
.meas tran pass_ro_48 PARAM='(freq_48>1e6)*(freq_48<2e9)*(high_48>0.8*vdd_val)*(low_48<0.2*vdd_val)'
.meas tran period_49 TRIG v(OSC49) VAL=vmid RISE=5 TARG v(OSC49) VAL=vmid RISE=15
.meas tran freq_49 PARAM='10/period_49'
.meas tran high_49 MAX v(OSC49) FROM=20n TO=80n
.meas tran low_49 MIN v(OSC49) FROM=20n TO=80n
.meas tran pass_ro_49 PARAM='(freq_49>1e6)*(freq_49<2e9)*(high_49>0.8*vdd_val)*(low_49<0.2*vdd_val)'
.meas tran period_50 TRIG v(OSC50) VAL=vmid RISE=5 TARG v(OSC50) VAL=vmid RISE=15
.meas tran freq_50 PARAM='10/period_50'
.meas tran high_50 MAX v(OSC50) FROM=20n TO=80n
.meas tran low_50 MIN v(OSC50) FROM=20n TO=80n
.meas tran pass_ro_50 PARAM='(freq_50>1e6)*(freq_50<2e9)*(high_50>0.8*vdd_val)*(low_50<0.2*vdd_val)'
.meas tran period_51 TRIG v(OSC51) VAL=vmid RISE=5 TARG v(OSC51) VAL=vmid RISE=15
.meas tran freq_51 PARAM='10/period_51'
.meas tran high_51 MAX v(OSC51) FROM=20n TO=80n
.meas tran low_51 MIN v(OSC51) FROM=20n TO=80n
.meas tran pass_ro_51 PARAM='(freq_51>1e6)*(freq_51<2e9)*(high_51>0.8*vdd_val)*(low_51<0.2*vdd_val)'
.meas tran period_52 TRIG v(OSC52) VAL=vmid RISE=5 TARG v(OSC52) VAL=vmid RISE=15
.meas tran freq_52 PARAM='10/period_52'
.meas tran high_52 MAX v(OSC52) FROM=20n TO=80n
.meas tran low_52 MIN v(OSC52) FROM=20n TO=80n
.meas tran pass_ro_52 PARAM='(freq_52>1e6)*(freq_52<2e9)*(high_52>0.8*vdd_val)*(low_52<0.2*vdd_val)'
.meas tran period_53 TRIG v(OSC53) VAL=vmid RISE=5 TARG v(OSC53) VAL=vmid RISE=15
.meas tran freq_53 PARAM='10/period_53'
.meas tran high_53 MAX v(OSC53) FROM=20n TO=80n
.meas tran low_53 MIN v(OSC53) FROM=20n TO=80n
.meas tran pass_ro_53 PARAM='(freq_53>1e6)*(freq_53<2e9)*(high_53>0.8*vdd_val)*(low_53<0.2*vdd_val)'
.meas tran period_54 TRIG v(OSC54) VAL=vmid RISE=5 TARG v(OSC54) VAL=vmid RISE=15
.meas tran freq_54 PARAM='10/period_54'
.meas tran high_54 MAX v(OSC54) FROM=20n TO=80n
.meas tran low_54 MIN v(OSC54) FROM=20n TO=80n
.meas tran pass_ro_54 PARAM='(freq_54>1e6)*(freq_54<2e9)*(high_54>0.8*vdd_val)*(low_54<0.2*vdd_val)'
.meas tran period_55 TRIG v(OSC55) VAL=vmid RISE=5 TARG v(OSC55) VAL=vmid RISE=15
.meas tran freq_55 PARAM='10/period_55'
.meas tran high_55 MAX v(OSC55) FROM=20n TO=80n
.meas tran low_55 MIN v(OSC55) FROM=20n TO=80n
.meas tran pass_ro_55 PARAM='(freq_55>1e6)*(freq_55<2e9)*(high_55>0.8*vdd_val)*(low_55<0.2*vdd_val)'
.meas tran period_56 TRIG v(OSC56) VAL=vmid RISE=5 TARG v(OSC56) VAL=vmid RISE=15
.meas tran freq_56 PARAM='10/period_56'
.meas tran high_56 MAX v(OSC56) FROM=20n TO=80n
.meas tran low_56 MIN v(OSC56) FROM=20n TO=80n
.meas tran pass_ro_56 PARAM='(freq_56>1e6)*(freq_56<2e9)*(high_56>0.8*vdd_val)*(low_56<0.2*vdd_val)'
.meas tran period_57 TRIG v(OSC57) VAL=vmid RISE=5 TARG v(OSC57) VAL=vmid RISE=15
.meas tran freq_57 PARAM='10/period_57'
.meas tran high_57 MAX v(OSC57) FROM=20n TO=80n
.meas tran low_57 MIN v(OSC57) FROM=20n TO=80n
.meas tran pass_ro_57 PARAM='(freq_57>1e6)*(freq_57<2e9)*(high_57>0.8*vdd_val)*(low_57<0.2*vdd_val)'
.meas tran period_58 TRIG v(OSC58) VAL=vmid RISE=5 TARG v(OSC58) VAL=vmid RISE=15
.meas tran freq_58 PARAM='10/period_58'
.meas tran high_58 MAX v(OSC58) FROM=20n TO=80n
.meas tran low_58 MIN v(OSC58) FROM=20n TO=80n
.meas tran pass_ro_58 PARAM='(freq_58>1e6)*(freq_58<2e9)*(high_58>0.8*vdd_val)*(low_58<0.2*vdd_val)'
.meas tran period_59 TRIG v(OSC59) VAL=vmid RISE=5 TARG v(OSC59) VAL=vmid RISE=15
.meas tran freq_59 PARAM='10/period_59'
.meas tran high_59 MAX v(OSC59) FROM=20n TO=80n
.meas tran low_59 MIN v(OSC59) FROM=20n TO=80n
.meas tran pass_ro_59 PARAM='(freq_59>1e6)*(freq_59<2e9)*(high_59>0.8*vdd_val)*(low_59<0.2*vdd_val)'
.meas tran period_60 TRIG v(OSC60) VAL=vmid RISE=5 TARG v(OSC60) VAL=vmid RISE=15
.meas tran freq_60 PARAM='10/period_60'
.meas tran high_60 MAX v(OSC60) FROM=20n TO=80n
.meas tran low_60 MIN v(OSC60) FROM=20n TO=80n
.meas tran pass_ro_60 PARAM='(freq_60>1e6)*(freq_60<2e9)*(high_60>0.8*vdd_val)*(low_60<0.2*vdd_val)'
.meas tran period_61 TRIG v(OSC61) VAL=vmid RISE=5 TARG v(OSC61) VAL=vmid RISE=15
.meas tran freq_61 PARAM='10/period_61'
.meas tran high_61 MAX v(OSC61) FROM=20n TO=80n
.meas tran low_61 MIN v(OSC61) FROM=20n TO=80n
.meas tran pass_ro_61 PARAM='(freq_61>1e6)*(freq_61<2e9)*(high_61>0.8*vdd_val)*(low_61<0.2*vdd_val)'
.meas tran period_62 TRIG v(OSC62) VAL=vmid RISE=5 TARG v(OSC62) VAL=vmid RISE=15
.meas tran freq_62 PARAM='10/period_62'
.meas tran high_62 MAX v(OSC62) FROM=20n TO=80n
.meas tran low_62 MIN v(OSC62) FROM=20n TO=80n
.meas tran pass_ro_62 PARAM='(freq_62>1e6)*(freq_62<2e9)*(high_62>0.8*vdd_val)*(low_62<0.2*vdd_val)'
.meas tran period_63 TRIG v(OSC63) VAL=vmid RISE=5 TARG v(OSC63) VAL=vmid RISE=15
.meas tran freq_63 PARAM='10/period_63'
.meas tran high_63 MAX v(OSC63) FROM=20n TO=80n
.meas tran low_63 MIN v(OSC63) FROM=20n TO=80n
.meas tran pass_ro_63 PARAM='(freq_63>1e6)*(freq_63<2e9)*(high_63>0.8*vdd_val)*(low_63<0.2*vdd_val)'
.meas tran period_64 TRIG v(OSC64) VAL=vmid RISE=5 TARG v(OSC64) VAL=vmid RISE=15
.meas tran freq_64 PARAM='10/period_64'
.meas tran high_64 MAX v(OSC64) FROM=20n TO=80n
.meas tran low_64 MIN v(OSC64) FROM=20n TO=80n
.meas tran pass_ro_64 PARAM='(freq_64>1e6)*(freq_64<2e9)*(high_64>0.8*vdd_val)*(low_64<0.2*vdd_val)'
.meas tran period_65 TRIG v(OSC65) VAL=vmid RISE=5 TARG v(OSC65) VAL=vmid RISE=15
.meas tran freq_65 PARAM='10/period_65'
.meas tran high_65 MAX v(OSC65) FROM=20n TO=80n
.meas tran low_65 MIN v(OSC65) FROM=20n TO=80n
.meas tran pass_ro_65 PARAM='(freq_65>1e6)*(freq_65<2e9)*(high_65>0.8*vdd_val)*(low_65<0.2*vdd_val)'
.meas tran period_66 TRIG v(OSC66) VAL=vmid RISE=5 TARG v(OSC66) VAL=vmid RISE=15
.meas tran freq_66 PARAM='10/period_66'
.meas tran high_66 MAX v(OSC66) FROM=20n TO=80n
.meas tran low_66 MIN v(OSC66) FROM=20n TO=80n
.meas tran pass_ro_66 PARAM='(freq_66>1e6)*(freq_66<2e9)*(high_66>0.8*vdd_val)*(low_66<0.2*vdd_val)'
.meas tran period_67 TRIG v(OSC67) VAL=vmid RISE=5 TARG v(OSC67) VAL=vmid RISE=15
.meas tran freq_67 PARAM='10/period_67'
.meas tran high_67 MAX v(OSC67) FROM=20n TO=80n
.meas tran low_67 MIN v(OSC67) FROM=20n TO=80n
.meas tran pass_ro_67 PARAM='(freq_67>1e6)*(freq_67<2e9)*(high_67>0.8*vdd_val)*(low_67<0.2*vdd_val)'
.meas tran period_68 TRIG v(OSC68) VAL=vmid RISE=5 TARG v(OSC68) VAL=vmid RISE=15
.meas tran freq_68 PARAM='10/period_68'
.meas tran high_68 MAX v(OSC68) FROM=20n TO=80n
.meas tran low_68 MIN v(OSC68) FROM=20n TO=80n
.meas tran pass_ro_68 PARAM='(freq_68>1e6)*(freq_68<2e9)*(high_68>0.8*vdd_val)*(low_68<0.2*vdd_val)'
.meas tran period_69 TRIG v(OSC69) VAL=vmid RISE=5 TARG v(OSC69) VAL=vmid RISE=15
.meas tran freq_69 PARAM='10/period_69'
.meas tran high_69 MAX v(OSC69) FROM=20n TO=80n
.meas tran low_69 MIN v(OSC69) FROM=20n TO=80n
.meas tran pass_ro_69 PARAM='(freq_69>1e6)*(freq_69<2e9)*(high_69>0.8*vdd_val)*(low_69<0.2*vdd_val)'
.meas tran period_70 TRIG v(OSC70) VAL=vmid RISE=5 TARG v(OSC70) VAL=vmid RISE=15
.meas tran freq_70 PARAM='10/period_70'
.meas tran high_70 MAX v(OSC70) FROM=20n TO=80n
.meas tran low_70 MIN v(OSC70) FROM=20n TO=80n
.meas tran pass_ro_70 PARAM='(freq_70>1e6)*(freq_70<2e9)*(high_70>0.8*vdd_val)*(low_70<0.2*vdd_val)'
.meas tran period_71 TRIG v(OSC71) VAL=vmid RISE=5 TARG v(OSC71) VAL=vmid RISE=15
.meas tran freq_71 PARAM='10/period_71'
.meas tran high_71 MAX v(OSC71) FROM=20n TO=80n
.meas tran low_71 MIN v(OSC71) FROM=20n TO=80n
.meas tran pass_ro_71 PARAM='(freq_71>1e6)*(freq_71<2e9)*(high_71>0.8*vdd_val)*(low_71<0.2*vdd_val)'
.meas tran period_72 TRIG v(OSC72) VAL=vmid RISE=5 TARG v(OSC72) VAL=vmid RISE=15
.meas tran freq_72 PARAM='10/period_72'
.meas tran high_72 MAX v(OSC72) FROM=20n TO=80n
.meas tran low_72 MIN v(OSC72) FROM=20n TO=80n
.meas tran pass_ro_72 PARAM='(freq_72>1e6)*(freq_72<2e9)*(high_72>0.8*vdd_val)*(low_72<0.2*vdd_val)'
.meas tran period_73 TRIG v(OSC73) VAL=vmid RISE=5 TARG v(OSC73) VAL=vmid RISE=15
.meas tran freq_73 PARAM='10/period_73'
.meas tran high_73 MAX v(OSC73) FROM=20n TO=80n
.meas tran low_73 MIN v(OSC73) FROM=20n TO=80n
.meas tran pass_ro_73 PARAM='(freq_73>1e6)*(freq_73<2e9)*(high_73>0.8*vdd_val)*(low_73<0.2*vdd_val)'
.meas tran period_74 TRIG v(OSC74) VAL=vmid RISE=5 TARG v(OSC74) VAL=vmid RISE=15
.meas tran freq_74 PARAM='10/period_74'
.meas tran high_74 MAX v(OSC74) FROM=20n TO=80n
.meas tran low_74 MIN v(OSC74) FROM=20n TO=80n
.meas tran pass_ro_74 PARAM='(freq_74>1e6)*(freq_74<2e9)*(high_74>0.8*vdd_val)*(low_74<0.2*vdd_val)'
.meas tran period_75 TRIG v(OSC75) VAL=vmid RISE=5 TARG v(OSC75) VAL=vmid RISE=15
.meas tran freq_75 PARAM='10/period_75'
.meas tran high_75 MAX v(OSC75) FROM=20n TO=80n
.meas tran low_75 MIN v(OSC75) FROM=20n TO=80n
.meas tran pass_ro_75 PARAM='(freq_75>1e6)*(freq_75<2e9)*(high_75>0.8*vdd_val)*(low_75<0.2*vdd_val)'
.meas tran period_76 TRIG v(OSC76) VAL=vmid RISE=5 TARG v(OSC76) VAL=vmid RISE=15
.meas tran freq_76 PARAM='10/period_76'
.meas tran high_76 MAX v(OSC76) FROM=20n TO=80n
.meas tran low_76 MIN v(OSC76) FROM=20n TO=80n
.meas tran pass_ro_76 PARAM='(freq_76>1e6)*(freq_76<2e9)*(high_76>0.8*vdd_val)*(low_76<0.2*vdd_val)'
.meas tran period_77 TRIG v(OSC77) VAL=vmid RISE=5 TARG v(OSC77) VAL=vmid RISE=15
.meas tran freq_77 PARAM='10/period_77'
.meas tran high_77 MAX v(OSC77) FROM=20n TO=80n
.meas tran low_77 MIN v(OSC77) FROM=20n TO=80n
.meas tran pass_ro_77 PARAM='(freq_77>1e6)*(freq_77<2e9)*(high_77>0.8*vdd_val)*(low_77<0.2*vdd_val)'
.meas tran period_78 TRIG v(OSC78) VAL=vmid RISE=5 TARG v(OSC78) VAL=vmid RISE=15
.meas tran freq_78 PARAM='10/period_78'
.meas tran high_78 MAX v(OSC78) FROM=20n TO=80n
.meas tran low_78 MIN v(OSC78) FROM=20n TO=80n
.meas tran pass_ro_78 PARAM='(freq_78>1e6)*(freq_78<2e9)*(high_78>0.8*vdd_val)*(low_78<0.2*vdd_val)'
.meas tran period_79 TRIG v(OSC79) VAL=vmid RISE=5 TARG v(OSC79) VAL=vmid RISE=15
.meas tran freq_79 PARAM='10/period_79'
.meas tran high_79 MAX v(OSC79) FROM=20n TO=80n
.meas tran low_79 MIN v(OSC79) FROM=20n TO=80n
.meas tran pass_ro_79 PARAM='(freq_79>1e6)*(freq_79<2e9)*(high_79>0.8*vdd_val)*(low_79<0.2*vdd_val)'
.meas tran period_80 TRIG v(OSC80) VAL=vmid RISE=5 TARG v(OSC80) VAL=vmid RISE=15
.meas tran freq_80 PARAM='10/period_80'
.meas tran high_80 MAX v(OSC80) FROM=20n TO=80n
.meas tran low_80 MIN v(OSC80) FROM=20n TO=80n
.meas tran pass_ro_80 PARAM='(freq_80>1e6)*(freq_80<2e9)*(high_80>0.8*vdd_val)*(low_80<0.2*vdd_val)'
.meas tran period_81 TRIG v(OSC81) VAL=vmid RISE=5 TARG v(OSC81) VAL=vmid RISE=15
.meas tran freq_81 PARAM='10/period_81'
.meas tran high_81 MAX v(OSC81) FROM=20n TO=80n
.meas tran low_81 MIN v(OSC81) FROM=20n TO=80n
.meas tran pass_ro_81 PARAM='(freq_81>1e6)*(freq_81<2e9)*(high_81>0.8*vdd_val)*(low_81<0.2*vdd_val)'
.meas tran period_82 TRIG v(OSC82) VAL=vmid RISE=5 TARG v(OSC82) VAL=vmid RISE=15
.meas tran freq_82 PARAM='10/period_82'
.meas tran high_82 MAX v(OSC82) FROM=20n TO=80n
.meas tran low_82 MIN v(OSC82) FROM=20n TO=80n
.meas tran pass_ro_82 PARAM='(freq_82>1e6)*(freq_82<2e9)*(high_82>0.8*vdd_val)*(low_82<0.2*vdd_val)'
.meas tran period_83 TRIG v(OSC83) VAL=vmid RISE=5 TARG v(OSC83) VAL=vmid RISE=15
.meas tran freq_83 PARAM='10/period_83'
.meas tran high_83 MAX v(OSC83) FROM=20n TO=80n
.meas tran low_83 MIN v(OSC83) FROM=20n TO=80n
.meas tran pass_ro_83 PARAM='(freq_83>1e6)*(freq_83<2e9)*(high_83>0.8*vdd_val)*(low_83<0.2*vdd_val)'
.meas tran period_84 TRIG v(OSC84) VAL=vmid RISE=5 TARG v(OSC84) VAL=vmid RISE=15
.meas tran freq_84 PARAM='10/period_84'
.meas tran high_84 MAX v(OSC84) FROM=20n TO=80n
.meas tran low_84 MIN v(OSC84) FROM=20n TO=80n
.meas tran pass_ro_84 PARAM='(freq_84>1e6)*(freq_84<2e9)*(high_84>0.8*vdd_val)*(low_84<0.2*vdd_val)'
.meas tran period_85 TRIG v(OSC85) VAL=vmid RISE=5 TARG v(OSC85) VAL=vmid RISE=15
.meas tran freq_85 PARAM='10/period_85'
.meas tran high_85 MAX v(OSC85) FROM=20n TO=80n
.meas tran low_85 MIN v(OSC85) FROM=20n TO=80n
.meas tran pass_ro_85 PARAM='(freq_85>1e6)*(freq_85<2e9)*(high_85>0.8*vdd_val)*(low_85<0.2*vdd_val)'
.meas tran period_86 TRIG v(OSC86) VAL=vmid RISE=5 TARG v(OSC86) VAL=vmid RISE=15
.meas tran freq_86 PARAM='10/period_86'
.meas tran high_86 MAX v(OSC86) FROM=20n TO=80n
.meas tran low_86 MIN v(OSC86) FROM=20n TO=80n
.meas tran pass_ro_86 PARAM='(freq_86>1e6)*(freq_86<2e9)*(high_86>0.8*vdd_val)*(low_86<0.2*vdd_val)'
.meas tran period_87 TRIG v(OSC87) VAL=vmid RISE=5 TARG v(OSC87) VAL=vmid RISE=15
.meas tran freq_87 PARAM='10/period_87'
.meas tran high_87 MAX v(OSC87) FROM=20n TO=80n
.meas tran low_87 MIN v(OSC87) FROM=20n TO=80n
.meas tran pass_ro_87 PARAM='(freq_87>1e6)*(freq_87<2e9)*(high_87>0.8*vdd_val)*(low_87<0.2*vdd_val)'
.meas tran period_88 TRIG v(OSC88) VAL=vmid RISE=5 TARG v(OSC88) VAL=vmid RISE=15
.meas tran freq_88 PARAM='10/period_88'
.meas tran high_88 MAX v(OSC88) FROM=20n TO=80n
.meas tran low_88 MIN v(OSC88) FROM=20n TO=80n
.meas tran pass_ro_88 PARAM='(freq_88>1e6)*(freq_88<2e9)*(high_88>0.8*vdd_val)*(low_88<0.2*vdd_val)'
.meas tran period_89 TRIG v(OSC89) VAL=vmid RISE=5 TARG v(OSC89) VAL=vmid RISE=15
.meas tran freq_89 PARAM='10/period_89'
.meas tran high_89 MAX v(OSC89) FROM=20n TO=80n
.meas tran low_89 MIN v(OSC89) FROM=20n TO=80n
.meas tran pass_ro_89 PARAM='(freq_89>1e6)*(freq_89<2e9)*(high_89>0.8*vdd_val)*(low_89<0.2*vdd_val)'
.meas tran period_90 TRIG v(OSC90) VAL=vmid RISE=5 TARG v(OSC90) VAL=vmid RISE=15
.meas tran freq_90 PARAM='10/period_90'
.meas tran high_90 MAX v(OSC90) FROM=20n TO=80n
.meas tran low_90 MIN v(OSC90) FROM=20n TO=80n
.meas tran pass_ro_90 PARAM='(freq_90>1e6)*(freq_90<2e9)*(high_90>0.8*vdd_val)*(low_90<0.2*vdd_val)'
.meas tran period_91 TRIG v(OSC91) VAL=vmid RISE=5 TARG v(OSC91) VAL=vmid RISE=15
.meas tran freq_91 PARAM='10/period_91'
.meas tran high_91 MAX v(OSC91) FROM=20n TO=80n
.meas tran low_91 MIN v(OSC91) FROM=20n TO=80n
.meas tran pass_ro_91 PARAM='(freq_91>1e6)*(freq_91<2e9)*(high_91>0.8*vdd_val)*(low_91<0.2*vdd_val)'
.meas tran period_92 TRIG v(OSC92) VAL=vmid RISE=5 TARG v(OSC92) VAL=vmid RISE=15
.meas tran freq_92 PARAM='10/period_92'
.meas tran high_92 MAX v(OSC92) FROM=20n TO=80n
.meas tran low_92 MIN v(OSC92) FROM=20n TO=80n
.meas tran pass_ro_92 PARAM='(freq_92>1e6)*(freq_92<2e9)*(high_92>0.8*vdd_val)*(low_92<0.2*vdd_val)'
.meas tran period_93 TRIG v(OSC93) VAL=vmid RISE=5 TARG v(OSC93) VAL=vmid RISE=15
.meas tran freq_93 PARAM='10/period_93'
.meas tran high_93 MAX v(OSC93) FROM=20n TO=80n
.meas tran low_93 MIN v(OSC93) FROM=20n TO=80n
.meas tran pass_ro_93 PARAM='(freq_93>1e6)*(freq_93<2e9)*(high_93>0.8*vdd_val)*(low_93<0.2*vdd_val)'
.meas tran period_94 TRIG v(OSC94) VAL=vmid RISE=5 TARG v(OSC94) VAL=vmid RISE=15
.meas tran freq_94 PARAM='10/period_94'
.meas tran high_94 MAX v(OSC94) FROM=20n TO=80n
.meas tran low_94 MIN v(OSC94) FROM=20n TO=80n
.meas tran pass_ro_94 PARAM='(freq_94>1e6)*(freq_94<2e9)*(high_94>0.8*vdd_val)*(low_94<0.2*vdd_val)'
.meas tran period_95 TRIG v(OSC95) VAL=vmid RISE=5 TARG v(OSC95) VAL=vmid RISE=15
.meas tran freq_95 PARAM='10/period_95'
.meas tran high_95 MAX v(OSC95) FROM=20n TO=80n
.meas tran low_95 MIN v(OSC95) FROM=20n TO=80n
.meas tran pass_ro_95 PARAM='(freq_95>1e6)*(freq_95<2e9)*(high_95>0.8*vdd_val)*(low_95<0.2*vdd_val)'
.meas tran period_96 TRIG v(OSC96) VAL=vmid RISE=5 TARG v(OSC96) VAL=vmid RISE=15
.meas tran freq_96 PARAM='10/period_96'
.meas tran high_96 MAX v(OSC96) FROM=20n TO=80n
.meas tran low_96 MIN v(OSC96) FROM=20n TO=80n
.meas tran pass_ro_96 PARAM='(freq_96>1e6)*(freq_96<2e9)*(high_96>0.8*vdd_val)*(low_96<0.2*vdd_val)'
.meas tran period_97 TRIG v(OSC97) VAL=vmid RISE=5 TARG v(OSC97) VAL=vmid RISE=15
.meas tran freq_97 PARAM='10/period_97'
.meas tran high_97 MAX v(OSC97) FROM=20n TO=80n
.meas tran low_97 MIN v(OSC97) FROM=20n TO=80n
.meas tran pass_ro_97 PARAM='(freq_97>1e6)*(freq_97<2e9)*(high_97>0.8*vdd_val)*(low_97<0.2*vdd_val)'
.meas tran period_98 TRIG v(OSC98) VAL=vmid RISE=5 TARG v(OSC98) VAL=vmid RISE=15
.meas tran freq_98 PARAM='10/period_98'
.meas tran high_98 MAX v(OSC98) FROM=20n TO=80n
.meas tran low_98 MIN v(OSC98) FROM=20n TO=80n
.meas tran pass_ro_98 PARAM='(freq_98>1e6)*(freq_98<2e9)*(high_98>0.8*vdd_val)*(low_98<0.2*vdd_val)'
.meas tran period_99 TRIG v(OSC99) VAL=vmid RISE=5 TARG v(OSC99) VAL=vmid RISE=15
.meas tran freq_99 PARAM='10/period_99'
.meas tran high_99 MAX v(OSC99) FROM=20n TO=80n
.meas tran low_99 MIN v(OSC99) FROM=20n TO=80n
.meas tran pass_ro_99 PARAM='(freq_99>1e6)*(freq_99<2e9)*(high_99>0.8*vdd_val)*(low_99<0.2*vdd_val)'
.meas tran period_100 TRIG v(OSC100) VAL=vmid RISE=5 TARG v(OSC100) VAL=vmid RISE=15
.meas tran freq_100 PARAM='10/period_100'
.meas tran high_100 MAX v(OSC100) FROM=20n TO=80n
.meas tran low_100 MIN v(OSC100) FROM=20n TO=80n
.meas tran pass_ro_100 PARAM='(freq_100>1e6)*(freq_100<2e9)*(high_100>0.8*vdd_val)*(low_100<0.2*vdd_val)'
.meas tran period_101 TRIG v(OSC101) VAL=vmid RISE=5 TARG v(OSC101) VAL=vmid RISE=15
.meas tran freq_101 PARAM='10/period_101'
.meas tran high_101 MAX v(OSC101) FROM=20n TO=80n
.meas tran low_101 MIN v(OSC101) FROM=20n TO=80n
.meas tran pass_ro_101 PARAM='(freq_101>1e6)*(freq_101<2e9)*(high_101>0.8*vdd_val)*(low_101<0.2*vdd_val)'
.meas tran period_102 TRIG v(OSC102) VAL=vmid RISE=5 TARG v(OSC102) VAL=vmid RISE=15
.meas tran freq_102 PARAM='10/period_102'
.meas tran high_102 MAX v(OSC102) FROM=20n TO=80n
.meas tran low_102 MIN v(OSC102) FROM=20n TO=80n
.meas tran pass_ro_102 PARAM='(freq_102>1e6)*(freq_102<2e9)*(high_102>0.8*vdd_val)*(low_102<0.2*vdd_val)'
.meas tran period_103 TRIG v(OSC103) VAL=vmid RISE=5 TARG v(OSC103) VAL=vmid RISE=15
.meas tran freq_103 PARAM='10/period_103'
.meas tran high_103 MAX v(OSC103) FROM=20n TO=80n
.meas tran low_103 MIN v(OSC103) FROM=20n TO=80n
.meas tran pass_ro_103 PARAM='(freq_103>1e6)*(freq_103<2e9)*(high_103>0.8*vdd_val)*(low_103<0.2*vdd_val)'
.meas tran period_104 TRIG v(OSC104) VAL=vmid RISE=5 TARG v(OSC104) VAL=vmid RISE=15
.meas tran freq_104 PARAM='10/period_104'
.meas tran high_104 MAX v(OSC104) FROM=20n TO=80n
.meas tran low_104 MIN v(OSC104) FROM=20n TO=80n
.meas tran pass_ro_104 PARAM='(freq_104>1e6)*(freq_104<2e9)*(high_104>0.8*vdd_val)*(low_104<0.2*vdd_val)'
.meas tran period_105 TRIG v(OSC105) VAL=vmid RISE=5 TARG v(OSC105) VAL=vmid RISE=15
.meas tran freq_105 PARAM='10/period_105'
.meas tran high_105 MAX v(OSC105) FROM=20n TO=80n
.meas tran low_105 MIN v(OSC105) FROM=20n TO=80n
.meas tran pass_ro_105 PARAM='(freq_105>1e6)*(freq_105<2e9)*(high_105>0.8*vdd_val)*(low_105<0.2*vdd_val)'
.meas tran period_106 TRIG v(OSC106) VAL=vmid RISE=5 TARG v(OSC106) VAL=vmid RISE=15
.meas tran freq_106 PARAM='10/period_106'
.meas tran high_106 MAX v(OSC106) FROM=20n TO=80n
.meas tran low_106 MIN v(OSC106) FROM=20n TO=80n
.meas tran pass_ro_106 PARAM='(freq_106>1e6)*(freq_106<2e9)*(high_106>0.8*vdd_val)*(low_106<0.2*vdd_val)'
.meas tran period_107 TRIG v(OSC107) VAL=vmid RISE=5 TARG v(OSC107) VAL=vmid RISE=15
.meas tran freq_107 PARAM='10/period_107'
.meas tran high_107 MAX v(OSC107) FROM=20n TO=80n
.meas tran low_107 MIN v(OSC107) FROM=20n TO=80n
.meas tran pass_ro_107 PARAM='(freq_107>1e6)*(freq_107<2e9)*(high_107>0.8*vdd_val)*(low_107<0.2*vdd_val)'
.meas tran period_108 TRIG v(OSC108) VAL=vmid RISE=5 TARG v(OSC108) VAL=vmid RISE=15
.meas tran freq_108 PARAM='10/period_108'
.meas tran high_108 MAX v(OSC108) FROM=20n TO=80n
.meas tran low_108 MIN v(OSC108) FROM=20n TO=80n
.meas tran pass_ro_108 PARAM='(freq_108>1e6)*(freq_108<2e9)*(high_108>0.8*vdd_val)*(low_108<0.2*vdd_val)'
.meas tran period_109 TRIG v(OSC109) VAL=vmid RISE=5 TARG v(OSC109) VAL=vmid RISE=15
.meas tran freq_109 PARAM='10/period_109'
.meas tran high_109 MAX v(OSC109) FROM=20n TO=80n
.meas tran low_109 MIN v(OSC109) FROM=20n TO=80n
.meas tran pass_ro_109 PARAM='(freq_109>1e6)*(freq_109<2e9)*(high_109>0.8*vdd_val)*(low_109<0.2*vdd_val)'
.meas tran period_110 TRIG v(OSC110) VAL=vmid RISE=5 TARG v(OSC110) VAL=vmid RISE=15
.meas tran freq_110 PARAM='10/period_110'
.meas tran high_110 MAX v(OSC110) FROM=20n TO=80n
.meas tran low_110 MIN v(OSC110) FROM=20n TO=80n
.meas tran pass_ro_110 PARAM='(freq_110>1e6)*(freq_110<2e9)*(high_110>0.8*vdd_val)*(low_110<0.2*vdd_val)'
.meas tran period_111 TRIG v(OSC111) VAL=vmid RISE=5 TARG v(OSC111) VAL=vmid RISE=15
.meas tran freq_111 PARAM='10/period_111'
.meas tran high_111 MAX v(OSC111) FROM=20n TO=80n
.meas tran low_111 MIN v(OSC111) FROM=20n TO=80n
.meas tran pass_ro_111 PARAM='(freq_111>1e6)*(freq_111<2e9)*(high_111>0.8*vdd_val)*(low_111<0.2*vdd_val)'
.meas tran period_112 TRIG v(OSC112) VAL=vmid RISE=5 TARG v(OSC112) VAL=vmid RISE=15
.meas tran freq_112 PARAM='10/period_112'
.meas tran high_112 MAX v(OSC112) FROM=20n TO=80n
.meas tran low_112 MIN v(OSC112) FROM=20n TO=80n
.meas tran pass_ro_112 PARAM='(freq_112>1e6)*(freq_112<2e9)*(high_112>0.8*vdd_val)*(low_112<0.2*vdd_val)'
.meas tran period_113 TRIG v(OSC113) VAL=vmid RISE=5 TARG v(OSC113) VAL=vmid RISE=15
.meas tran freq_113 PARAM='10/period_113'
.meas tran high_113 MAX v(OSC113) FROM=20n TO=80n
.meas tran low_113 MIN v(OSC113) FROM=20n TO=80n
.meas tran pass_ro_113 PARAM='(freq_113>1e6)*(freq_113<2e9)*(high_113>0.8*vdd_val)*(low_113<0.2*vdd_val)'
.meas tran period_114 TRIG v(OSC114) VAL=vmid RISE=5 TARG v(OSC114) VAL=vmid RISE=15
.meas tran freq_114 PARAM='10/period_114'
.meas tran high_114 MAX v(OSC114) FROM=20n TO=80n
.meas tran low_114 MIN v(OSC114) FROM=20n TO=80n
.meas tran pass_ro_114 PARAM='(freq_114>1e6)*(freq_114<2e9)*(high_114>0.8*vdd_val)*(low_114<0.2*vdd_val)'
.meas tran period_115 TRIG v(OSC115) VAL=vmid RISE=5 TARG v(OSC115) VAL=vmid RISE=15
.meas tran freq_115 PARAM='10/period_115'
.meas tran high_115 MAX v(OSC115) FROM=20n TO=80n
.meas tran low_115 MIN v(OSC115) FROM=20n TO=80n
.meas tran pass_ro_115 PARAM='(freq_115>1e6)*(freq_115<2e9)*(high_115>0.8*vdd_val)*(low_115<0.2*vdd_val)'
.meas tran period_116 TRIG v(OSC116) VAL=vmid RISE=5 TARG v(OSC116) VAL=vmid RISE=15
.meas tran freq_116 PARAM='10/period_116'
.meas tran high_116 MAX v(OSC116) FROM=20n TO=80n
.meas tran low_116 MIN v(OSC116) FROM=20n TO=80n
.meas tran pass_ro_116 PARAM='(freq_116>1e6)*(freq_116<2e9)*(high_116>0.8*vdd_val)*(low_116<0.2*vdd_val)'
.meas tran period_117 TRIG v(OSC117) VAL=vmid RISE=5 TARG v(OSC117) VAL=vmid RISE=15
.meas tran freq_117 PARAM='10/period_117'
.meas tran high_117 MAX v(OSC117) FROM=20n TO=80n
.meas tran low_117 MIN v(OSC117) FROM=20n TO=80n
.meas tran pass_ro_117 PARAM='(freq_117>1e6)*(freq_117<2e9)*(high_117>0.8*vdd_val)*(low_117<0.2*vdd_val)'
.meas tran period_118 TRIG v(OSC118) VAL=vmid RISE=5 TARG v(OSC118) VAL=vmid RISE=15
.meas tran freq_118 PARAM='10/period_118'
.meas tran high_118 MAX v(OSC118) FROM=20n TO=80n
.meas tran low_118 MIN v(OSC118) FROM=20n TO=80n
.meas tran pass_ro_118 PARAM='(freq_118>1e6)*(freq_118<2e9)*(high_118>0.8*vdd_val)*(low_118<0.2*vdd_val)'
.meas tran period_119 TRIG v(OSC119) VAL=vmid RISE=5 TARG v(OSC119) VAL=vmid RISE=15
.meas tran freq_119 PARAM='10/period_119'
.meas tran high_119 MAX v(OSC119) FROM=20n TO=80n
.meas tran low_119 MIN v(OSC119) FROM=20n TO=80n
.meas tran pass_ro_119 PARAM='(freq_119>1e6)*(freq_119<2e9)*(high_119>0.8*vdd_val)*(low_119<0.2*vdd_val)'
.meas tran period_120 TRIG v(OSC120) VAL=vmid RISE=5 TARG v(OSC120) VAL=vmid RISE=15
.meas tran freq_120 PARAM='10/period_120'
.meas tran high_120 MAX v(OSC120) FROM=20n TO=80n
.meas tran low_120 MIN v(OSC120) FROM=20n TO=80n
.meas tran pass_ro_120 PARAM='(freq_120>1e6)*(freq_120<2e9)*(high_120>0.8*vdd_val)*(low_120<0.2*vdd_val)'
.meas tran period_121 TRIG v(OSC121) VAL=vmid RISE=5 TARG v(OSC121) VAL=vmid RISE=15
.meas tran freq_121 PARAM='10/period_121'
.meas tran high_121 MAX v(OSC121) FROM=20n TO=80n
.meas tran low_121 MIN v(OSC121) FROM=20n TO=80n
.meas tran pass_ro_121 PARAM='(freq_121>1e6)*(freq_121<2e9)*(high_121>0.8*vdd_val)*(low_121<0.2*vdd_val)'
.meas tran period_122 TRIG v(OSC122) VAL=vmid RISE=5 TARG v(OSC122) VAL=vmid RISE=15
.meas tran freq_122 PARAM='10/period_122'
.meas tran high_122 MAX v(OSC122) FROM=20n TO=80n
.meas tran low_122 MIN v(OSC122) FROM=20n TO=80n
.meas tran pass_ro_122 PARAM='(freq_122>1e6)*(freq_122<2e9)*(high_122>0.8*vdd_val)*(low_122<0.2*vdd_val)'
.meas tran period_123 TRIG v(OSC123) VAL=vmid RISE=5 TARG v(OSC123) VAL=vmid RISE=15
.meas tran freq_123 PARAM='10/period_123'
.meas tran high_123 MAX v(OSC123) FROM=20n TO=80n
.meas tran low_123 MIN v(OSC123) FROM=20n TO=80n
.meas tran pass_ro_123 PARAM='(freq_123>1e6)*(freq_123<2e9)*(high_123>0.8*vdd_val)*(low_123<0.2*vdd_val)'
.meas tran period_124 TRIG v(OSC124) VAL=vmid RISE=5 TARG v(OSC124) VAL=vmid RISE=15
.meas tran freq_124 PARAM='10/period_124'
.meas tran high_124 MAX v(OSC124) FROM=20n TO=80n
.meas tran low_124 MIN v(OSC124) FROM=20n TO=80n
.meas tran pass_ro_124 PARAM='(freq_124>1e6)*(freq_124<2e9)*(high_124>0.8*vdd_val)*(low_124<0.2*vdd_val)'
.meas tran period_125 TRIG v(OSC125) VAL=vmid RISE=5 TARG v(OSC125) VAL=vmid RISE=15
.meas tran freq_125 PARAM='10/period_125'
.meas tran high_125 MAX v(OSC125) FROM=20n TO=80n
.meas tran low_125 MIN v(OSC125) FROM=20n TO=80n
.meas tran pass_ro_125 PARAM='(freq_125>1e6)*(freq_125<2e9)*(high_125>0.8*vdd_val)*(low_125<0.2*vdd_val)'
.meas tran period_126 TRIG v(OSC126) VAL=vmid RISE=5 TARG v(OSC126) VAL=vmid RISE=15
.meas tran freq_126 PARAM='10/period_126'
.meas tran high_126 MAX v(OSC126) FROM=20n TO=80n
.meas tran low_126 MIN v(OSC126) FROM=20n TO=80n
.meas tran pass_ro_126 PARAM='(freq_126>1e6)*(freq_126<2e9)*(high_126>0.8*vdd_val)*(low_126<0.2*vdd_val)'
.meas tran period_127 TRIG v(OSC127) VAL=vmid RISE=5 TARG v(OSC127) VAL=vmid RISE=15
.meas tran freq_127 PARAM='10/period_127'
.meas tran high_127 MAX v(OSC127) FROM=20n TO=80n
.meas tran low_127 MIN v(OSC127) FROM=20n TO=80n
.meas tran pass_ro_127 PARAM='(freq_127>1e6)*(freq_127<2e9)*(high_127>0.8*vdd_val)*(low_127<0.2*vdd_val)'
.meas tran period_ia TRIG v(OSC_INVA) VAL=vmid RISE=5 TARG v(OSC_INVA) VAL=vmid RISE=15
.meas tran freq_ia PARAM='10/period_ia'
.meas tran high_ia MAX v(OSC_INVA) FROM=20n TO=80n
.meas tran low_ia MIN v(OSC_INVA) FROM=20n TO=80n
.meas tran pass_ro_ia PARAM='(freq_ia>1e6)*(freq_ia<2e9)*(high_ia>0.8*vdd_val)*(low_ia<0.2*vdd_val)'
.meas tran period_ib TRIG v(OSC_INVB) VAL=vmid RISE=5 TARG v(OSC_INVB) VAL=vmid RISE=15
.meas tran freq_ib PARAM='10/period_ib'
.meas tran high_ib MAX v(OSC_INVB) FROM=20n TO=80n
.meas tran low_ib MIN v(OSC_INVB) FROM=20n TO=80n
.meas tran pass_ro_ib PARAM='(freq_ib>1e6)*(freq_ib<2e9)*(high_ib>0.8*vdd_val)*(low_ib<0.2*vdd_val)'
.control
run
quit
.endc
.end
