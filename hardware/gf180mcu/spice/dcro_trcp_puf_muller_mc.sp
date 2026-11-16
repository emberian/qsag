* ==============================================================================
* Dregg-180 Foundry BSIM4 Characterization Deck 3:
*   1) GALS DCRO (qsag_dcro: nand2_1 + 32 x dlya_1 + 32-way AND/OR mux + fine buf/mux)
*      Oscillation Frequency (MHz) at Min (tap=3), Raw-0, Mid (tap=15), Max (tap=31)
*   2) TRCP Mixed-Gate Critical-Path Replica (nand2 + aoi22 + xor2 & RTL oai21 + aoi21 + xor2)
*      Delay Tracking Ratio vs Pure-Inverter (inv_2), Parallel-NAND2, and Stacked Datapath
*   3) AOI222 + NOR2 Muller C-Element (qsag_muller_c) Static Hazard & State Retention Check
*   4) Nominal 5-Stage RO-PUF Ring Frequencies (nand2_2 + 4x inv_2 & RTL 5x nand2_1)
*      (Paired with N=80 Foundry Pelgrom Monte Carlo mismatch deck ro_puf_pelgrom_mc.sp!)
*
* Foundry PDK: GlobalFoundries 180nm (gf180mcuD, 5.0V 7-track mcu7t5v0)
* ==============================================================================

.include "/spice/pdk/ngspice/design.ngspice"
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.param vdd_val=5.00
.temp 25
* __CORNER_END__

.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"

VVDD VDD 0 {vdd_val}
VVSS VSS 0 0.0
VEN  EN  0 PWL(0 0 1.0n 0 1.2n {vdd_val})

* ==============================================================================
* 1. Exact qsag_dcro Ring Subcircuit (qsag_gals_clk_rst.sv:16-89)
*    Fixed one-hot tap select for steady-state transistor frequency characterization
* ==============================================================================
.subckt dcro4_chain s_in s_out vdd vss
X0 s_in n1    vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C0 n1   vss   3.0f
X1 n1   n2    vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C1 n2   vss   3.0f
X2 n2   n3    vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C2 n3   vss   3.0f
X3 n3   s_out vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C3 s_out vss  3.0f
.ends dcro4_chain

* Active path through 32-input AND/OR mux tree (1 x and2_2 + 5 x or2_2 w/ side inputs = 0)
.subckt dcro_mux_tree tap_sig fine0 fine1 fb_out vdd vss
X_AND tap_sig vdd   g0  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__and2_2
C_G0  g0      vss   3.0f
X_OR1 g0      vss   o1  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__or2_2
C_O1  o1      vss   3.0f
X_OR2 o1      vss   o2  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__or2_2
C_O2  o2      vss   3.0f
X_OR3 o2      vss   o3  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__or2_2
C_O3  o3      vss   3.0f
X_OR4 o3      vss   o4  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__or2_2
C_O4  o4      vss   3.0f
X_OR5 o4      vss   m5  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__or2_2
C_M5  m5      vss   3.0f
* Fine trim stages: u_f0 (buf_1) + u_fm0 (mux2_1) + u_f1a/u_f1b (2x buf_1) + u_fm1 (mux2_1)
X_F0  m5      f0d       vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_1
X_FM0 m5      f0d fine0 f0  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__mux2_1
X_F1A f0      f1a       vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_1
X_F1B f1a     f1d       vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_1
X_FM1 f0      f1d fine1 fb_out vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__mux2_1
C_FB  fb_out  vss   4.0f
.ends dcro_mux_tree

* Complete 32-stage qsag_dcro exporting tap0 (s[1]), tap3 (s[4]), tap15 (s[16]), tap31 (s[32])
.subckt dcro_core en fb_in osc_s0 tap0 tap3 tap15 tap31 vdd vss
X_ISO  en    en_iso        vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_2
X_NAND fb_in en_iso osc_s0 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_S0   osc_s0 vss 4.0f
* First 4 stages unpacked to expose s[1] (tap=0) and s[4] (tap=3 min legal!)
X_D0 osc_s0 tap0 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C_D0 tap0   vss  3.0f
X_D1 tap0   s2   vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C_D1 s2     vss  3.0f
X_D2 s2     s3   vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C_D2 s3     vss  3.0f
X_D3 s3     tap3 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
C_D3 tap3   vss  3.0f
* Remaining 28 stages (7 x dcro4_chain) -> tap15 = s[16], tap31 = s[32]
X_C1 tap3  s8    vdd vss dcro4_chain
X_C2 s8    s12   vdd vss dcro4_chain
X_C3 s12   tap15 vdd vss dcro4_chain
X_C4 tap15 s20   vdd vss dcro4_chain
X_C5 s20   s24   vdd vss dcro4_chain
X_C6 s24   s28   vdd vss dcro4_chain
X_C7 s28   tap31 vdd vss dcro4_chain
.ends dcro_core

* Instantiate 4 DCRO operating points simultaneously:
*   (a) RAW0: tap=0,  fine=00
X_DCRO0  EN FB_R0 OSC_RAW0  T0_A T3_A T15_A T31_A VDD VSS dcro_core
X_MUX_R0 T0_A  VSS VSS FB_R0 VDD VSS dcro_mux_tree

*   (b) MIN_LEGAL: tap=3, fine=00 (RTL tap_lim >= 3)
X_DCRO_MIN EN FB_MIN OSC_MIN T0_B T3_B T15_B T31_B VDD VSS dcro_core
X_MUX_MIN  T3_B VSS VSS FB_MIN VDD VSS dcro_mux_tree

*   (c) MID: tap=15, fine=01
X_DCRO_MID EN FB_MID OSC_MID T0_C T3_C T15_C T31_C VDD VSS dcro_core
X_MUX_MID  T15_C VDD VSS FB_MID VDD VSS dcro_mux_tree

*   (d) MAX: tap=31, fine=11
X_DCRO_MAX EN FB_MAX OSC_MAX T0_D T3_D T15_D T31_D VDD VSS dcro_core
X_MUX_MAX  T31_D VDD VDD FB_MAX VDD VSS dcro_mux_tree

* ==============================================================================
* 2. TRCP Mixed-Gate Tracking vs Pure Inverter, Parallel-NAND2 & Stacked Datapath
* ==============================================================================
V_TRCP_IN TRCP_LAUNCH 0 PULSE(0 {vdd_val} 3.0n 0.15n 0.15n 40n 90n)
X_TL_ISO  TRCP_LAUNCH TL0 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2

* (2A) Prompt Mixed-Gate Stage: nand2_1 (series inner A1) -> aoi22_1 (series stack) -> xor2_1
.subckt trcp_mixed_nand_aoi22_xor a y vdd vss
X_TH th vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__tieh
X_TL tl vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__tiel
X_ND a  th m1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_M1 m1 vss 4.0f
X_AO m1 th tl tl m2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__aoi22_1
C_M2 m2 vss 5.0f
X_XR m2 tl y  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__xor2_1
C_Y  y  vss 5.0f
.ends trcp_mixed_nand_aoi22_xor

.subckt trcp_mixed4 a y vdd vss
X0 a  n1 vdd vss trcp_mixed_nand_aoi22_xor
X1 n1 n2 vdd vss trcp_mixed_nand_aoi22_xor
X2 n2 n3 vdd vss trcp_mixed_nand_aoi22_xor
X3 n3 y  vdd vss trcp_mixed_nand_aoi22_xor
.ends trcp_mixed4

* 16 mixed stages
X_TM0 TL0 TM4  VDD VSS trcp_mixed4
X_TM1 TM4 TM8  VDD VSS trcp_mixed4
X_TM2 TM8 TM12 VDD VSS trcp_mixed4
X_TM3 TM12 TRCP_MIX_OUT VDD VSS trcp_mixed4

* (2B) Exact RTL qsag_trcp_chain Stage (oai21_1 -> aoi21_1 -> xor2_1, 24 stages = len=5)
.subckt trcp_rtl_stage a y vdd vss
X_TH1 th1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__tieh
X_TL1 tl1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__tiel
X_OAI a   tl1 th1 m1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__oai21_1
C_1   m1  vss 4.0f
X_AOI m1  th1 tl1 m2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__aoi21_1
C_2   m2  vss 4.0f
X_XOR m2  tl1 y   vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__xor2_1
C_3   y   vss 4.0f
.ends trcp_rtl_stage

.subckt trcp_rtl6 a y vdd vss
X0 a  n1 vdd vss trcp_rtl_stage
X1 n1 n2 vdd vss trcp_rtl_stage
X2 n2 n3 vdd vss trcp_rtl_stage
X3 n3 n4 vdd vss trcp_rtl_stage
X4 n4 n5 vdd vss trcp_rtl_stage
X5 n5 y  vdd vss trcp_rtl_stage
.ends trcp_rtl6

X_TR0 TL0  TR6  VDD VSS trcp_rtl6
X_TR1 TR6  TR12 VDD VSS trcp_rtl6
X_TR2 TR12 TR18 VDD VSS trcp_rtl6
X_TR3 TR18 TRCP_RTL_OUT VDD VSS trcp_rtl6

* (2C) Pure-Inverter Reference Chain (48 x inv_2)
.subckt inv8_chain a y vdd vss
X0 a  n1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C0 n1 vss 3.0f
X1 n1 n2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C1 n2 vss 3.0f
X2 n2 n3 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C2 n3 vss 3.0f
X3 n3 n4 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C3 n4 vss 3.0f
X4 n4 n5 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C4 n5 vss 3.0f
X5 n5 n6 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C5 n6 vss 3.0f
X6 n6 n7 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C6 n7 vss 3.0f
X7 n7 y  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_2
C7 y  vss 3.0f
.ends inv8_chain

X_IV0 TL0  IV8  VDD VSS inv8_chain
X_IV1 IV8  IV16 VDD VSS inv8_chain
X_IV2 IV16 IV24 VDD VSS inv8_chain
X_IV3 IV24 IV32 VDD VSS inv8_chain
X_IV4 IV32 IV40 VDD VSS inv8_chain
X_IV5 IV40 PURE_INV_OUT VDD VSS inv8_chain

* (2D) Legacy Trap-T9 Parallel-PMOS NAND2(.A1(a), .A2(a)) Chain (48 stages)
.subckt par_nand8_chain a y vdd vss
X0 a  a  n1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X1 n1 n1 n2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X2 n2 n2 n3 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X3 n3 n3 n4 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X4 n4 n4 n5 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X5 n5 n5 n6 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X6 n6 n6 n7 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
X7 n7 n7 y  vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
.ends par_nand8_chain

X_PN0 TL0  PN8  VDD VSS par_nand8_chain
X_PN1 PN8  PN16 VDD VSS par_nand8_chain
X_PN2 PN16 PN24 VDD VSS par_nand8_chain
X_PN3 PN24 PN32 VDD VSS par_nand8_chain
X_PN4 PN32 PN40 VDD VSS par_nand8_chain
X_PN5 PN40 PAR_NAND_OUT VDD VSS par_nand8_chain

* (2E) Representative Han-Carlson + Karatsuba-CSA Critical Datapath Cone (12 complex stages)
.subckt datapath_crit_stage a y vdd vss
X_AOI a   vdd vss vss m1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__aoi22_1
R_W1  m1  m1w 22.0
C_W1  m1w vss 8.0f
X_OAI m1w vss vdd m2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__oai21_1
R_W2  m2  m2w 22.0
C_W2  m2w vss 8.0f
X_XOR vdd m2w m3 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__xor2_1
X_FO  m3  unused_fo vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_1
R_W3  m3  m3w 22.0
C_W3  m3w vss 8.0f
X_MUX vss vdd m3w y vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__mux2_2
C_W4  y   vss 6.0f
.ends datapath_crit_stage

.subckt datapath_crit4 a y vdd vss
X0 a  n1 vdd vss datapath_crit_stage
X1 n1 n2 vdd vss datapath_crit_stage
X2 n2 n3 vdd vss datapath_crit_stage
X3 n3 y  vdd vss datapath_crit_stage
.ends datapath_crit4

X_DP0 TL0 DP4 VDD VSS datapath_crit4
X_DP1 DP4 DP8 VDD VSS datapath_crit4
X_DP2 DP8 DATAPATH_OUT VDD VSS datapath_crit4

* ==============================================================================
* 3. AOI222 + NOR2 Muller C-Element (qsag_muller_c.sv:10-33) Hazard & Retention
* ==============================================================================
.subckt qsag_muller_c_cell a b rst_n q vdd vss
X_RI  rst_n rst             vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__inv_1
X_MAJ a b a q b q zn        vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__aoi222_1
C_ZN  zn vss 2.5f
X_Q   zn rst q              vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nor2_2
C_Q   q  vss 3.5f
.ends qsag_muller_c_cell

* Exhaustive hazard-stress waveform:
*   0..3ns:    rst_n=0 -> q=0
*   6..10ns:   a=0->1->0 while b=0 (Static-0 hazard test on input A)
*   13..17ns:  b=0->1->0 while a=0 (Static-0 hazard test on input B)
*   20ns:      a=0->1, then 23ns: b=0->1 -> Consensus rise q: 0 -> 1!
*   28..32ns:  a=1->0->1 while b=1 (Static-1 retention & consensus handoff A)
*   35..39ns:  b=1->0->1 while a=1 (Static-1 retention & consensus handoff B)
*   42ns:      b=1->0 (hold 1!), then 46ns: a=1->0 -> Consensus fall q: 1 -> 0!
V_MC_RSTN MC_RSTN_RAW 0 PWL(0 0 2.5n 0 2.7n {vdd_val})
V_MC_A    MC_A_RAW    0 PWL(0 0 6.0n 0 6.2n {vdd_val} 10.0n {vdd_val} 10.2n 0 20.0n 0 20.2n {vdd_val} 28.0n {vdd_val} 28.2n 0 32.0n 0 32.2n {vdd_val} 46.0n {vdd_val} 46.2n 0)
V_MC_B    MC_B_RAW    0 PWL(0 0 13.0n 0 13.2n {vdd_val} 17.0n {vdd_val} 17.2n 0 23.0n 0 23.2n {vdd_val} 35.0n {vdd_val} 35.2n 0 39.0n 0 39.2n {vdd_val} 42.0n {vdd_val} 42.2n 0)

X_MCA_ISO MC_A_RAW    MC_A    VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_MCB_ISO MC_B_RAW    MC_B    VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_MCR_ISO MC_RSTN_RAW MC_RSTN VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2

X_DUT_MC  MC_A MC_B MC_RSTN MC_Q VDD VSS qsag_muller_c_cell
X_MC_LOAD MC_Q MC_Q_DLY VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__dlya_1

* ==============================================================================
* 4. Nominal 5-Stage RO-PUF Topologies (nand2_2 + 4x inv_2 & RTL 5x nand2_1)
* ==============================================================================
X_PUF_INV0 PUF_INV_OSC EN PUF_I1 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__nand2_2
C_PI1 PUF_I1 VSS 5.0f
X_PUF_INV1 PUF_I1 PUF_I2 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__inv_2
C_PI2 PUF_I2 VSS 5.0f
X_PUF_INV2 PUF_I2 PUF_I3 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__inv_2
C_PI3 PUF_I3 VSS 5.0f
X_PUF_INV3 PUF_I3 PUF_I4 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__inv_2
C_PI4 PUF_I4 VSS 5.0f
X_PUF_INV4 PUF_I4 PUF_INV_OSC VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__inv_2
C_PI5 PUF_INV_OSC VSS 5.0f

* Exact dregg_puf_ro5 (buf_2 iso + 5 x nand2_1)
X_PUF_NISO EN PUF_EN_ISO VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_PUF_ND0  PUF_ND_OSC PUF_EN_ISO PUF_N1 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_PN1 PUF_N1 VSS 5.0f
X_PUF_ND1  PUF_N1 PUF_N1 PUF_N2 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_PN2 PUF_N2 VSS 5.0f
X_PUF_ND2  PUF_N2 PUF_N2 PUF_N3 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_PN3 PUF_N3 VSS 5.0f
X_PUF_ND3  PUF_N3 PUF_N3 PUF_N4 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_PN4 PUF_N4 VSS 5.0f
X_PUF_ND4  PUF_N4 PUF_N4 PUF_ND_OSC VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__nand2_1
C_PN5 PUF_ND_OSC VSS 5.0f

.tran 20p 220n

.param vmid='0.5*vdd_val'

* --- DCRO Periods & Frequencies (MHz) ---
.meas tran per_dcro_raw0 TRIG v(OSC_RAW0) VAL=vmid RISE=3 TARG v(OSC_RAW0) VAL=vmid RISE=7
.meas tran f_dcro_raw0_mhz PARAM='4.0e-6 / per_dcro_raw0'
.meas tran per_dcro_min  TRIG v(OSC_MIN)  VAL=vmid RISE=3 TARG v(OSC_MIN)  VAL=vmid RISE=7
.meas tran f_dcro_min_mhz  PARAM='4.0e-6 / per_dcro_min'
.meas tran per_dcro_mid  TRIG v(OSC_MID)  VAL=vmid RISE=2 TARG v(OSC_MID)  VAL=vmid RISE=5
.meas tran f_dcro_mid_mhz  PARAM='3.0e-6 / per_dcro_mid'
.meas tran per_dcro_max  TRIG v(OSC_MAX)  VAL=vmid RISE=2 TARG v(OSC_MAX)  VAL=vmid RISE=4
.meas tran f_dcro_max_mhz  PARAM='2.0e-6 / per_dcro_max'

* --- TRCP vs Pure-Inverter vs Parallel-NAND vs Datapath Critical Delay ---
.meas tran t_trcp_mix    TRIG v(TL0) VAL=vmid RISE=1 TARG v(TRCP_MIX_OUT) VAL=vmid RISE=1
.meas tran t_trcp_rtl    TRIG v(TL0) VAL=vmid RISE=1 TARG v(TRCP_RTL_OUT) VAL=vmid RISE=1
.meas tran t_pure_inv    TRIG v(TL0) VAL=vmid RISE=1 TARG v(PURE_INV_OUT) VAL=vmid RISE=1
.meas tran t_par_nand    TRIG v(TL0) VAL=vmid RISE=1 TARG v(PAR_NAND_OUT) VAL=vmid RISE=1
.meas tran t_datapath    TRIG v(TL0) VAL=vmid RISE=1 TARG v(DATAPATH_OUT) VAL=vmid RISE=1

* --- Muller C-Element Hazard & Propagation Measurements ---
.meas tran mc_stat0_max  MAX v(MC_Q) FROM=4.5n  TO=19.5n
.meas tran t_mc_rise     TRIG v(MC_B) VAL=vmid RISE=2 TARG v(MC_Q) VAL=vmid RISE=1
.meas tran mc_stat1_min  MIN v(MC_Q) FROM=25.5n TO=45.5n
.meas tran mc_stat1_droop PARAM='vdd_val - mc_stat1_min'
.meas tran t_mc_fall     TRIG v(MC_A) VAL=vmid FALL=3 TARG v(MC_Q) VAL=vmid FALL=1

* --- Nominal PUF 5-Stage Ring Frequencies (MHz) ---
.meas tran per_puf_inv10 TRIG v(PUF_INV_OSC) VAL=vmid RISE=4 TARG v(PUF_INV_OSC) VAL=vmid RISE=14
.meas tran f_puf_inv_mhz PARAM='10.0e-6 / per_puf_inv10'
.meas tran per_puf_nd10  TRIG v(PUF_ND_OSC)  VAL=vmid RISE=4 TARG v(PUF_ND_OSC)  VAL=vmid RISE=14
.meas tran f_puf_nd_mhz  PARAM='10.0e-6 / per_puf_nd10'

.end
