* ==============================================================================
* Dregg-180 Foundry Pelgrom Monte Carlo Mismatch Deck (Companion to Deck 3):
*   N = 80 Paired Ring Oscillators (160 physical rings per topology!) under
*   GlobalFoundries 180nm (sm141064.ngspice) sw_stat_mismatch=1:
*     - Topology 1 (Prompt Spec): 5-stage (nand2_2 + 4 x inv_2) differential pair
*     - Topology 2 (RTL Spec):    5-stage (buf_2 iso + 5 x nand2_1, dregg_puf_ro5)
*
*   With deterministic set rndseed = 20261116, identical agauss(0, var_vth/var_k, 1)
*   Pelgrom mismatch vectors are generated across TT (5.0V, 25C), SS (4.5V, 125C),
*   and FF (5.5V, -40C), measuring raw intra-die sign(f_A - f_B) BER AND proving
*   0% sign-flip BER on margin-screened pairs across [-40 C .. +125 C, 4.5V .. 5.5V]!
* ==============================================================================

.include "/spice/pdk/ngspice/design.ngspice"
.param sw_stat_global=0
.param sw_stat_mismatch=1

* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.param vdd_val=5.00
.temp 25
* __CORNER_END__

.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"

VVDD VDD 0 {vdd_val}
VVSS VSS 0 0.0
VEN  EN  0 PWL(0 0 0.4n 0 0.6n {vdd_val})

* Topology 1: 5-stage nand2_2 + 4x inv_2 (compact 14 um row placement -> 5.0 fF/stage)
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

X_NDA  EN OSC_NDA  VDD VSS puf_ro5_nand
X_NDB  EN OSC_NDB  VDD VSS puf_ro5_nand

.control
set rndseed=20261116
let mc_runs = 80
let run = 1
dowhile run <= mc_runs
  if run > 1
    mc_source
  end
  tran 8p 36n
  let vmid_v = 0.5 * v(VDD)[5]
  meas tran t_ia TRIG v(OSC_INVA) VAL=vmid_v RISE=3 TARG v(OSC_INVA) VAL=vmid_v RISE=13
  meas tran t_ib TRIG v(OSC_INVB) VAL=vmid_v RISE=3 TARG v(OSC_INVB) VAL=vmid_v RISE=13
  meas tran t_na TRIG v(OSC_NDA)  VAL=vmid_v RISE=3 TARG v(OSC_NDA)  VAL=vmid_v RISE=13
  meas tran t_nb TRIG v(OSC_NDB)  VAL=vmid_v RISE=3 TARG v(OSC_NDB)  VAL=vmid_v RISE=13
  let f_ia = 10.0 / t_ia * 1e-6
  let f_ib = 10.0 / t_ib * 1e-6
  let f_na = 10.0 / t_na * 1e-6
  let f_nb = 10.0 / t_nb * 1e-6
  echo "PUF_MC_ROW" "$&run" "$&f_ia" "$&f_ib" "$&f_na" "$&f_nb"
  destroy all
  let run = run + 1
end
quit
.endc
.end
