* Output noise current of one ring stage (nand2_1 used as inverter) from the foundry BSIM4 noise model.
* The output node is held by an ideal source; a CCVS turns the cell's output current into v(o) (1 V per A),
* so onoise_spectrum is the cell's output current noise in A/sqrt(Hz).  Bias points along a transition.
.include "/spice/pdk/ngspice/design.ngspice"
.param sw_stat_global=0 sw_stat_mismatch=0
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.temp 27
.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
VDD vdd 0 5
VIN in 0 dc 5 ac 1
VOUT x 0 2.5
VS x out 0
H1 o 0 VS 1
RO o 0 1e12
X0 in in out vdd vdd 0 0 gf180mcu_fd_sc_mcu7t5v0__nand2_1
.control
foreach vi 5 3.5 2.5 1.5 0
  foreach vo 0.5 1.5 2.5 3.5 4.5
    alter vin dc = $vi
    alter vout dc = $vo
    op
    let idc = i(vs)
    noise v(o) vin dec 1 1e3 1e9
    setplot noise1
    echo "BIAS vin=$vi vout=$vo"
    print onoise_spectrum
    setplot op1
    print i(vs)
    destroy all
  end
end
.endc
.end
