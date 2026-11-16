#!/usr/bin/env python3
"""Run OpenSTA on the fully linked hierarchical standard-cell netlist.
SRAM has no timing model: reports cover logic register paths only. Clock is ideal,
no parasitics, no uncertainty; reported period is data path plus setup, not signoff.
"""
import pathlib,sys,subprocess,os
from run_hier import LIBS,PDK,RUN
root=pathlib.Path(__file__).resolve().parents[1];os.chdir(root)
lib=sys.argv[1];out=pathlib.Path('synth/astra')/lib
sta=next(pathlib.Path('/home/build/qsag-ni-asic/tools').glob('opensta*/bin/sta'))
lf,_,_=LIBS[lib];period=100000 if lib=='asap7' else 100
text=f'''read_liberty {PDK+lf}
read_verilog {out}/linked.v
link_design qsag_ni_asic_top
create_clock -name core -period {period} [get_ports clk]
set_input_delay 0 -clock core [get_ports {{rst cmd_valid cmd_op* cmd_idx* cmd_addr* cmd_data*}}]
set_output_delay 0 -clock core [get_ports {{cmd_ready rsp_valid rsp_data*}}]
set_false_path -from [get_ports rst]
report_units
check_setup -verbose
report_checks -path_delay max -group_path_count 5 -format full_clock_expanded -digits 4
report_clock_min_period -digits 4
report_worst_slack -max -digits 4
report_check_types -max_slew -max_capacitance -violators
exit
'''
(out/'sta.tcl').write_text(text)
with (out/'sta.log').open('w') as f:
    p=subprocess.run(RUN+[str(sta),'-exit',str(out/'sta.tcl')],stdout=f,stderr=subprocess.STDOUT)
print(lib,'sta exit',p.returncode)
if p.returncode:raise SystemExit(p.returncode)
log=(out/'sta.log').read_text()
if 'Error:' in log:raise SystemExit('OpenSTA reported errors: '+str(out/'sta.log'))
for line in log.splitlines():
    if 'period' in line or 'slack' in line or 'Warning:' in line:print(line)
