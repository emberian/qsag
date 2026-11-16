#!/usr/bin/env python3
"""bb2: separately map reusable macros and flattened control, then link their netlists.
Each leaf is independently bounded by swarm-build (16 GiB / 600 s). No area estimate:
all black boxes except SRAM are replaced before final hierarchical stat/check.
"""
import os, subprocess, pathlib, sys, concurrent.futures, json, re
ROOT=pathlib.Path(__file__).resolve().parents[1]
os.chdir(ROOT)
os.environ['PATH']='/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:'+os.environ['PATH']
os.environ['TMPDIR']=str(ROOT/'synth'/'work_astra')
pathlib.Path(os.environ['TMPDIR']).mkdir(exist_ok=True)
RUN=['env','SWARM_MEM_MAX=16G','swarm-build','timeout','--kill-after=10s','600s']
PDK='/home/build/qsag-ni-asic/pdk/'
LIBS={'sky130':('sky130_fd_sc_hd__tt_025C_1v80.lib',3.7536,12000),
'ihp130':('sg13g2_stdcell_typ_1p20V_25C.lib',7.2576,10000),
'nangate45':('NangateOpenCellLibrary_typical.lib',.798,3000),
'asap7':('asap7_merged_RVT_TT.lib',.05832,1800)}
# Cut only at named, parameter-free modules. Final adders remain in their caller.
MACROS=['qsag_gl64_mul_tree','qsag_gl64_fold','qsag_p2_me','qsag_p2_mi_fused',
'qsag_p2_canopy_ff','qsag_ext4_kara_inputs','qsag_ext4_kara_combine',
'qsag_keccak_round','qsag_gf128_mul','qsag_tower128_to_poly','qsag_poly_to_tower128']
RTL=' '.join(str(p) for p in sorted(pathlib.Path('rtl').glob('*.sv')))
ABC='+strash;dretime;&get,-n;&dch,-f;&nf,{D};&put;buffer,-c;topo;upsize,{D};dnsize,{D};stime,-p'
def run(lib,mod):
    lf,ge,period=LIBS[lib]; out=pathlib.Path('synth/astra')/lib;out.mkdir(parents=True,exist_ok=True)
    log=out/(mod+'.log'); sv=out/(mod+'.v')
    cut=' '.join('--blackboxed-module '+m for m in MACROS) if mod=='qsag_ni_asic_top' else ''
    script=f'''plugin -i slang
read_slang -Irtl {cut} {RTL} --top {mod}
hierarchy -check -top {mod}
synth -top {mod} -flatten -noabc
dfflibmap -liberty {PDK+lf}
abc -liberty {PDK+lf} -D {period} -script {ABC}
opt_clean
check
tee -o {out/mod}.json stat -json -liberty {PDK+lf}
write_verilog -noattr -noexpr -nodec -selected {sv}
'''
    # Select only the top: imported macro declarations must not be re-emitted.
    script=script.replace('write_verilog',f'select {mod}\nwrite_verilog')
    (out/(mod+'.ys')).write_text(script)
    with log.open('w') as f:
        p=subprocess.run(RUN+['yosys','-T','-s',str(out/(mod+'.ys'))],stdout=f,stderr=subprocess.STDOUT)
    print(lib,mod,'exit',p.returncode,flush=True)
    if p.returncode: raise RuntimeError(str(log))
    return str(sv)
def link(lib):
    lf,ge,period=LIBS[lib]; out=pathlib.Path('synth/astra')/lib
    script=f'read_liberty -lib {PDK+lf}\nread_verilog -sv rtl/sram_dp_blackbox.sv\n'
    script+='\n'.join('read_verilog '+str(out/(m+'.v')) for m in MACROS+['qsag_ni_asic_top'])
    script+=f'\nhierarchy -check -top qsag_ni_asic_top\ncheck\ntee -o {out}/linked.json stat -json -liberty {PDK+lf}\nwrite_verilog -noattr {out}/linked.v\n'
    (out/'link.ys').write_text(script)
    with (out/'link.log').open('w') as f:
        subprocess.run(RUN+['yosys','-T','-s',str(out/'link.ys')],stdout=f,stderr=subprocess.STDOUT,check=True)
    d=json.loads((out/'linked.json').read_text());area=d['design']['area']
    result={'library':lib,'area_um2':area,'kGE':area/ge/1000,'abc_target_ps':period,'macros':{}}
    for m in MACROS+['qsag_ni_asic_top']:
        txt=(out/(m+'.log')).read_text()
        delays=re.findall(r'Delay\s*=\s*([0-9.]+) ps',txt)
        result['macros'][m]={'delay_ps':float(delays[-1]) if delays else None}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result),flush=True)
if __name__=='__main__':
    lib=sys.argv[1]
    if len(sys.argv)>2 and sys.argv[2]=='link': link(lib)
    else:
        mods=sys.argv[2:] or MACROS+['qsag_ni_asic_top']
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: list(ex.map(lambda m:run(lib,m),mods))
