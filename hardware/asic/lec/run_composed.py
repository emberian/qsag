#!/usr/bin/env python3
import pathlib,subprocess,os,time,json
root=pathlib.Path(__file__).resolve().parents[1];os.chdir(root)
os.environ['PATH']='/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:'+os.environ['PATH']
w=pathlib.Path('lec/work/astra');w.mkdir(parents=True,exist_ok=True)
os.environ['TMPDIR']=str(w.resolve())
run=['env','SWARM_MEM_MAX=16G','swarm-build','timeout','--kill-after=10s','600s']
results=[]
def check(name,base,query,expect):
    p=w/(name+'.smt2');p.write_text(base+query+'\n(check-sat)\n')
    t=time.monotonic()
    # Every result and mutation must be decided; unknown is an error.
    out=subprocess.run(run+['bitwuzla','-t','90000',str(p)],capture_output=True,text=True)
    value=out.stdout.strip();print(name,expect,value,round(time.monotonic()-t,3),flush=True)
    results.append({'name':name,'expect':expect,'result':value,'seconds':time.monotonic()-t})
    return value==expect
ok=True
for name,mod,n in [('csa64','csa_identity',None),('clmul8','clmul_identity',8),('clmul16','clmul_identity',16),('reduce255','gf_reduce_identity',None)]:
    smt=w/(name+'.ys.smt2')
    cmd=f'plugin -i slang; read_slang -Irtl rtl/qsag_asic_keccak_clmul.sv lec/composed.sv --top {mod} '+(f'-G N={n}' if n else '')+f'; proc; flatten; opt_clean; write_smt2 -wires {smt}'
    with (w/(name+'.yosys.log')).open('w') as f:subprocess.run(run+['yosys','-Q','-T','-p',cmd],stdout=f,stderr=subprocess.STDOUT,check=True)
    base=smt.read_text()+f'\n(declare-const s |{mod}_s|)\n'
    # A mismatch is impossible. Flipping the one-bit equality output is observable.
    ok &= check(name,base,f'(assert (|{mod}_n bad| s))','unsat')
    ok &= check(name+'_mut',base,f'(assert (not (|{mod}_n bad| s)))','sat')
# Integer modular composition is deliberately separate from BV bit-blasting.
# R(s+c) = R(R(s)+R(c)); high-bit fold and complement correction.
p=2**64-2**32+1
lemmas={
'mod_add':f'(not (= (mod (+ s c) {p}) (mod (+ (mod s {p}) (mod c {p})) {p})))',
'fold64':f'(not (= (mod (* s {2**64}) {p}) (mod (* s {2**32-1}) {p})))',
'fold96':f'(not (= (mod (* s {2**96}) {p}) (mod (- s) {p})))',
'complement64':f'(not (= (mod (- s) {p}) (mod (+ (- {2**64-1} s) {-((2**64-1)%p)}) {p})))'}
for name,expr in lemmas.items():
    for mut in [False,True]:
        query='(set-logic QF_LIA)\n(declare-const s Int)\n(declare-const c Int)\n(assert '+(f'(not {expr})' if mut else expr)+')\n(check-sat)\n'
        path=w/(name+('_mut' if mut else '')+'.smt2');path.write_text(query)
        t=time.monotonic();o=subprocess.run(run+['z3','-T:30',str(path)],capture_output=True,text=True);v=o.stdout.strip();expected='sat' if mut else 'unsat'
        print(path.stem,expected,v,flush=True);results.append({'name':path.stem,'expect':expected,'result':v,'seconds':time.monotonic()-t});ok &= v==expected
(root/'logs/astra_composed.json').write_text(json.dumps(results,indent=2)+'\n')
raise SystemExit(0 if ok else 1)
