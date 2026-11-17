#!/usr/bin/env python3
"""Compare stock vs repaired diode charge, then check dQ/dV=C across PVT/FCS."""
import argparse
from pathlib import Path
import re
import platform
import subprocess


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--stock',required=True)
    p.add_argument('--fixed',required=True)
    p.add_argument('--output',type=Path,default=Path('engine_regression'))
    a=p.parse_args()
    if platform.system() != 'Linux':p.error('Linux build host required')
    a.output.mkdir(parents=True,exist_ok=True)
    template=(Path(__file__).parent/'diode_sidewall_regression.sp').read_text()
    for label,exe,temp,fcs in [('stock',a.stock,-40,.5)]+[
            (f'fixed_{t}_{f}',a.fixed,t,f) for t in [-40,27,125] for f in [.35,.5]]:
        case=(a.output/label).resolve();case.mkdir(exist_ok=True)
        source=template.replace('.temp -40',f'.temp {temp}').replace('fcs=0.5',f'fcs={fcs}')
        (case/'test.sp').write_text(source)
        proc=subprocess.run([exe,'-n','-b','test.sp'],cwd=case,capture_output=True,text=True,timeout=60)
        log=proc.stdout+proc.stderr;(case/'ngspice.log').write_text(log)
        rows=[]
        for line in (case/'diode_trace.dat').read_text().splitlines():
            try:row=[float(x) for x in line.split()]
            except ValueError:continue
            rows.append(row)
        final_time=rows[-1][0]
        if label=='stock':
            assert 'aborted' in log and final_time<5e-6, 'Stock unexpectedly passed; re-examine baseline'
            print(f'EXPECTED STOCK ABORT: {final_time:.12g}s',flush=True)
            continue
        assert proc.returncode==0 and 'aborted' not in log and abs(final_time-5e-6)<1e-15
        residual=[]
        for r,s in zip(rows,rows[1:]):
            # v(node) is negative forward diode voltage; cap is @dtest[cd].
            dv=r[1]-s[1]
            if 1e-7<abs(dv)<.002 and .05 < -r[1] < .48:
                dq=s[2]-r[2]; cap=(s[3]+r[3])/2
                residual.append(abs(dq/dv-cap)/cap)
        assert len(residual)>100
        worst=max(residual)
        assert worst<.01, (label,worst)
        print(f'PASS {label}: tstop={final_time:.9g}s, max dQ/dV-vs-C residual={worst:.6g}, samples={len(residual)}',flush=True)

if __name__=='__main__':main()
