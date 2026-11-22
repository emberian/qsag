#!/usr/bin/env python3
"""Linux-only ngspice matrix. A completed process alone is never a PASS."""
from __future__ import annotations
import argparse
import concurrent.futures
import hashlib
import json
import math
from pathlib import Path
import platform
import re
import shutil
import statistics
import subprocess
import time

DECKS = ['brands_chaum_and_vernier_tdc', 'ro_puf_pelgrom_mc',
         'nfc_13p56mhz_afe', 'pdn_ssn_ground_bounce']
MEAS = re.compile(r'^([a-z][a-z0-9_]*)\s*=\s*([-+]?\d+(?:\.\d*)?(?:[eE][-+]?\d+)?)', re.M)
CORNER = {'TT': ('typical', 5.0, 1.0), 'SS': ('ss', 4.5, 1.1), 'FF': ('ff', 5.5, .9)}


def count_distribution(f: float, window: float) -> dict[int, float]:
    """Uniform start phase plus independent {-1,0,+1} stop uncertainty."""
    n = math.floor(f * window)
    frac = f * window - n
    out: dict[int, float] = {}
    for count, prob in [(n, 1-frac), (n+1, frac)]:
        for error in (-1, 0, 1):
            out[count+error] = out.get(count+error, 0) + prob/3
    return out


def bit_error(a: float, b: float, window: float, enroll_sign: bool) -> float:
    return sum(pa*pb*(0.5 if ca == cb else float((ca > cb) != enroll_sign))
               for ca, pa in count_distribution(a, window).items()
               for cb, pb in count_distribution(b, window).items())


def bch_tail(probabilities: list[float]) -> float:
    """Exact Poisson-binomial P(errors>5) for 63 independent disjoint RO pairs."""
    p = [1.0] + [0.0]*len(probabilities)
    for e in probabilities:
        p = [p[0]*(1-e)] + [p[k]*(1-e)+p[k-1]*e for k in range(1, len(p))]
    return sum(p[6:])


def puf_summary(freq: list[float], enrolled: list[float]) -> dict:
    signs = [enrolled[2*i] > enrolled[2*i+1] for i in range(63)]
    rows = []
    # 50MHz core: original 8 cycles, then geometrically increasing windows.
    for cycles in [8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]:
        window = cycles/50e6
        p = [bit_error(freq[2*i], freq[2*i+1], window, signs[i]) for i in range(63)]
        rows.append({'cycles':cycles, 'window_us':window*1e6, 'ber':sum(p)/63,
                     'bch_fail':bch_tail(p), 'fits_14bit':max(freq)*window+2 < 16384})
    passing = [r for r in rows if r['bch_fail'] <= 1e-6 and r['fits_14bit']]
    return {'mean_mhz':statistics.mean(freq)/1e6,
            'sigma_mhz':statistics.stdev(freq)/1e6,
            'relative_sigma_pct':100*statistics.stdev(freq)/statistics.mean(freq),
            'sign_flips':sum((freq[2*i]>freq[2*i+1]) != signs[i] for i in range(63)),
            'first_passing_window_us':passing[0]['window_us'] if passing else None,
            'window_rows':rows}


def run_one(base: Path, output: Path, deck: str, corner: str, temp: int, seed: int,
            timeout: int, slew: int, executable: str, pdk: str) -> dict:
    label = f'{deck}_{corner}_{temp:+d}' + (f'_sl{slew}' if deck == DECKS[3] else '')
    case = output/label
    case.mkdir(parents=True, exist_ok=True)
    source = (base/(deck+'.sp')).read_text().replace('/spice/pdk', pdk)
    source = re.sub(r'seed=\d+',f'seed={seed}',source)
    flavor, voltage, cap_factor = CORNER[corner]
    a, b = source.index('* __CORNER_BEGIN__'), source.index('* __CORNER_END__')
    block = source[a:b].replace(' typical', ' '+flavor)
    for family in ('diode', 'res'):
        block = block.replace(f'{family}_typical', f'{family}_{flavor}')
    block = re.sub(r'vdd_val=[\d.]+', f'vdd_val={voltage}', block)
    block = re.sub(r'cap_nmos_06v0_corner=[\d.]+', f'cap_nmos_06v0_corner={cap_factor}', block)
    block = re.sub(r'\.temp \S+', f'.temp {temp}', block)
    block = re.sub(r'slew_sel=\d', f'slew_sel={slew}', block)
    source = source[:a]+block+source[b:]
    shutil.copyfile(base/'moscap_with_esr.inc', case/'moscap_with_esr.inc')
    source = source.replace('"moscap_with_esr.inc"', '"'+str(case/'moscap_with_esr.inc')+'"')
    (case/'deck.sp').write_text(source)
    init = (base/'.spiceinit').read_text()
    init = re.sub(r'setseed \d+', f'setseed {seed}', init)
    (case/'.spiceinit').write_text(init)
    command = [executable,'-b','deck.sp']
    start = time.monotonic()
    with (case/'ngspice.log').open('w') as log:
        try:
            p = subprocess.run(command, cwd=case, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
            code = p.returncode
        except subprocess.TimeoutExpired:
            code = 124
    logtext = (case/'ngspice.log').read_text(errors='replace')
    measured = {k:float(v) for k,v in MEAS.findall(logtext)}
    flags = {k:v for k,v in measured.items() if k.startswith('pass_')}
    expected = 130 if deck == DECKS[1] else 3
    errors = [line.strip() for line in logtext.splitlines()
              if re.search(r'error:|failed!|aborted|timestep too small|cannot compute',line,re.I)]
    complete = code == 0 and not errors and bool(re.search(r'ngspice-\S+ done', logtext)) and len(flags) == expected
    status = 'PASS' if complete and all(v == 1 for v in flags.values()) else 'FAIL' if complete else 'ERROR'
    result = {'case':label,'deck':deck,'corner':corner,'temp_c':temp,'vdd':voltage,
              'seed':seed,'slew':slew if deck == DECKS[3] else None,
              'status':status,'completed':complete,'returncode':code,
              'seconds':round(time.monotonic()-start,2),'command':command,
              'measurements':measured,'errors':errors,
              'deck_sha256':hashlib.sha256(source.encode()).hexdigest()}
    (case/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'{status}: {label} ({result["seconds"]}s), {len(flags)}/{expected} .meas pass flags',flush=True)
    return result


def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--ngspice',default='ngspice')
    ap.add_argument('--pdk',default='/spice/pdk')
    ap.add_argument('--decks',nargs='+',choices=DECKS,default=DECKS)
    ap.add_argument('--corners',nargs='+',choices=CORNER,default=list(CORNER))
    ap.add_argument('--temps',nargs='+',type=int,default=[-40,27,125])
    ap.add_argument('--jobs',type=int,default=3)
    ap.add_argument('--seed',type=int,default=20261116)
    ap.add_argument('--timeout',type=int,default=900)
    ap.add_argument('--output',type=Path,default=Path('results'))
    ap.add_argument('--slews',nargs='+',type=int,choices=[0,1],default=[0,1])
    args=ap.parse_args()
    if platform.system() != 'Linux':
        ap.error('Simulations run on Linux build hosts only; no ngspice on macOS.')
    if not 1 <= args.jobs <= 4:
        ap.error('--jobs must be 1..4 for shared-host resource control')
    base=Path(__file__).resolve().parent
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=True)
    executable = shutil.which(args.ngspice)
    if executable is None:
        ap.error('ngspice executable not found')
    args.ngspice = executable
    version = subprocess.run([executable,'-v'],capture_output=True,text=True,check=True)
    manifest = {'executable':executable, 'version':version.stdout+version.stderr,
                'executable_sha256':hashlib.sha256(Path(executable).read_bytes()).hexdigest(),
                'pdk':args.pdk, 'files':{}}
    for file in [base/'moscap_with_esr.inc', base/'.spiceinit',
                 Path(args.pdk)/'ngspice/design.ngspice',
                 Path(args.pdk)/'ngspice/sm141064.ngspice',
                 Path(args.pdk)/'ngspice/sm141064.spice',
                 Path(args.pdk)/'gf180mcu_fd_io.spice',
                 Path(args.pdk)/'gf180mcu_fd_sc_mcu7t5v0.spice']:
        manifest['files'][str(file)]=hashlib.sha256(file.read_bytes()).hexdigest()
    (output/'toolchain.json').write_text(json.dumps(manifest,indent=2)+'\n')
    results=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures=[pool.submit(run_one,base,output,d,c,t,args.seed,args.timeout,s,args.ngspice,args.pdk)
                 for d in args.decks for c in args.corners for t in args.temps
                 for s in (args.slews if d==DECKS[3] else [1])]
        for f in concurrent.futures.as_completed(futures):results.append(f.result())
    results.sort(key=lambda r:r['case'])
    ro=[r for r in results if r['deck']==DECKS[1] and r['completed']]
    reference=next((r for r in ro if r['corner']=='TT' and r['temp_c']==27),None)
    for r in ro:
        freq=[r['measurements'][f'freq_{i}'] for i in range(128)]
        r['puf_local']=puf_summary(freq,freq)
        if reference:
            enrolled=[reference['measurements'][f'freq_{i}'] for i in range(128)]
            r['puf_vs_tt27']=puf_summary(freq,enrolled)
    (output/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
    n=sum(r['status']=='PASS' for r in results)
    print(f'MATRIX: {n}/{len(results)} deck checks PASS; see summary.json for numbers and BER model.',flush=True)
    return int(n != len(results))

if __name__=='__main__':
    raise SystemExit(main())
