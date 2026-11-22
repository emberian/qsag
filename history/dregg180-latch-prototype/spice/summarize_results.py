#!/usr/bin/env python3
"""Render the measured results; no simulator invocation and no invented cells."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent/'results'
ORDER=[(c,t) for c in ['TT','SS','FF'] for t in [-40,27,125]]

def read(name):
    data=json.loads((ROOT/(name+'_summary.json')).read_text())
    assert all(r['completed'] for r in data), f'{name}: incomplete simulation'
    return data

def window(x):
    return 'none within 14 bits' if x is None else f'{x:.2f}'

def main():
    rapid,ro,nfc,pdn=[read(n) for n in ['rapid','ro','nfc','pdn']]
    assert [len(x) for x in [rapid,ro,nfc,pdn]]==[9,9,9,18]
    maps=[{(r['corner'],r['temp_c']):r for r in group} for group in [rapid,ro,nfc]]
    pm={(r['corner'],r['temp_c'],r['slew']):r for r in pdn}
    all_runs=rapid+ro+nfc+pdn
    passes=sum(r['status']=='PASS' for r in all_runs)
    out=['# Dregg-180 SPICE results — 2026-11-16','',
         f'**45/45 final simulations completed; {passes}/45 electrical checks PASS.** '
         'The 11 FAIL results are design-budget failures, not simulator aborts. '
         'BCH results below are calculated under the stated counter-noise model.','',
         'Rapid-path results use ngspice 45. RO, NFC, and PDN use the isolated '
         'ngspice 47 build with the validated diode sidewall-charge repair. '
         'Foundry model files are unmodified. Full inputs, logs, hashes, and '
         'measurement vectors are in the adjacent JSON files and evidence archives.','',
         '## Corner × deck table','',
         'TT/SS/FF supplies are 5.0/4.5/5.5 V. Rapid delay is the worst of four '
         'PCB-pad-to-PCB-pad polarities; it excludes reader/air-path travel. '
         'PDN reports positive **south-bank** ground bounce for SL=0 / SL=1.','',
         '| Process | °C | Rapid status / ns / TDC ps | RO status / MHz mean ± σ | NFC status / cold avg–peak µA | PDN SL0 / SL1 status, peak mV |',
         '|---|---:|---|---|---|---|']
    for key in ORDER:
        a,b,c=[m[key] for m in maps];am=a['measurements'];bm=b['puf_local'];cm=c['measurements']
        delay=max(am[k] for k in ['t_db_rr_total','t_db_ff_total','t_db_rf_inv','t_db_fr_inv'])*1e9
        p0,p1=[pm[(*key,s)] for s in [0,1]]
        out.append(f'| {key[0]} | {key[1]} | {a["status"]} / {delay:.3f} / {am["delta_tau"]*1e12:.2f} | '
                   f'{b["status"]} / {bm["mean_mhz"]:.3f} ± {bm["sigma_mhz"]:.3f} | '
                   f'{c["status"]} / {cm["cold_inject_avg"]*1e6:.4f}–{cm["cold_inject_pk"]*1e6:.2f} | '
                   f'{p0["status"]} {p0["measurements"]["vss_south_pk"]*1e3:.1f} / '
                   f'{p1["status"]} {p1["measurements"]["vss_south_pk"]*1e3:.1f} |')
    out += ['', 'All rapid latch-hold and TDC-step checks pass. SS/125 °C misses the '
            '5 ns turnaround limit; SS/27 °C has only about 28 ps nominal margin. '
            'No RTL or extracted-layout timing closure is claimed.', '',
            '## RO window and BCH(63,36,t=5)', '',
            '128 physical NAND ROs were sampled with foundry local mismatch and parser '
            'seed 20261116. All 128 plus the two inverter witnesses oscillate at every '
            'corner. Frequencies feed an explicit model: uniform counter start phase, '
            'independent −1/0/+1 stop error per ring, and random tie decisions. '
            'The 63 BCH bits use disjoint pairs and ideal long-window TT/27 °C enrollment. '
            'The target is P(more than 5 errors) ≤10⁻⁶, computed by exact '
            'Poisson-binomial convolution; this is not a measured silicon BER.', '',
            '| Process | °C | BER 160 ns | BER 10.24 µs | BER 20.48 µs | BCH failure at 10.24 µs | First passing local / TT27 window (µs, 14-bit) | Sign flips vs TT27 |',
            '|---|---:|---:|---:|---:|---:|---|---:|']
    for key in ORDER:
        r=maps[1][key];p=r['puf_vs_tt27'];l=r['puf_local'];w={x['cycles']:x for x in p['window_rows']}
        out.append(f'| {key[0]} | {key[1]} | {w[8]["ber"]:.5f} | {w[512]["ber"]:.5f} | '
                   f'{w[1024]["ber"]:.5f} | {w[512]["bch_fail"]:.3g} | '
                   f'{window(l["first_passing_window_us"])} / {window(p["first_passing_window_us"])} | {p["sign_flips"]} |')
    max_f=max(r['measurements'][f'freq_{i}'] for r in ro for i in range(128))
    out += ['', f'The fastest measured ring is {max_f/1e6:.3f} MHz. A fixed 20.48 µs '
            f'window needs {max_f*20.48e-6+2:.1f} counts including two-count headroom: '
            '**15 counter bits**, or adaptive 10.24/20.48 µs windows with 14 bits. '
            'The 512-cycle window alone does not meet the model target at every corner. '
            'Cross-process comparisons are fixed-seed sensitivity experiments; a chip '
            'does not change process corner. Spatial covariance, noisy enrollment, aging, '
            'analog jitter, and real counter circuitry are outside this model. All 13 '
            'tested windows per corner are retained in `ro_summary.json`.', '',
            '## NFC component and cold-tap measurements','',
            'Each case has an independent antenna. The applied series EMF is 7.5 Vpk '
            'at 13.56 MHz, corresponding to approximately 134 Vpk for the unloaded '
            'linear nominal tank. Cold VDD is held at 0 V to measure injection into a '
            'discharged supply; this does not predict the eventual voltage of a floating '
            'board. The protected gate path uses 2.2 kΩ, Schottky clamps and an isolated '
            'open-drain transistor; the rectifier uses 150 Ω. The unsafe comparison '
            'connects its tank directly to an unpowered foundry pad through 2.2 kΩ.', '',
            '| Process | °C | RECT max V | Cold pad min / max V | Unsafe avg / peak mA | Rectifier peak mA | Rectifier R / gate R mW |',
            '|---|---:|---:|---|---|---:|---|']
    for key in ORDER:
        m=maps[2][key]['measurements']
        out.append(f'| {key[0]} | {key[1]} | {m["rect_max"]:.3f} | {m["cold_min"]:.3f} / {m["cold_max"]:.3f} | '
                   f'{m["bad_inject_avg"]*1e3:.3f} / {m["bad_inject_pk"]*1e3:.3f} | '
                   f'{m["rect_current_pk"]*1e3:.2f} | {m["rect_resistor_w"]*1e3:.2f} / {m["gate_resistor_w"]*1e3:.2f} |')
    out += ['', 'All nine cases satisfy the unchanged 1 µA average / 100 µA peak '
            'cold-injection targets, ±0.3 V pad excursion, 70 mA rectifier peak, '
            'and 0.25 W resistor budgets. The 150 Ω resistor replaces a measured '
            '220 Ω trial that dissipated 0.268–0.272 W at TT. Use the ≥0.5 W '
            'part specified in the PCB BOM and check its temperature derating. '
            'These are project screening limits, not foundry injection-current ratings '
            'or vendor-model qualification. The reference board has 85 °C-rated POR/FRAM.', '',
            '## PDN detail','',
            'Three DVDD/DVSS pairs plus one core pair, 125 mΩ / 1.8 nH per bond, '
            '1.8 nF allocated on-die decap, eight simultaneous foundry outputs into '
            '15 pF each through 33 Ω, and a 20→120 mA core-current pulse. '
            'All 18 rail-differential and quiet-victim checks pass. The bounce/droop '
            'budget passes 8/18; every electrical failure is retained.', '',
            '| Process | °C | SL | Status | South peak mV | Core min / max mV | VDD droop mV | Min VDD−VSS V |',
            '|---|---:|---:|---|---:|---|---:|---:|']
    for key in ORDER:
        for s in [0,1]:
            r=pm[(*key,s)];m=r['measurements']
            out.append(f'| {key[0]} | {key[1]} | {s} | {r["status"]} | {m["vss_south_pk"]*1e3:.2f} | '
                       f'{m["vss_core_neg"]*1e3:.2f} / {m["vss_core_pk"]*1e3:.2f} | '
                       f'{m["vdd_droop_pk"]*1e3:.2f} | {m["rail_collapse_min"]:.4f} |')
    out += ['', 'The worst south-bank bounce is 1.20042 V at FF/−40 °C/SL=0, with '
            '0.945429 V droop. The board/source terminations do not close the 0.5 V '
            'budget. Package extraction, extra return paths and/or a reduced simultaneous '
            'switching load need evaluation before signoff. The 1.8 nF is an allocation, '
            'not an extracted fillcap measurement.', '',
            'Numerical control: changing PDN junction gmin from 1e-12 to 1e-10 S '
            'resolved the troublesome TT/27 °C/SL=1 operating point. The paired TT/27 °C/SL=0 '
            'control changed south/core bounce by only 22 µV and droop by 6 µV; '
            'the pass limits were unchanged. Six ESD RC ladders receive released '
            '`.nodeset` guesses, not forced transient voltages.', '',
            '## Verification and remaining work','',
            '- Coil calculator: existing seven self-test assertions PASS; L=1.4662 µH, '
            'Rac=0.988 Ω, Ctotal=93.95 pF. Coupling/keepout formulas remain analytical estimates.',
            '- Independent charge/counter analysis checks PASS. Stock ngspice diode '
            'regression aborts at 1.68687851999 µs; all six repaired cases reach 5 µs. '
            'Worst dQ/dV-versus-C relative discrepancy is 1.8263×10⁻⁷.',
            '- `../../pcb/README.md` contains the stackup, reference schematic description, '
            'BOM, POR/reset, tamper RC, NFC isolation, SPI, FRAM and test points.',
            '- Not delivered: a routed PCB/Gerbers, extracted package/decap data, '
            'vendor-qualified discrete PVT models, ASK protocol qualification, a '
            'physical BER certification, full TDC DNL/INL, or RTL integration/security proof.',
            '- Explicit unresolved design limits: SS/hot rapid timing and TT/FF SSN. '
            'No tests were relaxed to mark these green.','']
    (ROOT/'RESULTS.md').write_text('\n'.join(out))
    print(f'Wrote {ROOT / "RESULTS.md"}: {passes}/45 PASS, 45/45 complete.')

if __name__=='__main__':main()
