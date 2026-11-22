"""Run with OpenROAD -python. Reload the emitted DEF against the run's LEFs."""
import json
import os
from pathlib import Path
import re
import odb

cfg = json.loads(Path(os.environ['RESOLVED']).read_text())
db = odb.dbDatabase.create()
views = [cfg['TECH_LEFS']['nom_*'], *cfg['CELL_LEFS'], *cfg['PAD_LEFS']]
for macro in cfg['MACROS'].values():
    views.extend(macro['lef'])
for path in dict.fromkeys(views):
    odb.read_lef(db, path)
odb.read_def(db.getTech(), os.environ['PLACED_DEF'])
block = db.getChip().getBlock()
units = block.getDbUnitsPerMicron()
assert units == 2000, units

def box(rect):
    return [rect.xMin(), rect.yMin(), rect.xMax(), rect.yMax()]

def pin_net(inst, pin):
    term = inst.findITerm(pin)
    assert term and term.getNet(), (inst.getName(), pin)
    return term.getNet()

def strap(inst, pin):
    net = pin_net(inst, pin)
    drivers = [t.getInst().getMaster().getName().split('__')[-1]
               for t in net.getITerms() if t.getIoType() == 'OUTPUT']
    assert len(drivers) == 1, (net.getName(), drivers)
    return drivers[0]

data = dict(units=units, die=box(block.getDieArea()), instances=[], dq={}, sram={})
for inst in block.getInsts():
    name, master = inst.getName(), inst.getMaster().getName()
    status = inst.getPlacementStatus()
    assert status not in ('NONE', 'UNPLACED'), (name, status)
    data['instances'].append([name, master, inst.getOrient(), *box(inst.getBBox())])
    if 'sram512' in master:
        data['sram'][name] = {p:pin_net(inst,p).getName() for p in ['VDD','VSS','CLK']}
        assert all(data['sram'][name][p] == p for p in ['VDD','VSS'])
    m = re.fullmatch(r'bidir\[(\d+)\]\.pad',name.replace('\\',''))
    if m and int(m[1]) < 8:
        assert master == 'gf180mcu_fd_io__bi_t'
        drivers = [strap(inst,p) for p in ['PDRV1','PDRV0','SL']]
        assert drivers == ['tiel','tieh','tieh'], (name,drivers)
        data['dq'][name] = drivers
assert len(data['dq']) == 8 and len(data['sram']) == 2
Path(os.environ['GEOMETRY']).write_text(json.dumps(data,separators=(',',':')))
