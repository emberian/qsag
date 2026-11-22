"""Keep CTS spacing on the primary trees and use PDK default rules on gated subtrees."""
from pathlib import Path
import sys
import odb

odb_in = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('/work/ass2-excellence/pnr/librelane/runs/ass2/30-openroad-cts/chip_top.odb')
odb_out = Path(sys.argv[2]) if len(sys.argv) > 2 else Path('/work/ass2-excellence/pnr/postcts_primary_ndr.odb')
db = odb.dbDatabase.create()
odb.read_db(db, str(odb_in))
block = db.getChip().getBlock()
removed, retained = [], []
primary_rules = {
    net.getNonDefaultRule().getName() for net in block.getNets()
    if net.getNonDefaultRule() and any(label in net.getName() for label in ('clk_PAD2CORE', 'bidir_PAD2CORE'))
}
for net in block.getNets():
    rule = net.getNonDefaultRule()
    if rule is None or not rule.getName().startswith('CTS_NDR_'):
        continue
    if rule.getName() in primary_rules:
        retained.append(net.getName())
        continue
    net.setNonDefaultRule(None)
    removed.append(net.getName())
print('Retained primary-tree NDRs:', len(retained), '; default-width gated subnets:', len(removed))
odb.write_db(db, str(odb_out))
