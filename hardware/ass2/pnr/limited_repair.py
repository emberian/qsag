"""Use the installed LibreLane repair step with bounded setup search."""
import sys
from pathlib import Path
from librelane.__main__ import cli
from librelane.steps.openroad import ResizerTimingPostCTS

native_script = Path(ResizerTimingPostCTS.get_script_path(None))
text = native_script.read_text()
anchor = '    log_cmd repair_timing {*}$hold_args\n    log_cmd repair_timing {*}$setup_args'
assert text.count(anchor) == 1
limited = text.replace(anchor, '''    log_cmd repair_timing {*}$hold_args
    source $::env(SCRIPTS_DIR)/openroad/common/dpl.tcl
    estimate_parasitics -placement
    write_db [file join $::env(STEP_DIR) hold_legal.odb]
    log_cmd repair_timing {*}$setup_args -max_iterations 3 -max_passes 1 -skip_last_gasp''')
script = Path('/work/ass2-pnr/limited_postcts.tcl')
script.write_text(limited)
ResizerTimingPostCTS.get_script_path = lambda self: str(script)
cli()
