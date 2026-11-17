; Dregg-180 v2 microcode: the idle point.
;
; Address 0 is the only DISP. The dispatcher refuses bad magic, unknown opcodes and commands whose
; class the lifecycle state does not allow; everything else starts at its .entry address. A command ends
; with END or FAIL: padding, the wipe of all working rows and the return to address 0 are hardware.

idle:       DISP
