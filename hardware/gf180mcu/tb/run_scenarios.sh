#!/bin/sh
# Physical-fault and clocking scenarios of the chip testbench (remote, cwd = project root).
TAILN=${TAILN:-14} sh tb/run_all.sh "ss_100:clkswitch:quick ss_100:tamper:quick ss_100:glitch:quick ss_100:trng:quick ss_100:loops:quick spi:spiburst:quick async:tamper:quick"
