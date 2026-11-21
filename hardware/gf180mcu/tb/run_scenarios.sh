#!/bin/sh
# Physical-fault, clocking, and Houyhnhnm enclave security regression scenarios (remote, cwd = project root).
TAILN=${TAILN:-18} sh tb/run_all.sh "ss_100:clkswitch:quick ss_100:tamper:quick ss_100:glitch:quick ss_100:trng:quick ss_100:loops:quick spi:spiburst:quick async:tamper:quick spi:coldboot:quick ss_100:coldboot:quick async:coldboot:quick spi:diag:quick spi:prfcap:quick ss_100:prfcap:quick ss_100:tamperboot:quick spi:tamperboot:quick ss_100:bist:quick spi:bist:quick async:bist:quick spi:enclave:quick"
