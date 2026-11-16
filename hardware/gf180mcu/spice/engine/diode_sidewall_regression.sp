* GF180 nwp diode sidewall-charge continuity regression, issue #870.
* Coefficients: Copyright 2022 GlobalFoundries PDK Authors, Apache-2.0.
.model nwp d cj=0.00014917 cjsw=5.8113e-10 cta=0.0023998
+ ctp=0.0010977 level=3 mj=0.33979 mjsw=0.2257 pb=0.5755
+ php=0.55456 tlevc=1 tpb=0.0027641 tphp=0.0019629 tref=25
+ fcs=0.5
VDRV drive 0 PWL(0 0 1u 0 2u -0.5 3u -0.5 4u 0 5u 0)
RDRV drive node 50k
DTEST 0 node nwp area=1.56942828e-11 pj=2.17286e-05
.temp -40
.options method=gear reltol=1e-5 vntol=1e-7 abstol=1e-13 itl4=200
.control
set num_threads=1
set numdgt=15
set wr_singlescale
set wr_vecnames
save all @dtest[charge] @dtest[cd]
tran 1n 5u 0 1n
wrdata diode_trace.dat v(node) @dtest[charge] @dtest[cd]
meas tran final_voltage FIND v(node) AT=5u
quit
.endc
.end
