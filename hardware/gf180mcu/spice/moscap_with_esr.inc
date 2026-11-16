* Deck-local override: original sm141064 rev9 6V NMOSCAP C(V), plus
* 1 ohm unit-cell electrode/contact spreading resistance. Instance m scales
* both C and conductance. Corner factors match moscap_{typical,ss,ff}.
* Do NOT also load the foundry moscap library (duplicate subckt).
* Package damping is separate: 0.125 ohm + 1.8 nH per bondwire.
.subckt cap_nmos_06v0 1 2 c_length=3e-6 c_width=3e-6 dtemp=0
R_electrode 1 ci 1
* Charge integral: dQ/dV is the foundry C(V), strictly positive.
C_moscap ci 2 Q='cap_nmos_06v0_corner*c_length*c_width*(0.001107*v(ci,2)+0.00107/6.25*(ln(cosh(6.25*v(ci,2)-4.1875))-ln(cosh(4.1875))))'
.ends cap_nmos_06v0
