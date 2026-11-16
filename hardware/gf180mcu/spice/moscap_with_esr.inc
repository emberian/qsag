* Deck-local 6V NMOSCAP, using the sm141064 rev9 C(V) coefficients.
* Electrode/contact spreading ESR: 1 ohm per unit cell, divided by multiplicity.
* Foundry models on disk are unmodified. Do not load the duplicate moscap lib.
* Q(V) integrates the positive foundry differential C(V). A voltage-scaled
* charge state avoids a 1H differentiator driven by picoamp charge values in
* ngspice's native Q= expansion. Cq*d(Vq)/dt = dQ/dt exactly.
* Explicit m consumes instance multiplicity once, including ESR scaling.
.subckt cap_nmos_06v0 1 2 c_length=3e-6 c_width=3e-6 dtemp=0 m=1
.func logcosh(x) {abs(x)+ln(1+exp(-2*abs(x)))-0.6931471805599453}
R_electrode 1 ci {1/m}
B_charge q 0 V='(0.001107*v(ci,2)+0.00107/6.25*(logcosh(6.25*v(ci,2)-4.1875)-logcosh(4.1875)))/0.002177'
C_charge q qsense {m*cap_nmos_06v0_corner*c_length*c_width*0.002177}
V_sense qsense 0 0
F_charge ci 2 V_sense 1
.ends cap_nmos_06v0
