* Seed reproducibility diagnostic (same parser RNG as foundry agauss).
.options seed=20261116
.param draw_a=agauss(1,0.1,1) draw_b=agauss(1,0.1,1)
V_A a 0 {draw_a}
V_B b 0 {draw_b}
R_A a 0 1k
R_B b 0 1k
.control
op
echo PARSER_SEED $rndseed
print v(a) v(b)
quit
.endc
.end
