#!/usr/bin/env python3
"""Independent mathematical checks for capacitor and counter/BCH analysis."""
import math
from run_corners import count_distribution, bit_error, bch_tail


def charge_density(v):
    def logcosh(x):
        return abs(x)+math.log1p(math.exp(-2*abs(x)))-math.log(2)
    return .001107*v+.00107/6.25*(logcosh(6.25*v-4.1875)-logcosh(4.1875))


def main():
    for v in [-.5,0,.3,.5,.67,.8,1,4.5,5,5.5]:
        h=1e-5
        numerical=(charge_density(v+h)-charge_density(v-h))/(2*h)
        foundry=.001107+.00107*math.tanh(6.25*v-4.1875)
        assert abs(numerical-foundry) < 1e-10, (v,numerical,foundry)
        assert numerical > 0
    for cycles in [.1,1,2.5,17.2,16300.8]:
        d=count_distribution(cycles,1)
        assert abs(sum(d.values())-1)<1e-12
        assert abs(sum(n*p for n,p in d.items())-cycles)<1e-10
    assert abs(bit_error(100,100,1,True)-.5)<1e-12
    assert bit_error(110,100,1,True)==0
    assert bit_error(110,100,1,False)==1
    assert bch_tail([1]*5+[0]*58)==0
    assert bch_tail([1]*6+[0]*57)==1
    p=.02
    expected=sum(math.comb(63,k)*p**k*(1-p)**(63-k) for k in range(6,64))
    assert abs(bch_tail([p]*63)-expected)<1e-14
    print('PASS: positive foundry dQ/dV at 10 biases; count moments/ties; BCH tail vs binomial and 5/6-error boundary.')

if __name__=='__main__':main()
