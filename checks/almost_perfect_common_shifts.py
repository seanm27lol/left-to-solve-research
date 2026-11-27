"""Check the symbolic identities and rational bounds for the common-shift proof."""
from fractions import Fraction
import sympy as sp

def verify():
    a, b, c, k, L, u = sp.symbols('a b c k L u')
    bases = [x*L-1 for x in (a, b, c)]
    prod = sp.prod(bases)
    envelope = (k*L-2)*prod-(k*L-1)*sp.prod(x-1 for x in bases)
    delta = k*(a*b+a*c+b*c)-a*b*c
    assert sp.expand(envelope-delta*L**3+3*k*(a+b+c)*L**2-(2*(a+b+c)+7*k)*L+6)==0
    pr = k*u*L**2-u*L+1
    psum = u*L-2
    two_factors = pr**2+pr*psum+psum**2-pr+psum+1
    C = (k*L-1)*pr**2
    F = 3*k**2*u*L**3+(u**2-5*k*u)*L**2+1
    assert sp.expand(C-(k*L-2)*two_factors-F)==0
    B = 9*k**4*u*L**2-3*k**2*u*(4*k+u)*L+18*k**3+7*k**2*u-k*u**2+u**3
    r0 = -(45*k**3+7*k**2*u-k*u**2+u**3)
    r1 = 3*k**2*(9*k**2+22*k*u+u**2)
    r2 = -u*(27*k**4+10*k**3*u+12*k**2*u**2-6*k*u**3+u**4)
    assert sp.expand(27*k**3*C-B*F-r0-r1*L-r2*L**2)==0
    assert sp.expand(B.subs(L,0)+27*k**3+r0)==0
    q = sp.symbols("q")
    small, center = 2*q+1, 4*q+3
    lower = q*(small**2+small+1)*(center**2+center+1)**2 - (q+1)*small**2*center**4
    assert sp.expand(lower) == 64*q**5+64*q**4-224*q**3-474*q**2-330*q-81
    assert min(sp.Poly(lower.subs(q,q+3), q).all_coeffs()) > 0
    t=Fraction(1,4)
    assert 45*t**3+7*t**2+t+1<3
    assert 3*(9*t**2+22*t+1)<22
    assert 27*t**4+10*t**3+12*t**2+6*t+1<4
    assert 24+44+512+27==607
    v = sp.symbols('v')
    T = v-k*u
    for sign in (1,-1):
        product, base_sum = v*L**2-sign*u*L+1, u*L-2*sign
        level = k*L-sign
        phi_pair = product**2+product*base_sum+base_sum**2-product+base_sum+1
        num = level*product**2
        den = num-(level-1)*phi_pair
        quotient, _ = sp.div(num, den, L)
        assert sp.cancel(quotient.coeff(L)-k*v/T)==0
        wanted = -3*k*(u*T+k*v)/T**2 if sign==1 else k*(u*T+k*v)/T**2
        assert sp.cancel(quotient.subs(L,0)+sign-wanted)==0
    plus_bases = [x*L+1 for x in (a, b, c)]
    plus_envelope = k*L*sp.prod(plus_bases)-(k*L+1)*a*b*c*L**3
    assert sp.expand(plus_envelope-L*(delta*L**2+k*(a+b+c)*L+k))==0
    plus_product, plus_sum = k*u*L**2+u*L+1, u*L+2
    plus_cyclotomic_pair = plus_product**2+plus_product*plus_sum+plus_sum**2-plus_product+plus_sum+1
    plus_f = (k*L+1)*plus_product**2-k*L*plus_cyclotomic_pair
    assert sp.expand(plus_f+k**2*u*L**3-(u**2-5*k*u)*L**2-(2*u-8*k)*L-1)==0

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O to check the identities.')
    verify()
    print('Verified the envelope and division identities and the coefficient bounds.')
