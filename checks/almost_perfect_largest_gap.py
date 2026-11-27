"""Symbolic certificate for the prime-gap bound and exhaustive 3-component check.

Use Python 3.8+ with SymPy for the symbolic identities.
"""
from math import isqrt
import sympy as sp


def polynomials(h):
    g = h**4 + h*h + 1
    a = (2*(h**4-3*h*h-1), (h+1)*(3*h**4+2*h**3-11*h*h+2*h-5),
         (h+1)*(h**5+4*h**4+3*h**3-12*h*h+h-6), 5*h**5+6*h**4-5*h**3-2*h*h-3*h-4)
    b = (a[0], 3*h**5+h**4-9*h**3+3*h**2-3*h-1,
         (h+1)*(h+2)*(h*h-h+1)**2, -(h*h-h+1)**2*(h*h+h+1))
    return g*g, a, b


def evaluate(coefficients, x):
    value = 0
    for coefficient in coefficients:
        value = value*x + coefficient
    return value


def phi(x):
    return x*x+x+1


def check_symbolic():
    x, h, u, v = sp.symbols("x h u v")
    w, a, b = polynomials(h)
    a, b = evaluate(a,x), evaluate(b,x)
    assert sp.expand(a*x*x*(x+h)**2-b*phi(x)*phi(x+h)-w)==0
    for expression in (a, w*x**3-a, 9*h**4*x**3-a):
        poly = sp.Poly(expression.subs(x,h+u).subs(h,2+v),u,v)
        assert poly.TC()>0 and min(poly.coeffs())>=0
    A = sp.Poly(a.subs(h,2*v).subs(x,2*u+1),u,v,modulus=2)
    assert A.as_expr()==1


def covers(h, max_level=21):
    base = 1 << max_level
    w, a, _ = polynomials(h)
    xmax = w # r < W and r >= 2^21+1
    if xmax<=base:
        return 0,0,0,0
    # Positive residual when r>=9h^4. Otherwise check negative indices too.
    limit=(w-1)//(base+1)
    k_start=1 if base>=9*h**4 else -limit
    if not k_start%2:
        k_start += 1

    levels=[(1, list(range(k_start, limit+1, 2)))]
    # A(r)+k*Phi(r)*Phi(r+h) == 0 at current precision. Lift each r
    # and retain only k satisfying the next bit. Phi(r)*Phi(r+h) is a unit.
    # Equivalent to enumerating odd r mod 2^21 and solving for k, but
    # this tree prunes branches with no allowed k.
    for prec in range(2,max_level+1):
        mod=1<<prec
        half=mod//2
        next_level=[]
        for r, ks in levels:
            for lifted in (r,r+half):
                residue=(-evaluate(a,lifted)*pow(phi(lifted)*phi(lifted+h),-1,mod))%mod
                allowed=[k for k in ks if k%mod==residue]
                if allowed:
                    next_level.append((lifted,allowed))
        levels=next_level

    representatives=integral=perfect=candidates=0
    for r0, ks in levels:
        for k in ks:
            for r in range(base+r0, (w-1)//abs(k)+1,base):
                representatives+=1
                s=r+h
                nom=evaluate(a,r)+k*phi(r)*phi(s)
                A,rem=divmod(nom,w)
                if rem:
                    continue
                integral+=1
                if A<=0:
                    continue
                N=A&-A
                assert N>=base
                p=isqrt(A//N)
                if N*p*p!=A:
                    continue
                perfect+=1
                if not N<p<r:
                    continue
                if (N-1)*phi(p)*phi(r)*phi(s)==N*(p*r*s)**2-1:
                    candidates+=1
                    print('integer solution',h,p,r,s,N,flush=True)
    return representatives,integral,perfect,candidates


if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    import sys
    cutoff=int(sys.argv[1]) if len(sys.argv)>1 else 24
    check_symbolic()
    expected = (0,0,0,29,223,1106,4216,13346,36691,90317,307225,652570)
    for h in range(2,cutoff+1,2):
        counts = covers(h)
        if h<=24:
            assert counts==(expected[h//2-1],0,0,0), (h,counts)
        print(h,counts,flush=True)
