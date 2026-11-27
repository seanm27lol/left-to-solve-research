"""Exact k = 10 certificate. Run beside chebyshev_small_shift_ratios.py with SymPy 1.14."""
from itertools import product
from math import gcd, isqrt, prod

import sympy as sp

from chebyshev_small_shift_ratios import large_ratios, small_pairs

K = 10
CUTOFF = 10000
G_MIN = 1001
X, LAM = sp.symbols("x lambda")
# h, lower S/g, cap for gz/w, factorization of the integer Bezout constant,
# expected (progressions, g-values counted with class, quadratic discriminants).
FAMILIES = {
    11: (39, 48, 15000, {2: 5, 43: 1, 179: 1, 317: 1, 163050143: 1},
         (288, 52313, 522725)),
    17: (1943, 54, 55000, {2: 3, 5: 1, 7: 3, 432161: 1, 7125293627: 1},
         (864, 8440, 63863)),
}


def numerators(ell, h, x):
    m, t, s = (ell-K)**2, K*ell, K+ell
    de = (K*x-1)*(ell*x-1)
    excess = t*s - 2*t*t*x + h*de
    return m + x*excess, -m + s*h*x*x - 2*x*(h+t*s), m, excess


def exclude_mod_nine():
    # Each numerator is a polynomial, so period 9*9=81 covers division by 9.
    for x in range(81):
        an, bn, m, excess = numerators(13, 347, x)
        if an % m or bn % m or excess % m:
            continue
        A, B = an//m, bn//m
        n = A*(10*x-1)*(13*x-1)
        if n % 3 != 1:
            continue
        units = [i for i in range(1, 9) if i%3 and (n-1)%gcd(i-1, 9)==0]
        for a, b, c in product(units, repeat=3):
            assert (a*b*c-A)%9 or (a*b+b*c+c*a-B)%9


def positive_on_tail(expr):
    shifted = sp.Poly(sp.expand(expr.subs(X, G_MIN+X)), X)
    assert shifted.TC() > 0 and min(shifted.all_coeffs()) >= 0


def integer_coeffs(expr, symbol, size):
    coeff = [sp.expand(expr).coeff(symbol, i) for i in range(size)]
    assert all(c.is_Integer for c in coeff)
    assert sp.expand(expr - sum(c*symbol**i for i, c in enumerate(coeff))) == 0
    return list(map(int, coeff))


def check_shape(ell, h, lower, cap):
    m, t = (ell-K)**2, K*ell
    an, bn, _, _ = numerators(ell, h, X)
    A, B = sp.expand(an/m), sp.expand(bn/m)
    de = (K*X-1)*(ell*X-1)
    assert sp.expand(B*de-A*((K+ell)*X-2)) == 1
    R0, J0 = A-B-1, sp.expand(A*de-1-t*X**2*(A-B-1))
    # S^2 >= 3B; S<60g. These three positive polynomials prove 1 < J/R < 2.
    positive_on_tail(3*B-(lower*X)**2)
    positive_on_tail((J0-t*X**2*(60*X))-(R0+60*X))
    positive_on_tail(2*(R0+lower*X)-(J0-t*X**2*(lower*X)))

    quotient, rem = sp.div(sp.Poly(J0-LAM*R0, X), sp.Poly(t*X**2+LAM, X))
    q = sp.Poly(sp.expand(quotient.as_expr()*m*t), X, LAM)
    assert q.degree(X) == 1 and q.degree(LAM) == 1
    assert all(c.is_Integer for c in q.coeffs())
    scaled = sp.Poly(sp.expand(rem.as_expr()*m*t), X)
    E, F = [integer_coeffs(scaled.nth(i), LAM, 3) for i in (1, 0)]
    # E and F are divided by w^2 here. On 1<lambda<2 the following loose
    # bounds exclude an identically or pointwise zero residual at all g>=1001.
    assert E[0]>0 and E[1]<0 and E[2]>0
    max_E = E[0]+E[1]+4*E[2]
    abs_F = sum(abs(c)*2**j for j,c in enumerate(F))
    assert max_E<0 and G_MIN*max_E+abs_F<0
    assert -E[0]-2*E[1]+abs_F < cap*t
    return A, B, E, F


def prime(n):
    return n>=2 and all(n%d for d in range(2, isqrt(n)+1))


def compress(residues, modulus, p):
    # Project to smaller modulus only when all p lifts are present.
    while modulus%p==0:
        smaller = modulus//p
        projected = {r%smaller for r in residues}
        if len(projected)*p != len(residues):
            break
        residues, modulus = projected, smaller
    return [(r,modulus) for r in sorted(residues)]


def valuation_below(value, p, level):
    for i in range(level):
        if value%p:
            return i
        value //= p
    return level


def small_options(ell, h, p, exponent):
    level = {2:6, 5:2, 7:3}[p]
    modulus, denom = p**level, (ell-K)**2
    p_part = p**valuation_below(denom, p, 8)
    unit_inverse = pow(denom//p_part, -1, modulus)
    bins = {}
    multiplier = 2 if 2*(ell-K)%p==0 else 1
    for x in range(modulus*p_part):
        an, bn, _, excess = numerators(ell, h, x)
        if any(u%p_part for u in (an, bn, excess)):
            continue
        A, B = ((u//p_part)*unit_inverse%modulus for u in (an,bn))
        d, e = K*x-1, ell*x-1
        n = A*d*e
        if n%p==0 or (p==2 and (x%2 or n%4!=1)):
            continue
        if (A*e+1)%gcd(modulus,K*x) or (A*d+1)%gcd(modulus,ell*x):
            continue
        vp = valuation_below(2*A-B+1, p, level)
        vn = valuation_below(n-1, p, level)
        upper = multiplier*exponent
        if vp<level:
            upper = min(upper, vp)  # w | 2A-B+1
        if vn<level:
            upper = min(upper, multiplier*vn)  # w | L^2, or no triple overlap
        for j in range(2 if p==2 else 0, upper+1):
            bins.setdefault(j,set()).add(x)
    return [(a,m,p**j) for j,residues in bins.items()
            for a,m in compress(residues,modulus*p_part,p)]


def overlap_options(ell, h, factors, A, B):
    P = sp.Poly(2*A-B+1,X).clear_denoms(convert=True)[1]
    Q = sp.Poly(A*(K*X-1)*(ell*X-1)-1,X).clear_denoms(convert=True)[1]
    u,v,unit = sp.gcdex(P,Q)
    assert unit.degree()==0
    bound = prod(p**j for p,j in factors.items())
    u, v = (pol.mul_ground(bound/unit.LC()) for pol in (u,v))
    assert all(c.is_Integer for row in (u,v) for c in row.all_coeffs())
    assert (u*P+v*Q).as_expr()==bound
    options = []
    for p,j in factors.items():
        assert prime(p)
        if p>13:
            common = sp.gcd(P.set_modulus(p), Q.set_modulus(p)).monic()
            assert j==1 and 2*(ell-K)%p and common.degree()==1
            options.append([(0,1,1),(int(-common.TC())%p,p,p)])
        else:
            options.append(small_options(ell,h,p,j))
    for p in (3,5,11,17):
        if p in factors:
            continue
        allowed = []
        for x in range(p):
            an, _, denom, _ = numerators(ell,h,x)
            assert denom%p
            A_mod = an*pow(denom,-1,p)%p
            d, e = K*x-1, ell*x-1
            n = A_mod*d*e
            if n%p==0 or (p==3 and n%3!=1):
                continue
            if (e*A_mod+1)%gcd(p,K*x) or (d*A_mod+1)%gcd(p,ell*x):
                continue
            allowed.append(x)
        if len(allowed)*3<p*2:  # Optional necessary filter; omission enlarges the cover.
            options.append([(a,m,1) for a,m in compress(set(allowed),p,p)])
    return options


def verify_family(ell):
    h, lower, cap, factors, expected = FAMILIES[ell]
    A, B, E, F = check_shape(ell,h,lower,cap)
    options = overlap_options(ell,h,factors,A,B)
    classes = g_values = discriminants = 0
    for row in product(*options):
        w = prod(factor for _,_,factor in row)
        residue, period = 0, 1
        for local, modulus, _ in row:
            if modulus>1:
                residue += period*((local-residue)*pow(period,-1,modulus)%modulus)
                period *= modulus
        first = G_MIN+(residue-G_MIN)%period
        classes += 1
        for g in range(first,cap*w,period):
            g_values += 1
            aa = E[2]*g+F[2]
            bb = (E[1]*g+F[1])*w
            cc = (E[0]*g+F[0])*w*w
            assert aa>0
            upper = (cap*w-1)//g
            discriminants += upper
            for z in range(1,upper+1):
                disc = (bb+z)**2-4*aa*(cc+K*ell*w*g*g*z)
                assert disc<0 or isqrt(disc)**2!=disc, (ell,h,g,w,z)
    assert (classes,g_values,discriminants)==expected
    print(f'(10,{ell},{h}): {classes} classes, {g_values} parameters, '
          f'{discriminants} discriminants, zero squares.')


if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O so all certificates are checked.')
    assert small_pairs([K],CUTOFF)==[171,25,0]
    assert large_ratios(K,CUTOFF)==[(11,39),(13,347),(17,1943)]
    exclude_mod_nine()
    for ell in FAMILIES:
        verify_family(ell)
