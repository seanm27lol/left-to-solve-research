"""Exact identities and constants for the almost-perfect prime spacing estimates."""
from itertools import combinations_with_replacement
from math import gcd, prod

import sympy as sp


def check_envelopes():
    n, y, x = sp.symbols("N y x", positive=True)
    points = [3*n-3, 3*n-1, 3*n+1]
    gap = (n-1)*sp.prod(v*v+v+1 for v in points) - n*sp.prod(points)**2
    assert sp.expand(gap) == 81*n**4 - 117*n**2 + 57*n - 21
    trace, low, high = 9*y*y-1, 3*y*y-y-1, 3*y*y+y
    for points, expected in [
        ((low, low+2, trace-2*low-2), (y-1)*(2*y+1)*(3*y-1)),
        ((trace-2*high+2, high-2, high), y*(2*y+1)*(3*y-2)),
    ]:
        gap = y*y*sp.prod(t-1 for t in points) - (y*y-1)*sp.prod(points)
        assert sp.expand(gap-expected) == 0
    f = sp.log(1+1/x+1/x**2)
    h = sp.log(x/(x-1))
    assert sp.factor(f.diff(x, 2)) == (2*x**3+7*x**2+4*x+2)/(x**2*(x*x+x+1)**2)
    assert sp.factor(h.diff(x, 2)) == (2*x-1)/(x**2*(x-1)**2)
    i, m = sp.symbols("i m", integer=True, positive=True)
    offset = i-(m+1)/2
    assert sp.factor(sp.summation(offset**2, (i, 1, m))) == m*(m-1)*(m+1)/12
    assert 2*(40**3-1)*7**3 > 40**3 * 8**3


def check_three_prime_widths():
    m, width, theta, n, t = sp.symbols("m W theta N t")
    deviations = tuple((v-(1+theta)/3)*width for v in (0, theta, 1))
    variance = sum(u**2 for u in deviations)/2
    triple_product = sp.prod(deviations)
    assert sp.expand(variance-width**2*(1-theta+theta**2)/3) == 0
    assert sp.expand(triple_product+(1+theta)*(2-theta)*(2*theta-1)*width**3/27) == 0
    central = -m**3 + 3*n*m**2 - 3*n*m + n
    exact = (n-1)*sp.prod(m+u for u in deviations) - n*sp.prod(m+u-1 for u in deviations)
    assert sp.expand(exact-central-(m-n)*variance+triple_product) == 0

    upper = central + (m-n)*width**2/3 + 2*width**3/27
    for center_offset, root_multiple, endpoint_width, expected in (
        (-sp.Rational(1, 3), 1, 3*t-1, -(54*t**3+27*t**2-36*t+4)/27),
        (3, 6, 3*t-3, -(19*t**2+36*t+60)/3),
        (7, 3, 6*t-6, -(182*t**2+360*t+825)/3),
    ):
        endpoint = upper.subs({m: 3*n+center_offset, width: endpoint_width})
        assert sp.expand(endpoint.subs(n, t**2/root_multiple)-expected) == 0



def check_shifted_prime_identities():
    p, r, s, n, z = sp.symbols("p r s N z")
    e = sp.symbols("e", positive=True, integer=True)
    root = p*r*s
    cyclotomics = sp.prod(q*q+q+1 for q in (p, r, s))
    difference = (root+1)*(n*root-1) - (n-1)*(cyclotomics+root)
    assert sp.expand(difference-n*root**2+1+(n-1)*cyclotomics) == 0
    a, b, c = sp.symbols("a b c")
    shifted = (cyclotomics+root).subs({p: -1+a*z, r: -1+b*z, s: -1+c*z})
    assert sp.Poly(shifted, z).nth(0) == sp.Poly(shifted, z).nth(1) == 0
    assert sp.Poly(shifted, z).nth(2) == a*a+b*b+c*c
    # Geometric sum minus (1-z)^e with q=-1+z. Denominator 2-z
    # is a unit as a series over the rationals and at every odd prime.
    series = (1+(1-z)**(2*e+1))/(2-z) - (1-z)**e
    assert series.subs(z, 0) == series.diff(z).subs(z, 0) == 0
    assert sp.factor(series.diff(z, 2).subs(z, 0)) == e*(e+1)


def check_residues():
    residues = (p for p in range(24) if gcd(p, 6) == 1)
    for triple in combinations_with_replacement(residues, 3):
        factors = [p*p+p+1 for p in triple]
        if all(f%3 and f%8 in (1, 7) for f in factors) and prod(factors)%8 == 1:
            assert set(triple) <= {5, 23} and triple.count(5)%2 == 0


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    check_envelopes()
    check_three_prime_widths()
    check_residues()
    check_shifted_prime_identities()
    print("Verified the envelope and width identities, constants and odd-level residue conditions.")
