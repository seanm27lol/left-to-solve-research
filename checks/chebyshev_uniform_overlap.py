"""Check the resultant and remainder identities in the uniform overlap proof.
Run with Python 3.12 and SymPy 1.14.0. All coefficients are rational.
"""

from math import comb

import sympy as sp


def check_positive_resultant():
    x, r, level, y = sp.symbols("x r H y")
    ell = 1 + r
    s, t = 1 + ell, ell
    de = t*x**2 - s*x + 1
    a = r**2 + x*(t*s - 2*t**2*x + level*de)
    b = -r**2 + s*level*x**2 - 2*x*(level + t*s)
    p = 2*a - b + r**2
    f = sp.cancel((a*de - r**2)/x)
    assert sp.expand(b*de - a*(s*x-2) - r**2) == 0
    assert sp.expand(p.subs(x, 0)) == 4*r**2

    resultant = sp.resultant(p, f, x)
    prefactor = r**2 * (1+r)**2 * level**3
    factor = sp.Poly(sp.cancel(resultant/prefactor), r, level, domain=sp.QQ)
    assert sp.expand(resultant - prefactor*factor.as_expr()) == 0

    poly = sp.Poly(factor.as_expr().subs(level, 4*r**2*y), r, y)
    dr, dy = poly.degree_list()
    assert (dr, dy) == (12, 4)
    coefficients = []
    for i in range(dr + 1):
        for j in range(dy + 1):
            bernstein = sum(
                c * sp.Rational(comb(i, m), comb(dr, m))
                  * sp.Rational(comb(j, n), comb(dy, n))
                for (m, n), c in poly.terms() if m <= i and n <= j
            )
            coefficients.append(bernstein)
    assert (len(coefficients), min(coefficients), max(coefficients)) == (65, 64, 20224)
    print("All 65 Bernstein coefficients are positive; extrema 64 and 20224.")


def check_remainder():
    x, s, t, h, lam = sp.symbols("x s t h lambda")
    m = s**2 - 4*t
    de = t*x**2 - s*x + 1
    a = m + x*(t*s - 2*t**2*x + h*de)
    n = sp.cancel((a*de - m)/x)
    linear = 2*((h*s + t**2)*lam - h*s - 3*t**2)
    constant = h*((lam - 1)**2 - s**2*lam/t) + t*s*(5-3*lam) - s**3
    assert sp.expand(sp.rem(n, t*x**2+lam, x) - linear*x - constant) == 0
    assert sp.expand(n.subs(x, 0) - (h + 5*t*s - s**3)) == 0
    print("Verified the quadratic remainder and the lambda = 0 case.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    check_positive_resultant()
    check_remainder()
