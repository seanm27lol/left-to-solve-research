#!/usr/bin/env python3
"""Exact certificate for the Chebyshev five-prime branch (7, 11, 442).

Run with Python 3.8+. The inputs are the family formulas for A=abc and
B=ab+ac+bc, d=7g-1 < e=11g-1 < a < b < c < 2d, and the required shifts
d+1,e+1,a-1,b-1,c-1 dividing n-1, where n=Ade. The five primes exceed 3.

Write S=a+b+c, R=(a-1)(b-1)(c-1), L=lcm(a-1,b-1,c-1), w=R/L,
J=n-1-77g²R, and k=J/L. Thus kR=wJ. The first enumeration enlarges this
system to a finite list of quadratic discriminants in k. The second uses
the additional negative-shift residues to enumerate discriminants in g.
A nonnegative perfect square is necessary in either enumeration.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb, gcd, isqrt, prod


# Polynomial coefficients in ascending degree, for the indeterminate g.
A8 = (8, 914, -9907, 17017)  # 8A
B4 = (-4, -914, 1989)        # 4B
P = (16, 1828, -11896, 17017)  # 4(2A-B+1)
N = (770, -25743, 265721, -1069145, 1310309)  # 8(n-1)/g
U = (35208505871, -111642799613, -582543875991, 7110817638925)
V = (2334186280, -3228450042, -92348281025)
ROOTS = {7: (4,), 11: (5,), 41: (18, 29), 11683657: (5633197,)}
K = prod(ROOTS)


def coefficients(values):
    result = list(values)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def add(*terms):
    return coefficients(sum(p[i] for p in terms if i < len(p))
                        for i in range(max(map(len, terms))))


def scale(factor, p):
    return coefficients(factor * c for c in p)


def mul(p, q):
    result = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return coefficients(result)


def evaluate(p, x):
    answer = 0
    for c in reversed(p):
        answer = answer * x + c
    return answer


def gcd_mod(p, q, ell):
    def reduce_mod(f):
        return coefficients(c % ell for c in f)

    p, q = reduce_mod(p), reduce_mod(q)
    while q != (0,):
        inverse = pow(q[-1], -1, ell)
        while p != (0,) and len(p) >= len(q):
            offset = (0,) * (len(p) - len(q))
            p = reduce_mod(add(p, offset + scale(-p[-1] * inverse, q)))
        p, q = q, p
    return reduce_mod(scale(pow(p[-1], -1, ell), p))


def positive_from(p, start):
    """Positive coefficients after translation prove positivity for g >= start."""
    shifted = [sum(p[i] * comb(i, j) * start**(i-j) for i in range(j, len(p)))
               for j in range(len(p))]
    return shifted[0] > 0 and min(shifted) >= 0


def r8(s):
    return add(A8, scale(-2, B4), scale(8, s), (-8,))


def j8(s):
    return add((0, 770, -26359, 54587), (0, 0) + scale(-616, s))


def check_algebra():
    de = (1, -18, 77)
    assert add(mul(scale(2, B4), de), scale(-1, mul(A8, (-2, 18)))) == (8,)
    assert add(A8, scale(-1, B4), (4,)) == P
    assert add(mul(A8, de), (-8,)) == (0,) + N

    # This identity proves the complete odd support bound for pairwise gcds.
    # If t divides two shifts, B=2A+1 mod t. If t is odd, P(0)=16 shows
    # gcd(t,g)=1, hence t divides N as well. Thus the odd part divides K.
    assert K == 36885305149
    assert add(mul(U, P), mul(V, N)) == (64*K,)
    for ell, roots in ROOTS.items():
        assert all(ell % t for t in range(2, isqrt(ell)+1))
        factors = (1,)
        for root in roots:
            factors = mul(factors, (-root, 1))
            # All three shifts divisible would force A=1 mod ell.
            assert (evaluate(A8, root) - 8) % ell
        assert gcd_mod(P, N, ell) == tuple(c % ell for c in factors)

    # S²>=3B. Also S²-3B=(c-a)²-(b-a)(c-b)<(3g-1)².
    assert positive_from(add(scale(3, B4), (0, 0, -4*38**2)), 18)
    assert positive_from(add(scale(4, mul((-1, 39), (-1, 39))),
                             scale(-3, B4), scale(-4, mul((-1, 3), (-1, 3)))), 18)
    # For each positive threshold t, J-tR decreases as S increases.
    for start, s, top, bottom, sign in (
        (18, (0, 42), 1, 1, 1), (18, (0, 38), 11, 6, -1),
        (522, (-1, 39), 179, 100, 1), (522, (0, 38), 46, 25, -1),
    ):
        assert positive_from(scale(sign, add(scale(bottom, j8(s)), scale(-top, r8(s)))), start)

    # QZ-(Eg+F)=77w(8kR-8wJ). Both sides are affine in S and homogeneous
    # quadratics in (k,w), so these six specializations check every coefficient.
    for s, (k, w) in product((0, 1), ((0, 1), (1, 0), (1, 1))):
        assert j8((s,)) == add((0,) + N, scale(-77, (0, 0) + r8((s,))))
        q = (k, 0, 77*w)
        z_signed = (616*w*s-13885*k+26359*w, 17017*k-54587*w)
        e = 17017*k*k - 265721*k*w + 59290*w*w
        f = k*(25743*w-13885*k)
        lhs = add(mul(q, z_signed), (-f, -e))
        rhs = scale(77*w, add(scale(k, r8((s,))), scale(-w, j8((s,)))))
        assert lhs == rhs

    # For t=k/w in (1,11/6), E/w² and (E+F)/w² are negative:
    # both are decreasing quadratics on this interval and negative at 1.
    upper = Fraction(11, 6)
    for a, b, c in ((17017, -265721, 59290), (3132, -239978, 59290)):
        assert 2*a*upper + b < 0 and a+b+c < 0
    assert 25743-13885*upper > 0  # F>0
    # z=-(Eg+F)/Q>0, and gz < -E/(77w), maximized at the endpoint.
    maximum = (-17017*upper**2 + 265721*upper - 59290)/77
    assert maximum == Fraction(1213099, 252) < 4814


def check_local_conditions():
    # g|A-1 follows from g|n-1 and de=1 mod g. Test the exact periods
    # 8m to account for all denominators of A and B modulo m.
    for modulus in (32, 3):
        units = [x for x in range(1, modulus) if gcd(x, modulus) == 1]
        triples = list(combinations_with_replacement(units, 3))
        residues, low_shifts = set(), set()
        for g in range(0, 8*modulus, 2):
            if evaluate(A8[1:], g) % 8:
                continue
            an, bn = evaluate(A8, g), evaluate(B4, g)
            if an % 8 or bn % 4:
                continue
            a_prod, b_sum = an//8, bn//4
            n = a_prod * (7*g-1) * (11*g-1)
            if gcd(n, modulus) != 1:
                continue
            for x, y, z in triples:
                if (x*y*z-a_prod) % modulus or (x*y+x*z+y*z-b_sum) % modulus:
                    continue
                shifts = (x-1, y-1, z-1, 7*g, 11*g)
                if any((n-1) % gcd(shift, modulus) for shift in shifts):
                    continue
                residues.add(g % (16 if modulus == 32 else 3))
                low_shifts.add(tuple(sorted(gcd(s, modulus) for s in shifts[:3])[:2]))
        assert residues == ({2} if modulus == 32 else {0})
        if modulus == 32:
            assert low_shifts == {(4, 4)}
    # Thus g=18 mod 48 and w has 2-part 16. At an odd prime in w the
    # pair bound above gives exponent one; three-way overlap was excluded.
    # For the z-first check, 7g|n-1 and 11g|n-1 require 7,11|N(g).
    for ell, wanted in ((7, {0, 4}), (11, {0, 5})):
        assert {g for g in range(ell) if evaluate(N, g) % ell == 0} == wanted


def crt(residue, modulus, next_residue, next_modulus):
    divisor = gcd(modulus, next_modulus)
    difference = next_residue - residue
    if difference % divisor:
        return None
    reduced = next_modulus // divisor
    multiplier = 0 if reduced == 1 else (difference//divisor)*pow(modulus//divisor, -1, reduced)
    period = modulus * reduced
    return (residue + modulus*multiplier) % period, period


def add_discriminant(counts, disc, witness):
    counts["tested"] += 1
    if disc >= 0:
        counts["nonnegative"] += 1
        if isqrt(disc)**2 == disc:
            raise AssertionError(f"square discriminant {disc} at {witness}")


def g_first(h, g0, counts):
    w = 16*h
    first, step = crt(g0, h, 18, 48)
    assert step == 48*h and 18 <= first < step
    for g in range(first, 4814*w, step):
        counts["g"] += 1
        aa = 17017*g-13885
        bb0 = (-265721*g+25743)*w
        cc0, cc1 = 59290*g*w*w, 77*w*g*g
        assert aa > 0
        for z in range(1, (4814*w-1)//g+1):
            disc = (bb0+z)**2 - 4*aa*(cc0+cc1*z)
            add_discriminant(counts, disc, (h, g, z))


def z_first(h, g0, counts):
    w = 16*h
    progressions = [crt(g0, h, 18, 24)]  # intentionally weaker than mod 48
    for ell, options in ((7, (0, 4)), (11, (0, 5))):
        results = [crt(r, m, v, ell) for r, m in progressions for v in options]
        progressions = [item for item in results if item is not None]
    first = min(r or m for r, m in progressions)
    assert first >= 522
    # Z=-z gives k(17017g-13885)=-z mod h. At g>=522 the interval
    # 179/100 < k/w < 46/25 has width <h in k, so one lift suffices.
    c = 17017*g0-13885
    assert gcd(c, h) == 1
    inverse = pow(c, -1, h) if h > 1 else 0
    lo, hi = 716*h//25+1, (736*h-1)//25
    assert hi-lo < h
    for z in range(1, (5000*w-1)//first+1):  # loosens 4814 to 5000
        counts["z"] += 1
        k = lo + (-z*inverse-lo) % h
        if k > hi:
            continue
        e = 17017*k*k-265721*k*w+59290*w*w
        f = k*(25743*w-13885*k)
        disc = e*e-4*77*w*z*(k*z+f)
        add_discriminant(counts, disc, (h, z, k))


def main():
    if not __debug__:
        raise SystemExit("Run without -O to enable every certificate check.")
    check_algebra()
    check_local_conditions()
    g_counts, z_counts = Counter(), Counter()
    cases = supports = 0
    for size in range(len(ROOTS)+1):
        for primes in combinations(ROOTS, size):
            supports += 1
            for roots in product(*(ROOTS[p] for p in primes)):
                cases += 1
                g0, h = 0, 1
                for ell, root in zip(primes, roots):
                    g0, h = crt(g0, h, root, ell)
                assert h == prod(primes)
                g_first(h, g0, g_counts)
                z_first(h, g0, z_counts)
    assert (supports, cases) == (16, 24)
    assert g_counts == {"g": 38517, "tested": 1803673, "nonnegative": 1803673}
    assert z_counts == {"z": 84342, "tested": 67500, "nonnegative": 67500}
    print(f"Verified {supports} supports and {cases} residue classes.")
    print(f"g-first: {g_counts['g']} g values, {g_counts['tested']} discriminants, 0 squares.")
    print(f"z-first: {z_counts['z']} z values, {z_counts['tested']} discriminants, 0 squares.")


if __name__ == "__main__":
    main()
