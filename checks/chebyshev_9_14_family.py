"""Exact certificate excluding the ordered Chebyshev family (k, ell, h) = (9, 14, 893).

All prime sizes are covered. Run with Python 3.8 or later. The paper gives
the integer-remainder argument that bounds the two loops at the end.
"""
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod

# Coefficients are in decreasing order.
P = (225036, -125121, 15164, 100)
T = (14177268, -9176580, 1792877, -136334, 3216)
U = (533230687536659028, -23948148964731516, -6802399560094291, 1410759090662028)
V = (-8463979167248556, -392376686459487, 142668941504950)
LARGE_ROOTS = {47: 33, 1237: 797, 6451: 3203, 88861: 79288}
OVERLAP_BOUND = 599899224946122000


def evaluate(coefficients, x):
    value = 0
    for coefficient in coefficients:
        value = value * x + coefficient
    return value


def prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


def a_num(g):
    return 112518*g**3 - 52291*g*g + 3791*g + 25


def b_num(g):
    return 20539*g*g - 7582*g - 25


def verify_identities():
    # U*P + V*T has degree at most six. Seven points certify the identity.
    assert OVERLAP_BOUND == 2**4 * 3**2 * 5**3 * prod(LARGE_ROOTS)
    assert all(prime(p) for p in LARGE_ROOTS)
    for g in range(7):
        assert evaluate(U,g) * evaluate(P,g) + evaluate(V,g) * evaluate(T,g) == OVERLAP_BOUND
        d, e = 9*g-1, 14*g-1
        A, B = Fraction(a_num(g), 25), Fraction(b_num(g), 25)
        assert evaluate(P,g) == 25*(2*A-B+1)
        assert g*evaluate(T,g) == 25*(d*e*A-1)
        assert B*d*e - A*(d+e) == 1
        for S in (0, 1):
            R = A-B+S-1
            J = A*d*e-1-126*g*g*R
            assert 25*R == 112518*g**3-72830*g*g+11373*g+25+25*S
            assert 25*J == 359879*g**3-139484*g*g+3216*g-3150*g*g*S
            for w, kappa in product(range(3), repeat=2):
                c3 = 359879*w-112518*kappa
                c2 = -139484*w+72830*kappa
                E = 112518*kappa*kappa - 1792877*kappa*w + 405216*w*w
                F = kappa*(136334*w-72830*kappa)
                q = 126*w*g*g + kappa
                assert (q*(3150*w*S-c3*g-c2) - E*g-F
                        == 3150*w*(kappa*R-w*J))

    # At these four primes a direct sweep of the field checks every common root.
    for p, root in LARGE_ROOTS.items():
        assert [g for g in range(p) if evaluate(P,g)%p==0 and evaluate(T,g)%p==0] == [root]

    # Explicit sufficient bounds in the range g >= 38. All polynomial degrees
    # are known; coefficient positivity after g -> t+38 proves positivity.
    for coefficients in [(1592,-22746,-75),(42004,-60478,-31737,-75),(4524,35774,119282,275)]:
        shifted = [0]
        for c in coefficients:
            shifted = ([38*shifted[0]] + [a+38*b for a,b in zip(shifted,shifted[1:])] + [shifted[-1]])
            shifted[0] += c
        assert all(a > 0 for a in shifted[:-1])
    hi = Fraction(11,6)
    lo = Fraction(3,2)
    assert 112518*hi**2 - 1792877*lo + 405216 < 0
    assert 136334-72830*hi > 0
    assert (112518-72830)*hi**2 - (1792877-136334)*lo + 405216 < 0
    assert 1792877-2*112518*hi > 0
    assert (-112518*hi**2+1792877*hi-405216)/126 == Fraction(7510619,378) < 20000


def truncated_valuation(value, p, level):
    # A zero residue leaves this valuation unconstrained. The minimum below
    # will always be strictly below level, making the final bound exact.
    for exponent in range(level):
        if value % p:
            return exponent
        value //= p
    return 2*level


def small_prime_parameters(p, level):
    m = p**level
    scale = gcd(25, m)
    period = m*scale
    assert gcd(25//scale, m) == 1
    inverse = pow(25//scale,-1,m)
    results = {}
    for g in range(period):
        if p == 2 and g%2:
            continue
        d, e = 9*g-1, 14*g-1
        if (d*e)%p == 0:
            continue
        if (a_num(g)%scale or b_num(g)%scale or (112518*g*g-52291*g+3791)%scale):
            continue
        A = ((a_num(g)//scale)*inverse)%m
        B = ((b_num(g)//scale)*inverse)%m
        n = A*d*e
        if A%p == 0 or (p==2 and (n-1)%4) or (p==3 and (n-1)%3):
            continue
        if (e*A+1)%gcd(m,9*g) or (d*A+1)%gcd(m,14*g):
            continue
        vpoly = truncated_valuation((2*A-B+1)%m, p, level)
        vnorm = truncated_valuation((n-1)%m, p, level)
        upper = min(vpoly, (1 if p==3 else 2)*vnorm)
        assert upper < level
        results[g] = upper
    return period, results


def compress(residues, modulus, p):
    while modulus%p==0:
        short = modulus//p
        projected = {v%short for v in residues}
        if len(projected)*p != len(residues):
            break
        modulus, residues = short, projected
    return [(v,modulus) for v in sorted(residues)]


def local_options():
    result = []
    for p, j, lower in [(2,4,2),(3,3,0),(5,2,0)]:
        period, vals = small_prime_parameters(p,j)
        if p==5:
            assert all(v%25==13 for v in vals)
        opts = []
        for exponent in range(lower,max(vals.values())+1):
            admissible = {v for v,u in vals.items() if u>=exponent}
            opts.extend((p**exponent,a,m) for a,m in compress(admissible,period,p))
        result.append(opts)
    for p, root in LARGE_ROOTS.items():
        result.append([(1,0,1),(p,root,p)])
    return result


def main():
    verify_identities()
    counts = [0,0,0]
    squares = []
    for steps in product(*local_options()):
        w = prod(f for f,_,_ in steps)
        residue, step = 0, 1
        for _,local,mod in steps:
            if mod>1:
                residue += step*((local-residue)*pow(step,-1,mod)%mod)
                step *= mod
                residue %= step
        counts[0] += 1
        first = 38+(residue-38)%step
        for g in range(first,20000*w,step):
            counts[1] += 1
            upper = (20000*w-1)//g
            counts[2] += upper
            aa = 112518*g-72830
            bb0 = (-1792877*g+136334)*w
            cc0 = 405216*g*w*w
            cc1 = 126*w*g*g
            for z in range(1,upper+1):
                disc = (bb0+z)**2-4*aa*(cc0+cc1*z)
                if disc>=0 and isqrt(disc)**2==disc:
                    squares.append((w,g,z))
    assert counts == [800,153593,2776728]
    assert squares == []
    print(f'{counts[0]} CRT progressions; {counts[1]} parameter values with overlap class; '
          f'{counts[2]} quadratic discriminants; {len(squares)} squares.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    main()
