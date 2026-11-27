"""Exact certificates for unbounded component obstructions.

Run with Python 3.10+ (no third-party packages):
    python3 verify_almost_perfect_component_obstructions.py

For N=2**t, t>=21, the proved necessary conditions are
    N+1 does not divide gcd(D_p,D_r,D_s),
    N-1 does not divide gcd(D_p,D_r,D_s).
These do NOT assert nonexistence of all three-prime almost-perfect numbers.

The N+1 proof first shows N+1 divides 9*(x+1) for every base if it
divides all three D values. Write L=(N+1)/9 (possibly rational), and
x=a*L-1. The coefficients a<b<c are EVEN INTEGERS. The envelope and
its exact precision force 10<=a<=26, b<180, and
    K=9*(a*b+a*c+b*c)-a*b*c > 0, 4 divides K,
    a*b*c > K*(N-1)/2 >= 2*(N-1).
The strict-pair finite range gives a*b*c<=3806960, below
2*(2**21-1)=4194302. The two boundary pairs (10,90),(12,36) force
9*(N+1)<D_s<10*(N+1), contradicting the divisibility assumption.

This program verifies the polynomial identities, signs on unbounded
half-lines by positive coefficients after translation, and the COMPLETE
coefficient enumeration. It performs no search over t or prime sizes.
It also checks the algebra for the even-level unsplit-pair obstruction.
See the accompanying proof text for the field classification, lifting,
envelope inequalities, and logical scope.
"""

from fractions import Fraction

if not __debug__:
    raise SystemExit("Run without -O: exact certificate assertions must be enabled.")


class Poly:
    def __init__(self, terms, n):
        self.n = n
        self.terms = {e: Fraction(c) for e, c in terms.items() if c}

    def coerce(self, x):
        return x if isinstance(x, Poly) else Poly({(0,) * self.n: x}, self.n)

    def __add__(self, other):
        other = self.coerce(other)
        d = self.terms.copy()
        for e, c in other.terms.items():
            d[e] = d.get(e, 0) + c
        return Poly(d, self.n)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()}, self.n)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        d = {}
        for e, c in self.terms.items():
            for f, k in other.terms.items():
                g = tuple(x + y for x, y in zip(e, f))
                d[g] = d.get(g, 0) + c * k
        return Poly(d, self.n)

    __rmul__ = __mul__

    def __pow__(self, n):
        result = self.coerce(1)
        for _ in range(n):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def phi(x):
    return x * x + x + 1


def translate(poly, offset):
    assert poly.n == 1
    variable = Poly({(1,): 1}, 1)
    out = variable.coerce(0)
    for (exponent,), coefficient in poly.terms.items():
        out += coefficient * (variable + offset)**exponent
    return out


def positive_after(poly, offset):
    shifted = translate(poly, offset)
    assert all(coefficient > 0 for coefficient in shifted.terms.values())
    assert shifted.terms.get((0,), 0) > 0


a = Poly({(1, 0): 1}, 2)
z = Poly({(0, 1): 1}, 2)
f = a**3 + z
g = (1 + 2 * z) * a**2 - (2 + z) * a - 3 * z
assert (
    (-(2 * z + 1) * a + 3 * z + 3) * f
    + (a**2 - a + 2 * z + 2) * g
    == 3 + (2 * a - 3) * (2 * a + 1) * (z**2 + z + 1)
)

L = Poly({(1,): 1}, 1)
N = 9 * L - 1
M = 9 * L
certs = {
    (10, 90): (
        24300 * L**3 + 5500 * L**2 + 1,
        -4 * L**2 * (116032500 * L**3 + 1274875 * L**2 + 170100 * L - 1217),
        10 * L**2 * (6561000 * L**4 - 48600000 * L**3 - 230500 * L**2 - 75330 * L + 521),
    ),
    (12, 36): (
        11664 * L**3 + 144 * L**2 + 1,
        -72 * L**2 * (676512 * L**3 - 91566 * L**2 + 4536 * L - 25),
        18 * L**2 * (839808 * L**4 - 2985984 * L**3 + 407088 * L**2 - 20088 * L + 67),
    ),
}
for (aa, bb), (expected_F, expected_E9, expected_E10) in certs.items():
    p, r = aa * L - 1, bb * L - 1
    C0 = N * p**2 * r**2
    F = C0 - (N - 1) * phi(p) * phi(r)
    assert F == expected_F
    for q, expected in [(9, expected_E9), (10, expected_E10)]:
        D = q * M
        minus_Q = -D**2 + (C0 + F) * D - F * (F - 1)
        assert minus_Q == expected
        positive_after(-minus_Q if q == 9 else minus_Q, 8)
    positive_after(C0 - 10*M, 8)

T = Poly({(1,): 1}, 1)
d = Fraction(11, 6) * T + Fraction(1, 2)
p, r, s = d - 1, 2 * d - 1, 3 * d - 1
residual = (T - 1) * phi(p) * phi(r) * phi(s) - T * (p * r * s)**2 + 1
assert residual == Fraction(-1, 1296) * (11 * T + 3) * (
    26620 * T**4 + 37631 * T**3 + 10593 * T**2 + 4581 * T + 135
)

p, r, s = 2 * T - 1, 4 * T - 3, 6 * T - 5
residual = (T - 1) * phi(p) * phi(r) * phi(s) - T * (p * r * s)**2 + 1
assert residual == -2 * (T - 1) * (
    96 * T**5 - 592 * T**4 + 1152 * T**3 - 1018 * T**2 + 434 * T - 73
)
positive_after(-residual, 4)

# Exact upper-envelope polynomial in the affine coefficients.
aa = Poly({(1, 0, 0, 0): 1}, 4)
bb = Poly({(0, 1, 0, 0): 1}, 4)
cc = Poly({(0, 0, 1, 0): 1}, 4)
ll = Poly({(0, 0, 0, 1): 1}, 4)
nn = 9*ll - 1
pp, rr, ss = aa*ll-1, bb*ll-1, cc*ll-1
K = 9*(aa*bb + aa*cc + bb*cc) - aa*bb*cc
S = aa+bb+cc
assert (nn-1)*pp*rr*ss - nn*(pp-1)*(rr-1)*(ss-1) == (
    K*ll**3 - 27*S*ll**2 + (2*S+63)*ll - 6
)

# Polynomial positivity in the unsplit-component pair inequality.
x = Poly({(1, 0): 1}, 2)
gap = Poly({(0, 1): 1}, 2)
y = x + gap
Tpair = x*x + x*y + y*y + x+y+1
Rpair = 2*x*x*y*y + x*y*(x+y) + x*x+y*y
assert 2*phi(x)*phi(y)-(x+1)*phi(y)-(y+1)*phi(x) == Rpair
positive_difference = 3*Rpair - 2*x*x*Tpair
assert positive_difference == (
    gap*(2*x*x*(2*y+x) + x*(3*y+4*x)) + 2*x**3+x*x+3*y*y
)
assert len(positive_difference.terms) == 8
assert all(value > 0 for value in positive_difference.terms.values())

maximum = (0, None)
count = 0
max_c = 0
prefixes = 0
admissible_prefixes = 0
strict_pair_max_ab = 0
boundary_pairs = []
for aa in range(10, 27, 2):
    for bb in range(aa + 2, 180, 2):
        prefixes += 1
        delta = aa * bb - 9 * aa - 9 * bb
        if delta < 0:
            strict_pair_max_ab = max(strict_pair_max_ab, aa*bb)
            continue
        if delta == 0:
            boundary_pairs.append((aa, bb))
            continue
        # Strict cc < 9*aa*bb/delta, and cc is even.
        max_cc = (9 * aa * bb - 1) // delta
        max_cc -= max_cc % 2
        if max_cc > bb:
            admissible_prefixes += 1
        for cc in range(bb + 2, max_cc + 1, 2):
            K = 9 * (aa * bb + aa * cc + bb * cc) - aa * bb * cc
            assert K > 0 and K % 4 == 0
            count += 1
            max_c = max(max_c, cc)
            value = aa * bb * cc
            if value > maximum[0]:
                maximum = (value, (aa, bb, cc))

assert maximum == (3806960, (10, 92, 4138))
assert prefixes == 720
assert admissible_prefixes == 100
assert count == 10074
assert strict_pair_max_ab == 880 < 2**21-1
assert boundary_pairs == [(10, 90), (12, 36)]
assert max_c == 4138
assert maximum[0] < 2 * (2**21 - 1)
print("PASS: Bezout identity and boundary-pair identities and signs for all L>=8")
print("PASS: envelope identity, common-shift identity, and N-1 exclusion for all N>=4")
print("PASS: unsplit-pair identity and its eight positive coefficients")
print("PASS: complete coefficient enumeration", {
    "prefixes": prefixes, "admissible_prefixes": admissible_prefixes,
    "triples": count, "maximum_abc": maximum, "max_c": max_c,
    "strict_pair_max_ab": strict_pair_max_ab, "boundary_pairs": boundary_pairs,
})
print("ALL CHECKS PASSED. The unrestricted almost-perfect case is not settled.")
