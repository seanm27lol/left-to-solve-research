"""Exclude the Chebyshev top-index (7,10,23) family using the lower shifts.

Run with Python 3.8+ (standard library). Polynomial coefficients are ascending.
"""
from itertools import combinations, product
from math import gcd, isqrt, prod

P = (4, -1556, -18427, 9660)
F = (-338, -28618, -720099, -5681340, 3042900)
U = (19538197375049, 466269573740589, 5354603308283040, -2769237917415900)
V = (-792176604159, -17354576221277, 8791231483860)
ROOTS = ((23, -4), (257, -21), (29259726079, -1421483446))
GAMMA_RESIDUES = (48, 138, 426, 516)
BOUND = 25000


def evaluate(coeffs, t):
    value = 0
    for coeff in reversed(coeffs):
        value = value * t + coeff
    return value


def monic_gcd(f, g, p):
    def trim(poly):
        while poly and poly[-1] == 0:
            poly.pop()
        return poly

    a = trim([c % p for c in f])
    b = trim([c % p for c in g])
    while b:
        inverse = pow(b[-1], -1, p)
        while len(a) >= len(b):
            offset = len(a) - len(b)
            factor = a[-1] * inverse
            for i, coeff in enumerate(b):
                a[offset + i] = (a[offset + i] - factor * coeff) % p
            trim(a)
        a, b = b, a
    inverse = pow(a[-1], -1, p)
    return tuple(c * inverse % p for c in a)


def check_identities():
    primes = [p for p, _ in ROOTS]
    for p, root in ROOTS:
        assert all(p % d != 0 for d in range(2, isqrt(p) + 1))
        assert monic_gcd(P, F, p) == ((-root) % p, 1)

    # The two sides are polynomials of degree at most six in t.
    for t in range(7):
        g = 3 * t
        X = 4830 * t**3 - 9409 * t**2 - 389 * t + 1
        Z = 391 * t**2 - 778 * t + 1
        n = (7 * g + 1) * (10 * g + 1) * X
        assert evaluate(P, t) == 2 * X + Z + 1
        assert evaluate(F, t) * t == n - 1
        assert evaluate(U,t)*evaluate(P,t) + evaluate(V,t)*evaluate(F,t) == 2*prod(primes)

    # Check the cleared remainder identity as a polynomial in (g, kappa, w, S).
    # The unexpanded J9 has degree at most five in g. The grid covers these degrees.
    for g, kappa, w, S in product(range(7), range(3), range(3), range(2)):
        X9 = 1610*g**3 - 9409*g**2 - 1167*g + 9
        Z9 = 391*g**2 - 2334*g + 9
        R9 = X9 + Z9 + 9*(S-1)
        J9 = (7*g+1)*(10*g+1)*X9 - 9 - 70*g**2*R9
        assert R9 == 1610*g**3 - 9018*g**2 - 3501*g + 9*S + 9
        assert J9 == -630*S*g**2 + 5037*g**3 - 29248*g**2 - 1014*g
        z = 630*w*S + (1610*kappa-5037*w)*g - 9018*kappa + 29248*w
        E = 1610*kappa*kappa + 240033*kappa*w - 70980*w*w
        F0 = -9018*kappa*kappa + 28618*kappa*w
        assert (70*w*g*g+kappa)*z-E*g-F0 == 70*w*(kappa*R9-w*J9)


def progressions():
    for size in range(4):
        for selected in combinations(ROOTS, size):
            H = prod(p for p, _ in selected)
            for initial, w2 in product(GAMMA_RESIDUES, (4, 8, 16)):
                g, step = initial, 630
                for p, root in selected:
                    assert gcd(step, p) == 1
                    g += step * ((3*root-g) * pow(step, -1, p) % p)
                    step *= p
                assert 0 <= g < step
                if g < 254:
                    g += step
                yield w2*H, g, step


def check_discriminants():
    class_count = gamma_count = checks = 0
    for w, first, step in progressions():
        class_count += 1
        for g in range(first, BOUND*w, step):
            gamma_count += 1
            A = 1610*g - 9018
            B0 = (240033*g + 28618)*w
            C0 = -70980*g*w*w
            Cz = -70*w*g*g
            for z in range(1, (BOUND*w-1)//g+1):
                checks += 1
                delta = (B0-z)**2 - 4*A*(C0+Cz*z)
                assert delta < 0 or isqrt(delta)**2 != delta, (w, g, z)
    assert (class_count, gamma_count, checks) == (96, 35540, 308878)
    print(f"{class_count} classes, {gamma_count} parameters with multiplicity, "
          f"{checks} discriminants, zero squares.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O to enable the certificate assertions.")
    check_identities()
    check_discriminants()
