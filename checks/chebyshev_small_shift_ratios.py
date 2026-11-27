"""Verify the negative-shift ratio reduction, using exact arithmetic throughout."""

from fractions import Fraction
from itertools import product
from math import gcd, isqrt

SMALL_EIGHT = 1000
SMALL_NINE = 2000


def prime(p):
    return p >= 2 and all(p % v for v in range(2, isqrt(p) + 1))


def small_pairs(ratios, cutoff):
    prime_table = [prime(p) for p in range(2 * cutoff + 1)]
    # Counts are prime pairs, products in the CRT class and eligible factorizations.
    counts = [0, 0, 0]
    for k in ratios:
        for ell in range(k + 1, 2 * k):
            if gcd(k, ell) != 1:
                continue
            for g in range(2, (cutoff + 1) // k + 1, 2):
                d, e = k*g - 1, ell*g - 1
                if not (7 <= d < e < 2*d and prime_table[d] and prime_table[e]):
                    continue
                counts[0] += 1
                m, v = d * (d+1), e * (e+1)
                if gcd(e, m) != 1 or gcd(d, v) != 1:
                    continue
                x, y = -pow(e, -1, m), -pow(d, -1, v)
                h = gcd(m, v)
                if (y-x) % h:
                    continue
                # Solve the pair of congruences, retaining the full positive period.
                period = m * (v // h)
                first = (x + m * ((y-x) // h) * pow(m // h, -1, v // h)) % period
                A = first + ((e**3-first) // period + 1) * period
                while A < 4 * d**2 * e:
                    counts[1] += 1
                    for a in range(e+2, 2*d, 2):
                        if not prime_table[a] or A % a:
                            continue
                        bc = A // a
                        for b in range(a+2, isqrt(bc)+1, 2):
                            if b >= 2*d or not prime_table[b] or bc % b:
                                continue
                            c = bc // b
                            if b < c < 2*d and prime_table[c]:
                                counts[2] += 1
                    A += period
    assert counts[2] == 0
    return counts


def large_ratios(k, cutoff):
    survives = set()
    # This rational upper bound on 1/g holds whenever d exceeds the cutoff.
    x = Fraction(k, cutoff)
    for ell in range(k+1, 2*k):
        if gcd(k, ell) != 1:
            continue
        r = ell-k
        lower = 27*r**2*(k-x)**2*(ell-x)**2 / (k+ell)**3
        upper = 4*k*r**2 + 2*k**2*ell**2*x / ((k-x)*(ell-x))
        # Every condition in this loop is periodic in g modulo 2*k*ell*r^2.
        for g in range(0, 2*k*ell*r*r, 2):
            d, e = k*g-1, ell*g-1
            if gcd(d, ell*r) != 1 or gcd(e, k*r) != 1:
                continue
            for h in range(lower.numerator // lower.denominator+1,
                           (upper.numerator-1) // upper.denominator+1):
                w = k*ell*(k+ell) - 2*k*k*ell*ell*g + h*d*e
                if w % r**2 == (h*e*e-ell**3) % k == (h*d*d-k**3) % ell == 0:
                    survives.add((ell,h))
    return sorted(survives)


def eighth_ratio():
    k, ell, h = 8, 11, 283
    rows = []
    for g in range(81):
        d,e = k*g-1, ell*g-1
        w = k*ell*(k+ell) - 2*k*k*ell*ell*g + h*d*e
        t = (k+ell)*h*g*g - 2*g*(h+k*ell*(k+ell))
        if w % 9 or t % 9 or (d*e) % 3 == 0:
            continue
        A,B = 1+g*(w//9), t//9-1
        if A*d*e % 3 == 1:
            rows.append((g,A%9,B%9))
    assert rows == [(1,1,0),(28,7,3),(55,4,6)]
    for _, A, B in rows:
        matches = [s for s in product((1,2), repeat=3) if s[0]*s[1]*s[2] % 3 == A%3
                   and (s[0]*s[1]+s[0]*s[2]+s[1]*s[2])%3 == B%3]
        assert matches == [(1,1,1)]
        assert (B-2*A-1)%9 != 0
    return rows


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    small_eight = small_pairs(range(2, 9), SMALL_EIGHT)
    small_nine = small_pairs([9], SMALL_NINE)
    assert small_eight == [329, 106, 0]
    assert small_nine == [93, 11, 0]
    assert small_nine == [93, 11, 0]
    print('Small range [negative pairs, possible products, eligible factorizations]')
    print('k = 2 to 8, d <= 1000:', small_eight)
    print('k = 9, d <= 2000:', small_nine)
    for k in range(2, 10):
        got = large_ratios(k, SMALL_NINE if k == 9 else SMALL_EIGHT)
        expected = {7: [(11,442)], 8: [(11,283)], 9: [(13,562),(14,893)]}
        assert got == expected.get(k, [])
        print('k =', k, 'surviving (ell, h) =', got)
    print('k = 8: all lifts fail modulo 9:', eighth_ratio())
