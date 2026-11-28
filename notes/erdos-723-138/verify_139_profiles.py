"""Exact deficit profile and parity checks for the 139-block extension theorem."""
from fractions import Fraction
from itertools import product

T = (2, 3, 4, 5, 6)
EXPECTED = [
    (108, 0, 0, 0, 3),
    (102, 0, 6, 0, 1),
    (99, 0, 9, 0, 0),
    (86, 19, 0, 1, 0),
    (81, 24, 0, 0, 0),
]


def distributions():
    for a, b, c, d in product(range(25), range(10), range(5), range(4)):
        if 3*a + 8*b + 15*c + 24*d != 72:
            continue
        remaining = 234-3*a-4*b-5*c-6*d
        assert remaining >= 0 and remaining % 2 == 0
        n = (remaining//2, a, b, c, d)
        assert sum(n) <= 157
        yield n


def neighborhoods(n, a):
    available = tuple(count-(t == a) for t, count in zip(T, n))
    result = []
    for heavy in product(*(range(count+1) for count in available[1:])):
        light = 12*a-sum(heavy)
        if light < 0 or light > available[0]:
            continue
        gaps = (light, *heavy)
        if sum((t-2)*j for t, j in zip(T, gaps)) != a*(6-a):
            continue
        if a % 2 and sum(available[i]-gaps[i] for i in (1, 3)) < 13-a:
            continue
        result.append(gaps)
    return result


def main():
    initial = list(distributions())
    assert len(initial) == 23
    surviving = []
    table = []
    for n in initial:
        m = n[0]
        opt = {t: neighborhoods(n, t) for t, count in zip(T, n) if count}
        if any(not v for v in opt.values()):
            continue
        if n[-1] >= 2 and m < 108:
            continue
        low_h = sum(count*min(g[0] for g in opt[t]) for t, count in zip(T[1:], n[1:]) if count)
        hi_h = sum(count*max(g[0] for g in opt[t]) for t, count in zip(T[1:], n[1:]) if count)
        low_l = m * min(sum(g[1:]) for g in opt[2])
        hi_l = m * max(sum(g[1:]) for g in opt[2])
        lo, hi = max(low_h, low_l), min(hi_h, hi_l)
        if lo > hi:
            continue
        ratio = Fraction(4*m*m, 26*m-lo)
        table.append((n, lo, hi, ratio))
        if ratio <= 18:
            assert ratio > 17
            surviving.append(n)
    assert len(table) == 9
    assert surviving == EXPECTED
    for n, lo, hi, ratio in table:
        print(n, (lo, hi), ratio, "survives" if ratio <= 18 else "excluded")
    for n in range(1, 44):
        for b in range(n+1):
            # Multiply Cauchy's connectivity inequality by 19.
            assert 19*4*n*(86-n) > 19*(29*(8*n-3*b)+b*(55-b))-(8*n-3*b)**2
    for i in range(1, 20):
        j = 19-i
        if i*j >= 86:
            assert min(i*(j-j%2), j*(i-i%2)) < 86
    print("Verified 23 initial distributions, nine incidence bounds and five survivors.")


if __name__ == "__main__":
    main()
