#!/usr/bin/env python3
"""Exact audits for the power-of-two singleton reduction.

The theorem itself uses Bang--Zsigmondy, Mihailescu, Bennett--Levin, and LTE.
This standard-library script checks the elementary divisor-count reduction,
all exceptional factorizations used in the proof, and the cyclotomic overlap
which leaves the Fermat-prime-square branch.  The bounded enumeration is an
audit, not a substitute for the cutoff-free proof.
"""

from math import gcd


def factor(n):
    answer = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            answer[p] = answer.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        answer[n] = answer.get(n, 0) + 1
    return answer


def tau(n):
    result = 1
    for exponent in factor(n).values():
        result *= exponent + 1
    return result


def minus_shape(n):
    fac = factor(n)
    exponents = sorted(fac.values())
    if len(fac) == 1:
        return "p" if exponents == [1] else (
            "p2" if exponents == [2] else "p3" if exponents == [3] else None
        )
    return "pq" if exponents == [1, 1] else None


def valuation(n, p):
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer


def main():
    # Exact divisor-count implication over a range much larger than the
    # exceptional values.  The note supplies the general elementary proof.
    for a in range(2, 1_000_001):
        primitive_classes = tau(a) - 1 - int(a % 6 == 0)
        if primitive_classes <= 3:
            assert a == 6 or minus_shape(a) in {"p", "p2", "p3", "pq"}

    assert factor(2**6 - 1) == {3: 2, 7: 1}
    assert factor(2**9 + 1) == {3: 3, 19: 1}
    assert valuation(2**27 + 1, 19) == 1

    # The first residual Fermat-prime-square overlap: t=1, x=4, p=5.
    x, p = 4, 5
    f0 = x + 1
    f1 = (x**p + 1) // (x + 1)
    f2 = (x ** (p * p) + 1) // (x**p + 1)
    assert f0 == 5
    assert factor(f1) == {5: 1, 41: 1}
    assert valuation(f0, p) == valuation(f1, p) == valuation(f2, p) == 1
    assert valuation(x ** (p * p) + 1, p) == 3

    # Check the gcd formulas for the first several symbolic parameter values.
    for t in range(1, 7):
        x = 2 ** (2**t)
        for p in (3, 5, 7, 11, 13):
            f1 = (x**p + 1) // (x + 1)
            assert gcd(x + 1, f1) == gcd(x + 1, p)

    print("VERIFIED: divisor classes and exceptional factorizations")
    print("VERIFIED: the Fermat-prime-square overlap has total valuation three")


if __name__ == "__main__":
    main()

