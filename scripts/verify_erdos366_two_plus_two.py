#!/usr/bin/env python3
"""Exact elementary checks for the Erdős 366 two-plus-two reduction.

The cutoff-free proof uses Bang--Zsigmondy and Mihăilescu.  This script only
audits the divisor-count classifications and the elementary congruences; its
bounded loops are not substitutes for those theorems.
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
    answer = 1
    for exponent in factor(n).values():
        answer *= exponent + 1
    return answer


def prime(n):
    return n >= 2 and len(factor(n)) == 1 and next(iter(factor(n).values())) == 1


def plus_shape(a):
    """a=2^t, 2^t*s with s odd prime, or exceptional 9."""
    if a == 9:
        return True
    while a % 2 == 0:
        a //= 2
    return a == 1 or prime(a)


def minus_shape(a):
    exponents = sorted(factor(a).values())
    return a == 6 or len(exponents) == 1 and exponents[0] in (1, 2)


def cyclotomic_odd_plus(y, ell):
    return (y**ell + 1) // (y + 1)


def cyclotomic_odd_minus(y, ell):
    return (y**ell - 1) // (y - 1)


def main():
    for a in range(3, 1_000_001):
        odd = a
        t = 0
        while odd % 2 == 0:
            odd //= 2
            t += 1
        plus_classes = tau(odd) - int(t == 0 and odd % 3 == 0)
        if plus_classes <= 2:
            assert plus_shape(a)

        minus_classes = tau(a) - 1 - int(a % 6 == 0)
        if minus_classes <= 2:
            assert minus_shape(a)

    for a in range(3, 12):
        modulus = 2**a
        for ell in (3, 5, 7):
            y_upper = modulus + 1
            y_lower = modulus - 1
            assert cyclotomic_odd_minus(y_upper, ell) % modulus == ell % modulus
            assert cyclotomic_odd_plus(y_lower, ell) % modulus == ell % modulus
            assert gcd(y_upper - 1, cyclotomic_odd_minus(y_upper, ell)) == gcd(modulus, ell)
            assert gcd(y_lower + 1, cyclotomic_odd_plus(y_lower, ell)) == gcd(modulus, ell)

    print("VERIFIED: both divisor-count shape classifications")
    print("VERIFIED: the cyclotomic congruences in both orientations")


if __name__ == "__main__":
    main()
