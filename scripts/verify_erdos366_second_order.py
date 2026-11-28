#!/usr/bin/env python3
"""Exact audits for second-order support congruences in Erdős 366.

The bounded loops verify the elementary arithmetic and threshold comparisons;
the accompanying note gives the cutoff-free binomial proof.
"""

from math import comb


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 1
    return True


def quadratic(b: int, c: int, u: int, v: int) -> int:
    return comb(b, 2) * u * u + b * c * u * v + comb(c, 2) * v * v


def audit_binomial_identity(step: int, u: int, v: int, b: int, c: int) -> None:
    """Check the second-order identity after division by ``step``."""
    product = (1 + step * u) ** b * (1 + step * v) ** c
    lhs = (product - 1) // step
    rhs = b * u + c * v + step * quadratic(b, c, u, v)
    assert (lhs - rhs) % (step * step) == 0


def main() -> None:
    # Audit the binomial identity at the 2A step used by the minus family.
    for A in range(3, 30, 2):
        for u in range(1, 6):
            for v in range(1, 6):
                for b in range(3, 8):
                    for c in range(3, 8):
                        audit_binomial_identity(2 * A, u, v, b, c)

    # Audit the same identity at the 4A step used by the plus family.
    for s in range(2, 8):
        A = 2**s
        for u in range(1, 5):
            for v in range(1, 5):
                for b in range(3, 7):
                    for c in range(3, 7):
                        audit_binomial_identity(4 * A, u, v, b, c)

    # Distinct primes in one residue class have multipliers at least 1 and 2.
    for A in range(3, 43):
        if is_prime(A):
            assert 2**A - 1 < (2 * A + 1) ** 3 * (4 * A + 1) ** 3
    assert 2**43 - 1 >= (2 * 43 + 1) ** 3 * (4 * 43 + 1) ** 3

    for s in (4, 5):
        A = 2**s
        assert 2**A + 1 < (4 * A + 1) ** 3 * (8 * A + 1) ** 3
    A = 64
    assert 2**A + 1 >= (4 * A + 1) ** 3 * (8 * A + 1) ** 3

    # The plus-family second-order right side reduces to zero modulo 4A.
    for s in range(4, 12):
        A = 2**s
        assert 2 ** (A - s - 2) % (4 * A) == 0

    print("VERIFIED: both second-order binomial congruences")
    print("VERIFIED: independent exponent bounds A>=43 and A>=64")


if __name__ == "__main__":
    main()
