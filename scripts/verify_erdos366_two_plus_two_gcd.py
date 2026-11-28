#!/usr/bin/env python3
"""Finite audit of the divisor-count classifications used in the proof.

The mathematical cutoff-free step is Bang--Zsigmondy; this program checks
the subsequent elementary shape deductions over a large exact range.
"""


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def tau_from_factorization(fac: dict[int, int]) -> int:
    value = 1
    for exponent in fac.values():
        value *= exponent + 1
    return value


def is_prime_or_prime_square_shape(fac: dict[int, int]) -> bool:
    return not fac or (len(fac) == 1 and next(iter(fac.values())) in (1, 2))


def odd_part(n: int) -> int:
    while n % 2 == 0:
        n //= 2
    return n


def main() -> None:
    limit = 1_000_000
    for g in range(1, limit + 1):
        fac = factor(g)
        if tau_from_factorization(fac) - 1 <= 2:
            assert is_prime_or_prime_square_shape(fac)

        ufac = factor(odd_part(g))
        if tau_from_factorization(ufac) <= 2:
            assert not ufac or (
                len(ufac) == 1 and next(iter(ufac.values())) == 1
            )

    print("VERIFIED: minus-orientation divisor-count classification")
    print("VERIFIED: plus-orientation odd-part classification")
    print(f"AUDITED: 1 <= g <= {limit}")


if __name__ == "__main__":
    main()
