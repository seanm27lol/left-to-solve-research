#!/usr/bin/env python3
"""Exact audits for the prime-exponent Mersenne congruence sieve."""


def factor(n: int) -> dict[int, int]:
    answer: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            answer[d] = answer.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        answer[n] = answer.get(n, 0) + 1
    return answer


def check(p: int) -> dict[int, int]:
    factors = factor(2**p - 1)
    assert all((q - 1) % (2 * p) == 0 for q in factors)
    data = [(q, e, (q - 1) // (2 * p)) for q, e in factors.items()]

    s1 = sum(e * k for _, e, k in data)
    s2 = sum(e * (e - 1) // 2 * k * k for _, e, k in data)
    for i in range(len(data)):
        for j in range(i + 1, len(data)):
            _, ei, ki = data[i]
            _, ej, kj = data[j]
            s2 += ei * ej * ki * kj

    quotient = (2 ** (p - 1) - 1) // p
    assert (quotient - s1 - 2 * p * s2) % (4 * p * p) == 0

    if p >= 5:
        odd_product = 1
        for q, e, _ in data:
            assert q % 8 in (1, 7)
            if e % 2:
                odd_product *= q
        assert odd_product % 16 == 15
    return factors


def main() -> None:
    # p=29 has exactly three support primes, so it exercises the target shape
    # even though its exponents are one rather than cubefull.
    assert check(29) == {233: 1, 1103: 1, 2089: 1}
    for p in (5, 7, 11, 13, 17, 19, 23, 31):
        check(p)
    print("VERIFIED: second-order Fermat-quotient congruence")
    print("VERIFIED: quadratic-residue and mod-16 restrictions")


if __name__ == "__main__":
    main()
