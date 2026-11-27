"""Certify the ordered five-factor Chebyshev exclusion a-e <= 100.

Run with Python 3.8+ and no third-party packages. The finite reduction and
expected counts are derived in notes/chebyshev-prime-gaps.md. Primality is unnecessary.
"""

from math import isqrt


MAX_GAP = 100


def primes_through(limit):
    """Return all primes <= limit using the sieve of Eratosthenes."""
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = bytes(2)
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes(1 + (limit - start) // prime)
    return [value for value in range(2, limit + 1) if sieve[value]]


def positive_divisors(value, primes):
    """Factor by trial division and enumerate the products of prime powers.

    The caller supplies primes up to at least the square root of the input.
    """
    divisors = [1]
    for prime in primes:
        if prime * prime > value:
            break
        if value % prime:
            continue
        old_divisors = divisors.copy()
        power = 1
        while value % prime == 0:
            value //= prime
            power *= prime
            divisors.extend(power * old for old in old_divisors)
    if value > 1:
        divisors += [value * old for old in divisors]
    return divisors


def verify():
    if not __debug__:
        raise SystemExit("Run without -O so the certificate assertions are active.")

    # (j+2)(k+2) < (2v+2)^2 by j+k < 4v and the arithmetic mean bound.
    upper_w = MAX_GAP * (2 * MAX_GAP + 2) ** 4
    primes = primes_through(isqrt(upper_w))
    assert sorted(positive_divisors(36, primes)) == [1, 2, 3, 4, 6, 9, 12, 18, 36]

    triples = surviving_divisors = integral_products = squares = 0
    for v in range(2, MAX_GAP + 1, 2):
        for j in range(3, 4 * v, 2):
            for k in range(1, min(j, 4 * v - j), 2):
                triples += 1
                gap_sum = j + k
                gap_product = j * k
                shifted_product = (j + 2) * (k + 2)
                w = v * shifted_product**2 - gap_sum - 4
                x = v * (gap_product * (j - k)) ** 2 - gap_sum**3
                assert 0 < w < upper_w and w % 2 == 0

                # d is odd, so d+1 = 2s; d+1 divides w iff s divides w/2.
                for half_shift in positive_divisors(w // 2, primes):
                    d = 2 * half_shift - 1
                    if d < 7 or d <= j + v:
                        continue
                    denominator = gap_sum * d - gap_product
                    assert denominator > 0
                    if x % denominator:
                        continue
                    surviving_divisors += 1

                    b = 2 * d - j
                    c = 2 * d - k
                    ea, remainder = divmod(v * d * b * c + 1, denominator)
                    if remainder:
                        continue
                    integral_products += 1
                    discriminant = v**2 + 4 * ea
                    if isqrt(discriminant) ** 2 == discriminant:
                        squares += 1

    counts = triples, surviving_divisors, integral_products, squares
    assert counts == (169150, 73, 14, 0), counts
    print(f"{triples:,} gap triples; {surviving_divisors} surviving divisors; "
          f"{integral_products} integral products; {squares} square discriminants.")


if __name__ == "__main__":
    verify()
