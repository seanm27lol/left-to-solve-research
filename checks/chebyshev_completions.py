"""Exhaust the last two prime factors for prescribed five- or seven-prime prefixes."""
from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations, product
from math import gcd, prod
from sympy import divisors, isprime, primerange


def admissible(n, p, sign):
    q = n // p
    return (q - sign) % p == 0 and (n - 1) % (p - sign) == 0 and (n - 1) % (p + sign) != 0


def signed_pairs(a, t, sx, sy, minimum):
    for x in range(minimum + 2, (2 * a) // abs(t) + 1, 2):
        denominator = t * x + sx * a
        if denominator:
            y, remainder = divmod(1 - sy * a * x, denominator)
            if not remainder and y > x and y % 2:
                yield x, y


def completions(prefix):
    a = prod(prefix)
    allowed = [tuple(s for s in (-1, 1) if gcd(a, p - s) == 1) for p in prefix]
    for signs in product(*allowed):
        t = sum(s * (a // p) for s, p in zip(signs, prefix))
        # Modulo each prefix prime, just its own summand survives.
        assert t
        for sx, sy in product((-1, 1), repeat=2):
            for x, y in signed_pairs(a, t, sx, sy, prefix[-1]):
                n = a * x * y
                if n % 12 != 1:
                    continue
                primes = (*prefix, x, y)
                signature = (*signs, sx, sy)
                if all(admissible(n, p, s) for p, s in zip(primes, signature)):
                    if isprime(x) and isprime(y):
                        yield n, primes, signature


def audit():
    # Compare the scan with a separate factorization of the bilinear equation.
    systems = pairs = 0
    for prefix in [(3,), (5,), (3, 5, 7), (7, 11, 13), (7, 11, 13, 17, 19)]:
        a = prod(prefix)
        for signs in product((-1, 1), repeat=len(prefix)):
            t = sum(s * (a // p) for s, p in zip(signs, prefix))
            for sx, sy in product((-1, 1), repeat=2):
                target = t + sx * sy * a * a
                expected = set()
                for d in divisors(abs(target)):
                    for u in (d, -d):
                        x, rx = divmod(u - sx * a, t)
                        y, ry = divmod(target // u - sy * a, t)
                        if not rx and not ry and prefix[-1] < x < y and x % 2 and y % 2:
                            expected.add((x, y))
                actual = set(signed_pairs(a, t, sx, sy, prefix[-1]))
                assert actual == expected, (prefix, signs, sx, sy)
                systems += 1
                pairs += len(actual)
    assert (5, 7) in set(signed_pairs(3, -1, 1, 1, 3))
    print(f"independent signed systems={systems} integral pairs={pairs}")

    partial, minimum_product = Fraction(), 1
    for count, p in enumerate(primerange(3, 12000), 1):
        partial += Fraction(1, p)
        minimum_product *= p
        if partial + Fraction(1, minimum_product) >= 2:
            print(f"reciprocal certificate holds through {count - 1} odd primes")
            assert count == 1412
            break
    else:
        raise AssertionError("threshold was not reached")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("factors", type=int, choices=[5, 7])
    parser.add_argument("prefix_limit", type=int)
    parser.add_argument("--audit", action="store_true", help="cross-check the pair solver and reciprocal threshold")
    args = parser.parse_args()
    if args.audit:
        audit()
    checked = hits = 0
    # The congruence argument excludes 3 and 5 for these two support sizes.
    for prefix in combinations(primerange(7, args.prefix_limit + 1), args.factors - 2):
        checked += 1
        for hit in completions(prefix):
            print("solution", hit)
            hits += 1
    print(f"factors={args.factors} prefix_limit={args.prefix_limit} prefixes={checked} hits={hits}")


if __name__ == "__main__":
    main()
