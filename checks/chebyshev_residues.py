"""Exhaust the signed prime residue patterns modulo 48 for five or seven factors."""

from itertools import combinations_with_replacement
from math import gcd, prod


def possible_patterns(factors):
    modulus = 48
    units = [r for r in range(modulus) if gcd(r, modulus) == 1]
    sign = {5: 1, 7: -1}[factors]
    patterns = set()
    for residues in combinations_with_replacement(units, factors):
        product = prod(residues)
        n = sign * product
        if n % 12 != 1:
            continue
        # Each term omits one occurrence, including repeated residue classes.
        symmetric_sum = sum(product // u for u in residues)
        if (symmetric_sum - sign) % modulus:
            continue
        if any((n - 1) % gcd(modulus, u - 1) for u in residues):
            continue
        b3 = sum(u % 3 == 2 for u in residues)
        b4 = sum(u % 4 == 3 for u in residues)
        patterns.add((b3, b4, n % modulus))
    return sorted(patterns)


if __name__ == "__main__":
    for factors in (5, 7):
        print(factors, possible_patterns(factors))
