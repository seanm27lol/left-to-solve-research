"""Exact leading-digit counts for A383307 and block checks for A309417."""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from math import factorial, prod


def check(n):
    free_unique = leading_nine = excess = qualifying = free_total = 0
    for word in combinations_with_replacement(range(10), n):
        counts = Counter(word)
        multiplicity = factorial(n) // prod(factorial(v) for v in counts.values())
        free_total += multiplicity
        largest = max(counts.values())
        winners = [j for j, v in counts.items() if v == largest]
        if len(winners) != 1:
            continue
        free_unique += multiplicity
        excess += (10 * largest - n) * multiplicity
        with_nonzero_lead, remainder = divmod(multiplicity * (n - counts[0]), n)
        assert remainder == 0
        if winners[0] == 9:
            leading_nine += with_nonzero_lead
        if winners[0] == max(word) - min(word):
            qualifying += with_nonzero_lead
    assert free_total == 10**n
    lhs = Fraction(leading_nine, 9 * 10**(n - 1))
    rhs = Fraction(free_unique, 10 * free_total) + Fraction(excess, 810 * n * free_total)
    assert lhs == rhs
    if n >= 2:
        observed = Fraction(qualifying, 9 * 10**(n - 1))
        missing_bound = Fraction(17, 9) * Fraction(9, 10)**(n - 1)
        assert abs(observed - lhs) <= missing_bound
    return qualifying


def check_subtraction_blocks(n, b):
    width = 10**b
    assert width > 9*n
    x = 10**n - 1
    block_sums = [0] * (10**n // width)
    visits = [0] * len(block_sums)
    while x:
        length = sum(map(int, str(x)))
        block = x // width
        block_sums[block] += length
        visits[block] += 1
        x -= length
    assert sum(block_sums) == 10**n - 1
    assert all(used > 0 and abs(total - width) <= 9*n for used, total in zip(visits, block_sums))
    return len(block_sums)


if __name__ == "__main__":
    counts = [check(n) for n in range(1, 11)]
    print("Leading-digit identity verified exactly for lengths 1 through 10.")
    print("A383307, lengths 2 through 10:", counts[1:])
    blocks = sum(check_subtraction_blocks(n, 2) for n in range(3, 7))
    print(f"A309417 telescoping and boundary errors checked on {blocks} decimal blocks.")
