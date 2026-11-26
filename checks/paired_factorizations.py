"""Compare prime-residue classification with all products of pairs with specified last digits."""
from collections import Counter
from math import isqrt
from sympy import factorint


def direct_products(limit, digit):
    products = set()
    for a in range(digit, isqrt(limit) + 1, 10):
        for b in range(a, limit // a + 1, 10):
            products.add(a * b)
    return products


def exceptional(u):
    counts = Counter()
    for p, multiplicity in factorint(u).items():
        counts[p % 5] += multiplicity
    if not counts[2] and not counts[3]:
        return "split"
    if not counts[4] and sorted((counts[2], counts[3])) == [0, 2]:
        return "two"
    return "qualified"


if __name__ == "__main__":
    limit = 200_000
    for digits, start, step, scale in [((4, 6), 16, 20, 4), ((3, 7), 9, 10, 1)]:
        observed = direct_products(limit, digits[0]) & direct_products(limit, digits[1])
        groups = Counter()
        predicted = set()
        for n in range(start, limit + 1, step):
            label = exceptional(n // scale)
            groups[label] += 1
            if label == "qualified":
                predicted.add(n)
        assert predicted == observed
        print(f"{digits}, X={limit}, qualified={len(predicted)}, split exceptions={groups['split']}, "
              f"two-prime-factor exceptions={groups['two']}")
