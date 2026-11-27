#!/usr/bin/env python3
"""Exact checks for top-family remainders. Standard library only."""
from fractions import Fraction
from math import isqrt

if not __debug__:
    raise SystemExit("Run without -O: the verifier uses assertions.")


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a): c[i] += x
    for i, x in enumerate(b): c[i] += x
    return c


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    return c


def evaluate(a, x):
    y = 0
    for c in reversed(a): y = y*x+c
    return y


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


xn = [9, -1167, -9409, 1610]
zn = [9, -2334, 391]
p = add(mul(mul([1,7], [1,10]), xn), [-9])
assert p == [0, -1014, -28618, -240033, -631260, 112700]
assert evaluate(p, Fraction(-2,7)) == Fraction(-298148,343)
assert evaluate(p, Fraction(-1,5)) == Fraction(-8467,125)

assert prime(19) and prime(3923) and prime(8467)
assert 298148 == 4*19*3923
divs = sorted({2**a*19**b*3923**c for a in range(3)
               for b in range(2) for c in range(2)})
assert all(298148 % x == 0 for x in divs)
possible_g = [(x-2)//7 for x in divs if x > 2 and (x-2)%14 == 0]
assert possible_g == [21296]
assert evaluate(zn, 21296) % 9 == 1
assert all((x-1)%5 for x in [8467])

# Check that the square-residue reformulation is exact at odd prime powers.
# These finite sanity checks are not substitutes for the modular proof.
for mod in (3,9,27,5,25,7,49,11,121,13,169,17,289):
    squares = {x*x % mod for x in range(mod)}
    assert ((3 % mod in squares) == (mod in (3,11,121,13,169)))

for mod, expected in [(3,[1]), (5,[4]), (7,[1]), (9,[]), (25,[])]:
    squares = {x*x % mod for x in range(mod)}
    possible = [v for v in range(mod) if v % 3 != 0] if mod in (3,9) else (
        [v for v in range(mod) if v % 5 != 0] if mod in (5,25) else
        [v for v in range(1,mod)])
    actual = [v for v in possible if (1-4*v)%mod in squares
              and v*(v-4)%mod in squares]
    assert actual == expected, (mod, actual, expected)

print("PASS: exact polynomial, factorization, complete exceptional divisor list,")
print("      and the two top forbidden tests for every admissible positive even g.")
print("This does not assert existence or nonexistence of the three lower primes.")
