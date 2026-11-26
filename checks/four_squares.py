from math import isqrt

# Bit n reports whether n is a sum of exactly j allowed squares.
cutoff = 24**4
limit = (1 << cutoff) - 1
squares = [i*i for i in range(isqrt(cutoff-1)+1) if i != 7]
bits = 1
for j in range(1, 5):
    next_bits = 0
    for square in squares:
        next_bits |= (bits << square) & limit
    bits = next_bits
    print(j,bits.bit_count())
assert bits == limit
