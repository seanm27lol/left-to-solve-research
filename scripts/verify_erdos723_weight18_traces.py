#!/usr/bin/env python3
"""Exact trace reduction for a weight-18 dependency in an order-12 plane.

The verifier uses only Python integers and the standard library.  It
enumerates all 467440 candidate traces on the 105 geometrically determined
points and checks the complete GF(2) relaxation of the exact-cover system.
The binary check is an audit and a negative result: parity does not exclude
any of the five values of t.
"""

from collections import Counter
from itertools import combinations, permutations


def affine_lines():
    points = tuple((x, y) for x in range(3) for y in range(3))
    lines = []
    for slope in range(3):
        for intercept in range(3):
            lines.append(tuple(
                index for index, (x, y) in enumerate(points)
                if (y - slope * x) % 3 == intercept
            ))
    for intercept in range(3):
        lines.append(tuple(
            index for index, (x, _) in enumerate(points) if x == intercept
        ))
    assert len(lines) == 12
    assert all(len(line) == 3 for line in lines)
    assert all(sum(set(left).isdisjoint(right) for right in lines) == 2
               for left in lines)
    return tuple(lines)


LINES = affine_lines()
P_POINTS = tuple(range(12))
N_POINTS = tuple(range(12, 24))


def grid(row, column):
    return 24 + 9 * row + column


def eligible_pairs():
    pairs = []
    for left, right in combinations(P_POINTS, 2):
        if left // 3 == right // 3:
            pairs.append((left, right))
    for left, right in combinations(range(12), 2):
        if left // 3 == right // 3:
            pairs.append((12 + left, 12 + right))
    assert len(pairs) == 24
    for positive in P_POINTS:
        for negative in N_POINTS:
            pairs.append((positive, negative))
    assert len(pairs) == 24 + 144
    for positive in P_POINTS:
        used_rows = set(LINES[positive])
        for row in range(9):
            if row not in used_rows:
                for column in range(9):
                    pairs.append((positive, grid(row, column)))
    assert len(pairs) == 24 + 144 + 648
    for negative_index in range(12):
        used_columns = set(LINES[negative_index])
        negative = 12 + negative_index
        for column in range(9):
            if column not in used_columns:
                for row in range(9):
                    pairs.append((negative, grid(row, column)))
    assert len(pairs) == 24 + 144 + 648 + 648
    for left, right in combinations(range(81), 2):
        left_row, left_column = divmod(left, 9)
        right_row, right_column = divmod(right, 9)
        if left_row != right_row and left_column != right_column:
            pairs.append((24 + left, 24 + right))
    assert len(pairs) == 24 + 144 + 648 + 648 + 2592
    normalized = tuple(dict.fromkeys(tuple(sorted(pair)) for pair in pairs))
    assert len(normalized) == 4056
    return normalized


ELIGIBLE = eligible_pairs()
PAIR_INDEX = {pair: index for index, pair in enumerate(ELIGIBLE)}
PAIR_COUNT = len(ELIGIBLE)
POINT_OFFSET = PAIR_COUNT
TYPE_OFFSET = POINT_OFFSET + 105


def column(points, trace_type):
    points = tuple(sorted(points))
    assert len(points) == 9 - trace_type
    assert len(set(points)) == len(points)
    vector = 1 << (TYPE_OFFSET + trace_type)
    for point in points:
        vector |= 1 << (POINT_OFFSET + point)
    for pair in combinations(points, 2):
        vector |= 1 << PAIR_INDEX[pair]
    return vector


def candidates():
    # Type 3: one full parallel class on each side and no grid points.
    for positive_class in range(4):
        positive = range(3 * positive_class, 3 * positive_class + 3)
        for negative_class in range(4):
            negative = range(12 + 3 * negative_class,
                             12 + 3 * negative_class + 3)
            yield 3, column((*positive, *negative), 3)

    # Type 2: two points from a parallel class on each side, plus a matching
    # on the three unused positive and negative selected lines.
    for positive_class in range(4):
        for positive in combinations(
                range(3 * positive_class, 3 * positive_class + 3), 2):
            used_rows = set(LINES[positive[0]]) | set(LINES[positive[1]])
            rows = [row for row in range(9) if row not in used_rows]
            assert len(rows) == 3
            for negative_class in range(4):
                for negative0 in combinations(
                        range(3 * negative_class, 3 * negative_class + 3), 2):
                    used_columns = (
                        set(LINES[negative0[0]]) | set(LINES[negative0[1]])
                    )
                    columns = [c for c in range(9) if c not in used_columns]
                    assert len(columns) == 3
                    negative = tuple(12 + index for index in negative0)
                    for matching in permutations(columns):
                        points = (*positive, *negative,
                                  *(grid(r, c) for r, c in zip(rows, matching)))
                        yield 2, column(points, 2)

    # Type 1: one affine triple on each side and a matching on the six
    # remaining selected lines.
    for positive in P_POINTS:
        rows = [row for row in range(9) if row not in LINES[positive]]
        for negative_index in range(12):
            columns = [c for c in range(9)
                       if c not in LINES[negative_index]]
            for matching in permutations(columns):
                points = (positive, 12 + negative_index,
                          *(grid(r, c) for r, c in zip(rows, matching)))
                yield 1, column(points, 1)

    # Type 0: a perfect matching of the full 9 by 9 grid.
    for matching in permutations(range(9)):
        yield 0, column((grid(row, c)
                         for row, c in enumerate(matching)), 0)


def add_to_binary_basis(basis, vector):
    while vector:
        pivot = vector.bit_length() - 1
        if pivot in basis:
            vector ^= basis[pivot]
        else:
            basis[pivot] = vector
            return


def binary_remainder(basis, vector):
    while vector:
        pivot = vector.bit_length() - 1
        if pivot not in basis:
            return vector
        vector ^= basis[pivot]
    return 0


def main():
    expected_by_type = {0: 362880, 1: 103680, 2: 864, 3: 16}
    basis = {}
    counts = Counter()
    for trace_type, vector in candidates():
        counts[trace_type] += 1
        add_to_binary_basis(basis, vector)
    assert dict(counts) == expected_by_type
    assert sum(counts.values()) == 467440
    assert len(basis) == 2642

    pair_total = (1 << PAIR_COUNT) - 1
    # P and N degrees are ten (even); grid degrees are eleven (odd).
    base_rhs = pair_total
    for point in range(24, 105):
        base_rhs |= 1 << (POINT_OFFSET + point)

    for t in range(5):
        type_counts = (31 - t, 96 + 3 * t, 12 - 3 * t, t)
        assert sum(type_counts) == 139
        assert sum((9 - a) * type_counts[a] for a in range(4)) == (
            24 * 10 + 81 * 11
        )
        assert sum(
            (9 - a) * (8 - a) // 2 * type_counts[a]
            for a in range(4)
        ) == PAIR_COUNT
        rhs = base_rhs
        for trace_type, number in enumerate(type_counts):
            if number % 2:
                rhs |= 1 << (TYPE_OFFSET + trace_type)
        assert binary_remainder(basis, rhs) == 0

    print(f"eligible pairs: {PAIR_COUNT}")
    print(f"candidate traces by type: {dict(sorted(counts.items()))}")
    print(f"total candidate traces: {sum(counts.values())}")
    print(f"binary constraint rank: {len(basis)}")
    print("VERIFIED: all five right-hand sides survive the complete parity relaxation")


if __name__ == "__main__":
    main()

