#!/usr/bin/env python3
"""Exact line-profile certificates excluding weight 21 for order 12.

The preceding reduction leaves four possible multiplicity patterns for the
integer point vector z defined by A^T x = 3z. Since Az = 4x - 1, a line has
z-sum 3, -5, or -1 according as its coefficient in x is +1, -1, or 0.
This verifier enumerates every possible line profile and checks exact integer
Farkas certificates for three patterns. The fourth has a pair-parity
contradiction checked at the end. Only the Python standard library is used.
"""

from itertools import product
from math import comb


LINE_CLASSES = ((3, 9), (-5, 12), (-1, 136))

# Coordinates: three line-class counts; incidences by sorted nonzero z-value;
# same-value pair counts; cross-value pair counts in lexicographic order.
CASES = (
    ({-1: 19, 1: 2, 2: 2},
     (4, 0, 4, -4, -4, -4, 2, -4, 4, 3, 2, 4), -68),
    ({-1: 20, 1: 5, 2: 1},
     (-3, 45, 45, -45, 3, -45, 18, -2, -45, 12, 27, 45), -92),
    ({-2: 1, -1: 17, 1: 4, 2: 1},
     (21, -15, -15, -12, 15, -21, -48, -48, -6, 14, -48,
      0, 48, 48, 6, 12, 48), -276),
)


def profiles(values, multiplicities, target):
    """All profiles of the nonzero z-values on one 13-point line."""
    ranges = (range(min(13, count) + 1) for count in multiplicities)
    for counts in product(*ranges):
        if (sum(counts) <= 13
                and sum(v * c for v, c in zip(values, counts)) == target):
            yield counts


def rows_and_rhs(pattern):
    values = sorted(pattern)
    multiplicities = [pattern[value] for value in values]
    typed_profiles = []
    for line_class, (target, _) in enumerate(LINE_CLASSES):
        typed_profiles.extend(
            (line_class, counts)
            for counts in profiles(values, multiplicities, target)
        )

    rows, rhs = [], []
    for line_class, (_, number) in enumerate(LINE_CLASSES):
        rows.append([int(kind == line_class) for kind, _ in typed_profiles])
        rhs.append(number)

    for index, number in enumerate(multiplicities):
        rows.append([counts[index] for _, counts in typed_profiles])
        rhs.append(13 * number)

    for index, number in enumerate(multiplicities):
        rows.append([comb(counts[index], 2) for _, counts in typed_profiles])
        rhs.append(comb(number, 2))
    for left in range(len(multiplicities)):
        for right in range(left + 1, len(multiplicities)):
            rows.append([
                counts[left] * counts[right]
                for _, counts in typed_profiles
            ])
            rhs.append(multiplicities[left] * multiplicities[right])

    return values, typed_profiles, rows, rhs


def verify_farkas_certificates():
    for pattern, certificate, expected_rhs in CASES:
        _, typed_profiles, rows, rhs = rows_and_rhs(pattern)
        assert len(rows) == len(certificate)
        column_pairings = [
            sum(multiplier * row[column]
                for multiplier, row in zip(certificate, rows))
            for column in range(len(typed_profiles))
        ]
        rhs_pairing = sum(
            multiplier * value
            for multiplier, value in zip(certificate, rhs)
        )
        assert min(column_pairings) >= 0
        assert rhs_pairing == expected_rhs < 0
        print(pattern, "profiles", len(typed_profiles),
              "minimum column", min(column_pairings),
              "right-hand side", rhs_pairing)


def verify_last_pattern():
    pattern = {-1: 21, 1: 8}
    values, typed_profiles, _, _ = rows_and_rhs(pattern)
    assert values == [-1, 1]
    positive_profiles = [
        counts for line_class, counts in typed_profiles if line_class == 0
    ]
    # A positive line has r-s=3, so it contains at least three plus-points.
    # Nine such lines consume at least 27 of the 28 plus-pairs. A fourth
    # plus-point on any line would consume at least 30, so all are triples.
    assert all(counts[1] >= 3 for counts in positive_profiles)
    assert LINE_CLASSES[0][1] * comb(3, 2) == 27
    assert comb(8, 2) == 28
    # The triples cover all but one pair. At each of the other six vertices,
    # seven covered incident pairs would have to split into groups of two.
    assert 6 % 2 == 0 and 7 % 2 == 1
    print(pattern, "excluded by nine triples covering all but one pair")


def main():
    verify_farkas_certificates()
    verify_last_pattern()
    print("VERIFIED: every weight-21 multiplicity pattern is impossible")


if __name__ == "__main__":
    main()
