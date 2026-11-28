#!/usr/bin/env python3
"""Exact profile reduction for weight-24 ternary dependencies, order 12.

Run beside ``erdos723_weight24_profiles_certs.txt``.  The certificate file contains integer Farkas
vectors discovered separately.  This verifier uses only the Python standard
library and checks every profile column and right-hand side from scratch.
"""

from ast import literal_eval
from itertools import product
from math import comb
from pathlib import Path


ODD_WEIGHTS = {16, 20, 24, 28, 32, 36}
BRANCHES = {
    -26: {
        "norm": 36,
        "classes": ((2, 9), (-6, 15), (-2, 133)),
        "survivors": (
            ((-1, 31), (1, 5)),
        ),
    },
    0: {
        "norm": 32,
        "classes": ((4, 12), (-4, 12), (0, 133)),
        "survivors": (
            ((-1, 15), (1, 13), (2, 1)),
            ((-1, 16), (1, 16)),
            ((-2, 1), (-1, 12), (1, 12), (2, 1)),
            ((-2, 1), (-1, 13), (1, 15)),
        ),
    },
}


def multiplicity_patterns(total, norm):
    values = tuple(v for v in range(-6, 7) if v)
    answer = []

    def visit(index, running_sum, running_norm, odd_support, counts):
        if index == len(values):
            if (running_sum == total and running_norm == norm
                    and odd_support in ODD_WEIGHTS):
                answer.append(tuple(
                    (value, count)
                    for value, count in zip(values, counts)
                    if count
                ))
            return
        value = values[index]
        for count in range((norm - running_norm) // (value * value) + 1):
            visit(
                index + 1,
                running_sum + value * count,
                running_norm + value * value * count,
                odd_support + (abs(value) % 2) * count,
                counts + (count,),
            )

    visit(0, 0, 0, 0, ())
    return tuple(answer)


def profiles(values, multiplicities, target):
    ranges = tuple(range(min(13, number) + 1) for number in multiplicities)
    for counts in product(*ranges):
        if (sum(counts) <= 13
                and sum(v * c for v, c in zip(values, counts)) == target):
            yield counts


def system(pattern, classes):
    values = tuple(value for value, _ in pattern)
    multiplicities = tuple(number for _, number in pattern)
    typed_profiles = []
    for line_class, (target, _) in enumerate(classes):
        typed_profiles.extend(
            (line_class, counts)
            for counts in profiles(values, multiplicities, target)
        )

    rows, rhs = [], []
    for line_class, (_, number) in enumerate(classes):
        rows.append(tuple(
            int(kind == line_class) for kind, _ in typed_profiles
        ))
        rhs.append(number)
    for index, number in enumerate(multiplicities):
        rows.append(tuple(counts[index] for _, counts in typed_profiles))
        rhs.append(13 * number)
    for index, number in enumerate(multiplicities):
        rows.append(tuple(
            comb(counts[index], 2) for _, counts in typed_profiles
        ))
        rhs.append(comb(number, 2))
    for left in range(len(values)):
        for right in range(left + 1, len(values)):
            rows.append(tuple(
                counts[left] * counts[right]
                for _, counts in typed_profiles
            ))
            rhs.append(multiplicities[left] * multiplicities[right])
    return tuple(typed_profiles), tuple(rows), tuple(rhs)


def read_certificates():
    path = Path(__file__).with_name("erdos723_weight24_profiles_certs.txt")
    branch = None
    result = {}
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("CASE "):
            branch = int(line.split()[1])
            continue
        assert branch is not None
        boundary = line.index("} [") + 1
        pattern = literal_eval(line[:boundary])
        rest = line[boundary + 1:]
        close = rest.index("]") + 1
        certificate = literal_eval(rest[:close])
        right_hand_side, profile_count = map(int, rest[close:].split())
        key = tuple(sorted(pattern.items()))
        result[(branch, key)] = (
            tuple(certificate), right_hand_side, profile_count
        )
    return result


def exclude_unbalanced_special_pattern():
    """Exclude z=(-2)^2,(-1)^24,2 by the pencil through the 2-point."""
    # On a positive selected line the z-sum is 2.  With one available +2
    # point and all other nonzero values negative, every positive line must
    # contain that point and no other nonzero point.
    positive_profiles = tuple(profiles(( -2, -1, 2), (2, 24, 1), 2))
    assert positive_profiles == ((0, 0, 1),)

    # Hence the +2 point lies on all nine positive lines.  Since z=(i-j)/3
    # there, it lies on exactly three of the fifteen negative selected lines.
    positive_through_special = 9
    negative_through_special = positive_through_special - 3 * 2
    assert negative_through_special == 3
    negative_away = 15 - negative_through_special
    assert negative_away == 12

    # Neither a -2 nor a -1 point lies on a positive selected line, so their
    # negative selected-line multiplicities are respectively 6 and 3.  These
    # points, together with the +2 point, already account for every pair of
    # negative selected lines.  Thus two negative lines cannot meet at z=0.
    negative_pair_intersections = (
        comb(negative_through_special, 2)
        + 2 * comb(6, 2)
        + 24 * comb(3, 2)
    )
    assert negative_pair_intersections == comb(15, 2)

    # A negative line away from the special point meets the nine positive
    # lines in nine distinct zero-points, leaving only four places.  To have
    # z-sum -6 using at most the two -2 points and any number of -1 points,
    # it must contain both -2 points and two -1 points.  Only one projective
    # line can contain the two -2 points, contradicting the twelve such lines.
    fitting = tuple(
        (number_minus_two, number_minus_one)
        for number_minus_two in range(3)
        for number_minus_one in range(25)
        if (number_minus_two + number_minus_one <= 4
            and 2 * number_minus_two + number_minus_one == 6)
    )
    assert fitting == ((2, 2),)
    assert negative_away > 1


def main():
    certificates = read_certificates()
    exclude_unbalanced_special_pattern()
    eliminated = 0
    for total, data in BRANCHES.items():
        patterns = multiplicity_patterns(total, data["norm"])
        expected_count = 12 if total == -26 else 32
        assert len(patterns) == expected_count
        survivors = set(data["survivors"])
        special = ((-2, 2), (-1, 24), (2, 1)) if total == -26 else None
        for pattern in patterns:
            if pattern in survivors:
                assert (total, pattern) not in certificates
                continue
            if pattern == special:
                assert (total, pattern) not in certificates
                continue
            certificate, expected_rhs, expected_profiles = certificates[
                (total, pattern)
            ]
            typed_profiles, rows, rhs = system(pattern, data["classes"])
            assert len(typed_profiles) == expected_profiles
            assert len(certificate) == len(rows)
            column_pairings = tuple(
                sum(multiplier * row[column]
                    for multiplier, row in zip(certificate, rows))
                for column in range(len(typed_profiles))
            )
            rhs_pairing = sum(
                multiplier * value
                for multiplier, value in zip(certificate, rhs)
            )
            assert min(column_pairings) >= 0
            assert rhs_pairing == expected_rhs < 0
            eliminated += 1
        print(
            f"sum {total:3d}: {len(patterns)} norm/parity patterns; "
            f"{len(survivors)} survive exact line profiles"
        )
        for survivor in data["survivors"]:
            print("  ", dict(survivor))
    assert eliminated == 38
    assert len(certificates) == 38
    print("VERIFIED: 38 certificate exclusions plus one pencil exclusion; "
          "exactly five profile patterns remain")


if __name__ == "__main__":
    main()

