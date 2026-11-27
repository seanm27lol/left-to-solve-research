#!/usr/bin/env python3
"""Exact verifier for the weight-21 ternary-code reduction for order 12.

The mathematical input is a hypothetical projective plane of order 12 and a
weight-21 word in the ternary line-dependency code.  The preceding hand
argument orients the word with 9 positive and 12 negative coordinates and
defines the integer vector z by A^T x = 3z.  It gives

    sum(z) = -13,        sum(z^2) = 29.

At a point, let i and j be the numbers of incident selected positive and
negative lines.  The local type obeys

    0 <= i <= 9, 0 <= j <= 12, i + j <= 13, i - j = 3z,

and the five global moment equations are

    sum i = 117, sum j = 156,
    sum C(i,2) = 36, sum C(j,2) = 66, sum i*j = 108.

All calculations below use Python integers and finite set dynamic programming.
No solver or third-party package is used.
"""

from functools import lru_cache


Moment = tuple[int, int, int, int, int]
TARGET: Moment = (117, 156, 36, 66, 108)
Z_VALUES = (-4, -3, -2, -1, 1, 2, 3)
ZERO: Moment = (0, 0, 0, 0, 0)


def add(left: Moment, right: Moment) -> Moment:
    return tuple(a + b for a, b in zip(left, right))  # type: ignore[return-value]


def within_target(state: Moment) -> bool:
    return all(value <= bound for value, bound in zip(state, TARGET))


def contribution(local_type: tuple[int, int]) -> Moment:
    i, j = local_type
    return (i, j, i * (i - 1) // 2, j * (j - 1) // 2, i * j)


LOCAL_TYPES = {
    z_value: tuple(
        (i, j)
        for i in range(10)
        for j in range(13)
        if 0 < i + j <= 13 and i - j == 3 * z_value
    )
    for z_value in range(-4, 4)
}


def norm_patterns() -> list[tuple[int, ...]]:
    """Enumerate n_k with sum(k*n_k)=-13 and sum(k^2*n_k)=29."""

    answer: list[tuple[int, ...]] = []

    def visit(index: int, norm: int, total: int, counts: tuple[int, ...]) -> None:
        if index == len(Z_VALUES):
            if norm == 29 and total == -13:
                answer.append(counts)
            return
        value = Z_VALUES[index]
        for count in range((29 - norm) // (value * value) + 1):
            visit(
                index + 1,
                norm + count * value * value,
                total + count * value,
                counts + (count,),
            )

    visit(0, 0, 0, ())
    return answer


@lru_cache(maxsize=None)
def fixed_value_states(z_value: int, count: int) -> frozenset[Moment]:
    """Moment states for exactly count points having the given nonzero z."""

    options = tuple(contribution(local) for local in LOCAL_TYPES[z_value])
    states: set[Moment] = {ZERO}
    for _ in range(count):
        states = {
            candidate
            for state in states
            for option in options
            if within_target(candidate := add(state, option))
        }
    return frozenset(states)


@lru_cache(maxsize=None)
def balanced_states(maximum_points: int) -> frozenset[Moment]:
    """States using at most maximum_points positive local types (r,r).

    Unused positions are filled by the local type (0,0), so this enforces the
    total limit of 157 plane points without explicitly storing zero points.
    """

    options = tuple(contribution(local) for local in LOCAL_TYPES[0])
    exact: set[Moment] = {ZERO}
    all_states: set[Moment] = {ZERO}
    for _ in range(maximum_points):
        exact = {
            candidate
            for state in exact
            for option in options
            if within_target(candidate := add(state, option))
        }
        if not exact:
            break
        all_states.update(exact)
    return frozenset(all_states)


def has_local_realization(pattern: tuple[int, ...]) -> bool:
    nonzero_points = sum(pattern)
    if nonzero_points > 157:
        return False

    states: set[Moment] = {ZERO}
    # Large absolute z-values have fewer local types, so this order keeps the
    # intermediate exact state sets small.  It does not affect the result.
    groups = sorted(zip(Z_VALUES, pattern), key=lambda item: -abs(item[0]))
    for z_value, count in groups:
        if count == 0:
            continue
        group = fixed_value_states(z_value, count)
        states = {
            candidate
            for state in states
            for addition in group
            if within_target(candidate := add(state, addition))
        }
        if not states:
            return False

    balanced = balanced_states(157 - nonzero_points)
    for state in states:
        remainder = tuple(
            target - used for target, used in zip(TARGET, state)
        )
        if remainder in balanced:
            return True
    return False


def as_dictionary(pattern: tuple[int, ...]) -> dict[int, int]:
    return {
        value: count
        for value, count in zip(Z_VALUES, pattern)
        if count != 0
    }


def odd_support(pattern: tuple[int, ...]) -> int:
    return sum(
        count
        for value, count in zip(Z_VALUES, pattern)
        if value % 2 != 0
    )


EXPECTED = (
    ((-1, 19), (1, 2), (2, 2)),
    ((-1, 20), (1, 5), (2, 1)),
    ((-1, 21), (1, 8)),
    ((-2, 1), (-1, 16), (1, 1), (2, 2)),
    ((-2, 1), (-1, 17), (1, 4), (2, 1)),
    ((-2, 2), (-1, 12), (3, 1)),
)


def exclude_thirteen_point_pattern(pattern: tuple[int, ...]) -> None:
    """Check the exact arithmetic behind exclusion of the |T|=13 case.

    The binary minimum-word theorem supplies the one non-arithmetic input:
    an odd-support binary incidence-code word of weight 13 is a line.
    The checks here show that this line would carry 36 incidences with the 12
    selected negative lines, although distinct projective lines allow only 12.
    """

    assert as_dictionary(pattern) == {-2: 2, -1: 12, 3: 1}
    assert odd_support(pattern) == 13

    # z=3 has only local type (9,0), consuming the entire positive-pair
    # budget C(9,2)=36.  All remaining positive counts are therefore <= 1.
    assert LOCAL_TYPES[3] == ((9, 0),)
    assert 9 * 8 // 2 == TARGET[2]

    # Under i <= 1, the smallest possible negative-pair contribution is
    # attained only by (0,6) for z=-2 and (0,3) for z=-1.  It already equals
    # the full budget 66, so every one of these local types is forced.
    forced_negative_pairs = 2 * (6 * 5 // 2) + 12 * (3 * 2 // 2)
    assert forced_negative_pairs == TARGET[3]

    # The remaining 108 positive incidences, negative incidences, and cross
    # pairs are supplied by exactly 108 balanced (1,1) points.
    balanced_count = TARGET[0] - 9
    assert balanced_count == 108
    assert 2 * 6 + 12 * 3 + balanced_count == TARGET[1]
    assert balanced_count == TARGET[4]

    # If the 13 odd points form a line, it is not selected: its z=3 point has
    # type (9,0), while its twelve z=-1 points have type (0,3).  Consequently
    # each of the 12 selected negative lines meets it once, but the forced
    # local types demand three incidences at each of twelve points.
    available_negative_line_incidences = 12
    demanded_negative_line_incidences = 12 * 3
    assert demanded_negative_line_incidences > available_negative_line_incidences


def exclude_seventeen_point_odd_set() -> None:
    """Verify the exact secant-count contradiction for an odd 17-set.

    The geometric proof first shows that only 1-, 3-, and 5-secants can
    occur.  These three equations determine their counts.  Pairwise
    intersections of the ten 5-secants must lie in the set, so their local
    multiplicities violate Cauchy's inequality.
    """

    # n1+n3+n5=157, n1+3n3+5n5=17*13, and
    # 3n3+10n5=C(17,2).  Elimination gives the unique solution below.
    n1, n3, n5 = 135, 12, 10
    assert n1 + n3 + n5 == 157
    assert n1 + 3 * n3 + 5 * n5 == 17 * 13
    assert 3 * n3 + 10 * n5 == 17 * 16 // 2

    sum_h = n5 * 5
    sum_choose_h_2 = n5 * (n5 - 1) // 2
    sum_h_sq = sum_h + 2 * sum_choose_h_2
    assert (sum_h, sum_choose_h_2, sum_h_sq) == (50, 45, 140)
    assert sum_h * sum_h > 17 * sum_h_sq


def main() -> None:
    all_norm_patterns = norm_patterns()
    assert len(all_norm_patterns) == 35

    # T is an odd set: every line meets it oddly.  A point outside T and its
    # 13-line pencil show |T| >= 13.
    blocking_candidates = [
        pattern for pattern in all_norm_patterns if odd_support(pattern) >= 13
    ]
    assert len(blocking_candidates) == 22

    survivors = [
        pattern
        for pattern in blocking_candidates
        if has_local_realization(pattern)
    ]
    rendered = tuple(
        tuple(sorted(as_dictionary(pattern).items())) for pattern in survivors
    )
    assert rendered == EXPECTED

    thirteen_point = [
        pattern for pattern in survivors if odd_support(pattern) == 13
    ]
    assert len(thirteen_point) == 1
    exclude_thirteen_point_pattern(thirteen_point[0])
    exclude_seventeen_point_odd_set()

    print(f"norm/sum multiplicity patterns: {len(all_norm_patterns)}")
    print(f"patterns with odd support at least 13: {len(blocking_candidates)}")
    print(f"patterns satisfying all five local moment budgets: {len(survivors)}")
    for pattern in survivors:
        print(f"  |T|={odd_support(pattern):2d}  z multiplicities={as_dictionary(pattern)}")
    print("excluded the unique |T|=13 pattern by the 36-versus-12 incidence count")
    print("excluded the |T|=17 pattern by the 5-secant Cauchy contradiction")
    print("VERIFIED: four weight-21 z-multiplicity patterns remain")


if __name__ == "__main__":
    main()
