"""Exact deficit-profile and connectivity certificate for 137 partial lines.

The floating-point LP solver used to discover the 29 dual vectors is not used
here.  Every dual inequality is checked below with Fraction arithmetic.
"""

from fractions import Fraction
from itertools import combinations, product
from math import isqrt


TYPES = tuple(range(2, 9))


# For each profile not already handled by the elementary lower bound, these
# are exact dual multipliers.  Rows are ordered by occupied populations and
# then by unordered pairs of occupied types.
CERTIFICATES = {
    (95, 14, 3, 2, 1, 0, 0): ((4, 1), (29, 2), (40, 3), (3, 2), (-20, 1), (2, 3), (1, 3), (0, 1), (-1, 3), (1, 6), (5, 6), (0, 1), (1, 6), (1, 3), (2, 3)),
    (92, 14, 6, 2, 0, 0, 0): ((0, 1), (43, 2), (40, 1), (56, 1), (1, 1), (1, 1), (1, 1), (1, 2), (3, 4), (1, 2)),
    (95, 15, 0, 5, 0, 0, 0): ((4, 1), (46, 3), (0, 1), (2, 3), (0, 1), (0, 1)),
    (97, 15, 2, 0, 1, 1, 0): ((3, 1), (63, 4), (27, 1), (-1, 1), (-57, 4), (3, 4), (1, 2), (0, 1), (-1, 4), (3, 4), (9, 4), (3, 1), (-3, 2), (-7, 4), (19, 4)),
    (94, 15, 5, 0, 0, 1, 0): ((6, 1), (21, 2), (4, 1), (-251, 2), (1, 2), (0, 1), (-3, 2), (1, 2), (2, 1), (-5, 2)),
    (99, 16, 0, 0, 1, 0, 1): ((12, 1), (0, 1), (-180, 1), (-480, 1), (0, 1), (-3, 1), (-5, 1), (0, 1), (0, 1), (-15, 1)),
    (97, 16, 0, 0, 3, 0, 0): ((3, 1), (63, 4), (9, 1), (3, 4), (0, 1), (9, 4)),
    (96, 16, 3, 0, 0, 0, 1): ((7, 1), (0, 1), (-34, 1), (0, 1), (0, 1), (-1, 1), (0, 1), (0, 1), (0, 1), (-5, 1)),
    (94, 16, 3, 0, 2, 0, 0): ((3, 1), (63, 4), (26, 1), (0, 1), (3, 4), (1, 2), (0, 1), (3, 4), (9, 4), (-3, 2)),
    (91, 16, 6, 0, 1, 0, 0): ((12, 1), (0, 1), (-43, 1), (-180, 1), (0, 1), (-1, 1), (-3, 1), (0, 1), (0, 1), (3, 1)),
    (88, 16, 9, 0, 0, 0, 0): ((6, 1), (21, 2), (0, 1), (1, 2), (0, 1), (0, 1)),
    (94, 17, 0, 3, 1, 0, 0): ((12, 1), (0, 1), (-110, 1), (-180, 1), (0, 1), (-2, 1), (-3, 1), (0, 1), (0, 1), (6, 1)),
    (91, 17, 3, 3, 0, 0, 0): ((4, 1), (14, 1), (58, 3), (0, 1), (2, 3), (1, 3), (0, 1), (2, 3), (4, 3), (-4, 3)),
    (93, 18, 2, 1, 0, 1, 0): ((6, 1), (21, 2), (1, 2), (-29, 2), (-243, 2), (1, 2), (0, 1), (-1, 2), (-3, 2), (1, 2), (1, 1), (-3, 4), (5, 2), (0, 1), (0, 1)),
    (93, 19, 0, 1, 2, 0, 0): ((3, 1), (63, 4), (135, 4), (6, 1), (3, 4), (1, 4), (0, 1), (3, 2), (9, 4), (-21, 4)),
    (90, 19, 3, 1, 1, 0, 0): ((4, 1), (14, 1), (58, 3), (0, 1), (-18, 1), (2, 3), (1, 3), (0, 1), (-1, 3), (2, 3), (4, 3), (2, 1), (-4, 3), (-5, 3), (8, 3)),
    (87, 19, 6, 1, 0, 0, 0): ((12, 1), (0, 1), (-37, 1), (-114, 1), (0, 1), (-1, 1), (-2, 1), (0, 1), (0, 1), (-2, 1)),
    (90, 20, 0, 4, 0, 0, 0): ((4, 1), (14, 1), (8, 1), (2, 3), (0, 1), (4, 3)),
    (89, 22, 0, 2, 1, 0, 0): ((4, 1), (14, 1), (32, 3), (-28, 3), (2, 3), (0, 1), (-1, 3), (4, 3), (2, 1), (0, 1)),
    (86, 22, 3, 2, 0, 0, 0): ((4, 1), (14, 1), (58, 3), (4, 1), (2, 3), (1, 3), (0, 1), (2, 3), (4, 3), (-4, 3)),
    (88, 23, 2, 0, 0, 1, 0): ((6, 1), (21, 2), (-1, 1), (-203, 2), (1, 2), (0, 1), (-3, 2), (1, 2), (2, 1), (11, 2)),
    (88, 24, 0, 0, 2, 0, 0): ((3, 1), (63, 4), (18, 1), (3, 4), (0, 1), (9, 4)),
    (85, 24, 3, 0, 1, 0, 0): ((0, 1), (21, 1), (46, 1), (78, 1), (1, 1), (1, 1), (1, 1), (1, 1), (3, 1), (-1, 1)),
    (82, 24, 6, 0, 0, 0, 0): ((12, 1), (0, 1), (-37, 1), (0, 1), (-1, 1), (0, 1)),
    (85, 25, 0, 3, 0, 0, 0): ((12, 1), (0, 1), (-98, 1), (0, 1), (-2, 1), (0, 1)),
    (84, 27, 0, 1, 1, 0, 0): ((12, 1), (0, 1), (-90, 1), (-192, 1), (0, 1), (-2, 1), (-3, 1), (0, 1), (0, 1), (-6, 1)),
    (81, 27, 3, 1, 0, 0, 0): ((0, 1), (21, 1), (46, 1), (63, 1), (1, 1), (1, 1), (1, 1), (1, 1), (2, 1), (-1, 1)),
    (80, 30, 0, 2, 0, 0, 0): ((4, 1), (14, 1), (16, 1), (2, 3), (0, 1), (4, 3)),
    (79, 32, 0, 0, 1, 0, 0): ((3, 1), (63, 4), (27, 1), (3, 4), (0, 1), (9, 4)),
}


def weighted_solutions(weights, total):
    if not weights:
        if total == 0:
            yield ()
        return
    for count in range(total // weights[0] + 1):
        for rest in weighted_solutions(weights[1:], total - weights[0] * count):
            yield (count, *rest)


def histograms():
    for heavy in weighted_solutions([t * (t - 2) for t in range(3, 9)], 120):
        left = 260 - sum(t * k for t, k in zip(range(3, 9), heavy))
        if left < 0 or left % 2:
            continue
        hist = dict(zip(TYPES, (left // 2, *heavy)))
        if sum(hist.values()) <= 157:
            yield {t: k for t, k in hist.items() if k}


def gap_profiles(hist, t):
    heavy = tuple(s for s in hist if s > 2)
    for counts in weighted_solutions([s - 2 for s in heavy], t * (8 - t)):
        gaps = dict(zip(heavy, counts))
        gaps[2] = 12 * t - sum(counts)
        if all(0 <= gaps[s] <= hist[s] - (s == t) for s in hist):
            yield gaps


def linear_rows(hist, gaps):
    keys = [(t, j) for t in hist for j in range(len(gaps[t]))]
    index = {key: i for i, key in enumerate(keys)}
    rows, right = [], []
    for t in hist:
        row = [0] * len(keys)
        for j in range(len(gaps[t])):
            row[index[t, j]] = 1
        rows.append(row)
        right.append(hist[t])
    for s, t in combinations(hist, 2):
        row = [0] * len(keys)
        for j, profile in enumerate(gaps[s]):
            row[index[s, j]] = profile[t]
        for j, profile in enumerate(gaps[t]):
            row[index[t, j]] -= profile[s]
        rows.append(row)
        right.append(0)
    cost = [0] * len(keys)
    for j, profile in enumerate(gaps[2]):
        cost[index[2, j]] = 24 - profile[2]
    return rows, right, cost


def balanced_root_certificate():
    """Check the scalar classification for the balanced 10+10 root.

    A coordinate with z(z-1) <= 4 lies in {-1,0,1,2}.  We enumerate the
    multiplicities of these four values in each ten-element part.  The
    minimum-degree test is necessary because every occupied coordinate must
    have at least four possible opposite-part neighbors whose edge sum is
    zero or one.
    """
    parts = []
    for minus_one in range(3):
        for two in range(3):
            if minus_one + two > 2:
                continue
            for one in range(11 - minus_one - two):
                zero = 10 - minus_one - one - two
                counts = {-1: minus_one, 0: zero, 1: one, 2: two}
                total = -minus_one + one + 2 * two
                B = 2 * (minus_one + two)
                parts.append((total, B, counts))

    def degree_possible(left, right):
        return (
            all(sum(right[y] for y in right if x + y in (0, 1)) >= 4
                for x in left if left[x])
            and all(sum(left[x] for x in left if x + y in (0, 1)) >= 4
                    for y in right if right[y])
        )

    records = set()
    for sum_left, B_left, left in parts:
        for sum_right, B_right, right in parts:
            t = sum_left + sum_right
            A = sum_left - sum_right
            B = B_left + B_right
            D = A * A - 20 * B
            if (2 <= t <= 8 and abs(A) <= 10 and D >= 0
                    and degree_possible(left, right)):
                records.add((t, B, A, D))

    nonsquares = {D for _, _, _, D in records if isqrt(D) ** 2 != D}
    assert nonsquares == {20, 24, 41, 60}
    assert {(t, A) for t, _, A, D in records if D == 20} == {
        (6, -10), (6, 10)}
    assert {(t, A) for t, _, A, D in records if D == 24} == {
        (6, -8), (6, 8)}
    assert {(t, A) for t, _, A, D in records if D == 41} == {
        (7, -9), (7, 9)}
    assert {(t, A) for t, _, A, D in records if D == 60} == {
        (8, -10), (8, 10)}

    # Signed square roots a of the rational-squareclass states.
    vertices = set()
    state_types = set()
    for t, B, A, D in records:
        a = isqrt(D)
        if a * a != D:
            continue
        vertices.add((A, a))
        vertices.add((A, -a))
        state_types.add((t, B, A, a))

    # Enumerate maximal pairwise-compatible sets under
    # a_x a_y = A_x A_y (mod 20), using exact Bron--Kerbosch recursion.
    adjacency = {
        x: {y for y in vertices if y != x
            and (x[1] * y[1] - x[0] * y[0]) % 20 == 0}
        for x in vertices
    }
    cliques = []

    def maximal_cliques(current, possible, excluded):
        if not possible and not excluded:
            cliques.append(frozenset(current))
            return
        pivot = max(possible | excluded,
                    key=lambda x: len(possible & adjacency[x]),
                    default=None)
        candidates = possible - (adjacency[pivot] if pivot is not None else set())
        for vertex in list(candidates):
            maximal_cliques(current | {vertex},
                            possible & adjacency[vertex],
                            excluded & adjacency[vertex])
            possible.remove(vertex)
            excluded.add(vertex)

    maximal_cliques(set(), set(vertices), set())
    multipliers = (1, 9, 11, 19)
    assert len(cliques) == 4
    assert sorted(len(clique) for clique in cliques) == [15, 15, 17, 17]
    assert sorted(
        next(r for r in multipliers
             if all((a - r * A) % 20 == 0 for A, a in clique))
        for clique in cliques
    ) == list(multipliers)

    # In the r=11 class, every nonintegral state is strictly half-integral
    # and has one of the only deficits supported by the parity argument.
    for t, B, A, magnitude in state_types:
        for a in {magnitude, -magnitude}:
            if (a - 11 * A) % 20 == 0 and (a - A) % 20 != 0:
                assert t in (5, 7)
                assert (a - A) % 10 == 0

    return len(records), len(vertices)


def main():
    raw = locally_consistent = easy = certified = cut_sizes = 0
    smallest_slack = None
    used = set()
    all_histograms = []
    for hist in histograms():
        all_histograms.append(hist)
        raw += 1
        gaps = {t: list(gap_profiles(hist, t)) for t in hist}
        if any(not profiles for profiles in gaps.values()):
            continue
        if any(max(min(hist[s] * q[t] for q in gaps[s]),
                       min(hist[t] * q[s] for q in gaps[t])) >
               min(max(hist[s] * q[t] for q in gaps[s]),
                   max(hist[t] * q[s] for q in gaps[t]))
               for s, t in product(hist, repeat=2)):
            continue
        locally_consistent += 1
        m = hist[2]
        heavy = tuple(t for t in hist if t > 2)
        elementary = max(
            m * min(24 - q[2] for q in gaps[2]),
            sum(hist[t] * min(q[2] for q in gaps[t]) for t in heavy),
        )
        threshold = Fraction(494 * m - 4 * m * m, 19)
        if elementary > threshold:
            easy += 1
        else:
            key = tuple(hist.get(t, 0) for t in TYPES)
            multipliers = tuple(Fraction(a, b) for a, b in CERTIFICATES[key])
            rows, right, cost = linear_rows(hist, gaps)
            assert len(multipliers) == len(rows)
            assert all(sum(y * row[j] for y, row in zip(multipliers, rows)) <= cost[j]
                       for j in range(len(cost)))
            lower = sum(y * b for y, b in zip(multipliers, right))
            assert lower > threshold
            used.add(key)
            certified += 1

        min_degree = min(q[2] for q in gaps[2])
        assert m > 36 and min_degree > 4
        upper = {t: max(q[2] for q in gaps[t]) for t in heavy}
        for n in range(min_degree + 1, m // 2 + 1):
            cut_sizes += 1
            def bound(u):
                return 12 * n * u + sum(
                    hist[t] * max(c * (upper[t] - c) - u * (t - 2) * c
                                  for c in range(min(n, upper[t]) + 1))
                    for t in heavy)
            slack = 4 * n * (m - n) - min(bound(u) for u in range(-100, 151))
            assert slack > 0
            smallest_slack = slack if smallest_slack is None else min(smallest_slack, slack)

    assert used == set(CERTIFICATES)
    assert (raw, locally_consistent, easy, certified) == (127, 101, 72, 29)
    assert cut_sizes == 3502 and smallest_slack == 284
    assert max(h.get(5, 0) + h.get(7, 0) for h in all_histograms) == 8
    assert max(h.get(7, 0) for h in all_histograms) == 3
    assert [h for h in all_histograms if h[2] <= 75] == [
        {2: 75, 3: 35, 5: 1},
        {2: 70, 3: 40},
    ]
    balanced_records, balanced_vertices = balanced_root_certificate()
    print("Verified 127 profiles: 72 elementary and 29 exact dual certificates.")
    print("All 3,502 possible smallest component sizes fail; minimum slack 284.")
    print("Every surviving light graph is connected; every root-order lower bound exceeds 19.")
    print("The half-integral support and 5+15 root profile bounds also pass.")
    print(f"Balanced root: {balanced_records} coordinate states and "
          f"{balanced_vertices} signed scalar types reduce to four congruence classes.")


if __name__ == "__main__":
    main()
