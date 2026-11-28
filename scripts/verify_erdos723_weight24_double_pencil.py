#!/usr/bin/env python3
"""Exact arithmetic for the two-special-point weight-24 branch.

This is a small standard-library audit of the pencil reduction recorded in
``notes/erdos-723-ternary-code.md``.  It is not a plane search.
"""

from math import comb


def main():
    # At the point q_+ with z=2, write i,j for the numbers of selected
    # positive and negative lines.  The i positive pencil lines need at
    # least two +1-points each.  If q_- lies on one of them, that line needs
    # two additional +1-points.  There are only twelve +1-points.
    pencil = []
    for i in range(13 + 1):
        for j in range(13 + 1 - i):
            for contains_other_special in (0, 1):
                if i - j != 6:
                    continue
                if 2 * i + 2 * contains_other_special > 12:
                    continue
                pencil.append((i, j, contains_other_special))
    assert pencil == [(6, 0, 0)]

    # Reversing signs gives the corresponding statement at q_-.
    # Hence the six positive q_+-lines partition the twelve +1-points
    # into pairs, and the six negative q_--lines partition the twelve
    # -1-points into pairs.
    assert 6 * 2 == 12

    # Let B,M be the other six positive and six negative selected lines.
    # At a +1-point, b-m=2.  If r is the total number of M-incidences on
    # the twelve +1-points, then the B-incidence total is 24+r.  The B-pair
    # budget is only C(6,2).  Convexity gives 12+2r as the minimum used
    # pair budget, leaving exactly r=0 or r=1.
    possible_r = tuple(
        r for r in range(13)
        if 12 + 2 * r <= comb(6, 2)
    )
    assert possible_r == (0, 1)

    for r in possible_r:
        ordinary_plus = 12 - r
        ordinary_minus = 12 - r
        # Nonzero local selected-line types (z,i,j), away from q_+,q_-.
        plus_types = {(1, 3, 0): ordinary_plus}
        minus_types = {(-1, 0, 3): ordinary_minus}
        if r:
            plus_types[(1, 4, 1)] = 1
            minus_types[(-1, 1, 4)] = 1
        assert sum(plus_types.values()) == 12
        assert sum(minus_types.values()) == 12

        # Selected-line profiles in value order (-2,-1,+1,+2).
        positive = [(0, 0, 2, 1)] * 6
        positive += [(0, 0, 4, 0)] * (6 - r)
        if r:
            positive.append((0, 1, 5, 0))
        negative = [(1, 2, 0, 0)] * 6
        negative += [(0, 4, 0, 0)] * (6 - r)
        if r:
            negative.append((0, 5, 1, 0))
        assert len(positive) == len(negative) == 12
        assert all(-2*a-b+c+2*d == 4 for a,b,c,d in positive)
        assert all(-2*a-b+c+2*d == -4 for a,b,c,d in negative)

        # Positive (respectively negative) pairs already used at nonzero
        # points leave 15-3r edges to be realized at zero-points.
        used_positive_pairs = comb(6, 2) + sum(
            number * comb(i, 2)
            for (_, i, _), number in plus_types.items()
        ) + sum(
            number * comb(i, 2)
            for (_, i, _), number in minus_types.items()
        )
        # q_+ uses 15; the twelve ordinary +1 local types use 36.  When
        # r=1, replacing (3,0) by (4,1) uses three additional pairs.  The
        # exceptional -1-point has only one positive line and uses none.
        assert used_positive_pairs == 51 + 3 * r
        remaining_positive_pairs = comb(12, 2) - used_positive_pairs
        assert remaining_positive_pairs == 15 - 3 * r

        # The two exceptional nonzero points, when present, use four
        # positive-negative pairs each.  Every residual intersection is a
        # zero-point and therefore contains equally many selected lines of
        # the two signs.  These are the exact edge and incidence budgets for
        # the residual balanced-clique cover.
        remaining_cross_pairs = 12 * 12 - 8 * r
        residual_half_incidences = (
            remaining_cross_pairs - 2 * remaining_positive_pairs
        )
        assert remaining_cross_pairs == (144, 136)[r]
        assert residual_half_incidences == (114, 112)[r]

    print("VERIFIED: the two-special-point branch has the exact double-pencil")
    print("reduction, with only r=0 or r=1 for the remaining selected lines")


if __name__ == "__main__":
    main()
