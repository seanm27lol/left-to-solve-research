"""Exact profile and connectivity certificate for 138 partial lines of order 12."""
from fractions import Fraction
from itertools import product


def weighted_solutions(weights, total):
    """Enumerate nonnegative integer vectors of the given weighted sum."""
    if not weights:
        if total == 0:
            yield ()
        return
    for count in range(total // weights[0] + 1):
        for rest in weighted_solutions(weights[1:], total-weights[0]*count):
            yield (count, *rest)


def histograms():
    for heavy in weighted_solutions([t*(t-2) for t in range(3, 8)], 95):
        left = 247 - sum(t*k for t, k in zip(range(3, 8), heavy))
        if left < 0 or left % 2:
            continue
        hist = dict(zip(range(2, 8), (left//2, *heavy)))
        if sum(hist.values()) <= 157:
            yield {t: k for t, k in hist.items() if k}


def gap_profiles(hist, t):
    heavy = tuple(s for s in hist if s > 2)
    for counts in weighted_solutions([s-2 for s in heavy], t*(7-t)):
        g = dict(zip(heavy, counts))
        g[2] = 12*t - sum(counts)
        if all(0 <= g[s] <= hist[s] - (s == t) for s in hist):
            yield g


def cross_consistent(hist, gaps):
    for s, t in product(hist, repeat=2):
        st = [hist[s]*q[t] for q in gaps[s]]
        ts = [hist[t]*q[s] for q in gaps[t]]
        if max(min(st), min(ts)) > min(max(st), max(ts)):
            return False
    return True


def main():
    n_raw = kept = cut_sizes = 0
    min_slack = min_ratio = None
    for hist in histograms():
        n_raw += 1
        gaps = {t: list(gap_profiles(hist, t)) for t in hist}
        if any(not opt for opt in gaps.values()) or not cross_consistent(hist, gaps):
            continue
        heavy = tuple(t for t in hist if t > 2)
        m = hist[2]
        min_degree = min(q[2] for q in gaps[2])
        min_edges = max(m*min(24-q[2] for q in gaps[2]),
                        sum(hist[t]*min(q[2] for q in gaps[t]) for t in heavy))
        ratio = Fraction(4*m*m, 26*m-min_edges)
        if ratio > 19:
            continue
        # At least 19 root vertices. Every component has at least min_degree+1 lights.
        assert m > 36 and min_degree > 4 and ratio > 18
        min_ratio = ratio if min_ratio is None else min(min_ratio, ratio)
        kept += 1
        upper = {t: max(q[2] for q in gaps[t]) for t in heavy}
        for n in range(min_degree + 1, m//2 + 1):
            cut_sizes += 1
            # One certificate value u per putative smallest component size.
            def bound(u):
                b = 10*n*u
                for t in heavy:
                    T = upper[t]
                    b += hist[t]*max(c*(T-c)-u*(t-2)*c for c in range(min(n,T)+1))
                return b
            best = min(bound(u) for u in range(-20, 51))
            slack = 4*n*(m-n) - best
            assert slack > 0, (hist, n, slack)
            min_slack = slack if min_slack is None else min(min_slack, slack)
    print(f"Initial histograms: {n_raw}; profiles after necessary bounds: {kept}.")
    print(f"Component sizes excluded: {cut_sizes}; smallest strict slack: {min_slack}.")
    print(f"Smallest root-order lower bound: {min_ratio} > 18.")


if __name__ == "__main__":
    main()
