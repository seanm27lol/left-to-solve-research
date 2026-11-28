"""Exact profile certificate for order 12, 139 old lines, no deficit one."""
from fractions import Fraction
from functools import lru_cache
from itertools import product


def weighted_solutions(weights, target):
    if not weights:
        if target == 0:
            yield ()
        return
    first, *rest = weights
    for k in range(target // first + 1):
        for other in weighted_solutions(rest, target - first * k):
            yield (k,) + other


def histograms():
    # Any positive deficit is at most 6 by the gap-neighbor deficit sum.
    heavy = (3, 4, 5, 6)
    for values in weighted_solutions([t * (t-2) for t in heavy], 72):
        p = {t:n for t,n in zip(heavy, values) if n}
        left = 234 - sum(t*n for t,n in p.items())
        if left < 0 or left % 2:
            continue
        p[2] = left//2
        p[0] = 157 - sum(p.values())
        if min(p.values()) >= 0:
            yield dict(sorted(p.items()))


def line_types(p):
    types = tuple(t for t in p if t>2)
    for values in product(*(range(min(p[t],18//t)+1) for t in types)):
        left = 18-sum(t*n for t,n in zip(types,values))
        if left<0 or left%2:
            continue
        counts = dict(zip(types, values))
        counts[2] = left//2
        counts[0] = 13 - sum(counts.values())
        if all(0<=counts[t]<=p[t] for t in p):
            yield counts


def neighbor_types(p, t):
    high = tuple(s for s in p if s>2)
    for values in weighted_solutions([s-2 for s in high], t*(6-t)):
        counts = dict(zip(high, values))
        counts[2] = 12*t - sum(values)
        counts[0] = 0
        if all(0<=counts[s]<=p[s]-(s==t) for s in p):
            yield counts


def pencil_possible(p,t,neighbors,lines):
    # Sum of the size vectors of the 13-t lines through a given t-point.
    # Coordinates 0 and 2 are determined by length 13 and weight 18.
    high=tuple(s for s in p if s>2)
    r=13-t
    target=tuple(p[s]-neighbors[s]+(r-1)*(s==t) for s in high)
    options=sorted({tuple(line[s] for s in high) for line in lines if line[t]})

    @lru_cache(None)
    def cover(i,slots,need):
        if i==len(options):
            return slots==0 and all(x==0 for x in need)
        remaining=options[i:]
        if any(not (slots*min(v[j] for v in remaining)<=need[j]<=slots*max(v[j] for v in remaining)) for j in range(len(need))):
            return False
        v=options[i]
        for copies in range(min([slots]+[n//k for n,k in zip(need,v) if k])+1):
            if cover(i+1,slots-copies,tuple(n-copies*k for n,k in zip(need,v))):
                return True
        return False
    return cover(0,r,target)


def prune_cross(p,profiles):
    # Keep necessary intervals for number of ordered t-to-s gap incidences.
    for t,s in product(p,repeat=2):
        bounds=[]
        for a,b in ((t,s),(s,t)):
            vals=[p[a]*q[b] for q in profiles[a]]
            bounds.append((min(vals),max(vals)))
        if max(lo for lo,_ in bounds)>min(hi for _,hi in bounds):
            return False
    return True


def run():
    raw=list(histograms())
    kept=[]
    for p in raw:
        lines=list(line_types(p))
        profiles={t:[n for n in neighbor_types(p,t) if pencil_possible(p,t,n,lines)] for t in p}
        if all(profiles.values()) and prune_cross(p,profiles):
            kept.append(p)
    expected=[
        {0:46,2:108,6:3},
        {0:48,2:102,4:6,6:1},
        {0:49,2:99,4:9},
        {0:51,2:86,3:19,5:1},
        {0:52,2:81,3:24},
    ]
    assert kept==expected, kept
    print(f"{len(raw)} moment histograms; {len(kept)} survive.")
    for p in kept:
        print(p)
    # Two components would give two large eigenvalues and at most 16 others.
    # Confirm the strict Cauchy-Schwarz contradictions for all five families.
    degree_tables = [{22:108},{21:72,20:30},{20:99},{18:55,16:31},{16:81}]
    expected_surplus = [1728,Fraction(17808,17),1188,Fraction(1201,1849),324]
    for hist, surplus in zip(degree_tables,expected_surplus):
        m = sum(hist.values())
        degree_sum = sum(d * count for d,count in hist.items())
        T, Q = 2*m, 4*m+degree_sum
        a, b = 2+Fraction(degree_sum,m),2+min(hist)
        assert (T-a-b)**2 - 16*(Q-a*a-b*b) == surplus > 0
        assert 34*b+2*b-2*T > 0
        assert Fraction((2*m)**2,degree_sum+2*m)>17
    print("Profile and spectral checks passed.")


if __name__=="__main__":
    run()
