"""Exact finite checks; the general graph proofs appear in the research report."""
from fractions import Fraction
from itertools import combinations
from math import gcd

def verify_graph_minimum_construction(n):
    p = next(d for d in range(2, n+1) if n%d == 0)
    r = 3*p-1
    clone = n//p
    vertices = [(a,i) for a in range(r) for i in range(clone)]
    neigh = {(a,i): {v for v in vertices if p <= (v[0]-a)%r < 2*p}
             for a,i in vertices}
    assert len(vertices) == 3*n-n//p
    assert all(len(v) == n for v in neigh.values())
    four_cycle = False
    for a,b in combinations(vertices,2):
        common = neigh[a] & neigh[b]
        if b in neigh[a]:
            assert not common
        else:
            assert common
            four_cycle |= len(common) >= 2
    assert four_cycle == (n>=3)
    cycle = [(a,0) for a in (0,p,2*p,1,p+1)]
    assert len(set(cycle))==5
    assert all(cycle[(k+1)%5] in neigh[cycle[k]] for k in range(5))

def verify_field_parameters():
    p = 659
    I = list(range(1,8))
    H = {pow(x,7,p) for x in range(1,p)}
    assert len(H)==94 and p-1 in H
    mu = {min(a,p-a) for a in H}
    labels = [(s*m*i)%p for s in (-1,1) for m in mu for i in I]
    assert sorted(labels) == list(range(1,p))
    def ratio(t):
        accepted = sum(i+j<=t for i in I for j in I)
        edges = (p-t)*(p-1)+len(mu)*accepted
        vertex = 2*p-1-t
        return Fraction(8*edges**2,p*vertex**3)
    results={t:ratio(t) for t in range(len(I),p+1)}
    assert 11==max(results,key=results.get)
    assert all(results[11]>r for t,r in results.items() if t!=11)
    assert results[11]>results[10]>1
    assert 8*428405**2-659*1306**3==284306256
    print('Erdős 573: exact comparisons passed for',len(results),'sizes')

if __name__ == "__main__":
    for n in range(2,61):
        verify_graph_minimum_construction(n)
    print('A182084: graph construction passed for 2 ≤ degree ≤ 60.')
    verify_field_parameters()
