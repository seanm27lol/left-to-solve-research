"""Try every assignment of embedding signs on two affine triple systems of order 9.
Stress test of the exceptional grid proof; completion follows from the general argument.
"""
from collections import Counter
from itertools import combinations, product


def triples():
    # Lines of four parallel classes in the affine plane over F_3.
    return [frozenset(i for i in range(9) if ((i//3 if d==3 else i%3-d*(i//3)) % 3)==a)
            for d,a in product(range(4),range(3))]


def test():
    lines=triples()
    assert len(set(lines))==12
    assert all(sum(i in b and j in b for b in lines)==1 for i,j in combinations(range(9),2))
    native=[1]*12+[-1]*12
    counts=Counter()
    examples={}
    for bits in product((-1,1),repeat=8):
        w=[bits[h//3] for h in range(24)]
        obs=[[0]*24 for _ in range(24)]
        for i,j in combinations(range(24),2):
            canonical=len(lines[i%12]&lines[j%12]) if i//12==j//12 else 0
            obs[i][j]=obs[j][i]=canonical+(w[i]*w[j]-native[i]*native[j])//2
        if any(x not in (0,1) for row in obs for x in row):continue
        counts['binary pairs']+=1
        if any(sum(row)!=9 for row in obs):continue
        counts['heavy neighbor profiles']+=1
        if bits not in ((1,1,1,1,-1,-1,-1,-1),(-1,-1,-1,-1,1,1,1,1)):
            examples.setdefault('false Gram completion',bits)
        # The two-heavy old lines supply at least 8 distinct opposite-type
        # partners with Gram product 0 at every heavy point.
        if any(sum(obs[i][j]==0 for j in range(24) if i//12!=j//12)<8 for i in range(24)):continue
        counts['two-heavy-line test']+=1
        assert all(w[i]*w[j] == native[i]*native[j] for i,j in combinations(range(24),2))
    assert counts['two-heavy-line test']==2
    print(counts)
    print(examples)


if __name__=='__main__':
    test()
