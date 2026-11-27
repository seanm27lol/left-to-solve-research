#!/usr/bin/env python3
"""Exact verifier for an endpoint-deficit lemma and k in {3,5,7}.

Standard library only.  The finite ranges are DERIVED in the accompanying
proof, not user-chosen search cutoffs.  No numerical assumption on v=a-e
is used.  All polynomial checks are coefficient identities.
"""
from fractions import Fraction
from math import gcd, isqrt
from collections import Counter

if not __debug__:
    raise SystemExit('Run without -O: assertions form part of this certificate.')

# Univariate polynomials in k, ascending coefficients, over Q.
def clean(p):
    p=list(map(Fraction,p))
    while len(p)>1 and not p[-1]:p.pop()
    return p

def add(a,b):
    c=[Fraction(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return clean(c)

def neg(a):return [-x for x in a]
def sub(a,b):return add(a,neg(b))
def scale(a,c):return clean([x*c for x in a])
def mul(a,b):
    c=[Fraction(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return clean(c)
def power(a,n):
    r=[Fraction(1)]
    for _ in range(n):r=mul(r,a)
    return r
def compose(a,b):
    r=[Fraction(0)]
    for x in reversed(a):r=add(mul(r,b),[x])
    return r
def evaluate_x(coeffs,node):
    r=[Fraction(0)]
    for p in reversed(coeffs):r=add(mul(r,node),p)
    return r

K=[0,1]
T=mul(power(K,2),mul(power([1,1],2),power([2,1],2)))
C=[16,48,24]
P=[mul(K,mul(power([1,1],2),power([2,1],2))),
   [8,28,42,20,2],[-8,-24,8,12],neg(C)]
for node,mult,target in [([0],K,T),([-1],[2,1],T),
                         ([0,Fraction(1,2)],K,scale(T,2)),
                         ([Fraction(1,2),Fraction(1,2)],[1,1],scale(T,2))]:
    assert sub(mul(mult,evaluate_x(P,node)),target)==[0]
# P(x) is a polynomial with integer coefficients in (2x,k).
for i,p in enumerate(P):
    assert all((q/Fraction(2**i)).denominator==1 for q in p)
# For k>=3, all non-leading coefficients of P are positive.
for p in P[:3]:
    shifted=compose(p,[3,1])
    assert shifted[0]>0 and all(q>=0 for q in shifted)
# Exact expansion of -P(k+z), by powers of z.
A=[ [0,-12,-32,-15,14,9],
    [-8,-12,54,108,46],
    [8,72,136,60], C]
# Verify coefficients without sampling k or z.
from math import comb
for j in range(4):
    r=[Fraction(0)]
    for i in range(j,4):
        r=add(r,scale(mul(P[i],power(K,i-j)),-comb(i,j)))
    assert r==clean(A[j])
    shifted=compose(r,[3,1])
    assert shifted[0]>0 and all(q>=0 for q in shifted)
print('PASS: exact interpolation, integer P(2x), strict positivity for all k>=3,x>=k.')

def sieve(n):
    a=bytearray(b'\1')*(n+1)
    a[:2]=b'\0\0'
    for p in range(2,isqrt(n)+1):
        if a[p]:a[p*p:n+1:p]=b'\0'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if a[p]],a

def bound_data(k):
    t=k*k*(k+1)**2*(k+2)**2
    B=2*t+6*k*k+12*k+4
    return B,k+(k+3)*B-1

EXPECTED={
 3:(43766,877,[(13,23,8641),(23,43,55829),(521,1039,148201229)]),
 5:(707316,4249,[(11,17,2275),(47,89,530743)]),
 7:(5084146,18717,[(43,79,226561),(14629,29251,3153054217219)])}
max_bound=max(t[0] for t in EXPECTED.values())
primes,prime_flags=sieve(2*max_bound)

for k,(expected_max,expected_pairs,expected_cofactors) in EXPECTED.items():
    B,max_d=bound_data(k)
    assert max_d==expected_max
    counts=Counter();cofactors=[]
    for d in primes:
        if d<7 or d<=k:continue
        if d>max_d:break
        c=2*d-k
        if not prime_flags[c]:continue
        G=gcd(d+1,c-1)
        assert G==gcd(d+1,k+3)
        if not d<k+G*B:continue
        counts['endpoint_pairs']+=1
        m1=d*(d+1);m2=c*(c-1)
        assert gcd(c,m1)==gcd(d,m2)==1
        assert gcd(m1,m2)==G
        r1=(-pow(c,-1,m1))%m1
        r2=pow(d,-1,m2)
        if (r2-r1)%G:continue
        counts['compatible_pairs']+=1
        period=m1*(m2//G)
        residue=(r1+m1*((((r2-r1)//G)*pow(m1//G,-1,m2//G))%(m2//G)))%period
        assert residue%m1==r1 and residue%m2==r2
        lo=d**3+1;hi=c**3-1
        first=residue+max(0,(lo-residue+period-1)//period)*period
        assert first>=lo and first-period<lo
        for X in range(first,hi+1,period):
            assert c*X%m1==m1-1 and d*X%m2==1
            cofactors.append((d,c,X))
            # To be eligible, every prime divisor must lie strictly in (d,c),
            # and there must be exactly three, each with exponent one.
            z=X;factors=[]
            for q in primes:
                if q>=c or q*q>z:break
                while z%q==0:
                    factors.append(q);z//=q
            if z>1:factors.append(z)
            eligible=(len(factors)==3 and len(set(factors))==3
                      and d<factors[0]<factors[1]<factors[2]<c)
            assert not eligible,(d,c,X,factors)
    assert counts['endpoint_pairs']==expected_pairs
    assert counts['compatible_pairs']==expected_pairs
    assert cofactors==expected_cofactors
    print(f'k={k}: d<={max_d}; endpoint pairs={expected_pairs}; cofactors={len(cofactors)}; eligible triples=0')
    for item in cofactors:print('  ',item)
print('PASS: no candidates for k=3,5,7, at any v or prime size. k=1 is excluded by c-1=2(d-1).')
