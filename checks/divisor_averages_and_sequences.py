from fractions import Fraction
from math import comb, gcd, prod, isqrt
import json
from pathlib import Path

def primes(bound):
    return [p for p in range(2,bound+1) if all(p%d for d in range(2,isqrt(p)+1))]
def divmean(n):
    m=n
    while not m%2:
        m//=2
    d=n//m
    b=(1<<d)-1
    L=m*b
    p=next(p for p in primes(6000) if p%2 and (p+1)%(2*m)==0)
    # Divide by n reduced iff gcd with n is one; compute the remaining geometric sum modulo n, logarithmically.
    def go(L):
        if L==0:return (1%n,0)
        qp,s=go(L//2)
        return ((qp*qp*p)%n,(s*(1+qp)+qp*qp)%n) if L%2 else ((qp*qp)%n,s*(1+qp)%n)
    return gcd(go(L)[1],n)
assert all(divmean(n)==1 for n in range(1,180))
row=[1]
for n in range(1,82):
    row=[0]+[(n-1)*(row[j] if j<len(row) else 0)+row[j-1] for j in range(1,n+1)]
    s=sum(Fraction((-1)**(n-j),row[j]) for j in range(1,n+1))
    if n>=4: assert abs(s-1)<=Fraction(2,n)
for p in primes(1300)[1:]:
    u=1; total=1
    for k in range(1,p+1):
        u=u*(4*k-2)//k
        total=2*total+u+(2*(u*k//(4*k-2)))
    assert (total-(2+4*(-1)**((p-1)//2)))%p==0
for n in range(1,85):
    row=[comb(k*k+n-1,n) for k in range(2*n+1)]; total=0; weight=1
    while row:
        total+=row[0]*weight; weight*=2; row=[v-u for u,v in zip(row,row[1:])]
    assert total%10==0
print("179 divisor-mean constructions, 81 signed Stirling rows, odd primes to 1300, 84 geometric-law coefficients passed.")
