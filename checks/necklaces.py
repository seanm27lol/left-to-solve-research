from math import gcd, comb
from itertools import product
from collections import Counter
from fractions import Fraction
import json,glob
def phi(k):return sum(gcd(i,k)==1 for i in range(1,k+1))
def H(d,n):return sum((-1)**j*comb(d,j)*comb((d-2*j)*n+d-1-j,d-1) for j in range((d-1)//2+1))
def cyclic(k,n):
 z=sum(phi(k//d)*H(d,n) for d in range(1,k+1) if k%d==0);assert z%k==0;return z//k
def solve(k,n,rev):
 c=cyclic(k,n)
 if not rev:return c
 if k==5:
  t=n//2;f=(2*t+1)*(2*n+1)-t*(t+1)
  return (c+f)//2
 f=sum((2*n+1-abs(s))*(2*n+1-2*abs(s)) for s in range(-n,n+1))
 return (2*c+f+H(3,n))//4
def brute(k,n,rev):
 necklaces=set()
 for x in product(range(-n,n+1),repeat=k):
  if sum(x):continue
  orbit=[x[i:]+x[:i] for i in range(k)]
  if rev:orbit.extend([v[::-1] for v in orbit])
  necklaces.add(min(orbit))
 return len(necklaces)
def auditgf(k,rev,coeff):
 den=[(-1)**j*comb(k,j) for j in range(k+1)]
 if rev and k==5:
  den=[sum((den[h-j] if 0<=h-j<len(den) else 0)*a for j,a in enumerate((1,2,1))) for h in range(k+3)]
 def N(i):return 0 if i<1 else solve(k,i,rev)
 assert [sum(a*N(i-j) for j,a in enumerate(den)) for i in range(1,31)]==coeff+[0]*(30-len(coeff))
 for n in (1,2):assert N(n)==brute(k,n,rev)
 cases=(N(1),N(2))
 print('count',k,rev,cases)
for k,rev,coeff in [(4,False,[6,-1,4,-1]),(5,False,[11,22,16,-4,1]),(6,False,[26,141,172,8,6,-1]),(7,False,[57,764,1727,750,71,-6,1]),(5,True,[7,24,27,30,5,-2,1]),(6,True,[18,59,96,-2,6,-1])]:
 auditgf(k,rev,coeff)
for n in range(1,9):
 necklaces=set(); k=2*n; a=b=0
 for raw in product('01',repeat=k):
  w=''.join(raw);rep=min(w[j:]+w[:j] for j in range(k))
  if rep in necklaces: continue
  necklaces.add(rep)
  orbit=[w[j:]+w[:j] for j in range(k)]
  if any(s==s[::-1] for s in orbit):a+=1
  elif w[::-1] in orbit:b+=1
 u=n//(n&(-n))
 assert (a,b)==(2**(n-1)+2**((u-1)//2),2**n-2**((u-1)//2))
 print('binary',n,(a,b))
