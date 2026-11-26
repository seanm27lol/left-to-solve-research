from math import comb, factorial
from itertools import product,combinations
from collections import Counter
from fractions import Fraction

def board(n,h,v):
 masks=[]
 for i in range(n if v else n-1):
  for j in range(n if h else n-1):
   bits={(i*n+j),((i+1)%n)*n+j,i*n+(j+1)%n,((i+1)%n)*n+(j+1)%n}
   masks.append(sum(1<<b for b in bits))
 return Counter(k.bit_count() for k in range(2**(n*n)) if all(k&m for m in masks))
for n in (2,3,4):
 print('boards',n,[(sum(board(n,h,v).values()),dict(sorted(board(n,h,v).items())) if n==3 else None) for h,v in [(0,0),(0,1),(1,1)]])
def K(lo,hi):
 return sum(all(x>=y for x,y in zip(t,t[1:])) for t in product(*(range(a,b+1) for a,b in zip(lo,hi))))
def D(lo,hi):
 from itertools import permutations
 n=len(lo);M=[[comb(b-a+1,j-i+1) if 0<=j-i+1<=b-a+1 else 0 for j,b in enumerate(hi)] for i,a in enumerate(lo)];return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*__import__('math').prod(M[i][k] for i,k in enumerate(p)) for p in permutations(range(n)))
def E(lo,hi):
 return sum(D(tuple(max(t,j) for t in lo[:i]),hi[:i])*D(lo[i+1:],tuple(min(j-1,t) for t in hi[i+1:])) for i in range(len(hi)) for j in range(lo[i]+1,hi[i]+1))
P=[t for t in product(range(5),repeat=3) if t[0]>=t[1]>=t[2]]
c=0
for lo in P:
 for hi in P:
  if not all(a<=b for a,b in zip(lo,hi)):continue
  assert K(lo,hi)==D(lo,hi)
  brute=sum(sum(x>lo[i] and (i==2 or x>t[i+1]) for i,x in enumerate(t)) for t in P if all(a<=x<=b for a,x,b in zip(lo,t,hi)))
  assert E(lo,hi)==brute
  c+=1
print('intervals',c,'example',E((0,0),(2,1)))
