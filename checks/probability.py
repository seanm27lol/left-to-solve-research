from fractions import Fraction as F
from itertools import product,combinations
from functools import lru_cache
from math import comb,ceil
from heapq import heapify,heappop,heappush
from collections import Counter
def compositions(total,m):
 if m==1:
  yield (total,);return
 for k in range(total+1):
  for a in compositions(total-k,m-1):yield (k,)+a
@lru_cache(None)
def cf(cs,k):
 if sum(cs)==0:return (0,0)
 best,most=10**9,0
 # enumerate all legal nonempty first boxes
 avail=[i for i,c in enumerate(cs) if c]
 for j in range(1,min(len(avail),k)+1):
  for I in combinations(avail,j):
   t=tuple(c-(i in I) for i,c in enumerate(cs)); b,r=cf(t,k)
   best=min(best,1+b);most=max(most,(j==k)+r)
 return best,most
ncase=0
for n in range(1,5):
 for m in range(9):
  for cs in compositions(m,n):
   for k in range(1,6):
    a=max(max(cs),ceil(m/k));b=max(r for r in range(m+1) if sum(min(c,r) for c in cs)>=k*r)
    assert (a,b)==cf(cs,k);ncase+=1
print('coupon partition',ncase)
ncase=0
for k in range(1,9):
 for p0 in range(1,9):
  for q0 in range(p0):
   p,q=F(p0,8),F(q0,8)
   w=[[comb(k,i)*x**i*(1-x)**(k-i) for i in range(k+1)] for x in (p,q)]
   adv=sum(((i>j)-(i<j))*wi*wj for i,wi in enumerate(w[0]) for j,wj in enumerate(w[1]))
   assert adv>=p-q;ncase+=1
print('binomial race',ncase)
for n in range(1,13):
 counts=Counter();good=Counter()
 for steps in product([-1,1],repeat=n):
  v=0;b=True
  for a in steps:v+=a;b&=v!=0
  counts[v]+=1;good[v]+=b
 for v,c in counts.items():assert F(abs(v),n)==F(good[v],c)
print('ballot all paths length 1..12')
def lin(A,b):
 n=len(A);B=[[F(z) for z in a]+[F(x)] for a,x in zip(A,b)]
 for i in range(n):
  u=next(u for u in range(i,n) if B[u][i]);B[u],B[i]=B[i],B[u];p=B[i][i];B[i]=[x/p for x in B[i]]
  for j in range(n):
   if j!=i:
    r=B[j][i];B[j]=[x-r*y for x,y in zip(B[j],B[i])]
 return [row[-1] for row in B]
def tree(n,word):
 ds=[1+word.count(i) for i in range(n)]; leaves=[i for i in range(n) if ds[i]==1];heapify(leaves);e=[]
 for i in word:
  l=heappop(leaves);ds[i]-=1;e.append((i,l))
  if ds[i]==1:heappush(leaves,i)
 e.append((heappop(leaves),heappop(leaves)));g=[[] for _ in range(n)]
 for i,j in e:g[i].append(j);g[j].append(i)
 return g
ncase=0
for n in range(2,6):
 for word in product(range(n),repeat=n-2):
  g=tree(n,word);m=n-1
  for root in range(n):
   par={root:None};order=[root]
   for i in order:
    for j in g[i]:
     if j!=par[i]:par[j]=i;order.append(j)
   s={i:1 for i in order}
   for i in order[:0:-1]:s[par[i]]+=s[i]
   exact=F(2*m+2*sum((2*s[i]-1)**2 for i in order[1:]),len(g[root]))
   vertices=order[1:]; A=[[len(g[i])*(i==j)-(j in g[i]) for j in vertices] for i in vertices]
   H=dict(zip(vertices,lin(A,[len(g[i]) for i in vertices])));H[root]=0
   V=dict(zip(vertices,lin(A,[len(g[i])+2*sum(H[j] for j in g[i]) for i in vertices])));V[root]=0
   raw=1+F(sum(2*H[j]+V[j] for j in g[root]),len(g[root]))
   assert raw==exact;ncase+=1
print('tree rootings',ncase)
ncase=0
V=range(1,8)
bases=[I for I in combinations(V,3) if I[0]^I[1]^I[2]]
for counts in compositions(5,7):
 val=sum(6*counts[i-1]*counts[j-1]*counts[k-1] for (i,j,k) in bases)
 assert F(val,5**3)<F(6*len(bases),7**3)
 ncase+=1
print('matroid laws',ncase)
