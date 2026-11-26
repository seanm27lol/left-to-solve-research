import numpy as np
from math import sqrt,cos,pi
from scipy.linalg import eigh_tridiagonal
rng=np.random.default_rng(334087)
worst=-np.inf; count=0; bad=0
for n in range(2,25):
 for rep in range(16):
  rank=1+rep%n
  R=rng.normal(size=(n,rank))*np.exp(rng.uniform(-4,4,size=(n,1)))
  if rep%4==0:R[::3]=0
  A=R@R.T
  A/=np.trace(A)
  for k in range(1,n+1):
   eig=np.linalg.eigvalsh(A-k*np.diag(np.diag(A)))[::-1]
   for m in range(1,n//k+1):
    v=eig[m-1:n-m*(k-1)].sum()
    worst=max(worst,v); bad+=v>1e-12; count+=1
print('trimmed blocks:',count,'max normalized sum',worst,'above tol',bad)
assert bad==0
nblock=0;stress=0
for n in range(4,101):
 for r in range(2,n//2+1):
  w=np.sqrt(np.arange(1,r)*(n-np.arange(1,r)))
  eig=eigh_tridiagonal(np.zeros(r),w,eigvals_only=True)
  largest=eig[-1]
  U=2*w[-1]*cos(pi/(r+1))
  for L in {2,r,max(2,int(sqrt(r)))}:
   low=2*w[r-L]*cos(pi/(L+1));assert low-1e-11<=largest<=U+1e-11
  nblock+=1
print('Kac principal blocks checked',nblock)
