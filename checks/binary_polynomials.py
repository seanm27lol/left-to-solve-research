from math import comb
from functools import reduce
from operator import xor
def divide(a,b):
 q=0
 while a and a.bit_length()>=b.bit_length():
  s=a.bit_length()-b.bit_length()
  q ^= 1<<s
  a ^= b<<s
 return q,a
def mul(a,b):
 return reduce(xor, (a<<j for j in range(b.bit_length()) if b>>j&1),0)
def power(p,e):
 a=1
 while e:
  if e&1:a=mul(a,p)
  e>>=1;p=mul(p,p)
 return a
def fibbit(n):
 f,g=0,1;w=0
 for k in range(3*2**n):
  w|=((f>>n)&1)<<k
  f,g=g,(f+g)%(2**(n+1))
 return w
for n in range(3,12):
 L=2**(n-2); b=[(pow(3,k,2**(n+1))>>n)&1 for k in range(4*L)]
 full=sum(t<<k for k,t in enumerate(b))
 for poly,exp in [(full,3*L-1),(full%2**(2*L),L-1)]:
  q,r=divide(poly,power(3,exp)); assert not r and q.bit_count()%2
for n in range(1,12):
 w=fibbit(n);q,r=divide(w,power(9,2**(n-1)-1));assert not r and q.bit_count()%2==0
 if n>=2: assert divide(q,7)[1]
a=[0]
for n in range(1,130):
 a.append(1-sum(comb(n,i)*((-4)**(i//2))*a[n-i] for i in range(2,n+1,2)))
 assert a[n]%4==1 and (a[n]-2*(2**n-4**n))%5==0
print('Power-of-three bit multiplicities: n=3..11. Fibonacci: n=1..11. A380056: n=1..129.')
print('Fibonacci n=2 factor after G:',bin(divide(fibbit(2),9)[0]))
