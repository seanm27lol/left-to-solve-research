#!/usr/bin/env python3
"""Exact certificate: top shift index >=9, apart from (K,L,z)=(7,10,23).

Run with ordinary Python 3.8+.  Uses no third-party packages.
This is a finite residue/polynomial certificate for an unbounded-g theorem,
not a prime search up to a cutoff.  The input theorem v=a-e >=502 is external.
"""
from math import comb, gcd, isqrt
from fractions import Fraction

if not __debug__:
    raise SystemExit('Run with assertions enabled (do not use python -O).')

# Polynomials use ascending coefficients.
def trim(a):
    a=list(a)
    while len(a)>1 and not a[-1]: a.pop()
    return a

def add(a,b):
    out=[0]*max(len(a),len(b))
    for i,x in enumerate(a): out[i]+=x
    for i,x in enumerate(b): out[i]+=x
    return trim(out)

def neg(a): return [-x for x in a]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return trim(out)

def scale(a,k): return trim([k*x for x in a])
def power(a,n):
    out=[1]
    for _ in range(n): out=mul(out,a)
    return out

def shift(a,h):
    out=[0]*len(a)
    for i,x in enumerate(a):
        for j in range(i+1): out[j]+=x*comb(i,j)*h**(i-j)
    return trim(out)

def evaluate(a,x):
    out=0
    for c in reversed(a): out=out*x+c
    return out

# K,L,g_min, strict lower bound on z, strict upper bound on z.
ROWS=[
    (3,4,506,0,2),
    (4,5,338,0,2),
    (5,6,254,1,3),
    (5,7,338,6,8),
    (6,7,204,0,5),
    (7,8,170,1,4),
    (7,9,204,6,13),
    (7,10,254,20,25),
    (8,9,146,1,5),
    (8,11,204,20,30),
]

# This list is exhaustive after 3b-2c>=3, which implies K<L<3K/2.
expected=[(K,L) for K in range(1,9) for L in range(K+1,(3*K+1)//2)
          if 2*L<3*K and gcd(K,L)==1]
assert [(r[0],r[1]) for r in ROWS]==expected

all_survivors=[]
gpoly=[0,1]
for K,L,g_min,lo,hi in ROWS:
    assert g_min%2==0
    assert (2*K-L)*g_min>=1012
    assert (2*K-L)*(g_min-2)<1012
    b=[1,K]; c=[1,L]; delta=(L-K)**2
    H=2*L-K
    lower_bound=Fraction(delta*L*L,4*(3*K-L))
    upper_bound=(Fraction(delta*K*L,2*H)+Fraction(2*K*L,g_min)
                 +Fraction(delta*(2*L*L-K*K),2*H*H*g_min)
                 +Fraction(delta,H*g_min*g_min))
    assert lo<=lower_bound and upper_bound<hi
    print('exact rational bounds',K,L,lower_bound,'< z <',upper_bound)
    bc=mul(b,c)
    # delta*X = z*g*b*c - E; E below.
    E=[-delta,K*L*(K+L),2*K*K*L*L]
    two_c_b=sub(scale(c,2),b)
    three_b_c=sub(scale(b,3),c)
    # Upper envelope X < (b^2 c^2+2)/(2(2c-b)).
    upper=sub(
        scale(mul(mul(gpoly,bc),two_c_b),2*hi),
        add(scale(add(power(bc,2),[2]),delta),scale(mul(two_c_b,E),2)))
    # Lower envelope X > (b c^3-4)/(4(3b-c)).
    lower=sub(
        add(scale(sub(mul(b,power(c,3)),[4]),delta),
            scale(mul(three_b_c,E),4)),
        scale(mul(mul(gpoly,bc),three_b_c),4*lo))
    for name,poly in [('lower',lower),('upper',upper)]:
        co=shift(poly,g_min)
        assert co[0]>0 and all(x>=0 for x in co), (K,L,name,co)
        print('positive polynomial',K,L,name,'at g =',g_min,'+ x:',co)
    period=2*K*L//gcd(2,K*L)
    survivors=[]
    for z in range(lo+1,hi):
        for gg in range(0,period,2):
            bb=K*gg+1; cc=L*gg+1
            if gcd(bb,L)!=1 or gcd(cc,K)!=1: continue
            if (z*cc*cc+delta*L)%K: continue
            if (z*bb*bb+delta*K)%L: continue
            survivors.append((z,gg))
    print('residue survivors',K,L,'modulus',period,':',survivors)
    all_survivors.extend((K,L,z,gg,period) for z,gg in survivors)
assert all_survivors==[(7,10,23,6,70),(7,10,23,26,70),
                       (7,10,23,48,70),(7,10,23,68,70)]

# Exceptional family and full top congruences.
# X(g)=(1610g^3-9409g^2-1167g+9)/9,
# Z(g)=(391g^2-2334g+9)/9.
# Z-integrality forces 3|g; for 3|g, g|(X-1) iff g=3 mod9.
for gg in range(9):
    znum=391*gg*gg-2334*gg+9
    assert (znum%9==0)==(gg%3==0)
classes=[gg for gg in range(630) if gg%9==3 and gg%70 in(6,26,48,68)]
assert classes==[48,138,426,516]
def exact_poly_div(a,b):
    a=trim([Fraction(x) for x in a]); b=trim([Fraction(x) for x in b])
    q=[Fraction(0)]*max(1,len(a)-len(b)+1)
    while a!=[0] and len(a)>=len(b):
        k=len(a)-len(b); coeff=a[-1]/b[-1]; q[k]+=coeff
        a=sub(a,[0]*k+scale(b,coeff))
    assert a==[0], ('nonzero polynomial remainder',a)
    assert all(x.denominator==1 for x in q), ('nonintegral quotient',q)
    return [int(x) for x in q]

# Symbolic integer-polynomial checks for EVERY g in each progression.
for g0 in classes:
    gg=[g0,630]; bb=add(scale(gg,7),[1]); cc=add(scale(gg,10),[1])
    xn=add(add(scale(power(gg,3),1610),scale(power(gg,2),-9409)),
           add(scale(gg,-1167),[9]))
    zn=add(scale(power(gg,2),391),add(scale(gg,-2334),[9]))
    assert all(x%9==0 for x in xn+zn)
    X=[x//9 for x in xn]; Z=[x//9 for x in zn]
    assert sub(mul(X,add(bb,cc)),mul(Z,mul(bb,cc)))==[1]
    exact_poly_div(sub(X,[1]),gg)
    q1=exact_poly_div(sub(mul(cc,X),[1]),mul(bb,sub(bb,[1])))
    q2=exact_poly_div(sub(mul(bb,X),[1]),mul(cc,sub(cc,[1])))
    print('exceptional progression',g0,'mod630; integer quotient polynomials:',q1,q2)

def is_prime_trial(n):
    if n<2: return False
    if n%2==0: return n==2
    return all(n%p for p in range(3,isqrt(n)+1,2))

gg=1776; bb=7*gg+1; cc=10*gg+1
X=(1610*gg**3-9409*gg**2-1167*gg+9)//9
Z=(391*gg**2-2334*gg+9)//9
assert (bb,cc,X,Z)==(12433,17761,998804996977,136570849)
assert is_prime_trial(bb) and is_prime_trial(cc) and is_prime_trial(X)
assert X*(bb+cc)-Z*bb*cc==1
assert (cc*X-1)%(bb*(bb-1))==0
assert (bb*X-1)%(cc*(cc-1))==0
print('Top-pair near miss:',gg,bb,cc,X,Z,'; X is prime, so NOT a full candidate.')
print('PASS: all K <=8 eliminated except K=7,L=10,z=23 in four progressions mod630.')
