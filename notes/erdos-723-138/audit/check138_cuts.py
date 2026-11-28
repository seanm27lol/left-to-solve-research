"""Independent enumeration for the 138-line order-twelve connectivity lemma."""
from fractions import Fraction
from itertools import product
from collections import Counter

def solve_high(weight,caps,budget):
    # First coordinate, n3, has small weight; deduce it from all later coordinates.
    for tail in product(*(range(min(caps[i],budget//weight[i])+1) for i in range(1,5))):
        remaining=budget-sum(w*t for w,t in zip(weight[1:],tail))
        if 0<=remaining<=caps[0]*weight[0] and remaining%weight[0]==0:
            yield [remaining//weight[0],*tail]

def profiles():
    for v in solve_high([3,8,15,24,35],[157]*5,95):
        mass=247-sum(i*t for i,t in enumerate(v,3))
        if mass>=0 and mass%2==0 and mass//2+sum(v)<=157:
            yield [mass//2,*v]

def local(h,t):
    caps=[n-(index==t) for index,n in enumerate(h,2)]
    for v in solve_high([1,2,3,4,5],caps[1:],t*(7-t)):
        lights=12*t-sum(v)
        if 0<=lights<=caps[0]:
            yield [lights,*v]

def qmax(y,u,maxc):
    # Integer maximum of c*(y-u-c) for 0<=c<=maxc.
    a=min(maxc,max(0,(y-u)//2))
    b=min(maxc,a+1)
    return max(c*(y-u-c) for c in (a,b))

counts=Counter(); ratios=[]; slacks=[]
for h in profiles():
    counts['hist']+=1
    active=[i for i,n in enumerate(h) if n]
    options={i:list(local(h,i+2)) for i in active}
    if any(not p for p in options.values()):continue
    if any(h[i]*max(v[j] for v in options[i]) < h[j]*min(v[i] for v in options[j]) for i in active for j in active):continue
    m=h[0]
    ext=max(m*(24-max(v[0] for v in options[0])),sum(h[i]*min(v[0] for v in options[i]) for i in active if i))
    ratio=Fraction(4*m*m,26*m-ext)
    if ratio>19:continue
    counts['kept']+=1;ratios.append(ratio)
    low=min(v[0] for v in options[0]); assert low>4 and m>36
    hi={i:max(v[0] for v in options[i]) for i in active if i}
    for n in range(low+1,m//2+1):
        bound=min(10*n*u+sum(h[i]*qmax(y,i*u,min(n,y)) for i,y in hi.items()) for u in range(-20,51))
        slacks.append(4*n*(m-n)-bound)
print(counts,min(ratios),len(slacks),min(slacks))
assert (counts['hist'],counts['kept'],min(ratios),len(slacks),min(slacks))==(48,39,Fraction(529,29),1270,796)
