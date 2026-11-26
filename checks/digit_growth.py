"""Exact rational bracket for the asymptotic constant of OEIS A379181."""
from fractions import Fraction
from itertools import product
from collections import Counter

def critical_polynomial(t):
    return 5*t**22+4*t**19+3*t**16+2*t**13+t**10-t**4-2*t-7

def numerator(t):
    return 3*t**5+sum(t**i for i in (6,9,15,18,21,24,27))

low, high = Fraction(9,10), Fraction(1)
assert critical_polynomial(low) < 0 < critical_polynomial(high)
for _ in range(60):
    midpoint=(low+high)/2
    if critical_polynomial(midpoint)>0:
        high=midpoint
    else:
        low=midpoint
assert Fraction('9.82786850121986167')<numerator(low)/high**12
assert numerator(high)/low**12<Fraction('9.82786850121986171')
print('9.82786850121986167 < lambda < 9.82786850121986171')

for n,expected in enumerate((10,9,9,237,1617),1):
    total=0
    for digits in product(range(10),repeat=n):
        if n>1 and digits[0]==0:
            continue
        q,r=divmod(sum(digits),n)
        if r:continue
        counts=Counter(digits)
        if all(counts[q]>counts[j] for j in range(10) if j!=q):
            total+=1
        if q==4:
            h=[5,5,6,9,5,15,18,21,24,27]
            assert sum(h[j] for j in digits)==12*n-5*(counts[4]-counts[0])-2*(counts[4]-counts[1])
    assert total==expected
print('Verified the reported first five OEIS terms and the integer change-of-measure identity.')
