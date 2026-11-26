"""Independent finite checks of four analytic and algebraic arguments. Python 3, standard library."""
from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial, isqrt, prod

def determinant(rows):
    matrix = [[Fraction(value) for value in row] for row in rows]
    det = Fraction(1)
    for i in range(len(matrix)):
        pivot = next((k for k in range(i,len(matrix)) if matrix[k][i]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != i:
            matrix[i],matrix[pivot] = matrix[pivot],matrix[i]
            det = -det
        factor = matrix[i][i]
        det *= factor
        for j in range(i+1,len(matrix)):
            scale = matrix[j][i]/factor
            for k in range(i+1,len(matrix)):
                matrix[j][k] -= scale*matrix[i][k]
    return det

for p in (2,3,5,7,11):
    for n in range(9):
        matrix = [[Fraction(1,1+p*(i+j)) for j in range(n+1)] for i in range(n+1)]
        exponent = 2*sum(k//(p**j) for k in range(1,n+1) for j in range(n+1))
        assert determinant(matrix).numerator == p**exponent

for n in range(1,9):
    for k in range(5):
        perm = sum(prod(1+k*(i==j) for i,j in enumerate(sigma)) for sigma in permutations(range(n)))
        assert perm == sum(comb(n,j)*factorial(n-j)*k**j for j in range(n+1))

def period(rad):
    a0=isqrt(rad)
    m, d, a=0,1,a0
    digits=[]
    while True:
        m=d*a-m
        d=(rad-m*m)//d
        a=(a0+m)//d
        digits.append(a)
        if a==2*a0:return digits

for rad,L,trace in ((133,16,5177198),(636,12,7011902)):
    digits=period(rad)
    assert len(digits)==L
    num0,num1,den0,den1=0,1,1,0
    sequence=[]
    for a in [isqrt(rad)]+digits*5:
        num0,num1=num1,a*num1+num0
        den0,den1=den1,a*den1+den0
        sequence.append(den1 if rad==133 else num1)
    assert all(sequence[j+2*L]==trace*sequence[j+L]-sequence[j] for j in range(len(sequence)-2*L))

for n in range(1,15):
    for digits in product('01',repeat=n):
        word=''.join(digits)
        joined=''.join(word[:i] for i in range(n,0,-1))
        expected=n<=2 or (n==3 and word==word[::-1]) or len(set(word))==1
        assert (joined==joined[::-1])==expected
print('45 exact Hankel determinants, 40 permanents, 2 continued-fraction recurrences, and every binary word through length 14 passed.')
