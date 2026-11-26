"""Independent finite checks of four analytic and algebraic arguments. Python 3, standard library."""
from fractions import Fraction
from itertools import combinations, permutations, product
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


def valuation(value, p):
    value = abs(value)
    assert value > 0
    exponent = 0
    while value % p == 0:
        value //= p
        exponent += 1
    return exponent


entry_checks = profiles = 0
for offset, step in [(2, 1), (1, 2), (2, 3), (3, 4), (5, 6), (7, 10)]:
    prime_factors = [p for p in (2, 3, 5) if step % p == 0]
    for size in range(1, 6):
        indices = range(size)
        matrix = [[Fraction(1, offset + step * (i + j)) for j in indices] for i in indices]
        det = determinant(matrix)
        for i, j in product(indices, repeat=2):
            cofactor = [[matrix[r][c] for c in indices if c != i] for r in indices if r != j]
            inverse_entry = (-1)**(i+j) * determinant(cofactor) / det
            b = prod(factorial(k) * factorial(size-1-k) for k in (i, j))
            denominator = step**(2*size-2) * prod(p**valuation(b, p) for p in prime_factors)
            assert inverse_entry.denominator == denominator
            entry_checks += 1
        for p in prime_factors:
            previous = 0
            for k in range(1, size+1):
                subsets = list(combinations(indices, k))
                minors = [determinant([[matrix[r][c] for c in cols] for r in rows])
                          for rows, cols in product(subsets, repeat=2)]
                minimum = min(valuation(x.numerator, p) - valuation(x.denominator, p) for x in minors)
                assert minimum - previous == 2*(k-1)*valuation(step, p) + 2*valuation(factorial(k-1), p)
                previous = minimum
            profiles += 1
print(f"Verified {entry_checks} inverse denominators and {profiles} local Smith profiles by exact minors.")
