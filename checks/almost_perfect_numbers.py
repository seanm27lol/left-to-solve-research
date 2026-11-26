"""Exact finite prime-support sieve for 2^a * p^(2e) * q^(2f)."""
from math import isqrt
from sympy import primerange

def verified_even_power(n, p):
    if n < p*p:
        return False
    while n % (p*p) == 0:
        n //= p*p
    return n == 1

def solve_small_coordinate(p, q, t, defect, constant):
    power = p*p
    found = set()
    while defect * power < 2*t*q:
        numerator = t*p*power - constant
        denominator = defect*power - t*q
        assert numerator > 0
        if denominator > 0 and numerator % denominator == 0:
            candidate = numerator // denominator
            if verified_even_power(candidate,q):
                found.add(power*candidate)
        power *= p*p
    return found

def sieve(a):
    t = 2**(a+1)-1
    bound = t*(t+1)
    pairs = 0
    found = set()
    for p in primerange(t+2, t+2+isqrt(bound-1)):
        qmax = t+1+(bound-1)//(p-t-1)
        for q in primerange(p+1, qmax+1):
            pairs += 1
            defect = bound-(p-t-1)*(q-t-1)
            constant = t+(p-1)*(q-1)
            found |= solve_small_coordinate(p,q,t,defect,constant)
            found |= solve_small_coordinate(q,p,t,defect,constant)
    return pairs, sorted(found)

if __name__ == '__main__':
    import sys
    for a in range(int(sys.argv[1])+1):
        print(a,*sieve(a),flush=True)
