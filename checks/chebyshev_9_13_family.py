"""Verify the all-parameter exclusion for the Chebyshev family (9,13,562).

Run with Python 3.8 or later, without -O. The only imports are from the
standard library. The accompanying note explains why the enumeration is finite.
"""
from itertools import combinations, product
from math import isqrt, prod


LARGE_PRIMES = (1666729, 2236651)


def overlap_polynomials(g):
    p = ((32877*g - 22962)*g + 3136)*g + 16
    f = ((((3846609*g - 3048201)*g + 653495)*g - 53431)*g + 1392)*g
    return p, f


def check_identities():
    constant = 16 * 27 * prod(LARGE_PRIMES)
    # The first identity has degree at most seven. Eight evaluations suffice.
    for g in range(8):
        p, f = overlap_polynomials(g)
        u = (((221609361437164935*g - 173715183736960086)*g
              + 38473896617588464)*g - 3263658701032482)*g + 100653059283633
        v = (-1894097106300555*g + 1306667654424393)*g - 189245297914478
        assert u*p + v*f == constant
        d, e = 9*g-1, 13*g-1
        a8 = 32877*g**3 - 19871*g*g + 1568*g + 8  # 8abc
        b4 = 3091*g*g - 1568*g - 4  # 4(ab+bc+ac)
        assert b4*2*d*e-a8*(d+e) == 8
        assert a8*d*e-8 == f and a8-b4+4 == p

        # These identities are at most linear in S, quadratic in each of k and w.
        for S, k, w in product(range(2), range(3), range(3)):
            r8 = a8-2*b4+8*S-8
            j8 = f-117*g*g*r8
            assert j8 == g*(-936*S*g + 103127*g*g - 54367*g + 1392)
            t = (936*w*S - (103127*w-32877*k)*g - (26053*k-54367*w))
            E = 32877*k*k - 653495*k*w + 162864*w*w
            F = k*(53431*w-26053*k)
            assert (117*w*g*g+k)*t-E*g-F == 117*w*(k*r8-w*j8)
    assert [g for g in range(0,8,2) if (32877*g*g-19871*g+1568)%8==0] == [0]


def common_roots(m):
    return [g for g in range(m) if all(x%m == 0 for x in overlap_polynomials(g))]


def check_residues():
    assert all(all(p%d for d in range(2,isqrt(p)+1)) for p in LARGE_PRIMES)
    unique_roots = {3:2, 9:8, 27:17, 1666729:868893, 2236651:918968}
    for modulus,root in unique_roots.items():
        assert common_roots(modulus) == [root]
    return unique_roots


def verify():
    check_identities()
    roots = check_residues()
    classes = g_count = discriminants = squares = 0
    for exponent in range(4):
        for count in range(3):
            for large_factors in combinations(LARGE_PRIMES,count):
                moduli = list(large_factors)
                if exponent:
                    moduli.append(3**exponent)
                w = 4*prod(moduli)
                first, step = 0, 8
                for m in moduli:
                    first += step * ((roots[m]-first)*pow(step,-1,m)%m)
                    step *= m
                assert 0 <= first < step and step == 2*w and first%8 == 0
                assert all(first%m == roots[m] for m in moduli)
                classes += 1
                for g in range(first or step,9000*w,step):
                    g_count += 1
                    aa = 32877*g-26053
                    bb0 = (-653495*g+53431)*w
                    cc0 = 162864*g*w*w
                    cc1 = 117*w*g*g
                    for z in range(1,(9000*w-1)//g + 1):
                        discriminants += 1
                        delta = (bb0+z)**2 - 4*aa*(cc0+cc1*z)
                        if delta >= 0 and isqrt(delta)**2 == delta:
                            squares += 1
    results = classes, g_count, discriminants, squares
    assert results == (16,71999,1093956,0), results
    print('CRT classes:', classes)
    print('Parameters, counted per class:', g_count)
    print('Discriminants:', discriminants)
    print('Square discriminants:', squares)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    verify()
