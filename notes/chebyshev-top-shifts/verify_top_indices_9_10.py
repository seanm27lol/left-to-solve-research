"""Check the top index exclusions K=9,10,12 with Python's standard library."""
from fractions import Fraction
from itertools import product, combinations
from math import gcd, isqrt, prod
from verify_top_exception import evaluate, monic_gcd


def lcm(a, b):
    return a // gcd(a, b) * b


def ceil(x):
    return -(-x.numerator // x.denominator)


def check_indices():
    results = []
    for K in (9, 10, 12):
        for J in range(K+1, (3*K+1)//2):
            if gcd(K, J) > 1:
                continue
            D = (J-K)**2
            W = 2*J-K
            g0 = 2*ceil(Fraction(506, 2*K-J))
            lo = Fraction(D*J*J, 4*(3*K-J))
            hi = (Fraction(D*K*J, 2*W)
                  + (2*K*J + Fraction(D*(2*J*J-K*K), 2*W*W))/g0
                  + Fraction(D, W*g0*g0))
            period = lcm(lcm(2, K*J), D)
            for top_z in range(int(lo)+1, ceil(hi)):
                for g in range(0, period, 2):
                    b, c = K*g+1, J*g+1
                    if gcd(b*c, period) > 1:
                        continue
                    if (top_z*c*c+D*J) % K or (top_z*b*b+D*K) % J:
                        continue
                    if (top_z*b*c-K*J*(K+J)-2*K*K*J*J*g) % D:
                        continue
                    results.append((K, J, top_z, period, g))
    expected = [(10,13,23,1170,g) for g in (30,66,300,966)]
    assert results == expected, results


ROOTS = ((5,2), (193139,62582), (1510363823,317669003))
P = (4,-3956,-66013,17940)
F = (-920,-100342,-3443859,-38308140,10494900)
U = (750637786674080,25049195928215469,411000919835152140,-111293654758497900)
V = (-22102458180582,-708175480015043,190245563689740)


def identities():
    for p, root in ROOTS:
        assert all(p % d for d in range(2, isqrt(p)+1))
        assert monic_gcd(P,F,p) == ((-root)%p, 1)
    for t in range(7):  # All polynomial identities below have degree at most six.
        g = 3*t
        X = 8970*t**3 - 33271*t**2 - 989*t + 1
        Z = 529*t**2 - 1978*t + 1
        b, c = 10*g+1, 13*g+1
        assert X*(b+c)-Z*b*c == 1
        assert evaluate(P,t) == 2*X+Z+1
        assert t*evaluate(F,t) == b*c*X-1
        assert evaluate(U,t)*evaluate(P,t)+evaluate(V,t)*evaluate(F,t) == 16*prod(p for p, _ in ROOTS)
    for t in range(0,16,2):
        assert evaluate(P,t) % (16 if t%4==2 else 8) == (8 if t%4==2 else 4)
    for g,h,w,S in product(range(7),range(3),range(3),range(2)):
        X9 = 2990*g**3-33271*g**2-2967*g+9
        Z9 = 529*g**2-5934*g+9
        R9 = X9+Z9+9*(S-1)
        J9 = (10*g+1)*(13*g+1)*X9-9-130*g*g*R9
        assert R9 == 2990*g**3-32742*g**2-8901*g+9*S+9
        assert J9 == -1170*S*g*g+9177*g**3-101512*g*g-2760*g
        z = 1170*w*S+(2990*h-9177*w)*g-32742*h+101512*w
        E = 2990*h*h+1147953*h*w-358800*w*w
        F0 = -32742*h*h+100342*h*w
        assert (130*w*g*g+h)*z-E*g-F0 == 130*w*(h*R9-w*J9)


def classes():
    for size in range(4):
        for selected in combinations(ROOTS,size):
            H = prod(p for p,_ in selected)
            for initial, w2 in product((30,66,300,966),(4,8,16,32,64)):
                g, step = initial, 1170
                for p, root in selected:
                    if step % p == 0:
                        if (3*root-g) % p:
                            break
                    else:
                        g += step*((3*root-g)*pow(step,-1,p)%p)
                        step *= p
                else:
                    assert 0<=g<step
                    if g<146:
                        g+=step
                    yield w2*H,g,step


def verify_discriminants():
    classes_seen = parameters = checks = 0
    for w,first,step in classes():
        classes_seen += 1
        for g in range(first,80000*w,step):
            parameters += 1
            A = 2990*g-32742
            B0 = (1147953*g+100342)*w
            C0 = -358800*g*w*w
            Cz = -130*w*g*g
            for z in range(1,(80000*w-1)//g+1):
                checks += 1
                delta = (B0-z)**2-4*A*(C0+Cz*z)
                assert delta < 0 or isqrt(delta)**2 != delta, (w,g,z)
    assert (classes_seen,parameters,checks)==(120,474794,5448422)
    print(f"K=9,10,12 excluded. {classes_seen} classes, {parameters} parameters "
          f"with multiplicity, {checks} discriminants, zero squares.")


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("Run without -O to enable the certificate assertions.")
    check_indices()
    identities()
    verify_discriminants()
