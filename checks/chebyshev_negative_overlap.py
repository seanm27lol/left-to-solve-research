"""Check exact polynomial identities and the complete modulo-three cover."""
from fractions import Fraction
from itertools import product
import sympy as sp


def check_identities():
    d, e, v, j, k = sp.symbols("d e v j k")
    m, u, b, c = j+k, j*k, 2*d-j, 2*d-k
    a = e+v
    n = d*e*a*b*c
    cofactor = d*e*(a*b+b*c+c*a)-a*b*c*(d+e)
    assert sp.expand(cofactor-((m*d-u)*e*a-v*d*b*c)) == 0
    rearranged = d*((4*v-m)*d**2-m*(e*a-d**2)-2*v*m*d+v*u)+u*e*a+1
    assert sp.expand(rearranged+cofactor-1) == 0
    C, S = (j+2)*(k+2), m+4
    assert sp.expand((C+1-(v-1)*S).subs(j,j)) == sp.expand(j*k+2*m+5-(v-1)*S)
    assert sp.expand(S**2-4*C-(j-k)**2) == 0
    C = 4*v*(v-1)-1
    assert sp.expand((v-1)*C-1-v*(2*v-1)*(2*v-3)) == 0
    assert sp.expand(v*C**2-4*v-v*(2*v-3)*(2*v+1)*(2*v-1)**2) == 0
    assert Fraction(102, 101)*Fraction(401, 25)**3/2 < 2100


def check_mod_three():
    for branch in (2, 6):
        tested = 0
        permitted = 0
        # At branch 6 the division by three in v uses w modulo nine.
        for w in range(3 if branch == 2 else 9):
            if branch == 2:
                v = 2*w*w
                j, k = 2*v-3+2*w, 2*v-3-2*w
            else:
                if w%3 == 0:
                    continue
                v = 2*(w*w-1)//3
                j, k = 2*v-1+2*w, 2*v-1-2*w
            for d, e in product((1, 2), repeat=2):
                signed = ((e+v)%3, (2*d-j)%3, (2*d-k)%3, (-d)%3, (-e)%3)
                tested += 1
                if 0 not in signed and signed.count(2) == 2:
                    permitted += 1
        assert tested == (12 if branch == 2 else 24)
        assert permitted == 0


def check_small_triangular_gaps():
    for w, expected in ((10, 529), (11, 331)):
        v = w*(w+1)
        j, k = 2*w*w+4*w-1, 2*w*w-3
        W = v*(2*v-3)*(2*v+1)*(2*v-1)**2
        checked = 0
        for divisor in sp.divisors(W):
            d = divisor-1
            if d%2 == 0 or d <= j+v or d < 7 or d >= (16*v+4)**3:
                continue
            checked += 1
            assert (v*d*(2*d-j)*(2*d-k)+1) % ((j+k)*d-j*k)
        assert checked == expected
    v=sp.symbols("v")
    assert sp.expand((4*v-3)**2*v-(4*v-1)**2*(v-1)) == 1
    F = Fraction
    assert (3-F("1.005")**2-F("2.005")/400-F(1,10000))/F("2.01") > F("0.98")
    assert (F("3.005")-F("0.98"))/2 < F("1.02")
    assert F("16.04")**3/(F("0.99")*F("7.96")) < 530
    assert (4*150-3)*F("0.98") > 530


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    check_identities()
    check_mod_three()
    check_small_triangular_gaps()
    print("Verified the gap identities, both eliminated residue families and the uniform constant.")
