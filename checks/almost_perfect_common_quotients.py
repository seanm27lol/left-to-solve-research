"""Verify the common-quotient elimination identities over the integers."""
import sympy as sp


def verify():
    a, z, n = sp.symbols("a z N")

    def phi(x):
        return x*x + x + 1

    quartic = n**4 - 5*n**3 + 15*n**2 - 5*n + 1
    decic = n**10 + 4*n**9 + 6*n**8 - 30*n**7 + 39*n**5 - 30*n**3 + 6*n**2 + 4*n + 1
    equal = (1-a**3)*phi(a)**3 - a**3*(a**3-1)
    assert sp.resultant(n*a**3-1, equal, a) == sp.expand(-(n-1)**3*(n+1)**2*quartic)

    def reduce_z(expression):
        return sp.rem(sp.expand(expression), phi(z), z)

    quartic_source = phi(a)**2 - a*phi(a) + a*a
    assert sp.resultant(n*a**3-1, quartic_source, a) == sp.expand(quartic)
    assert sp.expand(phi(a)**3+a**3-(a+1)**2*quartic_source) == 0

    distinct = phi(a)*phi(a*z)*phi(a*z*z)
    assert reduce_z(distinct - (a**3-1)**2) == 0
    mixed = reduce_z((z-a**3)*phi(a)**2*phi(a*z) - a**3*(a**3-1))
    first = reduce_z(sp.resultant(n*a**3-z, mixed, a))
    second = sp.resultant(first, phi(z), z)
    assert second == sp.expand(phi(-n)*phi(n)**3*decic)
    quotient, remainder = sp.div(mixed, (a**3-1)*(a+1), a)
    assert remainder == 0
    term = a**5*(z+1)+a**4+a**3*(z+1)-a*a*z+a-z
    assert sp.expand(quotient-term) == 0
    reduced = reduce_z(sp.resultant(n*a**3-z, term, a))
    assert sp.resultant(reduced, phi(z), z) == decic
    print("Verified equal, distinct and mixed residue eliminants.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    verify()
