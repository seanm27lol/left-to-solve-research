"""Verify the norm identity and exhaust the two residue problems modulo 17."""
import sympy as sp


def phi(x):
    return x**2 + x + 1


def verify():
    a, b, y, z = sp.symbols("A B y z")
    v = y*z
    trace = v + 2*y + 2*z + 1
    target = (3*b + 4)*a - 3*b
    form = ((4*a - 3*b)*v + 3*b)**2 - b*(4*a - 3*b)*trace**2
    assert sp.expand(4*phi(y)*phi(z) - 3*(v - 1)**2 - trace**2) == 0
    assert sp.expand(form - 4*target -
                     4*(4*a - 3*b)*(a*v**2 - b*phi(y)*phi(z) - 1)) == 0
    # Test the one-base discriminant obstruction and the original equation
    # independently for each claimed residue class.
    for prime, period, exponent, bases in (
        (17, 8, 1, (1,)), (17, 8, 7, (1,)), (29, 28, 2, (24, 25, 26)),
    ):
        assert pow(2, period, prime) == 1
        level = pow(2, exponent, prime)
        squares = {k*k % prime for k in range(prime)}
        assert -3*level % prime not in squares
        for x in bases:
            a = level*x*x
            b = (level - 1)*phi(x)
            assert ((3*b + 4)*a - 3*b) % prime == 0
            assert (a*a - 14*a + 1) % prime not in squares
            for y in range(prime):
                for z in range(prime):
                    assert (b*phi(y)*phi(z) - a*y*y*z*z + 1) % prime != 0


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    verify()
    print("Norm identity verified. All modulo-17 and modulo-29 exclusions passed.")
