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
    assert pow(2, 8, 17) == 1
    for level in (1, 7):
        n = pow(2, level, 17)
        for y in range(17):
            for z in range(17):
                assert (3*(n - 1)*phi(y)*phi(z) - n*y*y*z*z + 1) % 17 != 0


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    verify()
    print("Norm identity verified. No residue pair survives at either level modulo 17.")
