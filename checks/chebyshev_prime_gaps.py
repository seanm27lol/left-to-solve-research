"""Exact interpolation and sign checks for the prime gap estimates."""
import sympy as sp


def positive_coefficients(expression, *variables):
    polynomial = sp.Poly(expression, *variables)
    assert polynomial.coeff_monomial(1) > 0
    assert min(polynomial.coeffs()) >= 0


def verify():
    x, h, u, v = sp.symbols("x h u v")
    denominator = h**2 * (h**2 - 1)**2
    nodes = ((0, -1, h), (-1, -1, h - 1), (-h, 1, h), (-h - 1, 1, h + 1))
    node_product = sp.prod(x - node for node, _, _ in nodes)
    numerator = (
        (6*h**2 - 2)*x**3
        + (9*h**3 + 10*h**2 - 3*h - 4)*x**2
        + (h**4 + 10*h**3 + 3*h**2 - 4*h - 2)*x
        - h*(h**2 - 1)**2
    )
    for node, target_num, target_den in nodes:
        assert sp.cancel(numerator.subs(x, node) / denominator - target_num / target_den) == 0
        factor = target_den * sp.diff(node_product, x).subs(x, node)
        sp.Poly(sp.cancel(denominator / factor), h, domain=sp.ZZ)

    # The negative-pair estimates use x>0 and h>=2. Their lower
    # polynomial vanishes at x=0, so factor out x before the sign test.
    lower = sp.cancel((numerator + denominator/h) / x)
    for expression in (lower, denominator*(x+h)**3 - numerator):
        positive_coefficients(expression.subs(h, 2+v), x, v)

    # Reflect the interpolant to get the positive pair. The last two
    # polynomials bound it below by both -(x+h)^3 and -2x^3.
    reflected = numerator.subs(x, -x-h)
    for expression in (-reflected, denominator*(x+h)**3 + reflected, 2*denominator*x**3 + reflected):
        positive_coefficients(expression.subs(x, h+u).subs(h, 2+v), u, v)
    positive_coefficients((18*h**2*x**3*denominator + reflected).subs(x, h+u).subs(h, 2+v), u, v)
    assert sp.rem(8*(2*x*(2*x-3)*(2*x-1)+1), 4*x-3, x) == -1


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable the certificate assertions.")
    verify()
    print("Verified both prime gap interpolants, the denominator and sign bounds, and the mixed-twin remainder.")
