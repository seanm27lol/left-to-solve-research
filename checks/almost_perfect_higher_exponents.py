"""Verify the four boundary constants with exact symbolic arithmetic."""
import sympy as s

def verify():
    A, B, z = s.symbols('A B z')
    T = A+B
    def H(x, indicator):
        return 1+x*z+2*x**2*z**2+(4-indicator)*x**3*z**3+(8-4*indicator)*x**4*z**4
    for i in (0, 1):
        for j in (0, 1):
            difference = s.Poly(H(T,0)-H(A,i)*H(B,j), z)
            assert difference.nth(0)==difference.nth(1)==0
            w2,w3,w4 = [difference.nth(k) for k in (2,3,4)]
            assert w2 == 3*A*B
            numerator = s.Poly((2*T**2+w2)*w2**2-(w4+T*w3)*w2+w3**2, A, B)
            assert all(c>0 for c in numerator.coeffs())

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    verify()
    print('Verified all four arbitrary-exponent boundary constants.')
