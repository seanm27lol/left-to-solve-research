"""Verify the integer-polynomial identities and signs in the uniform Mersenne proof."""
import sympy as sp


def verify():
    p, H, J, z, u, w = sp.symbols("p H J z u w")
    V = (p+1)*(z-1)-J
    C = (p+1)*p**2*(p+H)**2
    F = (p**2+1)*(p+H)**2 - (p**3-1)*(p+H+1)
    assert sp.Poly(F-(H-1)*p**3,p,H).TC() >= 0
    assert min(sp.Poly(F-(H-1)*p**3,p,H).coeffs()) >= 0
    Q = (H-1)**2*p**2+(H-1)*(H**2-H-2)*p+H**3-4*H**2+4*H+3
    R = (-2*H**4+2*H**3+4*H**2-6*H-6, -H**5-H**4+9*H**3-3*H**2-11*H-5,
         -H**5+3*H**4-H**3-3*H**2-7*H-3)
    assert sp.expand((H-1)**3*C-Q*F-sum(v*p**(2-i) for i,v in enumerate(R))) == 0
    for h in range(2,41,2):
        r2,r1,r0 = [x.subs(H,h) for x in R]
        assert 0<-r2<=3*h**4 and 0<-r1<=5*h**5 and 0<-r0<=5*h**5

    L, a, b = 2*p**2+3*p+3, p**3+2*p**2+2*p+3, 3*p**3+4*p**2+6*p+3
    E = L*z**2-(J*a+b)*z+(p**2+1)*J**2+a*J+L-2
    assert sp.expand(E-((p**2+1)*V**2-(p**3-1)*(V*(z-1)+z**2+z+1)-2))==0
    for j in (1,3):
        for f in (E,sp.diff(E,z)):
            assert min(sp.Poly(f.subs({z:4*p+4,J:j}),p).all_coeffs())>0
    X=(J+3)*p/2+(J-5)/4
    half=sp.Rational(1,2)
    for f in (16*E.subs(z,X+half), -16*E.subs(z,X-half), -E.subs(z,J+2)):
        poly=sp.Poly(f.subs(p,10*J+u).subs(J,5+w),u,w)
        assert min(poly.coeffs())>0 and poly.TC()>0
    poly=sp.Poly(16*E.subs(z,X),p,J,domain=sp.ZZ)
    assert sp.expand(poly.as_expr().subs(p,-1)-2*(21*J**2+78*J+77))==0
    assert 32 not in {x*x%64 for x in range(64)}


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable assertions.")
    verify()
    print("All uniform Mersenne branch sign and congruence certificates passed.")
