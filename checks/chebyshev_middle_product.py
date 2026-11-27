"""Verify the polynomial identity in the joint middle/top gap estimate."""
import sympy as sp

def main():
    m,u,v,d=sp.symbols("m u v d")
    M=m*d-u
    Q=d*(4*d**2-2*m*d+u)
    S=v*Q+1+(v-1)*M
    residual=m**3*S-v*(4*m*d-2*m**2+8*u)*M**2
    expected=m**3*(v-1)*M+m**3-v*u*(m**2-4*u)*(3*m*d-2*u)
    assert sp.expand(residual-expected)==0
    print("Verified the joint gap identity.")

if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    main()
