# The two largest odd primes in the three-prime square case

Let $N=2^t$ with $t\ge1$, and suppose three distinct odd primes $p<r<s$ satisfy
$$
(N-1)\Phi(p)\Phi(r)\Phi(s)=N(prs)^2-1,\qquad \Phi(x)=x^2+x+1.
$$
For $h=s-r$, we have
$$
N<r<(h^4+h^2+1)^2.
$$
Moreover, for every $t\ge21$ one has $s-r\ge26$. The argument also applies to distinct odd integers $p<r<s$ greater than one. It addresses the top two bases even when the smallest base is far from them.

## A polynomial identity

The reciprocal product gives
$$1+1/p<\prod_{x=p,r,s}(1+1/x+1/x^2)<N/(N-1),$$
so $p>N$ by oddness. Set $A=Np^2$, $B=(N-1)\Phi(p)$, $G=h^4+h^2+1$ and $W=G^2$. We have the exact identity $A r^2s^2-B\Phi(r)\Phi(s)=1$. In particular its two multiplying factors are coprime.

Write $A_0(X)=a_3X^3+a_2X^2+a_1X+a_0$, $B_0(X)=b_3X^3+b_2X^2+b_1X+b_0$, with the following coefficients.

| Degree | $a_i$ | $b_i$ |
|---|---|---|
| 3 | $2(h^4-3h^2-1)$ | $a_3$ |
| 2 | $(h+1)(3h^4+2h^3-11h^2+2h-5)$ | $3h^5+h^4-9h^3+3h^2-3h-1$ |
| 1 | $(h+1)(h^5+4h^4+3h^3-12h^2+h-6)$ | $(h+1)(h+2)(h^2-h+1)^2$ |
| 0 | $5h^5+6h^4-5h^3-2h^2-3h-4$ | $-(h^2-h+1)^2(h^2+h+1)$ |

Expansion gives
$$
A_0(X)X^2(X+h)^2-B_0(X)\Phi(X)\Phi(X+h)=W .
$$
One can obtain the cubics by the polynomial extended Euclidean algorithm over $\mathbb Q(h)$. Only the displayed identity and explicit coefficients are needed for the proof.

Evaluate at $r$, subtract $W$ times the original identity, and use coprimality. This yields an integer
$$
k=\frac{WA-A_0(r)}{\Phi(r)\Phi(s)}.
$$
It is odd. Indeed $A$ is even, both cyclotomic factors are odd, and $A_0(r)$ is odd since its coefficients in degrees $3,2,1,0$ are respectively even, odd, even, even at even $h$.

When $r\ge h\ge2$ the coefficient formulas give
$$0<A_0(r)<Wr^3,\qquad A_0(r)<9h^4r^3.$$
For a short exact sign certificate substitute $h=2+v$ and $r=h+u$. Each of $A_0(r)$, $Wr^3-A_0(r)$ and $9h^4r^3-A_0(r)$ has positive constant and nonnegative coefficients in $u,v$. The accompanying script checks every coefficient. Since $0<A=Np^2<r^3$ and $\Phi(r)\Phi(s)>r^4$, we obtain $0<|k|<W/r$. Thus $r<W$. If $r<h$ the bound is immediate from $h<W$.

If $r\ge9h^4$, we additionally have $k>0$. Otherwise the nonzero negative residual would give $r^4<\Phi(r)\Phi(s)\le A_0(r)-WA<9h^4r^3$. In the range $r\ge9h^4$ the proof also gives $r^4<W Np^2$.

## An exhaustive check of the small gaps

For $2\le h\le24$ and $t\ge21$, write $L=2^{21}$. Then $L<r$, so $r>h$ and the preceding estimates apply. For each even $h$, take every odd $k$ with $|k|\le\lfloor(W-1)/(L+1)\rfloor$. If $L\ge9h^4$ only positive $k$ remain. The condition $L\mid A$ gives
$$A_0(r)+k\Phi(r)\Phi(r+h)\equiv0\pmod L.$$
Compute all odd residues $r$ satisfying this congruence by lifting both representatives at each binary digit, starting at modulus 2. Equivalently the unit $\Phi(r)\Phi(r+h)$ fixes $k$ modulo each new power of two. For each resulting pair enumerate every $L<r<W/|k|$ in the residue class. Check $W\mid A_0(r)+k\Phi(r)\Phi(r+h)$ using ordinary integer arithmetic.

| $h$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 | 24 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Representatives before the division by $W$ | 0 | 0 | 0 | 29 | 223 | 1,106 | 4,216 | 13,346 | 36,691 | 90,317 | 307,225 | 652,570 |
| Divisible by $W$ | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

This excludes every gap through 24 at all levels $t\ge21$ and places no independent cutoff on prime sizes. Run the accompanying Python verifier with SymPy installed.
