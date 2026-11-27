# Independent proof for the smallest base 2N−1

No $N=2^t$, $t\ge21$, and odd integers $p<r<s$ with $p=2N-1$ satisfy $(N-1)\Phi(p)\Phi(r)\Phi(s)=N(prs)^2-1$ for $\Phi(x)=x^2+x+1$. Primality and finite checks of possible Mersenne primes are unnecessary.

Write $T=r+s$, $V=rs$, $J=(p+1)(T-1)-V$ and $h=r-p-1$. We only need the elementary envelope
$$
(N-1)prs\ge N(p-1)(r-1)(s-1).
$$
Indeed its integer difference exceeds $-(p-1)(r-1)(s-1)/(prs)^2>-1$, since the product of the infinite geometric sums exceeds the product of the finite sums $1+1/x+1/x^2$. The integer difference equals $(N-1)J$, so the odd integer $J$ is positive. Also $r<3p$. Otherwise, putting $q=N-1$ and using $p=2q+1$ and $s>r\ge3p>6q+1$, the upper product is at most $(1+1/(2q))(1+1/(6q))^2<1+1/q$, contradicting the envelope. Expanding gives a positive numerator $12q^2-14q-1$ in the inequality for $q\ge2$.

The assumed polynomial equation gives
$$
(p^2+1)V^2-(p^3-1)[V(T-1)+T^2+T+1]=2.\tag{1}
$$

## Small first gap

Let $H=r-p=h+1$. Suppose $H\le40$. Let $C=(p+1)p^2(p+H)^2$ and $F=(p^2+1)(p+H)^2-(p^3-1)(p+H+1)$. The component formulas at $s$ imply
$$
0<C/F-s<1/(s+1).
$$
In detail, with $C_0=C/2$, $F_0=F/2$, and $B_0=C_0-F_0$ the equation is $B_0\Phi(s)=C_0s^2-1$. Modulo $\Phi(s)$ it gives $C_0\equiv s$, so $D=(C_0-s)/\Phi(s)$ is integral. Then $F_0=D(s+1)+1>0$ using $F_0s^2=B_0(s+1)+1$, and $D$ is odd, hence positive. Finally $C_0=sF_0+D$, as claimed.

Polynomial division in $p$ gives $(H-1)^3 C=QF+R_2p^2+R_1p+R_0$ with $Q$ integral at all integer inputs, where
$$
Q=(H-1)^2p^2+(H-1)(H^2-H-2)p+H^3-4H^2+4H+3.
$$
The remainders are
$$
\begin{aligned}
R_2&=-2H^4+2H^3+4H^2-6H-6,\\
R_1&=-H^5-H^4+9H^3-3H^2-11H-5,\\
R_0&=-H^5+3H^4-H^3-3H^2-7H-3.
\end{aligned}
$$
For the even integers $2\le H\le40$, each is strictly negative, with $-R_2\le3H^4$ and $-R_0,-R_1\le5H^5$. Direct expansion gives $F\ge(H-1)p^3$. Hence
$$
0<Q-(H-1)^3s< H^3/p + (3H^4+10H^5/p)/[(H-1)p] <8H^3/p <1 .
$$
Here $2H/(H-1)\le4$, $10H/p<1/2$, and $p>2^{21}$. This is impossible for an integer.

## Larger first gap

We now have $h\ge41$. Write $L=2p^2+3p+3$, $a=p^3+2p^2+2p+3$ and $b=3p^3+4p^2+6p+3$. Substitute $V=(p+1)(T-1)-J$ in (1). This says $E(T)=0$ for the quadratic
$$
E(z)=Lz^2-(Ja+b)z+(p^2+1)J^2+aJ+L-2 .
$$
Dividing (1) by $V>0$ gives $J<[(p^2+p+2)/(p^2+1)](T-1)<2T$. At the root,
$$
aJ(T-1)=LT^2-bT+(p^2+1)J^2+L-2 .
$$
For $p>100$, $T>2p$, we have $L<2.04p^2$, $p^2+1<1.01p^2$, $T-1>.99T$, $a>p^3$, and $L-2<.001p^2T^2$. First substitute $J<2T$ on the right to obtain $J<7T/p$. Substituting this last bound into the same term then gives $J<3T/p$.

Since $h(s-p-1)=p(p+1)-J$ and $h<2p$, we have $T<4p+2+p(p+1)/h$. Consequently $J<12+6/p+3(p+1)/41<p/10$, as $p>1000$.

If $J=1$ or $3$ then $h(s-p-1)>p^2$, so arithmetic-geometric mean and parity give $T\ge4p+4$. But $E(4p+4)$ and $E'(4p+4)$ have positive coefficients in $p$ for both values, contradicting that $T$ is a root of an upward-opening quadratic. Hence $J\ge5$.

Set $X=(J+3)p/2+(J-5)/4$. With $p=10J+u$, $J=5+w$, each of the polynomials $16E(X+1/2)$, $-16E(X-1/2)$, $-E(J+2)$ has strictly positive constant and nonnegative coefficients in $u,w$. Thus the larger root of $E$ lies strictly within $1/2$ of $X$. The root $T$ is the larger one, since $T>J+2$ and $E(J+2)<0$. But $X$ is an integer or a half-integer, so the strict inequality and integrality of $T$ force $T=X$.

The polynomial $16E(X)$ has integer coefficients in $p,J$. At $p=-1$ it takes the value $2(21J^2+78J+77)$. As $p\equiv-1\pmod{128}$, its vanishing yields $21J^2+78J+77\equiv0\pmod{64}$. Multiplying by 21 and completing the square gives $(21J+39)^2\equiv32\pmod{64}$. This is impossible by the parity of the valuation of a square. The two gap cases exhaust the branch.

## Including the small levels and the quotient formulation

For $2\le t\le20$ it suffices to check the finitely many $p=2^{t+1}-1$ that pass exact trial division. Check all odd $p<r\le2p+1$, including composite values. The bound follows from $(r-p-1)(s-p-1)=p(p+1)-J\le p(p+1)$ and $s>r$. For $F>0$, the preceding component identity forces $s=\lfloor C/F\rfloor$. Substitution in the original equation eliminates every prefix with $s>r$. [Exact small-level check](../checks/almost_perfect_mersenne_low.py) · [Uniform polynomial check](../checks/almost_perfect_mersenne.py).

In the three-prime square case the component quotient is $D_p=(Nr^2s^2-p)/\Phi(p)$. Its second component identity gives $D_p p^2\equiv1-p\pmod{N-1}$. Since $p$ is a unit modulo $N-1$, divisibility of $D_p$ by $N-1$ would force $p\equiv1\pmod{N-1}$, and the ordering and abundance bounds would then give $p=2N-1$. Thus $N-1\nmid D_p$ at every $t\ge2$. [Smallest-prime bounds](almost-perfect-smallest-pair.md).
