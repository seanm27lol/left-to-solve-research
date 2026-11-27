# Excluding the tenth negative-shift ratio

Suppose $7\le d<e<a<b<c<2d$ are primes with the two negative signs at $d,e$. Put $n=abcde$, $g=\gcd(d+1,e+1)$ and $k=(d+1)/g$. Every Chebyshev candidate in this order satisfies **$k\ge 11$**.

The [small-ratio reduction](chebyshev-shift-bound.md) already excludes $k\le9$. For $k=10$ we rerun its exact small-prime-pair test through $d=10000$. There are 171 eligible negative pairs and 25 possible products of the three positive primes before testing their factorization. None factors as required. For $d>10000$, the same rational bounds and residue test give precisely $(\ell,h)=(11,39),(13,347),(17,1943)$. Thus $g\ge1001$ suffices below; the full proof covers every $g$.

Write $t=k\ell$, $s=k+\ell$, $m=(\ell-k)^2$, $d=kg-1$, $e=\ell g-1$. The negative-shift parametrization gives
$$
mA=m+g[ts-2t^2g+hde],\qquad mB=-m+shg^2-2g(h+ts)
$$
for $A=abc$, $B=ab+bc+ca$. Also $g\mid A-1$, $n\equiv1\pmod {12}$, and the five required shifts divide $n-1$. At $(13,347)$, the numerators for $A,B,(A-1)/g$ are integral polynomials with common denominator $9$. Enumerating $g\bmod81$ and the units $a,b,c\bmod9$, imposing integrality, the product and sum formulas, $n\equiv1\pmod3$, and $\gcd(p-1,9)\mid n-1$ at each positive prime $p$, gives no solutions. The verifier includes the complete residue loop.

## Bounds on the overlap

For either surviving shape let $S=a+b+c$, $R=(a-1)(b-1)(c-1)=A-B+S-1$, $L=\operatorname{lcm}(a-1,b-1,c-1)$, $w=R/L$, and $J=n-1-tg^2R$. Then $\kappa=J/L$ is integral, and $\lambda=\kappa/w=J/R$.

An integer dividing two positive shifts divides $2A-B+1$ and $n-1$. Clear denominators in these two polynomials and use the Euclidean algorithm over the rationals to certify integer Bézout combinations equal to the following constants. The verifier checks the Bézout coefficients are integers, their combination is the claimed constant, and the displayed factors are prime by trial division.

| $(\ell,h)$ | Bézout constant |
|---|---|
| $(11,39)$ | $2^5\cdot43\cdot179\cdot317\cdot163050143$ |
| $(17,1943)$ | $2^3\cdot5\cdot7^3\cdot432161\cdot7125293627$ |

Any prime $p$ dividing all three positive shifts satisfies $A=1,B=3,de=1\pmod p$ and $d+e=2\pmod p$ by $Bde-A(d+e)=1$. Hence $d=e=1\pmod p$ and $p\mid\ell(d-1)-k(e-1)=-2(\ell-k)$. If the sorted shift valuations are $u\le v\le z$, $v_p(w)=u+v$ while $v$ is at most the Bézout exponent. Thus $v_p(w)$ is at most that exponent when $p\nmid 2(\ell-k)$, and at most twice the exponent otherwise.

For primes above 13 in the table, the monic polynomial gcd over $\mathbb F_p$ is linear. Its root gives a unique necessary $g$ modulo $p$ whenever $p\mid w$. The exact gcd computation is part of the verifier. For $p=2,5,7$ in the support, we refine possible exponents using $w\mid 2A-B+1$. Indeed writing $u=a-1,v=b-1,z=c-1$ gives $2A-B+1=uv+uz+vz+2uvz$, and $w$ divides every pair product. Also $w\mid L^2\mid(n-1)^2$, with $v_p(w)\le v_p(n-1)$ when triple overlap is impossible. Compute these valuations up to $p^6$, $p^2$, $p^3$ for $p=2,5,7$, respectively. For each $q=p^j$ the period for $g$ is $q p^{v_p(m)}$, allowing exact division of the numerators modulo $q$. An undetermined higher valuation keeps the full Bézout upper bound. Integrality of $(A-1)/g$, the evenness of $g$, the local tests at $d,e$, and $v_2(w)\ge2$ give the class filters implemented in the certificate. Every small prime used here is less than $d$. Combining the allowed classes by CRT gives the complete enlarged cover used below.

## A positive integer remainder

Write $R=R_0+S$, $J=J_0-tg^2S$. The identity $J=\lambda R$ gives
$$
(tg^2+\lambda)S=J_0-\lambda R_0.
$$
For $\ell=11$ put $s_0=48$ and for $\ell=17$ put $s_0=54$. We have $s_0g<S<60g$ by $3B>(s_0g)^2$ and $c<2d$. Substitution at these endpoints gives $1<\lambda<2$. The verifier checks the needed bounds exactly: $3B-(s_0g)^2$, $J(60g)-R(60g)$ and $2R(s_0g)-J(s_0g)$ have positive constant and nonnegative coefficients after translation $g=1001+x$. Here the parenthesized argument of $J$ and $R$ is $S$.

Divide $J_0-\lambda R_0$ by $tg^2+\lambda$ as polynomials in $g$ and multiply the quotient and remainder by $mt$. Write the scaled quotient as $Q_1(g,\lambda)$, linear separately in both variables with integer coefficients, and the scaled remainder as $E(\lambda)g+F(\lambda)$. The integer $z=w(Q_1-mtS)$ then satisfies
$$
(twg^2+\kappa)z=-w^2[E(\lambda)g+F(\lambda)].
$$
The computer algebra in the certificate verifies the division, integrality and these coefficients.

| $(\ell,h)$ | $E(\lambda)$ | $F(\lambda)$ | $C$ |
|---|---|---|---:|
| $(11,39)$ | $4290\lambda^2-788079\lambda+256080$ | $-25838\lambda^2+74238\lambda$ | 15000 |
| $(17,1943)$ | $330310\lambda^2-4417967\lambda+885700$ | $-162722\lambda^2+278322\lambda$ | 55000 |

For clarity, put $E=e_2\lambda^2+e_1\lambda+e_0$ and $M=4|f_2|+2|f_1|$ for $F=f_2\lambda^2+f_1\lambda$. In both rows $E<4e_2+e_1+e_0<0$ and $1001(4e_2+e_1+e_0)+M<0$, so $z\ge1$. Also
$$
gz<\frac{w}{t}(-E+|F|/g)<\frac{w}{t}(-2e_1-e_0+M)<Cw .
$$
The first inequality uses $\kappa>0$, and the last is an integer comparison. Each shape therefore has an explicit finite certificate.

Finally the integer $\kappa$ must satisfy a quadratic with coefficients
$$
e_2g+f_2,\qquad (e_1g+f_1)w+z,\qquad e_0gw^2+twg^2z.
$$
In each class the certificate checks every $1001\le g<Cw$ and $1\le z\le\lfloor(Cw-1)/g\rfloor$. The leading coefficient is positive throughout, so a nonnegative square discriminant is necessary.

| $(\ell,h)$ | CRT progressions | $g$ counted with class | Discriminants | Squares |
|---|---:|---:|---:|---:|
| $(11,39)$ | 288 | 52,313 | 522,725 | 0 |
| $(17,1943)$ | 864 | 8,440 | 63,863 | 0 |

This excludes the equality $d+1=10g$. The remaining ratios are unbounded. To reproduce the calculation, run `python checks/chebyshev_ratio_ten.py` in the research repository with SymPy 1.14. The verifier reuses the existing small-ratio routines.
