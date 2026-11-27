# The two smallest primes at the modulus N−1

Let $N=2^t$, $q=N-1$, and suppose $2^{t-1}p^{2i}r^{2j}s^{2k}$ is almost perfect, where $p<r<s$ are distinct odd primes and $i,j,k\ge1$. Then for every $t\ge3$,
$$
 q\nmid\gcd(p-1,r-1).
$$
For $i=j=k=1$ this says $q\nmid\gcd(D_p,D_r)$, with no condition on $D_s$. In fact, $q\mid D_p$ alone requires $p=2N-1$ and $t+1$ prime. Thus $q\nmid D_p$ at every odd $t\ge3$.

## Forcing the smallest prime

Write $M=p^{2i}r^{2j}s^{2k}$. The divisor sum identity $(N-1)\sigma(M)=NM-1$ gives
$$
\prod_{x=p,r,s}(1+1/x+1/x^2)\le \sigma(M)/M < N/q
\le \prod_{x=p,r,s}x/(x-1).
$$
For the last inequality use the integer $qprs-N(p-1)(r-1)(s-1)>-(p-1)(r-1)(s-1)/M>-1$. In particular $p>N$. Also $p<3N$, since $(3N/(3N-1))^3<N/q$ and $x/(x-1)$ decreases. If $q\mid p-1$, oddness forces $p=2q+1=2^{t+1}-1$, the only eligible multiple of $2q$ plus one below $3N$ for $q\ge3$. Primality of $2^{t+1}-1$ requires $t+1$ prime by the difference of powers factorization.

## Separation when the smallest prime equals 2N−1

In fact, for any $t\ge2$ and any exponents, $p=2N-1$ forces
$$
 r+s\ge8N,\qquad (s-r)^2\ge8N.
$$
Set $T=r+s$. The function $f(x)=\log(1+1/x+1/x^2)$ decreases and is convex for $x>0$, as $f''(x)=(2x^3+7x^2+4x+2)/[x^2(x^2+x+1)^2]$. If the even integer $T$ is less than $8N$, the two-prime part of the lower product in the envelope is at least $(1+1/u+1/u^2)^2$, where $u=4N-1=4q+3$. With $p=2q+1$ its product with the smallest factor already exceeds $N/q$. The difference after multiplying by $qp^2u^4$ is
$$
q\Phi(p)\Phi(u)^2-(q+1)p^2u^4
=64q^5+64q^4-224q^3-474q^2-330q-81>0
$$
for $q\ge3$ (all coefficients are positive after $q=3+z$). This proves $T\ge 8N$. Substituting $p=2q+1$ in the upper envelope gives $rs\le2N(T-1)$. Therefore
$$
(s-r)^2=T^2-4rs\ge T(T-8N)+8N\ge8N .
$$

If $q\mid r-1$ as well, then $r\ge4q+1$. The upper envelope gives
$$
s-1\le\frac{(2q+1)(4q+1)}{2q-1}=4q+5+\frac{6}{2q-1}.
$$
For $t\ge3$ we have $q\ge7$, so the even integer $s-r$ is at most four. Its square is then at most 16, contradicting $8N\ge64$. Finally in the squarefree-root case $D_xx^2\equiv1-x\pmod q$ and every $x$ is a unit modulo $q$, proving the statements about the component quotients.

The conditions leave open the cases in which $q$ fails to divide either or both of the first two quotients.
