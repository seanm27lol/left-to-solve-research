# Congruences at primes dividing the shifted odd factors of an almost-perfect number

Let $n=2^{t-1}(prs)^2$ be almost perfect, with distinct odd primes $p,r,s$. Put $N=2^t$, $P=prs$, $A=\Phi(p)\Phi(r)\Phi(s)$, and $\Phi(x)=x^2+x+1$. Multiplicativity of the divisor sum gives $(N-1)A=NP^2-1$.

Let $\ell$ be any odd prime dividing $N-1$ such that $p,r,s\equiv-1\pmod\ell$. Put $h=v_\ell(N-1)$, $k=\min_{q\in\{p,r,s\}}v_\ell(q+1)$, and $y_q=(q+1)/\ell^k$. Then
$$
\ell^{h+2k}\mid P+1,\qquad \sum_q y_q\equiv0\pmod\ell,
$$
and more precisely
$$
 v_\ell(P+1)=h+2k\quad\Longleftrightarrow\quad\sum_q y_q^2\not\equiv0\pmod\ell.
$$
In particular, at least two of the three primes attain the minimum $k$. When exactly two attain it, the valuation is exactly $h+2k$.

Indeed, the original equation factors as
$$
(P+1)(NP-1)=(N-1)(A+P).
$$
Since $N\equiv1$ and $P\equiv-1\pmod\ell$, the factor $NP-1\equiv-2\pmod\ell$ is a unit. The identity $\Phi(q)=-q+(q+1)^2$ gives, by multiplying all three factors,
$$
 A+P\equiv\ell^{2k}\sum_q y_q^2\pmod{\ell^{2k+1}}.
$$
In the terms containing precisely one square the other two factors multiply to $1$ modulo $\ell$. Terms containing two or more squares are multiples of $\ell^{4k}$. The valuation and divisibility now follow. Expanding $P=\prod_q(-1+\ell^k y_q)$ modulo $\ell^{k+1}$ gives $\sum y_q\equiv0\pmod\ell$. One nonzero residue cannot sum to zero. If there are two, they are $u,-u$ for a unit $u$, and their squares sum to $2u^2\ne0\pmod\ell$.

For even $t$ take $\ell=3$. In this case $h=1+v_3(t/2)$, from $2^t=4^{t/2}$ and the lifting-the-exponent identity for $4^j-1$. If all three primes are $2\pmod3$, exactly two possibilities remain:

| Number attaining the minimum $k$ | Restrictions |
|---|---|
| Two | Their two $y_q$ are opposite modulo $3$, and $v_3(P+1)=h+2k$. |
| Three | All three $y_q$ are equal modulo $3$, and $v_3(P+1)\ge h+2k+1$. |

The last assertion uses that every nonzero square modulo $3$ equals $1$. For example, each permutation of $(2,8,8)\pmod9$ is excluded for every even $t$. If all three primes are individually $2$ or $5\pmod9$, all three must have the same residue modulo $9$ and $81\mid P+1$. Neither assertion imposes a size bound.

If $t$ is even and at least one of the primes is $1\pmod3$, a different test applies. Since $N\equiv1\pmod3$, the original equation gives $3\nmid P$, and $3\mid A$ because it divides the cyclotomic factor at the prime equal to $1\pmod3$. Consequently $N(P^2-1)=(N-1)(A-1)$ implies $v_3(P^2-1)=h$ exactly.

The divisibility has a version for arbitrary exponents in the square root. Suppose the odd part is $M=\prod_{i=1}^m q_i^{2e_i}$, with $e_i\ge1$. Under the same assumptions $\ell\mid N-1$ and $q_i\equiv-1\pmod\ell$ for every $i$, put $B=\prod_i(-q_i)^{e_i}$, $k=\min_i v_\ell(q_i+1)$, and $y_i=(q_i+1)/\ell^k$. Then
$$
\ell^{h+2k}\mid B-1,\qquad \sum_i e_i y_i\equiv0\pmod\ell,
$$
and $v_\ell(B-1)=h+2k$ exactly when $\sum_i\binom{e_i+1}{2}y_i^2\ne0\pmod\ell$.

For the proof, the defining equation gives $(B-1)(NB+1)=(N-1)(\sigma(M)-B)$ because $B^2=M$. Here $NB+1\equiv2\pmod\ell$. The finite geometric sum satisfies the polynomial congruence in $z$,
$$
 \sum_{j=0}^{2e}(-1+z)^j-(1-z)^e\equiv\binom{e+1}{2}z^2\pmod{z^3}.
$$
One verification uses $(2-z)\sum_{j=0}^{2e}(-1+z)^j=1+(1-z)^{2e+1}$ and expands through degree two. The constant and linear terms cancel, and the quadratic coefficient is $e(e+1)/2$. Multiply the congruences with $z=q_i+1$, using $(1-z)^{e_i}\equiv1\pmod\ell$, to obtain the claim about the valuation. Expanding $B$ modulo $\ell^{k+1}$ gives the weighted linear restriction.

For the complementary squarefree-root patterns at even $t$, the prime $3$ cannot divide $P$, since reducing $(N-1)A=NP^2-1$ modulo $3$ gives $P^2\equiv1$. If at least one prime is $1\pmod3$, then $3\mid A$. Hence $(N-1)(A-1)=N(P^2-1)$ gives $v_3(P^2-1)=h$. In particular, it is impossible for every prime to be individually congruent to $1$ or $-1$ modulo $3^{h+1}$ with at least one $1$ modulo $3$. For $t\equiv2,4\pmod6$, this excludes every pattern drawn from $1,8\pmod9$ that contains $1$.

## A unique least valuation at other primes

In the three-prime case with all exponents two, suppose an odd prime $\ell$ divides $p+1,r+1,s+1$. Suppose $p$ alone has the least valuation $k$. Even without assuming $\ell\mid N-1$, one has
$$
N\equiv p\pmod{\ell^{k+1}},\qquad v_\ell(N+1)=k.
$$
Indeed put $a=(p+1)/\ell^k$. Then $(P+1)/\ell^k\equiv a$ and $(A+P)/\ell^{2k}\equiv a^2\pmod\ell$. The factored identity forces $\ell^k\mid NP-1$ and hence $\ell^k\mid N+1$. Write $c=(N+1)/\ell^k$. Dividing the same identity by $\ell^{2k}$ and reducing modulo $\ell$ now gives $a(-c-a)=-2a^2$, because $NP-1=N(P+1)-(N+1)$ and $N\equiv-1\pmod\ell$. Therefore $c\equiv a\not\equiv0\pmod\ell$, as claimed. At even $t$, $N+1$ is one more than a square. In particular no prime $\ell\equiv3\pmod4$ can occur as such a unique minimum.

These constraints leave many possible combinations of prime residues. The companion note gives size constraints on the same candidates. [Prime spacing](almost-perfect-prime-spacing.md).
