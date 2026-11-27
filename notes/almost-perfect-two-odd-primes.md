# Almost-perfect numbers with at most two distinct odd prime divisors

**Theorem.** Let $N$ be a positive integer with $\sigma(N)=2N-1$, where $\sigma$ denotes the sum of all positive divisors. If $N$ has at most two distinct odd prime divisors, then $N$ is a power of two.

Ibrahim Amin Nicola Shnoudi states this result as Theorem 6.3 in *On the Almost Perfect Number Conjecture* (October 2026) and reports a Lean 4 proof. The argument below gives a self-contained derivation. Its companion Lean file starts from Mathlib’s divisor-sum function and counts the distinct odd primes dividing the integer. [Shnoudi’s overview, §4.1](https://www.academia.edu/179631267/On_the_Almost_Perfect_Number_Conjecture_Overview_of_the_Project) · [Archive copy](https://lifeofresearch.com/articles/144) · [Lean proof](../lean/research/AlmostPerfectTwoOdd.lean).

Every power of two satisfies the defining equation. The [full catalog question](https://lefttosolve.com/p/AlmostPerfectNumbers.exists_almost_perfect_not_power_of_two) remains open for integers with at least three distinct odd prime divisors.

## The odd part

Write $N=2^a b$ with $b$ odd and $a\ge0$. Put $H=2^{a+1}$ and $t=H-1$. Multiplicativity and the geometric series for the divisors of $2^a$ give
$$
t\sigma(b)=Hb-1,\qquad t(\sigma(b)-b)=b-1. \tag{1}
$$
Since $Hb-1$ is odd, $\sigma(b)$ is odd. The sum $1+p+\cdots+p^u$ for an odd prime $p$ is odd exactly when $u$ is even. Thus every prime exponent of $b$ is even. For any prime $p\mid b$, its proper divisor $b/p$ gives $b-1\ge tb/p$, so $p>t$. Since $p,t$ are odd, $p>H=t+1$.

When $b=1$, the solutions are exactly the powers of two, including 1. When $b=p^u>1$, the proper divisors sum to $(p^u-1)/(p-1)$. Equation (1) would force $p=t+1$, contrary to $p>H$.

## Both odd exponents must be two

Suppose $b=p^u q^v$ with distinct odd primes $p<q$. Then $u,v$ are positive even integers. Set
$$
 F=H(H-1)-(p-H)(q-H),\qquad C=t+(p-1)(q-1).
$$
Multiplying the first equation of (1) by $(p-1)(q-1)$ and expanding gives
$$
 Fp^u q^v= tp^{u+1}+tq^{v+1}-C. \tag{2}
$$
Here $C<t+q^2<q^3\le tq^{v+1}$ because $1\le t<p<q$ and $v\ge2$. Therefore $F\ge1$. Since $p-H$ is a positive integer, the definition of $F$ yields
$$
 q<H+H(H-1)=H^2<p^2.
$$
Dividing (2) by $p^u q^v$ gives
$$
 F<\frac{tp}{q^v}+\frac{tq}{p^u}. \tag{3}
$$
If $u\ge4$, the first summand is less than $t/p$ since $q>p$ and $v\ge2$. The second is less than $1/p$ since $t<p$ and $q<p^2$. Hence $F<H/p<1$, a contradiction. Thus $u=2$.

With $u=2$, equation (2) becomes
$$
 (Fp^2-tq)q^v=tp^3-C .
$$
Since $q<p^2$ and $t<p$, we have $C<t+(p-1)p^2<p^3$. The right side is positive. Its integer factor $Fp^2-tq$ is therefore at least 1, giving $q^v\le tp^3-C<p^4<q^4$. Evenness and positivity of $v$ now give $v=2$.

## The two squares lead to an impossible even integer

For $u=v=2$, inequality (3) gives $F<t/p+t<H$, again using $q<p^2$. The integer $F$ is odd because $H$ is even and $p-H,q-H$ are odd.

Put $S=p+q$ and define
$$
 P(X)=-X^2+\big((H+1)F+3H-1\big)X-F(F+H+1).
$$
We have $pq=H(S-1)-F$. The expansion
$$
 (p^2+p+1)(q^2+q+1)=(pq)^2+pqS+S^2-pq+S+1
$$
and the identity $pq=H(S-1)-F$ give
$$
 P(S)=t(p^2+p+1)(q^2+q+1)-Hp^2q^2+1=0
$$
by (1). The second root $S'=(H+1)F+3H-1-S$ is an even integer, since $H,S$ are even and $F$ is odd.

On the other hand,
$$
 P(0)=-F(F+H+1)<0,\qquad P(2)=F(H-F)+F+6(H-1)>0 .
$$
Because $P(X)=-(X-S)(X-S')$ and $S>2$, these signs force $0<S'<2$. This contradicts the parity of $S'$ and proves the theorem. All inequalities use only $H\ge2$, so the proof includes $a=0$.
