# A polynomial divisible by the common component quotient

Let $N=2^t$ and let $p,r,s$ be distinct odd primes satisfying $(N-1)\Phi(p)\Phi(r)\Phi(s)=NP^2-1$, where $P=prs$ and $\Phi(x)=x^2+x+1$. Put $D_x=(N(P/x)^2-x)/\Phi(x)$ and $G=\gcd(D_p,D_r,D_s)$. Define
$$
\begin{aligned}
Q_4(X)&=X^4-5X^3+15X^2-5X+1,\\
Q_{10}(X)&=X^{10}+4X^9+6X^8-30X^7+39X^5-30X^3+6X^2+4X+1,\\
H(X)&=(X-1)(X+1)^2(X^2+X+1)(X^2-X+1)Q_4(X)Q_{10}(X).
\end{aligned}
$$
Then $G\mid H(N)$. The bound includes prime powers and applies at every level. For each odd prime $\ell\equiv2\pmod3$ one also has
$$
v_\ell(G)\le v_\ell(N-1)+2v_\ell(N+1).
$$

## Reduction to three residue patterns

Let $q=\ell^j\mid G$, $j\ge1$. All $D_x$ are odd. Work modulo $q$ and put $C=NP^2$. The component identities give $x^3=C$ for all three bases. All are units, since if one were zero modulo $\ell$, so would all three distinct primes be. If $\ell\ne3$, distinct cube roots of unity modulo $q$ remain distinct modulo $\ell$. This follows because a cube root reducing to 1 satisfies $(z-1)(z^2+z+1)=0$, with the second factor a unit. Any nonidentity cube root $z$ satisfies $z^2+z+1=0$. Hence the three bases consist of three equal residues, exactly two equal residues, or all three distinct residues.

**Three equal.** Write the common residue as $a$. Then $Na^3=1$ and
$$
(1-a^3)\Phi(a)^3-a^3(a^3-1)=0.
$$
Here $N(a^3-1)=1-N$ and $N(a+1)(a^2-a+1)=N+1$. Since $\Phi(a)^3+a^3=(a+1)^2(\Phi(a)^2-a\Phi(a)+a^2)$, the equation implies
$$
 (N-1)(N+1)^2(\Phi(a)^2-a\Phi(a)+a^2)=0\pmod q.
$$
The resultant in $a$ of $Xa^3-1$ and $\Phi(a)^2-a\Phi(a)+a^2$ is $Q_4(X)$. Resultants are integer-polynomial combinations of their inputs. Multiplying the combination by $(N-1)(N+1)^2$ therefore gives $(N-1)(N+1)^2Q_4(N)=0$ modulo $q$. This step works over any modulus, including powers of 3, whenever the three bases coincide there.

**All distinct.** The three roots are $a,az,az^2$ for a primitive cube root $z$. Then $P=C=a^3$ and $NC=1$. Multiplication gives $\prod_x\Phi(x)=(C-1)^2$. The identity holds as a polynomial even when $C-1$ is a nonunit. Substituting into $(N-1)\prod_x\Phi(x)=C-1$ and multiplying by $N^2$ yields $(N-1)(N^2-N+1)=0$ modulo $q$.

**Exactly two equal.** Write the bases as $a,a,az$. Then $Na^3=z$, and after multiplication by $a^3$ the global equation gives
$$
(z-a^3)\Phi(a)^2\Phi(az)-a^3(a^3-1)=0.
$$
Reduce the left side modulo $z^2+z+1$. The result factors as $(a^3-1)(a+1)T(a,z)$, where
$$T(a,z)=a^5(z+1)+a^4+a^3(z+1)-a^2z+a-z.$$
Since $Na^3=z$, multiplying by $N^2(a^2-a+1)$ gives $(z-N)(z+N)T(a,z)=0$ modulo $q$. In the ring $z^2+z+1=0$, the factor $z-N$ divides $N^2+N+1$ and $z+N$ divides $N^2-N+1$. Consequently $L T(a,z)=0$ with $L=(N^2+N+1)(N^2-N+1)$. The exact iterated resultant
$$
 \operatorname{Res}_z\!\left(
 \operatorname{Res}_a(Xa^3-z,T(a,z)),\ z^2+z+1\right)=Q_{10}(X)
$$
implies $LQ_{10}(N)=0$ modulo $q$. Indeed each resultant has a polynomial Bézout identity, so $L$ times the inner resultant at $N,z$ vanishes, and then $L$ times the outer resultant at $N$ vanishes. Only ordinary multiplication by integer polynomials is involved. The accompanying checker calculates the identities over the integers.

**Powers of 3.** For $j\ge2$, each quotient of two bases is a unit with cube 1 modulo $3^j$. It reduces to 1 modulo 3 and therefore equals 1 modulo $3^{j-1}$ by $v_3(b^3-1)=v_3(b-1)+1$ for $b\equiv1\pmod3$ (the case $b=1$ is immediate). Apply the all-equal resultant at precision $3^{j-1}$. At least one of $N^2+N+1$ and $N^2-N+1$ is divisible by 3 because $N=2^t$. This supplies the last factor of 3 in $H(N)$ and also handles $j=1$ directly.

Thus every full prime power in $G$ divides $H(N)$. For the refinement at $\ell\equiv2\pmod3$, the cube map is bijective on units modulo $q$, so all three bases are equal. In the all-equal equation factor
$$
(a^3-1)(\Phi(a)^3+a^3)=(a-1)\Phi(a)(a+1)^2(\Phi(a)^2-a\Phi(a)+a^2).
$$
The factors $\Phi(a)$ and $\Phi(a)^2-a\Phi(a)+a^2$ are units, since a zero of either would give a nontrivial cube root of unity modulo $\ell$ (in the latter case use $-\Phi(a)/a$). Hence $(a-1)(a+1)^2=0$ modulo $q$. Using $Na^3=1$ and the fact that $a^2\pm a+1$ are units gives $(N-1)(N+1)^2=0$ modulo $q$ as stated.

In particular, when $t$ is odd, no prime $\ell\equiv5\pmod{24}$ divides $G$. Such a prime is $2\pmod3$, and so would force $N\equiv\pm1\pmod\ell$. Both choices are quadratic residues because $\ell\equiv1\pmod4$, whereas $2^t$ is a nonresidue because $\ell\equiv5\pmod8$.

## Valuations at the primes of $N-1$ and at 3

For every prime $\ell\mid N-1$ one has $v_\ell(G)\le v_\ell(N-1)+\mathbf1_{\ell=7}$. To see this for $\ell\ne3$, assume $\ell^j\mid G$. From $(N-1)\Phi(y)\Phi(z)=D_xx^2+x-1$ all three bases are 1 modulo $\ell$. Their cubes are equal modulo $\ell^j$, so all three bases equal a common residue $a$ there. In the all-equal equation $\Phi(a)^3+a^3$ takes the value 28 when $a=1$. For $\ell\ne7$ this is a unit. For $\ell=7$ its valuation is exactly 1 whenever $a\equiv1\pmod7$, since the derivative at 1 is 84. Thus $\ell^j\mid 7(a^3-1)$, and $Na^3=1$ yields the assertion. For $\ell=3\mid N-1$ let $h=v_3(N-1)$. If $3^{h+1}\mid G$, the same component formula first gives $x\equiv1\pmod3$ for each base and then $x\equiv1\pmod{3^{h+1}}$ because $3\mid\Phi(y)\Phi(z)$. This makes $v_3(NP^2-1)=h$, contradicting $(N-1)\prod_x\Phi(x)=NP^2-1$.

If $t$ is odd, then
$$
1\le v_3(G)\le 1+v_3(N+1)=2+v_3(t).
$$
All bases exceed $N$ by the divisor-sum inequality (for $N=2$, a base 3 is also excluded directly by the equation modulo 3). More directly, since $N\equiv-1\pmod3$, if any base is a multiple of 3 the equation modulo 3 would require $\prod\Phi(x)=2$, although $\Phi(x)$ is only 0 or 1 there. Thus all bases are units and $\prod\Phi(x)=1$ modulo 3, forcing every $x\equiv-1\pmod3$. Consequently every $D_x\equiv0\pmod3$ from its defining formula.

Write $h=v_3(N+1)$ and assume $3^{h+2}\mid G$. All bases equal a common $a$ modulo $3^{h+1}$ and $Na^3\equiv1$ at that precision. If $h=1$, $N$ is neither $1$ nor $-1$ modulo 9, whereas unit cubes modulo 9 are $\pm1$. If $h\ge2$, then $v_3(a^3+1)=h$, so $k=v_3(a+1)=h-1\ge1$. Each $x\equiv a\pmod {3^{k+2}}$, hence $v_3(P+1)=k+1$. Put $A=\prod_x\Phi(x)$. In the product expansion from $\Phi(x)=-x+(x+1)^2$, the three single-square terms of $(A+P)/3^{2k}$ are equal units modulo 9. Indeed $(x+1)/3^k$ are all equal modulo 9 and the complementary pair products are all equal modulo 9. Terms involving two or three squares vanish modulo 9. Thus $v_3(A+P)=2k+1$. But $NP-1=N(P+1)-(N+1)$ is divisible by $3^{k+1}$. The identity $(P+1)(NP-1)=(N-1)(A+P)$ contradicts the two valuations. Finally $v_3(N+1)=1+v_3(t)$ follows from $t$ odd by lifting the exponent.

This divisibility restricts the *common* quotient factors. It places no upper bound on the prime factors occurring in a single $D_x$.
