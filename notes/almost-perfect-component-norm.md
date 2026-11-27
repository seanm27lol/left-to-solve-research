# A norm obstruction for each fixed base

Write $N=2^t$, $\Phi(z)=z^2+z+1$ and assume
$$
(N-1)\Phi(x)\Phi(y)\Phi(z)=N(xyz)^2-1 .
$$
Here $x$ can be any one of the three bases. Set $A=Nx^2$, $B=(N-1)\Phi(x)$ and $T=(3B+4)A-3B$. Since $AV^2-B\Phi(y)\Phi(z)=1$ for $V=yz$, we have $\gcd(A,B)=1$. Define $Z=V+2y+2z+1$. The identity $4\Phi(y)\Phi(z)=3(V-1)^2+Z^2$ gives
$$
[(4A-3B)V+3B]^2-B(4A-3B)Z^2=4T .
$$
Let $\ell\ge5$ be a prime divisor of $T$. It divides none of $A,B,3B+4$. Indeed $\ell\mid A$ or $\ell\mid B$ would force both, and if $\ell\mid3B+4$ then $\ell\mid3B$. The equation $A(3B+4)\equiv3B$ yields
$$
B(4A-3B)\equiv -3A B^2\pmod\ell .
$$
Therefore if the Legendre symbol $(-3N/\ell)$ is $-1$, then $v_\ell(T)$ is even. For a nonsquare unit $c$ the valuation of $X^2-cY^2$ is twice the lesser of the valuations of $X,Y$; after dividing by that even power the remaining difference is nonzero modulo $\ell$. At even $t$, the excluded prime factors of odd valuation are precisely those $\ell\ge5$ congruent to $2\pmod3$. At odd $t$ their character is $(-6/\ell)=-1$.

More generally, suppose $n=2^{t-1}M y^2z^2$ is almost perfect, with $y,z$ distinct odd primes coprime to $M$. The odd cofactor $M$ is a square because $\sigma(n)$ is odd. Put $A=NM$ and $B=(N-1)\sigma(M)$. The same equation and proof give the same valuation restriction, without a bound on the number or exponents of the remaining prime factors.

## A restriction outside the Mersenne branch

For every level $t\equiv 1,7\pmod 8$ none of the three bases is $1\pmod{17}$. In fact $N=2^t$ is $2$ or $9$ modulo 17. With one fixed base $x=1$ modulo 17, the original equation becomes
$$
3(N-1)\Phi(y)\Phi(z)-Ny^2z^2+1=0\pmod {17}.
$$
For each of the two residues of $N$, evaluating the left hand side on the $17^2$ ordered pairs gives zero solutions. This test applies to any of the three bases independently. The norm criterion above also applies separately at all three. A uniform proof must still exclude triples satisfying every one of these conditions. [Exact check](../checks/almost_perfect_component_norm.py).
