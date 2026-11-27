# Erdős 366: an odd singleton in the four-prime-support case

This note treats one unbounded part of the exact weaker target. It does
**not** prove that consecutive cubefull integers do not exist. Assume that
$n,n+1$ are cubefull, that $\omega(n(n+1))=4$, and that one endpoint has
singleton support $p^A$ for an odd prime $p$. The other endpoint then has
support $\{2,q,r\}$.

The argument uses Bang--Zsigmondy, Proposition 1 of Bennett--Levin,
*The Nagell--Ljunggren equation via Runge's method*, Monatsh. Math. 177
(2015), 15--31, doi:10.1007/s00605-015-0748-1, and Lemma 2.6 of Zhu--Le--
Togbé, *New cases of the Nagell--Ljunggren equation*, Bull. Aust. Math. Soc.
85 (2012), 107--116, doi:10.1017/S000497271200010X.

## Upper odd singleton

Suppose $n+1=p^A$. Primitive divisors indexed by the divisors of $A$ leave
only

\[
 A\in\{\ell,\ell^2,4,8,2\ell\},
\]

where $\ell$ is an odd prime. Each discarded divisor would contribute a
new odd support prime.

The exponent $8$ is impossible: the support restriction forces $p=3$, but
$3^8-1=2^5\cdot5\cdot41$ is not cubefull. The exponent $\ell^2$ is
excluded by applying Bennett--Levin to the resulting prime-power value of
$\Phi_\ell(p)$ after $p-1$ has been forced to be a power of two. The case
$2\ell$ likewise forces $p=3$ and a prime-power value of $\Phi_\ell(3)$,
again excluded by Bennett--Levin.

If $A=4$, the support equations give

\[
 p^2+1=2q^u,\qquad u\ge3.
\]

Zhu--Le--Togbé Lemma 2.6 says that the only solution of
$X^2+1=2Y^k$ for $X,Y>1$ and $k>2$ is $(X,Y,k)=(239,13,4)$. But both
$239-1$ and $239+1$ contribute more odd support than the assumed total of
four. Therefore

\[
 \boxed{n+1=p^\ell\quad\text{with $\ell$ an odd prime}.}
\]

This is a classification of the exponent, not an exclusion of this last
family.

## Lower odd singleton

Suppose instead $n=p^A$. Parity makes $A$ odd, and primitive-divisor
counting leaves

\[
 \boxed{A\in\{\ell,\ell^2\}}
\]

for an odd prime $\ell$. In the square case, the support allocation is
forced all the way to

\[
 p+1=2^b,\qquad
 \Phi_{2\ell}(p)=\frac{p^\ell+1}{p+1}=q^c,
 \qquad
 \Phi_{2\ell^2}(p)=\frac{p^{\ell^2}+1}{p^\ell+1}=r^d.
\]

Here $p$ is a Mersenne prime, $\ell\ge5$, and Bennett--Levin gives that
$c,d$ are odd divisors of $p-1$. In particular, if a prime $s$ divides
$\gcd(c,d)$, Bennett--Levin Theorem 2 gives

\[
 p<4\max\!\left(1,\frac{\ell}{s}\right)
 s^{\,\ell-1+(\ell^2-\ell)/s}.
\]

The prime-exponent branch $A=\ell$ remains as well.

## Exact scope

The theorem above is cutoff-free, but it only treats the $1+3$ support
split when the singleton endpoint is an odd prime power. It does not cover
the $2+2$ support split, a singleton endpoint $2^A$, or candidates with at
least five support primes. No complete positive pair or unrestricted
impossibility follows from it.
