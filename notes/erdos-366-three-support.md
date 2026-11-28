# Erdős 366: exact three-prime-support reduction

This note gives an unbounded reduction, not a full solution. It uses the
classical Bang--Zsigmondy theorem and Proposition 1 of Bennett--Levin, *The
Nagell--Ljunggren equation via Runge's method*, Monatsh. Math. 177 (2015),
15--31, doi:10.1007/s00605-015-0748-1.

Assume $n,n+1$ are cubefull and $\omega(n(n+1))=3$. Coprimality splits
the three primes $1+2$ between the endpoints. Every candidate belongs to
one of these families:

1. \(n+1=2^A\), $n=q^b r^c$, where $A$ is prime;
2. \(n=2^A\), $n+1=q^b r^c$, where $A$ is a power of 2;
3. \(n=p^a\), $n+1=2^b q^c$, where
   \[
   p=2^b-1,\qquad (p^a+1)/(p+1)=\Phi_{2a}(p)=q^c.
   \]
   Here $p,q,a,b$ are primes, $a\ge5$, $b\ge17$, $c\ge3$ is odd,
   and $c\mid p-1$.

The fourth apparent family, $n+1=p^a$ with
\(p^a-1=2^bq^c\), is impossible.

## Odd singleton endpoint

Bang--Zsigmondy at the divisors of $a$ shows that $a$ is an odd prime.
For the upper endpoint it forces $p-1=2^b$ and \(\Phi_a(p)=q^c\).
Choose a prime \(\ell\mid c\) and rewrite the right side as
\((q^{c/\ell})^\ell\). Bennett--Levin Proposition 1 says that outside the
four known Nagell--Ljunggren solutions, \(\ell\) is odd and the base has a
prime divisor congruent to $1\pmod\ell$. The known positive prime-base
solution has exponent 2. Since $p$ is prime,
\(\ell\mid p-1=2^b\), a contradiction.

For the lower endpoint, Zsigmondy instead gives
\[
p+1=2^b,\qquad \Phi_{2a}(p)=q^c.
\]
Bennett--Levin applied at base $-p$ forces $a\ge5$, $p\ge10^4$, $c$
odd, and $c\mid p-1$. The known negative-base solution is excluded because
its positive $p$ does not have $p+1$ a power of two. Thus $p=2^b-1$
is Mersenne prime and $b\ge17$ is prime. Also
\[
\operatorname{ord}_{q}(p)=\operatorname{ord}_{q^3}(p)=2a,
\quad q\equiv1\pmod{2a},
\quad q^3\mid p^{q-1}-1.
\]

For every prime $r\mid c$,
\[
\boxed{v_r(p-1)+v_r(a-1)\ge v_r(c)+1.}
\]
Indeed, put $S=(p^a+1)/(p+1)=q^c$ and $c=r^k m$, $r\nmid m$. The
order of $q\pmod r$ divides $m$, so LTE gives
\(v_r(q^c-1)\ge k+1\). But
\(S-1=p(p^{a-1}-1)/(p+1)\), and LTE gives
\(v_r(S-1)=v_r(p-1)+v_r(a-1)\). If $c$ is squarefree and
\(\gcd(c,a-1)=1\), then $c^2\mid p-1$.

## Singleton endpoint $2^A$

For $2^A-1=q^b r^c$, primitive divisors over the divisors of $A$ reduce
to $A$ prime, a prime square, or the Zsigmondy exception 6. The
exception gives $63=3^2\cdot7$. The prime-square case would make
\(2^\ell-1\) one prime to exponent at least three, contrary to Mihăilescu.
Thus $A$ is prime.

For $2^A+1=q^b r^c$, write $A=2^s u$ with $u$ odd. Primitive-order
counting reduces to $u=1$, $u$ prime, or $A=9$. The exception has a
prime to the first power; the prime-$u$ case forces a perfect-power factor
\(2^{2^s}+1\), excluded by LTE and Mihăilescu. Hence $A$ is a power of two.

In both surviving power-of-two families, each odd support prime is a cubic
base-two Wieferich witness. The relevant order is $A$ in the minus branch
and $2A$ in the plus branch, so cubefullness implies
\(q^3\mid2^{q-1}-1\) and likewise for $r$.

There are two further exact restrictions. First,

\[
 \boxed{\gcd(b,c)=1.}
\]

Indeed, if a prime $d>1$ divided both exponents, then the right side would
be a perfect $d$th power, say $Y^d$.  In the minus branch this would give
$2^A-Y^d=1$, contradicting Mihăilescu's theorem. In the plus branch it
would give $Y^d-2^A=1$; the unique consecutive nontrivial perfect powers
would force $A=3$, which is not a surviving power-of-two exponent.

Second, the exponents are the exact base-two Wieferich valuations:

\[
 \boxed{b=v_q(2^{q-1}-1),\qquad c=v_r(2^{r-1}-1).}
\]

For the minus branch, $\operatorname{ord}_q(2)=A$ and $A\mid q-1$;
LTE applied to $(2^A)^{(q-1)/A}-1$ gives the equality. For the plus branch,
$\operatorname{ord}_q(2)=2A$ and the same argument applies. Thus any
three-support candidate requires two distinct primes whose exact base-two
Wieferich valuations are coprime integers at least three. This is an
unbounded restriction, not a proof that either residual family is empty.

The first nontrivial congruence beyond the valuations can also be recorded
exactly. In the minus branch write

\[
 q=1+2Au,\qquad r=1+2Av,\qquad
 T=\frac{2^{A-1}-1}{A}.
\]

Expansion modulo $(2A)^2$ gives

\[
 \boxed{bu+cv\equiv T\pmod{2A}.}
\]

Here $T$ is odd. The quadratic-character constraint also says that the
support primes are $1$ or $7\pmod8$, and at least one is $7\pmod8$ with
odd exponent.

In the plus branch the cases $A=4,8$ give only the single Fermat support
prime $17,257$, so a two-prime-support candidate has $A=2^s$ with $s\ge4$.
Euler's criterion strengthens $q,r\equiv1\pmod{2A}$ to
$q,r\equiv1\pmod{4A}$. Writing $q=1+4Au$ and $r=1+4Av$, expansion modulo
$(4A)^2$ gives

\[
 \boxed{bu+cv\equiv0\pmod{4A}.}
\]

In particular, if the two terms have unequal 2-adic valuations below
$s+2$, they cannot cancel; those parameter choices are excluded.

## Formal status and attribution

The pinned Mathlib contains no Bang--Zsigmondy theorem. A kernel-checked Lean
formalization exists in `facebookresearch/atlas-lean`. The main theorem
traces to Adam Kiezun's import (Muse Spark 1.3); the direct plus-case theorem
was added by Vivien Cabannes with Codex, citing Tomohiro Yamada. Those files
are not a pinned dependency and have additional repository notices, so any
port requires a license check and full original attribution.

The exact Erdős 366 target still permits these three families and every
candidate with at least four prime divisors in $n(n+1)$.
