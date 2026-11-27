# A restriction on the number of prime divisors in the Chebyshev test

Let $n$ be an odd squarefree integer greater than one that passes the Chebyshev congruence. Write $k$ for its number of prime divisors, and give each prime the sign $s_p$ from the [local criterion](17-chebyshev.md). For every $k\le2{,}451{,}595$,
$$
W=\sum_{p\mid n}s_p\frac np=1.
$$
In particular, **no composite with an even number of distinct prime divisors through 2,451,594 can pass the test**, with arbitrarily large primes. Even composites and integers divisible by a prime square already fail the local criterion. Odd factor counts, including five and seven, require further arguments.

## Bounding the two sums separately

For a candidate, $p-s_p$ divides $n-1$, $p+s_p$ does not divide $n-1$, and $n/p\equiv s_p\pmod p$. The last condition gives $W\equiv1\pmod n$. Set
$$
M=\operatorname{lcm}(1,2,\ldots,48),\qquad D=\gcd(M,n-1).
$$
The divisor $D$ is even. If $s_p=s$, then $p$ belongs to the set defined by
$$
\gcd(M,p-s)\mid D,\qquad p\nmid D,\qquad p+s\nmid D.
$$
Indeed $p$ divides $n$, and $D$ divides $n-1$. The eligibility test permits extra primes, which can only increase an upper bound for a sum of positive reciprocals.

Put $C=30{,}000{,}000$, $Q=10^{12}$ and $b=\lceil Q/C\rceil=33{,}334$. For any $K\ge k$ and either sign,
$$
Q\sum_{s_p=s}\frac1p\le
 Kb+\sum_{\substack{3\le p\le C\ \mathrm{prime}\\p\ \mathrm{eligible\ for}\ D,s}}
 (\lceil Q/p\rceil-b).
$$
Every prime above $C$ costs at most $b$ units. At or below $C$, the excess above $b$ is nonnegative and each eligible prime occurs at most once. Thus the cutoff applies only to calculating excess weights. It imposes no bound on a prime divisor of $n$.

The exact integer maxima over even $D\mid M$ at $K=2\cdot10^6$ are as follows.

| Sign | Maximum | Divisor attaining it |
| --- | ---: | ---: |
| $+1$ | 979,992,270,359 | 852,921,110,814,300 |
| $-1$ | 984,946,515,023 | 1,283,847,370,696,800 |

The checker forms all 294,912 divisors of $M$. For each odd prime $p\le C$, it adds its excess to the multiples of $\gcd(M,p-s)$, removing the multiples of $p$ or of $p+s$ by inclusion and exclusion. Summation over divisors in ascending prime-power order produces all the scores. It also explicitly sums the eligible primes at both maximizing divisors and checks every score against direct enumeration for three smaller moduli. [Standard-library verifier](../checks/chebyshev_even_factor_count.py).

## From the bound to an integer equality

Since $W/n$ is the difference of the two nonnegative sign sums, $|W|/n$ is at most the larger bound. At $k\le2\cdot10^6$ this is less than $0.985$. For $n\ge67$ it follows that $1-n<W<1+n$. At $n<67$ a squarefree odd composite has just two primes, so $|W|/n\le1/3+1/5<1-1/n$. An odd prime has $W=1$ directly. In all cases the congruence modulo $n$ forces $W=1$.

At $2\cdot10^6<k\le2{,}451{,}595$, use $K=2{,}451{,}595$ in the same table. Adding $451{,}595\,b$ gives a worst bound of $999{,}999{,}982{,}753/Q=1-17{,}247/Q$. Such $n$ exceeds $3^{17}>Q/17{,}247$. Once again $|W|<n-1$, so $W=1$. Its parity now forces $k$ to be odd because each summand is odd.

## A restriction on the number of negative signs

Throughout this range let $m$ count the negative signs. Then $k-2m\equiv1\pmod8$. In particular seven factors require exactly three negative signs.

To prove this, set $u_p=s_p p$, $S=\prod_p s_p=(-1)^m$ and let $b_4$ count the $u_p\equiv-1\pmod4$. Multiplication of $W=1$ by $S$ gives $e_{k-1}(u)=S$. Changing a single $u_p$ by four preserves $e_{k-1}\pmod8$, as its coefficient is a sum of $k-1$ odd products and $k$ is odd. Replacing all $u_p$ by $\pm1$ therefore gives
$$
(-1)^{b_4}(k-2b_4)\equiv(-1)^m\pmod8 .
$$
Let $r$ count primes $p\equiv3\pmod4$, and $j$ the negative signs among them. Multiplication of the Legendre symbols of $n/p\equiv s_p\pmod p$ over all $p\mid n$, pairing the two orientations of each pair of primes, gives $j\equiv\binom r2\pmod2$ by quadratic reciprocity. Hence $b_4=m+r-2j\equiv m+2r-r^2\pmod4$. Substitution for $r$ even or odd yields $k-2m\equiv1\pmod8$ in both cases. At $k=7$ this allows $m=3$ or $7$, and seven negative terms cannot sum to $1$.
