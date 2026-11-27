# Consecutive cubefull integers

The [Left to Solve target](https://lefttosolve.com/p/Erdos366.erdos_366.variants.weaker) asks for a positive integer $n$ such that every prime dividing either of $n,n+1$ occurs in that integer to exponent at least three. The two known mixed examples $8,9$ and $12167,12168$ each have a prime of exponent two. [Erdős Problems](https://www.erdosproblems.com/latex/366). A [previous calculation](https://github.com/techno-optimist/erdos-frontier-atlas/tree/main/certificates/erdos-366) reports no squarefull-to-cubefull pair through $10^{25}$, which also excludes cubefull-to-cubefull pairs there. The [existing formal reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/8b5cce60e6530ab80f3f733d66842191197941ce/reductions/Erdos366.erdos_366.variants.weaker.R2.lean) already proves the bounded $100000$ nonexistence assertion internally.

## Exact enumeration

There is a unique expression for a positive cubefull integer as $a^3 b^4 c^5$, with $a,b,c\ge1$, $b,c$ squarefree and $\gcd(b,c)=1$. For each prime of exponent $e>0$, retain a factor in $b$ if $e\equiv1\pmod3$, in $c$ if $e\equiv2\pmod3$, and in neither if $3\mid e$. The residual exponent is a nonnegative multiple of three. This proves existence and uniqueness, including when $a$ shares a prime with $b$ or $c$.

For $T=10^k$, generate all admissible $(b,c)$ with $b^4c^5\le T+1$ and every positive $a\le\lfloor\sqrt[3]{(T+1)/(b^4c^5)}\rfloor$. The code takes an initial floating-point cube-root estimate and corrects it in both directions using exact integers. All tested powers and products fit unsigned 128-bit arithmetic for $k\le26$.

Every even cubefull integer is divisible by eight. An odd cubefull integer can therefore belong to a consecutive pair only when it is $1$ or $7$ modulo eight. Its possible even neighbor is uniquely specified by that residue. For each eligible odd term up to $T+1$, insert this neighbor (when positive and within range) in a bit filter. Enumerate the even cubefull terms and retain every exact even term that passes the filter. Then enumerate the odd terms again and check the resulting neighbors against the retained sorted integers by exact binary search. An optional second bit filter accelerates these searches. Either filter can admit extra values, but a member sets both bits needed for its own lookup, so every actual match reaches exact comparison. Since $10^k$ is even, the largest even endpoint of any candidate with first endpoint at most $10^k$ is at most $10^k$. The upper odd endpoint $10^k+1$ is included.

The first independent check enumerates all exponents by ordinary prime divisibility for $T=10^3,10^5,10^6$. A separate unrestricted traversal of $a^3b^4c^5$ putting all outputs in a Python set directly counts neighbors at these levels and at $T=10^{12},10^{15}$.

The full run with $T=10^{26}$ produced the following exact counts. Thus any positive witness has $n>10^{26}$. This goes one order of magnitude beyond the previously cited range for the narrower cubefull-to-cubefull variant.

| Quantity | Count |
| --- | ---: |
| Distinct admissible $(b,c)$ | 5,259,863 |
| Cubefull terms through $10^{26}+1$ | 2,144,335,391 |
| Even terms | 1,516,537,298 |
| Eligible odd terms mapped to possible even neighbors | 314,133,319 |
| Even terms reaching the exact comparison list | 97,580,327 |
| Consecutive pairs | 0 |

A separate direct sort of 15,639,672 unrestricted products through $10^{19}+1$ gives 9,718,457 distinct terms and zero pairs. The canonical enumeration and the direct sort agree on the full distinct count. As a positive control, adding artificial odd endpoints 63 and 65 to a small run recovers both neighbors of 64.

Run from the certificate directory:

```sh
g++ -std=c++17 -O3 checks/consecutive_cubefull.cpp -o /tmp/check-cubefull
/tmp/check-cubefull 26
python3 checks/erdos366_crosscheck.py
g++ -std=c++17 -O3 checks/erdos366_direct_sort.cpp -o /tmp/direct-cubefull
/tmp/direct-cubefull
```

## A restriction valid at every height

Write $4n(n+1)=D Z^3$, where $D$ is cube-free. For any candidate define
$$X=D Z,\qquad Y=D(2n+1).$$
Then $Y^2=X^3+D^2$. For $D\le3162$ the parameter $k=D^2$ satisfies $1\le k\le10^7$. Bennett and Ghadermarzi resolved all integral solutions in this parameter range. Their complete Table 5 gives $\sqrt{X}/k<5$ for positive $k$ and $X>0$. It follows that
$$
(2n+1)^2=1+X^3/D^2 < 1+125^2 D^{10}.
$$
Thus $2n+1\le125D^5$ by integrality. In particular $n<2\cdot 10^{19}$, already in the excluded range. Every possible positive witness therefore has **$D\ge3163$**, independent of the size of either endpoint. [Bennett and Ghadermarzi, 2015, §5.3 and Table 5](https://personal.math.ubc.ca/~bennett/BeGh-LMSJCM-2015.pdf).

One can also exclude infinitely many pairs of cube-free coefficients directly. Write $n=A x^3$, $n+1=B y^3$ with $A,B$ cube-free. The cubefull conditions are equivalent to $\operatorname{rad}(A)\mid x$ and $\operatorname{rad}(B)\mid y$. Bennett's uniqueness theorem for $|A x^3-B y^3|=1$ shows that $|A-B|=1$ is impossible for a candidate: $(1,1)$ already solves that equation, and at least one of $A,B$ has a prime divisor. More generally, any one explicit solution of the same absolute-value equation failing the radical divisibilities rules out the entire coefficient pair, at every height. [Bennett, 2001, Theorem 1.1](https://personal.math.ubc.ca/~bennett/B-Crelle2.pdf).

The unresolved instance permits arbitrarily large $n$ and $D$ and need not have neighboring cube-free coefficients.
