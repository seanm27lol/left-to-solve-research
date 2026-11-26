# A prime-value bound and reciprocal LCM determinant integrality

## OeisA117531.conjecture — prime-valued quadratic rows

**Answer.** For every integer $n>13$ there is a composite entry among the $n$ numbers $T(k)=k^2-k+p_n$, $1\le k\le n$, where $p_n$ is the $n$-th prime starting at 2. The first 13 prime-indexed rows include the sharp example $p_{13}=41$. Ondrej Kutal recorded a proof in August 2026. The independent repository describes a Lean formalization conditional on a declared axiom for the established Stark–Heegner class-number-one classification. We reviewed the argument and the repository's stated trust boundary. We did not rebuild its Lean project. [Catalog](https://lefttosolve.com/p/OeisA117531.conjecture) · [OEIS entry source](https://github.com/oeis/oeisdata/blob/main/seq/A117/A117531.seq) · [Kutal's proof and formalization](https://github.com/TheSil/A117531_conjecture).

Let $P=p_n$, $M=4P-1$, and $\Delta=-M$. For each odd prime $q\le n$, if $\Delta$ is a square modulo $q$ (including zero), choose $1\le k\le q$ with $(2k-1)^2\equiv\Delta\pmod q$. The identity $4T(k)=(2k-1)^2-\Delta$ gives $q\mid T(k)$. Since $T(k)\ge P>n$, this produces a composite entry.

We have $M<n^2$ for $n\ge14$. Check $n=14,\ldots,19$ from the primes $43,47,53,59,61,67$. For $n\ge20$, the Rosser–Schoenfeld bound $p_n<n(\log n+\log\log n)$ suffices because $x/4-\log x-\log\log x$ is positive and increasing for $x\ge20$. If $M$ is composite, it has an odd prime factor $q\le\sqrt M<n$, so the previous obstruction applies. [Rosser–Schoenfeld](https://doi.org/10.1215/ijm/1255631807).

If $M$ is prime and no entry is composite, every odd prime $q\le n$ is inert in the imaginary quadratic field of discriminant $-M$. Indeed the discriminant is fundamental, the root obstruction rules out splitting, and the only ramified prime $M$ exceeds $n$. The prime 2 is inert because $-M\equiv5\bmod8$. Every ideal class has an integral representative of norm at most $(2/\pi)\sqrt M<n$ by Minkowski's bound. Every prime ideal factor of such a representative lies above an inert prime and hence is itself a principal ideal. The field therefore has class number one. The class-number-one classification gives $M\le163$, whereas $M\ge4\cdot43-1=171$. This is the required contradiction. [Stark's classification](https://doi.org/10.1307/mmj/1028999653).

## OeisA60841.conjecture1 — integrality of a reciprocal LCM determinant

**Answer.** For $n\ge1$, the reciprocal determinant of $M_{ij}=1/\operatorname{lcm}(i,j)$, $1\le i,j\le n$, is an integer exactly for $1\le n\le34$, $n=36$, and $n=38$. Daniel Veljjanoski recorded a proof on 10 November 2026. Its challenge is the same formal declaration. A different conjecture that denominators are always powers of 2 was disproved at $n=1807$; this counterexample concerns a separate statement. The two-adic argument below and its finite inequalities were checked independently, without rebuilding the external Lean project. [Catalog](https://lefttosolve.com/p/OeisA60841.conjecture1) · [OEIS source](https://github.com/oeis/oeisdata/blob/main/seq/A060/A060841.seq) · [Veljjanoski's proof](https://github.com/veljjanoski/oeis60841-palomar).

Let $E_{id}=1$ if $d\mid i$ and 0 otherwise. The identity $\sum_{d\mid m}\varphi(d)=m$ factors the gcd matrix as $E\operatorname{diag}(\varphi(d))E^\mathsf T$. The determinant of $E$ is 1 because it is unit lower triangular. Scaling each row $i$ and column $j$ by $1/i$ and $1/j$, respectively, gives $M$. Hence the reciprocal determinant is $(n!)^2/\prod_{k\le n}\varphi(k)$.

For every odd prime $p\le97$, count $v_2(p-1)$ once per multiple of $p$. Also count 1 per multiple of each of the six powers $2^j$ with $2\le j\le7$. Multiplicativity of $\varphi$ then bounds the two-adic order of the denominator product below by

$$
c(n)=\sum_{3\le p\le97,\ p\ {\rm prime}}v_2(p-1)\lfloor n/p\rfloor+\sum_{j=2}^{7}\lfloor n/2^j\rfloor .
$$

Denote the weights in these sums by $w_m$. Their sum is 49, and $S=\sum_m w_m/m>2.48$, by direct rational arithmetic. For $n\ge100$, the elementary bound $\lfloor n/m\rfloor\ge(n+1)/m-1$ gives $c(n)\ge(n+1)S-49>2n\ge2v_2(n!)$. Thus the reciprocal determinant has a factor of 2 in its reduced denominator.

For $n=35,37$ and $39\le n\le99$, the minimum of $c(n)-2v_2(n!)$ is 1. Exact divisibility for $1\le n\le38$ gives all the positive cases listed above. A finite check uses the elementary identities $v_2(n!)=\sum_{j\ge1}\lfloor n/2^j\rfloor$ and $\varphi(k)=\#\{i:1\le i\le k,\ \gcd(i,k)=1\}$.
