# Digit statistics, determinants, and recurrences

## Digit subtraction from a power of ten · A309417

Let $a(n)$ be the number of iterations of $x\mapsto x-s_{10}(x)$ from $10^n$ to zero. The catalog conjectures a consecutive-term ratio of ten. In fact,

$$
a(n)\sim \frac{2\,10^n}{9n}.
$$

Fix $0<\epsilon<4.5$. Among the $10^n$ numbers from zero through $10^n-1$, pad the expansions to length $n$. Under uniform choice these digits are independent with mean $4.5$. Hoeffding's inequality bounds the number with $|s_{10}(x)-4.5n|>\epsilon n$ by $2\cdot10^n\exp(-2\epsilon^2 n/81)$. The positive trajectory is strictly decreasing, so it visits any exceptional integer at most once. Exceptional steps therefore account for $o(10^n/n)$ visits and, since each has length at most $9n$, for total distance $o(10^n)$. The initial step has length one. All steps together traverse exactly $10^n$. Each remaining step has length between $(4.5-\epsilon)n$ and $(4.5+\epsilon)n$. Dividing the remaining distance by these bounds and sending $\epsilon$ to zero proves the asymptotic and the ratio. This also explains why assuming independent digits *along the trajectory* would be unnecessary. Replacing ten by a fixed base $b\ge2$ gives $2b^n/((b-1)n)$ by the same argument.

[Sequence and conjecture](https://oeis.org/A309417) · [Hoeffding's bounded-sum inequality](https://doi.org/10.1080/01621459.1963.10500830).

### A fourth-moment proof checked in Lean

Let $A=a(n)$, $B=10^n$, $u=nA/B$, and $s(x)$ be the decimal digit sum. The $A$ positive states form a set $S$ because every subtraction strictly decreases $x$. Telescoping gives $\sum_{x\in S}s(x)=B$. Thus the sum of $D(x)=2s(x)-9n$ along this specific path is $2B-9nA$.

Over all $B$ padded decimal words, appending digit $j$ adds $2j-9$ to $D$. Its mean square is 33 and its mean fourth power is $19338/10$. Odd moments of the increment vanish by symmetry. The resulting recurrence gives $\sum_{x<B}D(x)^4\le3300n^2B$. Including the initial state $B$ increases this bound to at most $10000n^2B$ for $n\ge1$. The fourth-power mean inequality on $S$ gives
$$
 (2B-9nA)^4\le A^3\sum_{x\in S}D(x)^4,\qquad
 n(2-9u)^4\le10000u^3.
$$
For $n\ge10001$, $u>1$ would imply $9u-2>u$ and hence $nu<10000$, a contradiction. Substituting $u\le1$ gives $|u-2/9|\le(10/9)n^{-1/4}$ and therefore the desired consecutive-term ratio. The proof uses no independence assumption on the visited states. [Complete Lean proof](../lean/proofs/oeis-a309417.lean)

### A rate from consecutive decimal blocks

The subtraction count satisfies the stronger estimate
$$
a(n)=\frac{2\,10^n}{9n}\left(1+O\!\left(\frac{\log n}{n}\right)\right).
$$
It follows that $a(n+1)/a(n)=10+O(\log n/n)$.

Take $b=\lceil3\log_{10} n\rceil$, $B=10^b$, and partition $[0,10^n)$ into the blocks $[hB,(h+1)B)$. For large $n$, $b<n$ and $B>9n$. The trajectory starts with $10^n\mapsto10^n-1$. Thereafter every positive step is at most $9n$, so the decreasing trajectory visits each block. Assign a step to the block of its starting point. In any block the first visited point lies within $9n$ of its upper endpoint. The destination of the last departing step lies within $9n$ of its lower endpoint. In the bottom block use the final state 0 as that destination. Telescoping shows that the sum of step lengths assigned to each block is $B+O(n)$ uniformly.

Write $D_h$ for the digit sum of $h$, $\mu=9n/2$, and $A_h=D_h+9b/2$. Every departure in the block has size $D_h+s_{10}(x\bmod B)$ and differs from $A_h$ by at most $9b/2$. Call a block typical when $D_h\ge9(n-b)/4$. There all step lengths are at least a constant times $n$, so the number of departures is $O(B/n)$. The preceding telescoping identity gives its more precise value $B/A_h+O(1+B b/n^2)$.

For uniform $h$ the $n-b$ padded digits are independent. Hoeffding's inequality puts the atypical fraction at $O(e^{-cn})$ for an absolute $c>0$. Each such block accounts for at most $B$ departures, since a positive state is never visited twice. Its comparison term $B/A_h$ is also at most $B$. Summing yields
$$
a(n)=10^n\,\mathbb E[1/A_h]+O\bigl(1+10^n/B+10^nb/n^2+10^n e^{-cn}\bigr).
$$
Now $\mathbb E A_h=\mu$ and $\operatorname{Var}(A_h)=33(n-b)/4$. Writing $z=A_h-\mu$, the identity $1/A_h=1/\mu-z/\mu^2+z^2/(\mu^2 A_h)$ gives $\mathbb E[1/A_h]=1/\mu+O(n^{-2})$: on typical blocks $A_h\gg n$, while the remainder is uniformly bounded on the exponentially small exceptional set. The stated rate follows from $B\ge n^3$ and $b=O(\log n)$. [Original OEIS conjecture](https://oeis.org/A309417)

## Digit range equals mode · A383307

For a uniformly random $n$-digit positive integer, failure to contain both 0 and 9 has probability at most $2(9/10)^{n-1}$. When both occur the range equals 9. The independent uniform suffix of length $n-1$ has a unique winner separated from all other digit counts by at least two with probability tending to one. Indeed, each pairwise count difference is a centered sum of bounded iid variables of positive variance. The central limit theorem and continuity of the normal law imply that the probability of any such difference lying in $[-1,1]$ tends to zero. A union bound over the 45 pairs proves the assertion. By symmetry digit 9 wins this well-separated contest with probability tending to $1/10$; the leading digit cannot change that winner. Hence $a(n)\sim(9/10)10^{n-1}$, proving the proposed ratio ten. The mean-equals-mode cousin A379181 has a different answer because a digit mean of $4.5$ cannot be a mode.

[Sequence and conjecture](https://oeis.org/A383307) · [Mean-equals-mode comparison](https://oeis.org/A379181).

### A finite Fourier proof checked in Lean

Fix two different digits. In a uniform suffix of length $n$, their count difference $D$ changes by $1,-1,0$ with probabilities $1/10,1/10,8/10$. For a fixed modulus $m\ge2$ and $\zeta=e^{2\pi i/m}$, Fourier inversion gives
$$
 \Pr(D\equiv r\bmod m)
 =\frac1m\sum_{j=0}^{m-1}\zeta^{-jr}
 \left(\frac{8+2\cos(2\pi j/m)}{10}\right)^n.
$$
Every nonconstant term decays, so the probability converges to $1/m$. For any fixed integer $r$, the probability that $D=r$ is bounded by the probability of its residue class. Sending $m$ to infinity shows that the probabilities of differences $-1,0,1$ each vanish. A missing digit has probability $(9/10)^n$. With probability tending to one all digits occur and all counts are separated by at least two. Any of the nine permitted leading digits then preserves the winner and gives range nine. The Lean proof checks the bijection with the integers in the catalog definition, including the nonzero leading digit. [Complete Lean proof](../lean/proofs/oeis-a383307.lean)

### An effective error bound for A383307

Let $f_n=a(n)/(9\cdot10^{n-1})$ for $n\ge2$, so that $f_n$ is the required probability for a uniform decimal word with nonzero leading digit. The following estimates quantify the convergence:
$$
-\frac92\sqrt{\frac{5\pi}{8n}}-E_n
\;\le\; f_n-\frac1{10}\;\le\;
\frac1{81}\sqrt{\frac9{10n}}+E_n,
\qquad E_n=\frac{17}{9}\left(\frac9{10}\right)^{n-1}.
$$
In particular the consecutive-term ratio is $10+O(n^{-1/2})$.

For an unrestricted uniform word write $C_j$ for the count of digit $j$, $M=\max_j C_j$, and $U$ for the event of a unique maximum. Let $H$ mean that 9 is the unique winner and $L$ mean that the first digit is nonzero. Symmetry gives $\Pr(H)=\Pr(U)/10$. Conditioning on the counts, the probability that the first digit is 0 is $C_0/n$. On $H$ the other nine labels are exchangeable and have total count $n-C_9$. Therefore
$$
\Pr(H\mid L)=\frac{\Pr(U)}{10}
+\frac1{81}\mathbb E\left[\left(\frac{M}{n}-\frac1{10}\right)\mathbf1_U\right].
$$
For example, this follows by substituting $\mathbb E[C_0\mathbf1_H]=\mathbb E[(n-C_9)\mathbf1_H]/9$ into $\Pr(H\mid L)=(10/9)\mathbb E[(1-C_0/n)\mathbf1_H]$. The correction is nonnegative and at most $\sqrt{9/(10n)}/81$: the maximum centered count divided by $n$ is at most the Euclidean norm of all ten centered frequencies, whose expected square is $9/(10n)$.

For two specified digits, the difference of their counts has per-position characteristic function $4/5+(1/5)\cos t$. Integrating its $n$th power over $[-\pi,\pi]$ and dividing by $2\pi$ gives the probability of an exact tie: integration extracts the constant Fourier coefficient. Since $1-\cos t\ge2t^2/\pi^2$ there, extending the Gaussian upper bound to the real line gives at most $\sqrt{5\pi/(8n)}$. A tie for first entails a tie for some pair, so $\Pr(U^c)\le45\sqrt{5\pi/(8n)}$.

When 0 and 9 both occur, the range equals 9, and the target event agrees with $H$. Conditional on $L$, the probabilities of missing 0 and missing 9 are $(9/10)^{n-1}$ and $(8/9)(9/10)^{n-1}$ respectively. Their sum is $E_n$. Combining the three estimates proves both inequalities. Since $f_n\to1/10$, dividing $10f_{n+1}$ by $f_n$ gives the claimed error rate for the ratio. [Original OEIS conjecture](https://oeis.org/A383307)

## Integers with two types of factorization · A347748 and A348546

For A347748 the factors must both end in 4 in one factorization and both end in 6 in another. Admissible integers lie in the class $16\bmod20$, equivalently $N=4t$ with $t\equiv4\bmod5$. If such $t$ has a prime divisor $p\equiv2\bmod5$, then $t/p\equiv2\bmod5$ and $N=(2p)(2t/p)$ supplies the 4-ending factors. A divisor $q\equiv3\bmod5$ gives 6-ending factors in the same way. For each of these prime classes the integers omitting all its primes have natural density zero. For any finite subset of those primes, the density avoiding them is the product of $1-1/p$ by the Chinese remainder theorem. The product tends to zero by the divergence of the reciprocal-prime sum in a reduced residue class. Thus A347748 counts a set of natural density $1/20$.

For A348546 the analogous necessary class is $9\bmod10$. A prime factor $p\equiv3\bmod10$ automatically has cofactor $N/p\equiv3\bmod10$. A prime factor $q\equiv7\bmod10$ supplies the second factorization. Almost every integer in the required class has both, by the same argument. Its density is $1/10$. Positive density $\delta$ gives $(9\delta+o(1))10^{n-1}$ such $n$-digit integers by subtraction of the two endpoint counts. Both catalog ratios therefore tend to ten. A search treating the two possible factorizations as independent would miss their common congruence restriction.

[First problem](https://oeis.org/A347748) · [Second problem](https://oeis.org/A348546) · [Related single-factorization density](https://oeis.org/A337856) · [Dirichlet's theorem and reciprocal primes in progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html).

### A common finite sieve checked in Lean

The same two classes of odd primes, $3$ and $7$ modulo 10, suffice for both catalog questions. For $N=4t$ such a prime divides $t$ whenever it divides $N$. Its residue modulo 5 supplies the required factorization of $4t$. For $N\equiv9\pmod{10}$, division by either prime leaves the cofactor in that prime's own class modulo 10.

The formal proof derives divergence of $\sum 1/p$ in each class from Mathlib’s pole estimate for its von Mangoldt series. If the reciprocal sum converged, dominated convergence would force $(s-1)\sum_n \Lambda(n)\mathbf1_{n\equiv a}/n^s$ to tend to zero. On prime terms the dominating function is $1/p$, by $t\le e^t$ with $t=(s-1)\log p$, and the prime-power remainder is summable. The pole estimate gives a strictly positive lower limit.

For a finite set $S$ of those primes put $d=\prod_{p\in S}p$. Integers avoiding $S$ are coprime to $d$. Their number in an interval of length $X$ is at most $\varphi(d)(\lfloor X/d\rfloor+1)$, and
$$
 \frac{\varphi(d)}{d}\left(1+\sum_{p\in S}\frac1p\right)\le1.
$$
Choosing $S$ first makes the limiting fraction arbitrarily small. Only a zero-density subset of either ambient progression can fail. This proves the two consecutive-term ratios independently of the sharper deficit estimates below. [Factors ending in 4 and 6](../lean/proofs/oeis-a347748.lean) · [Factors ending in 3 and 7](../lean/proofs/oeis-a348546.lean)

### Exact exceptional integers and the common leading deficit

Let $F_4(X)$ and $F_3(X)$ count qualifying positive integers at most $X$ for A347748 and A348546, respectively. With natural logarithms there is a common positive constant $K$ such that
$$
\begin{aligned}
 F_4(X)&=\frac{X}{20}-\frac{K}{4}\frac{X}{\sqrt{\log X}}+
 O\!\left(\frac{X}{(\log X)^{5/8}}\right),\\
 F_3(X)&=\frac{X}{10}-K\frac{X}{\sqrt{\log X}}+
 O\!\left(\frac{X}{(\log X)^{5/8}}\right).
\end{aligned}
$$

**Exact test.** In the first problem put $N=4u$ and require $u\equiv4\pmod5$. A factorization into two factors ending in 4 is equivalent to a divisor of $u$ congruent to 2 modulo 5. Both factors then have that residue after division by 2. The 6-ending factorization similarly requires a divisor congruent to 3. In the second problem put $N=u$ and require $u\equiv9\pmod{10}$. Now $u$ is odd, and reduction modulo 5 identifies the units modulo 10 with the units modulo 5. The two required factor pairs again amount to divisors in both classes 2 and 3 modulo 5.

Index the four unit classes modulo 5 by the exponents of the generator 2. The exponents of the prime factors of $u$, with multiplicity, sum to 2 modulo 4. Divisors correspond to subset sums. Subset sums 1 and 3 both occur unless one of the following two disjoint possibilities holds.

1. Every prime factor is $1$ or $4$ modulo 5. The ambient residue condition makes the number of 4-class prime factors odd.
2. Apart from primes $1$ modulo 5 there are exactly two prime factors, counted with multiplicity, both $2$ modulo 5 or both $3$ modulo 5.

Indeed if exponents 1 and 3 both appear, the singleton subsets suffice. One odd exponent together with an exponent 2 supplies both odd residues. Otherwise all odd exponents have the same sign and the other exponents are zero. Their number must be 2 modulo 4. At count 2 only one odd residue is attainable, while at count at least 6 a singleton and a triple give both. This also proves that an odd $u$ qualifies in the second problem precisely when $4u$ qualifies in the first.

**Counting the exceptions.** For the first class, all allowed primes are odd, so it is identical for the two problems in the variable $u$. Its unrestricted semigroup has Dirichlet series $D(s)=\prod_{p\equiv1,4\ (5)}(1-p^{-s})^{-1}$. Write $\chi$ for the quadratic character modulo 5. Comparing Euler factors gives
$$
D(s)^2=\zeta(s)(1-5^{-s})L(s,\chi)\prod_{p\equiv2,3\ (5)}(1-p^{-2s}).
$$
Chang and Martin's Theorem 3.4 for two reduced classes of the fixed modulus 5 gives the unrestricted count $2K X/\sqrt{\log X}+O(X/(\log X)^{3/2})$, where
$$
K=\frac{1}{2\sqrt\pi}\left(\frac45L(1,\chi)\prod_{p\equiv2,3\ (5)}(1-p^{-2})\right)^{1/2}.
$$
To select an odd number of 4-class factors, give those primes weight $-1$, give 1-class primes weight $1$ and all others weight zero, extending completely multiplicatively. This signed function has prime mean zero. The fixed-modulus summatory estimate in Loughran and Matthiesen, Lemma 2.8, gives $O(X/\log X)$ for its signed sum. Half the difference of the unrestricted and signed counts selects precisely the required integers.

For the second class give prime residues 1, 2, 3, 4 modulo 5 the weights $1,1/4,1/4,0$, and give 5 weight zero. This bounded, completely multiplicative function has prime mean $3/8$. Its value is $1/16$ on every integer in the second class, so the same lemma bounds their count by $O(X/(\log X)^{5/8})$. The estimate applies with finite exceptional primes because the weights on all other primes depend only on their classes modulo 5. Finally the ambient progressions supply $X/20+O(1)$ and $X/10+O(1)$ integers. In the first problem the cutoff for $u$ is $X/4$, giving the extra factor $1/4$. Subtracting the two exceptional counts proves the formulas.

[Chang and Martin, Theorem 3.4](https://arxiv.org/abs/1908.00035) · [Loughran and Matthiesen, Lemma 2.8](https://arxiv.org/abs/1904.12845) · [Exact factorization checks](../checks/paired_factorizations.py)

## Numerators of Hankel determinants · A122251

Fix a prime $p$ and $N=n+1$. For $H_{ij}=(1+p(i+j))^{-1}$, indexed from $0$ through $n$, Cauchy's double alternant yields

$$
\det H=\frac{p^{N(N-1)}\prod_{k=0}^{N-1}(k!)^2}
{\prod_{i,j=0}^{N-1}(1+p(i+j))}.
$$

The denominator is prime to $p$. For any other prime $q$ and any positive $e$, each row contains at least $\lfloor N/q^e\rfloor$ denominator factors divisible by $q^e$ since $p$ is a unit modulo $q^e$. Its $q$-valuation is at least that of $N!$. Also $k!(N-1-k)!\mid (N-1)!$ for every $k$, so $\prod(k!)^2\mid((N-1)!)^N$. Thus every numerator prime other than $p$ cancels. The reduced numerator is exactly

$$
p^{\,n(n+1)+2\sum_{k=1}^{n} v_p(k!)}
=(p^2)^{\sum_{k=1}^n\sum_{j=0}^{n}\lfloor k/p^j\rfloor}.
$$

This includes $n=0$. For entries $1/(a+d(i+j))$ with coprime positive $a,d$, the identical argument shows that the surviving primes are drawn from the divisors of $d$, with exponent $N(N-1)v_q(d)+2\sum_k v_q(k!)$ for each $q\mid d$.

[Sequence and conjecture](https://oeis.org/A122251) · [Krattenthaler, *Advanced determinant calculus*, equation 2.7](https://www.mat.univie.ac.at/~slc/wpapers/s42kratt.pdf).

### A recursive proof checked in Lean

Write $H_N(a,p)_{ij}=1/(a+p(i+j))$ for $0\le i,j<N$. Elimination at the top left gives
$$
 \det H_{n+1}(a,p)=\frac1a
 \left(\frac{p^n n!}{\prod_{i=1}^n(a+pi)}\right)^2
 \det H_n(a+2p,p).
$$
Indeed its Schur complement is $H_n(a+2p,p)$ with row and column $i$ both scaled by $pi/(a+pi)$ for $1\le i\le n$ in the original indexing.

Let $m=n!/p^{v_p(n!)}$. Since $p$ is invertible modulo $m$, the $n$ progression terms are congruent, after division by $p$ modulo $m$, to $n$ consecutive integers. Their product is divisible by $n!$, so $m$ divides the progression product. If $p\nmid a$, none of the progression terms is divisible by $p$. The sole surviving numerator factor at this step is $p^{2(n+v_p(n!))}$. Induction from the one-by-one determinant, followed by Legendre’s factorial formula, gives the exact signed numerator in the catalog for $a=1$. [Complete Lean proof](../lean/proofs/oeis-a122251.lean)

### Local Smith factors and denominators of every inverse entry

Take $H_{ij}=1/(a+d(i+j))$ for $0\le i,j<N$, with $a,d>0$ coprime. For each prime $p\mid d$, all entries are $p$-adic integers. The $N$ exponents in the Smith normal form over $\mathbb Z_p$, in increasing order, are
$$
e_j=2j\,v_p(d)+2v_p(j!),\qquad 0\le j<N.
$$
For row and column index sets $I,J$ of size $k$, the Cauchy determinant formula gives the valuation $k(k-1)v_p(d)+v_p(V(I))+v_p(V(J))$, where $V$ is the Vandermonde product of index differences. Each denominator factor is a unit at $p$. For distinct nonnegative integer indices $x_i$, the determinant of the integer matrix $[\binom{x_i}{j}]_{0\le i,j<k}$ equals $V(x)/\prod_{j<k} j!$, by the degrees and leading coefficients of the binomial polynomials. Thus the initial consecutive sets $I=J=\{0,\ldots,k-1\}$ attain the minimum valuation among all $k$-minors. The successive differences of these minimum valuations give the displayed Smith factors.

There is also an entrywise integrality result. Put $P_i=\prod_{h=0}^{N-1}(a+d(i+h))$ and $B_i=i!(N-1-i)!$. Cofactor division using the same determinant formula gives
$$
(H^{-1})_{ij}=(-1)^{i+j}\frac{P_iP_j}{(a+d(i+j))d^{2N-2}B_iB_j}.
$$
For $p\mid d$ every factor of $P_iP_j$ and $a+d(i+j)$ is a $p$-unit, giving the exact denominator valuation $(2N-2)v_p(d)+v_p(B_iB_j)$. For $q\nmid d$, any progression segment of length $h$ and difference $d$ has product with $q$-valuation at least $v_q(h!)$: for each power $q^e$ the segment contains at least $\lfloor h/q^e\rfloor$ multiples. The product $P_i/(a+d(i+j))$ splits into lengths $j$ and $N-1-j$ and therefore absorbs the $q$-part of $B_j$. The full product $P_j$ absorbs the $q$-part of $N!$, hence of $B_i$. Consequently the reduced denominator of the $(i,j)$ inverse entry is exactly
$$
d^{2N-2}\prod_{p\mid d}p^{v_p(B_iB_j)}.
$$
For $d=1$ this gives an integral inverse. For $N=1$ it gives denominator one and a single zero Smith exponent. These statements refine the determinant result but are only proved in writing here. [Classical Cauchy inverse and Hilbert-matrix context](https://www.govinfo.gov/content/pkg/GOVPUB-C13-0aff8ffb3645cbacfc18fe8af055fdf4/pdf/GOVPUB-C13-0aff8ffb3645cbacfc18fe8af055fdf4.pdf)

## A characteristic-polynomial coefficient · A001752

Put $M_{ij}=\lfloor(j-i+1)/2\rfloor$. The coefficient $c_n$ of $x^{n-2}$ in $\det(xI-M)$ is the sum of the two-by-two principal minors. The diagonal vanishes. Entries at separation $d>0$ contribute $-M_{i,i+d}M_{i+d,i}=\lfloor d^2/4\rfloor$, and there are $n-d$ such pairs. Hence $c_n=\sum_{d=1}^{n-1}(n-d)\lfloor d^2/4\rfloor\ge0$. The first differences of $\lfloor d^2/4\rfloor$ are $\lfloor d/2\rfloor$, giving its generating function $z^2/[(1-z)^3(1+z)]$. Convolution with the positive integers gives $\sum c_nz^n=z^3/[(1+z)(1-z)^5]$ when the missing small coefficients are set to zero. This proves $c_n=a(n-3)$ for $n>2$. An equivalent trace route uses $-\operatorname{tr}(M^2)/2$.

[Original conjecture and generating function](https://oeis.org/A001752).

## A permanent and an incomplete gamma function · A134558

Expand the permanent of $J+kI$, with $J$ the all-ones matrix, by marking the diagonal factors from which the $k$ term is chosen. A specified set of $j$ marks forces those positions to be fixed and leaves $(n-j)!$ completions. Therefore

$$
\operatorname{per}(J+kI)=\sum_{j=0}^{n}\binom nj k^j(n-j)!
=n!\sum_{j=0}^n k^j/j!=e^k\Gamma(n+1,k).
$$

The last identity follows by integration by parts for the upper incomplete gamma function. The empty permanent gives the correct $n=0$ convention. The exponential generating function in the matrix size is independently $e^{kz}/(1-z)$.

[Sequence](https://oeis.org/A134558) · [NIST DLMF, special values](https://dlmf.nist.gov/8.4).

## Fibonacci squares on arithmetic progressions · A047946

For fixed $n>0$ set $s=(-1)^n$, $a=5F_n^2+3s$ and $u_j=F_{nj}^2$. Squaring Binet's formula writes $u_j$ as a linear combination of $j$th powers of $\alpha^{2n},\beta^{2n},s$, where $\alpha,\beta$ are the roots of $x^2-x-1$. The first two roots sum to $5F_n^2+2s$ and their product is one. The three elementary symmetric functions are $a,sa,s$, respectively. Thus

$$
u_{j+3}=a u_{j+2}-sa u_{j+1}+s u_j.
$$

This gives both parity signatures in the source. The same characteristic roots follow from the symmetric square of the Fibonacci transfer matrix.

[Sequence and conjecture](https://oeis.org/A047946).

## Two periodic continued fractions · A041243 and A042220

Let $M(t)=\left(\begin{smallmatrix}t&1\\1&0\end{smallmatrix}\right)$. The standard complete-quotient algorithm gives the following repeating blocks, excluding the integer part. The matrix products are in the displayed digit order.

| Radicand | Repeating digits | Product |
|---|---|---|
| 133 | 1,1,7,5,1,1,1,2,1,1,1,5,7,1,1,22 | $\left(\begin{smallmatrix}5057659&2693520\\224460&119539\end{smallmatrix}\right)$ |
| 636 | 4,1,1,3,3,12,3,3,1,1,4,50 | $\left(\begin{smallmatrix}6981451&1529220\\139020&30451\end{smallmatrix}\right)$ |

Both blocks have even length $L$ and determinant one. Advancing by a period acts on the convergent state by the period matrix at that phase. Cyclic shifts have the same trace and determinant, and reversing matrix order transposes their product. Cayley–Hamilton gives $u_{j+2L}=\operatorname{tr}(T)u_{j+L}-u_j$ for each phase $j\ge0$. For the denominators of $\sqrt{133}$ the trace is $5{,}177{,}198$, and for the numerators of $\sqrt{636}$ it is $7{,}011{,}902$. These are exactly the proposed long recurrences. For reproducing the blocks, start with $a_0=\lfloor\sqrt D\rfloor$, $m=0$, $d=1$ and update $m'=da-m$, $d'=(D-(m')^2)/d$, $a'=\lfloor(a_0+m')/d'\rfloor$.

[Denominators](https://oeis.org/A041243) · [Numerators](https://oeis.org/A042220) · [*Continued Fractions and Linear Recurrences*](https://cs.uwaterloo.ca/~shallit/Papers/cflr.pdf).

## Modular periods of a hyperbolic-sine series · A224899

For $n\ge1$ write $a(n)=\sum_k n![x^n]\sinh(kx)^k$. Its $k$th summand counts $k^n$ times the number of ordered partitions of $n$ labels into $k$ nonempty odd-sized blocks. The factor ordering the blocks supplies $k!$, so all terms with $k\ge p$ vanish modulo a prime $p$. For odd $p$ every surviving term can also be written

$$
2^{-k}\sum_{j=0}^k(-1)^j\binom kj[k(k-2j)]^n.
$$

Fermat's theorem makes this expression periodic with period $p-1$ starting at $n=1$, including zero bases. For $p=2$ only $k=1$ survives, so the terms alternate between one and zero and have least period two. In particular $a(1)=1$ and $a(2)=8$ already refute the literal period-one claim. The conclusion for odd primes asserts a period and leaves its minimality open where relevant.

[Sequence and wording](https://oeis.org/A224899).

## Connected induced subgraphs of a prism · A286182

This formula already follows from Andrew Vince's enumeration. There is also a three-state transfer proof. Write $P_n=((1+\sqrt2)^n-(1-\sqrt2)^n)/(2\sqrt2)$ and $Q_n=(1+\sqrt2)^n+(1-\sqrt2)^n$. In a nonempty occupied rung let its state be top, bottom, or both. Adjacent occupied rungs have an edge between them precisely when the states are compatible, with adjacency matrix

$$
A=\begin{pmatrix}1&0&1\\0&1&1\\1&1&1\end{pmatrix}.
$$

If the support is a proper interval of $\ell$ rungs, all neighboring pairs must be compatible. There are $n$ choices of start and $\mathbf1^\top A^{\ell-1}\mathbf1=P_\ell+P_{\ell+1}$ words, since that sum starts $3,7$ and satisfies the Pell recurrence on the symmetric subspace. Summing $\ell=1,\ldots,n-1$ gives $n(P_{n+1}-2)$.

For full support at most one incompatible seam is allowed because the contracted rung graph is a cycle. If $B$ swaps the top and bottom states and has zero row and column for the third state, the count is $\operatorname{tr}(A^n)+n\operatorname{tr}(BA^{n-1})$. The antisymmetric line contributes $1$ to the first trace and $-1$ to the second. On the symmetric subspace $A$ has eigenvalues $1\pm\sqrt2$ and $B$ projects onto the equal-singleton direction. In the orthonormal symmetric basis $A$ has diagonal entries one and off-diagonal entries $\sqrt2$, so the contribution to the second trace is $Q_{n-1}/2$. Adding gives $1-3n+Q_n+3nP_n$ using $P_{n+1}+Q_{n-1}/2=3P_n$. This agrees with the directly counted degenerate terms $3,13$ at $n=1,2$ and satisfies the proposed recurrence with characteristic polynomial $(t-1)^2(t^2-2t-1)^2$.

[Sequence and recurrence](https://oeis.org/A286182) · [Vince, Lemma 7.2](https://people.clas.ufl.edu/avince/files/JGTfinal2.pdf).
