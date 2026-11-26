# Digit statistics, determinants, and recurrences

## Digit subtraction from a power of ten · A309417

Let $a(n)$ be the number of iterations of $x\mapsto x-s_{10}(x)$ from $10^n$ to zero. The catalog conjectures a consecutive-term ratio of ten. In fact,

$$
a(n)\sim \frac{2\,10^n}{9n}.
$$

Fix $0<\epsilon<4.5$. Among the $10^n$ numbers from zero through $10^n-1$, pad the expansions to length $n$. Under uniform choice these digits are independent with mean $4.5$. Hoeffding's inequality bounds the number with $|s_{10}(x)-4.5n|>\epsilon n$ by $2\cdot10^n\exp(-2\epsilon^2 n/81)$. The positive trajectory is strictly decreasing, so it visits any exceptional integer at most once. Exceptional steps therefore account for $o(10^n/n)$ visits and, since each has length at most $9n$, for total distance $o(10^n)$. The initial step has length one. All steps together traverse exactly $10^n$. Each remaining step has length between $(4.5-\epsilon)n$ and $(4.5+\epsilon)n$. Dividing the remaining distance by these bounds and sending $\epsilon$ to zero proves the asymptotic and the ratio. This also explains why assuming independent digits *along the trajectory* would be unnecessary. Replacing ten by a fixed base $b\ge2$ gives $2b^n/((b-1)n)$ by the same argument.

[Sequence and conjecture](https://oeis.org/A309417) · [Hoeffding's bounded-sum inequality](https://doi.org/10.1080/01621459.1963.10500830).

## Digit range equals mode · A383307

For a uniformly random $n$-digit positive integer, failure to contain both 0 and 9 has probability at most $2(9/10)^{n-1}$. When both occur the range equals 9. The independent uniform suffix of length $n-1$ has a unique winner separated from all other digit counts by at least two with probability tending to one. Indeed, each pairwise count difference is a centered sum of bounded iid variables of positive variance. The central limit theorem and continuity of the normal law imply that the probability of any such difference lying in $[-1,1]$ tends to zero. A union bound over the 45 pairs proves the assertion. By symmetry digit 9 wins this well-separated contest with probability tending to $1/10$; the leading digit cannot change that winner. Hence $a(n)\sim(9/10)10^{n-1}$, proving the proposed ratio ten. The mean-equals-mode cousin A379181 has a different answer because a digit mean of $4.5$ cannot be a mode.

[Sequence and conjecture](https://oeis.org/A383307) · [Mean-equals-mode comparison](https://oeis.org/A379181).

## Integers with two types of factorization · A347748 and A348546

For A347748 the factors must both end in 4 in one factorization and both end in 6 in another. Admissible integers lie in the class $16\bmod20$, equivalently $N=4t$ with $t\equiv4\bmod5$. If such $t$ has a prime divisor $p\equiv2\bmod5$, then $t/p\equiv2\bmod5$ and $N=(2p)(2t/p)$ supplies the 4-ending factors. A divisor $q\equiv3\bmod5$ gives 6-ending factors in the same way. For each of these prime classes the integers omitting all its primes have natural density zero. For any finite subset of those primes, the density avoiding them is the product of $1-1/p$ by the Chinese remainder theorem. The product tends to zero by the divergence of the reciprocal-prime sum in a reduced residue class. Thus A347748 counts a set of natural density $1/20$.

For A348546 the analogous necessary class is $9\bmod10$. A prime factor $p\equiv3\bmod10$ automatically has cofactor $N/p\equiv3\bmod10$. A prime factor $q\equiv7\bmod10$ supplies the second factorization. Almost every integer in the required class has both, by the same argument. Its density is $1/10$. Positive density $\delta$ gives $(9\delta+o(1))10^{n-1}$ such $n$-digit integers by subtraction of the two endpoint counts. Both catalog ratios therefore tend to ten. A search treating the two possible factorizations as independent would miss their common congruence restriction.

[First problem](https://oeis.org/A347748) · [Second problem](https://oeis.org/A348546) · [Related single-factorization density](https://oeis.org/A337856) · [Dirichlet's theorem and reciprocal primes in progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html).

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
