# The true growth rate for digit mean equals mode

Source: [OEIS A379181](https://oeis.org/A379181), including its Mathematica specification: an n-digit nonnegative integer is counted when the unique mode is the arithmetic mean of its digits. All positive-length words are unrestricted in the internal positions. The first digit is nonzero for n>1; the treatment of the one-digit zero cannot affect a limit. [Left to Solve](https://lefttosolve.com/p/oeis-a379181). Standard background on the lattice Fourier argument: [Lawler and Limic, *Random Walk: A Modern Introduction*, ch. 2](https://www.cambridge.org/core/books/abs/random-walk-a-modern-introduction/local-central-limit-theorem/2D2908A7742FFBEF09AFDA3E1F314582). The elementary argument establishing the precise local estimate used here is included below. No claim of publication priority.

**Result.** Set $h_0=h_1=h_4=5/3$ and $h_j=j$ for the remaining decimal digits. Write $Z(r)=\sum_{j=0}^{9} r^{h_j}$. Let $r$ be the unique solution in $(0,1)$ of $rZ'(r)=4Z(r)$ and let $\lambda=Z(r)/r^4$. Then for a constant $C>0$,
$$a(n)\sim C\lambda^n n^{-3/2},\qquad \lim_{n\to\infty}a(n+1)/a(n)=\lambda.$$
Numerically $r\approx0.9319103995938742$ and $\lambda\approx9.82786850121986$. In particular the conjectured ratio 10 fails. The elementary $9.927169\ldots$ ceiling is an independent disproof. The exact formula above requires both a digit-sum constraint and two binding mode inequalities.

**1. Tilt and uniqueness.** Give digit $j$ probability $q_j=r^{h_j}/Z(r)$. Its mean equals $rZ'(r)/Z(r)$ because the three weights at digits 0, 1 and 4 coincide, and their digit labels sum to $5=3(5/3)$. The logarithmic derivative of that weighted mean with respect to $r$ (i.e., its derivative in $\log r$) is the positive variance of $h_j$. The mean tends to $5/3$ as $r\downarrow0$ and equals $4.5$ at $r=1$. Thus the required $r$ exists uniquely. At this value $q_4=q_0=q_1>q_j$ for every $j\notin\{0,1,4\}$, since such $h_j\ge2$.

**2. Change of measure.** First count words with unique mode 4 and mean 4. Let $N_j$ be their digit counts, $S=\sum_j jN_j$, and $L_0=N_4-N_0$, $L_1=N_4-N_1$. On the event $S=4n$,
$$\sum_j h_jN_j=4n-(5L_0+2L_1)/3.$$
Consequently, for any restriction $E$ on words satisfying $S=4n$, their number is
$$\lambda^n\,\mathbf E_q\big[r^{(5L_0+2L_1)/3}\,\mathbf1_E\big].$$
The unique mode conditions against 0 and 1 are $L_0,L_1\ge1$. On this region the weight is at most one. For each of the seven other competitors $j$, $\Pr_q(N_j\ge N_4)\le e^{-c_j n}$ for some $c_j>0$, by the elementary Chernoff bound on iid bounded differences with strictly negative mean. (The mgf of $1_{D=j}-1_{D=4}$ is 1 at zero and has negative derivative.) Dropping these seven inequalities introduces $O(\lambda^n e^{-c n})$ error for some $c>0$.

**3. Lattice audit.** Under $q$ the iid integer increment is
$$X(j)=\left(j-4,\;\mathbf1_{j=4}-\mathbf1_{j=0},\;\mathbf1_{j=4}-\mathbf1_{j=1}\right).$$
All three means vanish. Differences of support points generate $\mathbb Z^3$: $X(3)-X(2)=(1,0,0)$, $X(0)-X(2)=(-2,-1,0)$, $X(1)-X(2)=(-1,0,-1)$. All have positive probability; the determinant of these three differences has absolute value one. The covariance $\Sigma$ is positive definite because a direction of zero variance must annihilate all differences. There is no residue-class obstruction for either the sum or the two tied counts.

For completeness let $T_n=\sum_{s=1}^n X_s$. Fourier inversion on $[-\pi,\pi]^3$ yields
$$\sup_{z\in\mathbb Z^3}\Pr(T_n=z)=O(n^{-3/2}),\qquad n^{3/2}\Pr(T_n=z)\longrightarrow K=1/[(2\pi)^{3/2}\sqrt{\det\Sigma}]$$
for each fixed $z$. Indeed $|\phi(t)|=1$ forces the phases to agree on every support difference, hence $t=0$ on the torus. Off any neighborhood of zero, compactness gives $|\phi(t)|\le\rho<1$. Near zero $\phi(t)=1-t^\top\Sigma t/2+O(\|t\|^3)$, so $|\phi(t)|\le e^{-c'\|t\|^2}$ and the inversion integral is $O(n^{-3/2})$ uniformly. Rescale $t=u/\sqrt n$ to obtain the Gaussian integral and the fixed-$z$ limit. This proof also works for the nonsymmetric increment law.

**4. Leading digit and summation.** Fix any set $A$ of allowed first digits. For every fixed $z$, conditioning on the first digit gives
$$\Pr(T_n=z,D_1\in A)=\sum_{j\in A}q_j\Pr(T_{n-1}=z-X(j))\sim q(A)K n^{-3/2}$$
if $q(A)>0$, with the same uniform $O(n^{-3/2})$ envelope. Evaluate at $z=(0,\ell_0,\ell_1)$ for $\ell_0,\ell_1\ge1$. The lattice estimates and the convergent positive geometric sum
$$G=\sum_{\ell_0,\ell_1\ge1} r^{(5\ell_0+2\ell_1)/3}=\frac{r^{5/3}}{1-r^{5/3}}\frac{r^{2/3}}{1-r^{2/3}}$$
allow dominated convergence after multiplication by $n^{3/2}$. Thus the mean-4 unique-mode contribution with first digit restricted to $A$ is asymptotic to $q(A)KG\lambda^n n^{-3/2}$. For actual integers $A$ excludes zero. Complement every digit $j\mapsto9-j$ to treat mean and unique mode 5. Its words are in bijection with mode-4 words whose first digit is different from **9**, so its constant is $(1-q_9)KG$. The two contributions are disjoint and sum to $C=(2-q_0-q_9)KG>0$ times $\lambda^n n^{-3/2}$.

**5. Competing means.** Any remaining integer mean is at most 3 or at least 6. With $b=4/5$, the number of all decimal words with sum at most $3n$ is bounded by
$$B^n,\qquad B=b^{-3}\sum_{j=0}^9 b^j=8.717049\ldots<9$$
(the decimal may be rounded; $B=(1-b^{10})/[(1-b)b^3]$). Digit complementation bounds the upper tail by the same count. Meanwhile AM–GM on the nine tilted weights at digits $0,\ldots,8$ gives $\sum_{j=0}^8r^{h_j}\ge9r^4$ since $\sum_{j=0}^8h_j=36$. The remaining weight is strictly positive, so $\lambda>9>B$. Both exceptional tails are exponentially smaller than the main asymptotic. This proves the result including its successive-ratio limit.

**Numerical reproduction.** Put $t=r^{1/3}$. The defining equation reduces to
$$5t^{22}+4t^{19}+3t^{16}+2t^{13}+t^{10}-t^4-2t-7=0.$$
Its unique root in $(0,1)$ is $t\approx0.9767679165098407$. With $U(t)=3t^5+t^6+t^9+t^{15}+t^{18}+t^{21}+t^{24}+t^{27}$, one has $\lambda=U(t)/t^{12}$. Rational bisection on $[9/10,1]$ for 60 steps, using $U(l)/u^{12}\le\lambda\le U(u)/l^{12}$ for the resulting bracket $[l,u]$, puts $\lambda$ between 9.82786850121986167 and 9.82786850121986171.
