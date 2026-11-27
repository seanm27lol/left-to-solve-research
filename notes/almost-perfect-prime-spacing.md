# Dispersion of the odd primes in an almost-perfect number

Let $N=2^t$ with $t\ge1$. Write a possible non-power-of-two almost-perfect number as $2^{t-1}M$, where $M=\prod_{i=1}^m p_i^{2e_i}$, $p_1<\cdots<p_m$ are odd primes, and $e_i\ge1$. The divisor sum equation is $(N-1)\sigma(M)=NM-1$. Put $S=\sum_i p_i$ and $W=p_m-p_1$. The exponents in the odd part are even because its divisor sum must be odd. The bounds below allow all positive $e_i$.

## Envelopes for the divisor sum

Set $f(x)=\log(1+x^{-1}+x^{-2})$ and $H(x)=\log(x/(x-1))$ for $x>1$. Both are decreasing and strictly convex. For example,
$$
 f''(x)=\frac{2x^3+7x^2+4x+2}{x^2(x^2+x+1)^2},\qquad H''(x)=\frac{2x-1}{x^2(x-1)^2}.
$$
The finite geometric sum gives the necessary inequalities
$$
 \sum_i f(p_i)<\log\frac N{N-1}\le\sum_i H(p_i).
$$
The strict lower inequality follows from $(N-1)\sigma(M)/M=N-1/M$; the upper one uses integrality. Indeed, were the upper product $\prod_i p_i/(p_i-1)$ less than $N/(N-1)$, then $N-(N-1)\prod_i p_i/(p_i-1)\ge1/\prod_i(p_i-1)>1/M$. This contradicts $\sigma(M)/M<\prod_i p_i/(p_i-1)$.

## Individual endpoints for three primes

For $m=3$, put $p=p_1,r=p_2,s=p_3$ and $\mu=S/3$. We prove
$$
 S\ge9N-1,\qquad p<3N-\sqrt N-1,\qquad s>3N+\sqrt N.
$$
For the trace bound, $(p,r,s)$ is more spread than $(\mu-2,\mu,\mu+2)$ in the sense of majorization: its minimum is no greater and its maximum no smaller, since adjacent odd primes differ by at least 2. Convexity of $f$ gives a larger or equal sum at $(p,r,s)$. If $S\le9N-3$, monotonicity bounds that sum below by its value on $U=(3N-3,3N-1,3N+1)$. At this comparison triple
$$
 (N-1)\prod_{u\in U}(u^2+u+1)-N\prod_{u\in U}u^2
 =81N^4-117N^2+57N-21>0\quad(N\ge2).
$$
This contradicts the lower envelope. Since $S$ is odd, $S\ge9N-1$.

Let $y=\sqrt N$, $p_0=3N-y-1$, $s_0=3N+y$, and $S_*=9N-1$. If $p\ge p_0$, then $(p_0,p_0+2,S-2p_0-2)$ majorizes $(p,r,s)$: the first entry is no larger and the third no smaller because $r\ge p_0+2$. Hence its sum of $H$ bounds the target sum from above. Lowering $S$ to $S_*$ increases this bound. At $U=(p_0,p_0+2,S_*-2p_0-2)$ one has
$$N\prod_{u\in U}(u-1)-(N-1)\prod_{u\in U}u=(y-1)(2y+1)(3y-1)>0.$$
This contradicts the upper envelope. If $s\le s_0$, apply the same argument to the majorant $(S-2s_0+2,s_0-2,s_0)$; the first coordinate is at most $p$ since $r\le s_0-2$. After lowering $S$ to $S_*$ all coordinates are greater than 1, and this time the displayed product difference is $y(2y+1)(3y-2)>0$.

## A bound independent of the number of odd primes

For every $m\ge3$ and every $N=2^t$ a hypothetical solution satisfies
$$
 W>\sqrt{4N-1}-2.
$$
For $N\ge16$ we also have the explicit trace bound $S\ge S_0+\eta_m$, with $S_0=m^2N-m(m-1)/2$ and $\eta_m=2$ for $m\equiv0,3\pmod4$, and $1$ otherwise.

Set $x_0=S_0/m$ and $t_i=i-(m+1)/2$. The consecutive comparison values $x_0+t_i=m(N-1)+i$ give an exact telescoping identity
$$
 \sum_i H(x_0+t_i)=\log\frac{N}{N-1}.
$$
If $S\le S_0$, convexity and monotonicity, using the minimum spacing 2, give $\sum_i f(p_i)\ge\sum_i f(x_0+2t_i)$. Indeed the differences $p_i-(S/m+2t_i)$ are nondecreasing with mean zero, which proves majorization of the equally spaced list. Let $a=x_0-(m-1)$ and $b=x_0+(m-1)$. On $[a,b]$ one has $H''(x)>2/b^3$. Using the convex function $H(x)-x^2/b^3$ on the two centered lists with offsets $2t_i$ and $t_i$, we obtain
$$
 \sum_i [H(x_0+2t_i)-H(x_0+t_i)]\ge \frac{3}{b^3}\sum_i t_i^2
 =\frac{m(m^2-1)}{4b^3}.
$$
The identity $f(x)=H(x)+\log(1-x^{-3})$ and $-\log(1-u)\le u/(1-u)$ bound the total loss in passing from $H$ to $f$ by $m/(a^3-1)$. For $N\ge16,m\ge3$ we have $a>40$, $b/a<8/7$ and $m^2-1\ge8$, so the gain is larger than the loss. This would give $\sum f(p_i)>\log[N/(N-1)]$, a contradiction. Thus $S>S_0$, and the parity $S\equiv m\pmod2$ supplies $S\ge S_0+\eta_m$.

Put $\mu=x_0+\eta_m/m$, and $v_i=p_i-S/m$. The upper envelope and Jensen's inequality give $\sum_i H(p_i)\ge mH(x_0)$. If $\mu>W+1$, lowering each coordinate to $\mu+v_i$ gives an upper bound for that sum. Taylor's theorem about $\mu$ and $H''(x)<2/(x-1)^3$ give
$$
 m[H(x_0)-H(\mu)]\le\frac{\sum_i v_i^2}{(\mu-W-1)^3}.
$$
The left side exceeds $\eta_m/\mu^2$ because $-H'(u)=1/[u(u-1)]$. Write $q_m=\lfloor m^2/4\rfloor$. The sum $\sum_i v_i^2$ is at most $q_m W^2/m$: this is the maximum of the convex variance sum on a cube of side $W$, obtained by placing the coordinates at the two endpoints as evenly as possible. Since $(1-u)^3\ge1-3u$ for $0\le u\le1$,
$$
 \frac{q_mW^2}{m\eta_m}+3(W+1)\ge\mu .
$$
The same inequality holds immediately if $\mu\le W+1$. Now $q_m\le m^2/4$ and $\eta_m\ge1$ yield
$$
 W^2+\frac{12}mW+2+\frac{10}m-\frac4{m^2}\ge4N .
$$
For $m\ge3$ the left side is less than $W^2+4W+5$, proving the claimed bound. If $N\le8$, it follows directly from $W\ge4$. The derivation leaves $m$ unbounded.

For fixed $m$ the last variance estimate also gives
$$
\liminf_{N\to\infty}\frac{W}{\sqrt{N}}\ge m\sqrt{\frac{\eta_m}{\lfloor m^2/4\rfloor}}
$$
along any sequence of candidates. It suffices to divide the estimate by $N$ on a subsequence with $W/\sqrt N$ bounded, since $\mu/N\to m$ there.

## A sharper three-prime width bound

With exactly three odd prime factors, $s-p>3\sqrt N-1$ holds for all $t\ge1$.

Let $m=(p+r+s)/3$ in the remainder of the proof. For $M=p^{2i}r^{2j}s^{2k}$ put $P=prs$ and $V=(p-1)(r-1)(s-1)$. The infinite geometric sums give $\sigma(M)/M<P/V$. Hence
$$E=(N-1)P-NV>-V/M>-1.$$
The integer $E$ is nonnegative. Put $W=s-p$, $u_1=p-m$, $u_2=r-m$, $u_3=s-m$, $L=\sum u_i^2/2$, and $T=u_1u_2u_3$. Expanding $P=m^3-mL+T$ and $V=(m-1)^3-(m-1)L+T$ yields
$$E=C(m)+(m-N)L-T,\qquad C(m)=-m^3+3Nm^2-3Nm+N.$$

Writing $r=p+\theta W$ with $0\le\theta\le1$ gives $L=W^2(1-\theta+\theta^2)/3\le W^2/3$. Also
$$
|T|=\frac{W^3}{27}(1+\theta)(2-\theta)|2\theta-1|\le\frac{2W^3}{27}.
$$
Indeed for $v=|2\theta-1|$ the product of the last three factors is $v(9-v^2)/4\le2$. Therefore
$$E\le C(m)+(m-N)W^2/3+2W^3/27.$$

Suppose $W\le 3\sqrt N-1$. The right-hand side increases with $W$ for $m\ge m_0=3N-1/3$, a condition already proved. It decreases with $m$ on that range, because its derivative is at most $-3m^2+6Nm-3N+3N=-3m(m-2N)<0$. Substitute $m_0$ and $3\sqrt N-1$ to obtain
$$
E\le-\frac{54N\sqrt N+27N-36\sqrt N+4}{27}<0 .
$$
The contradiction proves the claimed width bound.



## Squarefree roots when the level is an odd power of two

Define $\Phi(x)=x^2+x+1$. Suppose $i=j=k=1$ and $t\ge3$ is odd. Then $N\equiv2\pmod3$. If $3\mid P$, the right side of $(N-1)\Phi(p)\Phi(r)\Phi(s)=NP^2-1$ is 2 modulo 3, whereas the left can only be 0 or 1. Thus $3\nmid P$ and the right side is 1 modulo 3. Since $\Phi(x)\equiv0\pmod3$ at $x\equiv1\pmod3$, this forces all three primes to be 2 modulo 3.

Every prime divisor $q$ of any $\Phi(x)$ divides $NP^2-1$ and is odd. Thus $2$ is a square modulo $q$ because $t$ is odd and $2^tP^2\equiv1\pmod q$. By the supplementary law of quadratic reciprocity, $q\equiv1,7\pmod8$, so $\Phi(x)\equiv1,7\pmod8$. Of the four residues $5,11,17,23\pmod{24}$ for $x$, only $5,23$ have this property. At these residues $\Phi(x)$ is $7,1\pmod8$, respectively. The divisor equation modulo 8 gives $\Phi(p)\Phi(r)\Phi(s)\equiv1$, so the count of primes equal to $5\pmod{24}$ is even.

As $9N\equiv0\pmod{24}$, the already established lower bound $p+r+s\ge9N-1$ and the two possible residue patterns sharpen the result:

| Residues of the three primes modulo 24, in any order | Lower bound for $p+r+s$ | Width $W=s-p$ |
|---|---:|---:|
| $5,5,23$ | $9N+9$ | $W>3\sqrt{6N}-3$ |
| $23,23,23$ | $9N+21$ | $W>6\sqrt{3N}-6$ |

To check the two width bounds, repeat the preceding argument with the corresponding lower bound on $m$. At the proposed widths, $W^2<108N$ and $m\ge3N+3$. The derivative of $C(m)+(m-N)W^2/3+2W^3/27$ with respect to $m$ is at most $-3m(m-2N)+33N<0$ for $N\ge8$. For the first row evaluate the upper bound at $m=3N+3$, $W=3v-3$ and $v=\sqrt{6N}$. Its value is $-(19v^2+36v+60)/3$. For the second row, $m=3N+7$, $W=6v-6$ and $v=\sqrt{3N}$ give $-(182v^2+360v+825)/3$. Both contradict $E\ge0$.

## Splitting the cyclotomic factors at even levels

Suppose the three exponents in the odd part are all two and $t$ is even. Put $u=2^{t/2}$ and $P=prs$. The two odd integers $uP-1$ and $uP+1$ are coprime, and their product is $(N-1)\Phi(p)\Phi(r)\Phi(s)$. If each cyclotomic factor is a prime power, each one divides exactly one side. This remains true with multiplicities when two factors use the same prime. Some side consequently contains the product of two cyclotomic factors, so
$$
p^2r^2<\Phi(p)\Phi(r)\le uP+1.
$$
Integrality and the opposite parity of $pr$ and $us$ give $pr<us$. Each prime $q$ exceeds $N$ because $1+1/q< N/(N-1)$, so $s>\sqrt N\,p$. Thus whenever $s\le pr/\sqrt N$, at least one cyclotomic factor must have prime divisors on both sides.

## Scope and reproduction

Shnoudi reports exclusions through $t=16$ with three odd primes at arbitrary exponents and through $t=20$ when all exponents are two. Theorem 9.6 also reports a calculation excluding the latter case at any level when the largest-prime component quotient is at most 500,000. The spacing bounds above allow that quotient to grow and leave sufficiently dispersed primes open. The companion note gives congruences involving $p+1,r+1,s+1$. [Congruences](almost-perfect-prime-congruences.md). [Shnoudi, October 2026, Theorems 7.8 and 9.6](https://doi.org/10.5281/zenodo.23674490).

Run `python checks/almost_perfect_prime_spacing.py` with SymPy 1.14 to verify the polynomial identities and constants used above.

The [component audit](almost-perfect-component-audit.md) gives the subsequent restrictions on quotient divisors, even-level splits and the gap between the top two primes.
