# A sublinear bound for the shared negative shifts

Let $7\le d<e<a<b<c<2d$ be primes, let $n=abcde$, and assume the signs are negative at $d,e$ and positive at $a,b,c$. Write $A=abc$, $B=ab+ac+bc$. Assume the signed equation $Bde-A(d+e)=1$ and the five required shifts $d+1,e+1,a-1,b-1,c-1\mid n-1$. These are necessary conditions for a five-prime Chebyshev candidate in this ordering. Put $g=\gcd(d+1,e+1)$ and $k=(d+1)/g$.

**Theorem.** Every such candidate satisfies
$$
g<(16k)^{357},\qquad g<16(d+1)^{357/358}.
$$
In particular $g/(d+1)\to0$ along any sequence of candidates with $d\to\infty$. For each prescribed $k$, the inequality gives an effective finite search. The [earlier one-tenth bound](https://github.com/seanm27lol/left-to-solve-research/blob/521efbeb8e1c2e55da3605766f28216bc7f0d176/notes/chebyshev-shift-bound.md) is stronger at ordinary numerical scales. As $d$ grows, the new conclusion forces the ratio $k$ to grow as well. An upper bound on $k$ remains open.

## 1. The polynomial family

Set $\ell=(e+1)/g$, $m=(\ell-k)^2$, $t=k\ell$, and $s=k+\ell$. The [negative-shift parametrization](https://github.com/seanm27lol/left-to-solve-research/blob/521efbeb8e1c2e55da3605766f28216bc7f0d176/notes/chebyshev-shift-bound.md) gives $2\le k<\ell<2k$, $d=kg-1$, $e=\ell g-1$, and an integer $h$ defining three polynomials in $X$.
$$
 D=tX^2-sX+1,\qquad A_*=m+X(ts-2t^2X+hD),\qquad
 B_*=-m+shX^2-2X(h+ts).
$$
At $X=g$ they equal $de,mA,mB$, respectively. Thus $h>0$, since
$$hde=m(A-1)/g+t(2tg-s)>0.$$
The previous proof gives $A<4d^2e$ using the signed reciprocal equation and $c<2d$. It follows that
$$h<4km+\frac{2t^2g}{de}<4km+\frac{8k\ell}{g},$$
where $d>kg/2$ and $e>\ell g/2$. If $h>4km$, its integrality already gives $g<8k\ell$. Below suppose $0<h\le4km$.

## 2. Bounding the common factors of positive shifts

Use the integer polynomials
$$
P=2A_*-B_*+m,\qquad Q=A_*D-m.
$$
Every divisor shared by a pair of the positive shifts divides both $P(g)=m(2A-B+1)$ and $Q(g)=m(n-1)$. Indeed, if $a,b\equiv1$ modulo such a divisor, then $A\equiv c$, $B\equiv1+2c$. The shifts divide $n-1$ by hypothesis.

We show that $P,Q$ are coprime over $\mathbb Q$. This statement needs the restricted range of $h$. Normalize by putting $r=(\ell-k)/k$, $H=h/k^3$, and substituting $X=x/k$. Then $0<r<1$ and $0<H\le4r^2$. Dividing the specialized polynomials $P(x/k),Q(x/k)$ by $k^2$ gives precisely the polynomials obtained from the definitions above with $k=1$, $\ell=1+r$, and $h=H$. In this paragraph use those normalized polynomials and write $F(x)=Q(x)/x$. The constant of $P$ is $4r^2$. The exact resultant in $x$ is
$$
\operatorname{Res}_x(P,F)=r^2(1+r)^2H^3 G(r,H).
$$
The [symbolic certificate](../checks/chebyshev_uniform_overlap.py) forms these polynomials and computes the resultant over the rationals. To verify its sign everywhere, put $H=4r^2 y$ and expand $G(r,4r^2y)$ in the tensor-product Bernstein basis of bidegree $(12,4)$. All 65 coefficients lie between $64$ and $20224$. In detail, for monomial coefficients $c_{mn}$ the coefficient at $(i,j)$ is
$$
\sum_{m=0}^i\sum_{n=0}^j c_{mn}
\frac{\binom{i}{m}}{\binom{12}{m}}\frac{\binom{j}{n}}{\binom4n}.
$$
The Bernstein basis consists of nonnegative functions summing to one on the unit square, so this exact coefficient check proves strict positivity for the required continuum of shapes. Since $P(0)\ne0$, $P$ and $Q=xF$ are coprime as well. Undoing the normalization preserves coprimality.

Return to the original integer polynomials and let $\Delta=|\operatorname{Res}(P,Q)|>0$. The resultant is an integral polynomial combination of $P,Q$, so each pair-gcd divides $\Delta$. Set
$$
R=(a-1)(b-1)(c-1),\qquad L=\operatorname{lcm}(a-1,b-1,c-1),\qquad w=R/L .
$$
For any prime, sort its valuations in the three shifts as $u\le v\le z$. Then its valuation in $w$ is $u+v\le2v$, while the gcd of the two shifts with largest valuations has valuation $v$. Consequently $w\mid\Delta^2$.

## 3. A remainder that never vanishes identically

Write $S=a+b+c$, $J=n-1-tg^2R$, $\kappa=J/L\in\mathbb Z$, and $\lambda=\kappa/w=J/R$. Then $n-1=(tg^2+\lambda)R$. The next argument works for every rational $\lambda$.

Put $N(X)=Q(X)/X$. For $\lambda\ne0$, reduction modulo $tX^2+\lambda$ gives a linear remainder with coefficient of $X$ and constant term
$$
2\big[(hs+t^2)\lambda-hs-3t^2\big],\qquad
h\big[(\lambda-1)^2-s^2\lambda/t\big]+ts(5-3\lambda)-s^3 .
$$
If the linear coefficient is zero, then $\lambda=(hs+3t^2)/(hs+t^2)\in(1,3)$. In this interval $(\lambda-1)^2<4<s^2\lambda/t$ and $5-3\lambda<2<s^2/t$, so the constant is strictly negative. Thus $tX^2+\lambda$ does not divide $N$ or $Q=XN$. For $\lambda=0$, the constant $N(0)=h+s(5t-s^2)$ is positive because $s^2/t=2+\ell/k+k/\ell<9/2$. This excludes divisibility of $Q$ by $tX^2$.

In particular, dividing $Q(X)$ by the quadratic never gives an identically zero remainder. The argument permits a remainder to have an isolated root at an integer $g$; the estimates below include those roots.

## 4. Explicit dependence on the ratio

Use $T=16k$ and let $\|f\|_1$ denote the sum of absolute values of a polynomial's coefficients. Since $\ell<2k$, $m<k^2$, $t<2k^2$, $s<3k$, and $h\le4k^3$, the displayed formulas give
$$
\|D\|_1<T^2,\quad \|A_*\|_1<T^5,\quad \|B_*\|_1<T^4,\quad
\|P\|_1<T^6,\quad \|Q\|_1<T^8 .
$$
The determinant of the Sylvester matrix of $P,Q$ is bounded, by Hadamard's inequality on its five $P$ rows and three $Q$ rows, by $\|P\|_1^5\|Q\|_1^3<T^{54}$. Therefore $w<T^{108}$.

Let $J_0(X)=Q(X)-tX^2(A_*(X)-B_*(X)-m)$. Its quartic coefficient vanishes because the cubic coefficient of $A_*$ is $ht$ and the quadratic coefficient of $B_*$ is $sh$; the quintic terms also cancel. Thus $\deg J_0\le3$ and $\|J_0\|_1<T^9$. Since $R=A-B+S-1$,
$$
mJ=J_0(g)-tg^2mS.
$$
We have $S<6kg$, $R>(\ell g)^3$, and $g\ge1$. It follows that $|\lambda|<T^{10}$ and $|\kappa|<T^{118}$.

Define $V(X)=wQ(X)=\sum_{i=0}^5 v_i X^i$ and $U(X)=a_0X^2+b_0=m(wtX^2+\kappa)$. Then $\|V\|_1<T^{116}$ and $1\le a_0<T^{120}$, $|b_0|<T^{120}$. Multiplying the remainder of $V$ modulo $U$ by $a_0^2$ gives an integer polynomial $E(X)$ of degree at most one. Its coefficients are
$$
a_0^2v_j-a_0 b_0 v_{j+2}+b_0^2v_{j+4},\qquad j=0,1 .
$$
Each has absolute value less than $T^{356}$. The scaled quotient also has integer coefficients. Because $V(g)/U(g)=R$ is an integer, $U(g)\mid E(g)$. Section 3 proves $E$ is nonzero. If $E(g)=0$, the integer root of this nonzero linear polynomial satisfies $g<T^{356}$. Otherwise,
$$
g^2-T^{120}\le |U(g)|\le |E(g)|<T^{356}(g+1),
$$
which gives $g<T^{357}$ because $T\ge32$. This also covers the earlier case $g<8k\ell$. Finally $d+1=kg$ gives $g<16^{357/358}(d+1)^{357/358}<16(d+1)^{357/358}$.

The exponent was chosen for a direct height estimate. A proof excluding all five-prime candidates in this interval still needs an argument covering the unbounded ratios $k$. The spread question and the full primality conjecture remain open in this work.


## A test that also applies outside the ordered interval

Write the five signed coordinates as $u_i=\varepsilon_i p_i$. Their product is $n$, their fourth elementary symmetric sum is 1, and each required shift $|u_i-1|$ divides $n-1$. Choose any two signed coordinates $x,y$ and form
$$
\Delta_{xy}=(x+y)^2-4(xy)^3.
$$
This integer must be a square modulo each required shift belonging to one of the other three coordinates. To see this, call that coordinate $u$ and the two remaining coordinates $v,w$. Modulo $|u-1|$, $u=1$ and $xyvw=1$, so the coordinates are units. The fourth symmetric equation now gives $x^{-1}+y^{-1}+v^{-1}+w^{-1}=0$. Thus $(xy)^2(v+w)=-(x+y)$, which yields
$$
[(xy)^2(v-w)]^2\equiv \Delta_{xy}\pmod{|u-1|}.
$$
For example, take the signed-equation solution with coordinates $(-11,13,71,-10151,51531551)$. For $x=-11,y=13$ the discriminant is $2\pmod5$, whereas $5\mid71-1$. This identifies a failed positive shift using just three of the coordinates. The test gives ten necessary conditions and applies to each sign ordering. A proof that some test must fail for all sufficiently large ratios would still require a global argument.
