# Quantitative splitting at every even level

Let $N=2^t=U^2$, with even $t\ge2$, and suppose $2^{t-1}(prs)^2$ is almost perfect at distinct odd primes $p<r<s$. Write $P=prs$, $q=N-1$, $\Phi(x)=x^2+x+1$, and $R_\pm=UP\pm1$. The two sides $R_-,R_+$ are positive odd and coprime. For each $x=p,r,s$, put $A_x=\gcd(\Phi(x),R_+)$, $B_x=\Phi(x)/A_x$, and $m_x=\min(A_x,B_x)$. Then $A_x\mid R_+$ and $B_x\mid R_-$ by
$$R_+R_-=q\prod_x\Phi(x).$$
All factors are counted with multiplicity even if two cyclotomic values have a common prime. Thus there are $q_+q_-=q$ with $R_+=q_+\prod A_x$, $R_-=q_-\prod B_x$. An unsplit component has $m_x=1$.

**Theorem.** Each side receives a prime divisor from at least two components. In particular, any two unsplit components must occupy opposite sides. At every even level,
$$
\max_x m_x>\sqrt{2}\,(1-1/N)^{1/4}N^{1/8}.
$$
If exactly one component splits, its smaller side factor satisfies the stronger lower bound $2(1-1/N)^{1/2}N^{1/4}$ strictly.

For every pair of bases $y,z$, the divisor sum equation gives
$$
1+1/y+1/z<\prod_x(1+1/x+1/x^2)<1+1/q.
$$
Thus each base exceeds $N$ by parity and $\sqrt{yz}>2q$. Also $Uyz>x+1$ for each complementary triple $x,y,z$. Indeed reducing the divisor equation modulo $\Phi(x)$ gives $D_x=(Ny^2z^2-x)/\Phi(x)$ integral. It is positive because $F_x=Ny^2z^2-q\Phi(y)\Phi(z)=D_x(x+1)+1>0$, where $x^2F_x=q\Phi(y)\Phi(z)(x+1)+1$, and parity excludes zero. If $D_x=1$, then $q\Phi(y)\Phi(z)=x^2+x-1$, impossible modulo 3 since $3\mid q$. Hence $Ny^2z^2>(x+1)^2$.

If a side $R_\varepsilon$ receives no component then $R_\varepsilon\le q$, impossible. If it receives prime factors from just one component $x$, write $R_\varepsilon b=q_\varepsilon\Phi(x)$, where $b\mid\Phi(x)$ is the portion on the other side. As $R_\varepsilon\ge UP-1>q(x+1)$, we have $b<\Phi(x)/(x+1)=x+1/(x+1)$ and hence $b\le x$. Since $x\nmid\Phi(x)$, this gives $b<x$. Modulo $x$, the relation gives $x\mid q_\varepsilon-\varepsilon b$. The difference is even since both factors are odd. Its absolute value is less than $2x$, so it vanishes. This forces $\varepsilon=+1$ and $R_+=\Phi(x)$, contrary to $Uyz>x+1$. This proves the first assertion. In particular, two unsplit cyclotomic values are coprime. At most one base congruent to $1$ modulo $3$ has an unsplit component, since $3$ divides every such component.

Assign each component to the side containing its larger factor. The factors cannot tie since they are coprime and their product is greater than one. If all three are assigned to one side, the other satisfies $q\prod m_x\ge UP-1>qN^{5/2}$, as $P>N^3$. Hence some $m_x>N^{5/6}$, which implies the universal estimate. If exactly one component $x$ splits, this case is already impossible by the first assertion.

Otherwise exactly one component $x$ is assigned to some side $\varepsilon$. Let $y,z$ denote the other two bases and put $a=m_y m_z$, $b=m_x$. Then
$$
R_\varepsilon b=q_\varepsilon a\Phi(x),\qquad R_{-\varepsilon}a=q_{-\varepsilon}b\Phi(y)\Phi(z).
$$
From the first relation $K=(q_\varepsilon a-\varepsilon b)/x$ is an even integer. Rearranging gives
$$
K\Phi(x)=b\,[Uyz-\varepsilon(x+1)]>0.
$$
Thus $K\ge2$ and $q_\varepsilon a\ge2x-b>x$, since $b\le\sqrt{\Phi(x)}<x+1$ and $x\nmid b$. The second relation gives
$$
\frac ab\ge\frac{\Phi(y)\Phi(z)}{UP+1}>\frac{yz}{Ux},
$$
where $Ux[\Phi(y)\Phi(z)-y^2z^2]>yz$. Multiplication yields
$$
a^2>\frac{b yz}{qU}>4b\,\frac qU.
$$
Since $b\ge1$, at least one of $m_y,m_z$ exceeds $(4q/U)^{1/4}$ as claimed. If exactly one component splits, the inequality forces it to be $y$ or $z$. Its smaller side factor is then $a>2\sqrt{q/U}$. Both results allow the prime sizes and their ratios to grow.

## Distance of an unsplit largest prime from multiples of the level minus one

Let $N=2^t=U^2$ with even $t\ge22$, let $q=N-1$, and let $p<r<s$ be three odd primes such that $2^{t-1}(prs)^2$ is almost perfect. Call $\Phi(s)=s^2+s+1$ unsplit if it divides one of $Uprs+1,Uprs-1$. Let $a$ be the least absolute residue of $s$ modulo $q$. If $\Phi(s)$ is unsplit, then
$$
a\notin\{-1,0,1\},\qquad U<6000(1+|a|)^{16}.
$$
In particular the distance from $s$ to $q\mathbb Z$ grows at least on the scale of $N^{1/32}$ along any unbounded sequence of such levels.

**The coefficient of the unsplit factor.** Write $Uprs+\epsilon=b\Phi(s)$, $\epsilon=\pm1$. Since $b$ is odd and $b\equiv\epsilon\pmod s$, write $b=ms+\epsilon$ with even $m$. Then
$$
Upr=m\Phi(s)+\epsilon(s+1).
$$
If $m=0$, positivity would force $Upr=s+1$ and hence $D_s=1$, excluded by the component identity modulo three. More explicitly, $(N-1)\Phi(p)\Phi(r)=s^2+s-1$ in this case and no residue modulo three solves that quadratic. Negative $m$ is impossible. Since $pr<s^2$, we have $2\le m<U$, and since $m\ge2$, we also have $s<Up/m$. We use $p<3N$, which follows from $\prod_x x/(x-1)\ge N/(N-1)$ and $(3N/(3N-1))^3<N/(N-1)$.

**The bounded integer divisible by $U$.** The original divisor-sum equation gives $P^2\equiv1\pmod q$ for $P=prs$, and $U^2\equiv1\pmod q$. The even integer
$$
z=a[m\Phi(a)+\epsilon(a+1)]
$$
therefore has $z^2\equiv1\pmod q$, by comparison with $UP$ modulo $q$. In particular $a\ne0$, $|z|\ge U$, and $z^2=1+jq$ with $j\ge1$. Write $s=a+Lq$, where $L\ge1$, and set $v=a-L$. Then $s\equiv v\pmod U$, so $m\Phi(v)\equiv-\epsilon(v+1)\pmod U$. Eliminating $m$ gives
$$
z\Phi(v)\equiv \epsilon a(v-a)[(a+1)v+a]\pmod U.
$$
As $z^2\equiv1-j\pmod U$, it follows that $U$ divides
$$
K=a^2L^2[(a+1)v+a]^2+(j-1)\Phi(v)^2.
$$
If $j>1$ then $K>0$. If $j=1$ and $K=0$, the nonzero factors $a,L$ force $(a+1)(a-L)+a=0$. At $a=-1$ this is impossible. Otherwise $L=a+1-1/(a+1)$, which is integral only at $a=0,-2$ and then equals zero. Hence $K>0$ throughout.

Put $A=1+|a|\ge2$. We may assume $U\ge2A^2$ since smaller $U$ already satisfy the theorem. The inequalities $|z|\le mA^3+A^2$ and $|z|\ge U$ yield $m\ge U/(2A^3)$. Since $s<3NU/m$, $|a|\le q/2$, and $U/m>1$, we have $L\le4U/m\le8A^3$. Also $\sqrt j<2mA^3/U$, from $|z|\le (5/4)mA^3$ and $U\ge2048$, whence $\sqrt j\,L\le8A^3$. Now
$$
 |aL[(a+1)v+a]|\le A L\cdot A(A+L)\le72A^8,
$$
and
$$
 \sqrt j\,\Phi(v)\le (\sqrt j\,A+\sqrt j\,L)(A+L)
 \le(2A^4+8A^3)9A^3\le54A^7.
$$
Consequently $U\le K\le72^2 A^{16}+54^2 A^{14}<6000A^{16}$.

**The two residues nearest zero.** At $a=-1$ one gets $z=-m$, contradicting $|z|\ge U$. At $a=1$ one has $z=3m+2\epsilon$, positive and less than $3U$, with $1\le j\le8$. Reducing $z^2=1+jq$ modulo 16 gives $j\equiv1,13\pmod{16}$, hence $j=1$ and $3m+2\epsilon=U$. The eliminated congruence for $z\Phi(v)$ above equivalently gives $U\mid(s-1)(2s+1)$, hence $s\equiv1\pmod U$. So $s\ge1+Uq$, yet $s<3NU/m\le9NU/(U-2)<10N$. This contradiction also proves $q\nmid D_s$ whenever the largest component is unsplit, since $q\Phi(p)\Phi(r)=D_s s^2+s-1$ and $\gcd(s,q)=1$.

The argument uses only elementary divisibility and real inequalities. It allows a largest unsplit component at large distance from $q\mathbb Z$ and places no restriction on the residue in the split-largest branch.

## A quantitative result allowing both sides to receive factors

The two integers $UP-1,UP+1$ are coprime. Define
$$
B=\min\{\gcd(\Phi(s),UP-1),\gcd(\Phi(s),UP+1)\},\quad
A=1+|a|,\quad H=AB.
$$
For every candidate at even $t\ge22$, including those where all three cyclotomic factors split, one has
$$
U<600000\,B^6 A^{18}.
$$
In particular, bounded distance of $s$ from $q\mathbb Z$ would require divisors of $\Phi(s)$ growing on both sides of the factorization. For fixed $|a|$ the lower bound on the smaller divisor is of order $N^{1/12}$.

The two gcds multiply to $\Phi(s)$, since $\Phi(s)\mid(UP-1)(UP+1)$ and these two factors are coprime. Thus $B$ is odd and $B\le\sqrt{\Phi(s)}<s+1$. For an appropriate sign $\epsilon$, write $B(UP+\epsilon)=b\Phi(s)$, obtaining $b=ms+\epsilon B$ with even $m$. A negative $m$ would make $b$ negative, and $m=0$ would again imply $Upr=s+1$. Hence
$$
BUpr=m\Phi(s)+\epsilon B(s+1),\qquad 2\le m<BU,\qquad s<2BU p/m.
$$
The upper bound on $m$ follows from $pr<s^2$. For the final bound use $B(s+1)\le s^2+s<\Phi(s)$ and $m-1\ge m/2$.

The case $U<2BA^2$ already satisfies the claimed inequality, so assume $U\ge2BA^2$. We have $a\ne0$ because $\gcd(s,q)=1$. Put
$$
z=a[m\Phi(a)+\epsilon B(a+1)].
$$
Then $z$ is even, $z\equiv BUP\pmod q$, and $z^2=B^2+jq$ for an integer $j$. Because $B$ is odd, $j\ne0$. Since $B^2<q$, it follows that $j\ge1$ and $|z|\ge U$. Using $|z|\le mA^3+BA^2$ gives $m\ge U/(2A^3)$. Set $L=(s-a)/q\ge1$ and $v=a-L$. From $p<3N$, $N/q<1.01$, $|a|/q\le1/2$ and $BU/m>1$, we obtain $L<7BU/m\le14BA^3$. Also
$$
\sqrt j\le |z|/\sqrt q < 3mA^3/U < 3BA^3,
$$
since $BA^2\le U/2\le mA^3$. Reducing the equation for $BUpr$ modulo $U$ gives $m\Phi(v)\equiv-\epsilon B(v+1)$. Elimination now gives
$$
z\Phi(v)\equiv-\epsilon Bc\pmod U,\qquad
c=aL[(a+1)v+a].
$$
Consequently $U\mid K=B^2c^2+(j-B^2)\Phi(v)^2$. As in the unsplit calculation, $c\ne0$ for every nonzero integer $a$ and positive $L$.

The bounds above imply $|v|+1\le A+L\le15BA^3$, $|Bc|\le210 B^3 A^8$, and $\Phi(v)\le225B^2A^6$. Therefore $|K|\le44100B^6 A^{16}+506250B^6 A^{18}<600000B^6 A^{18}$. This proves the claim unless $K=0$.

If $K=0$, the integer $B^2-j$ is the square of the rational number $Bc/\Phi(v)\ne0$, hence equals $k^2$ for an integer $1\le k<B$. Since $\Phi(v)$ is odd and $z\Phi(v)\equiv-\epsilon Bc\pmod U$, one has $z=\lambda U\pm k$ for some integer $\lambda$. Then $z^2=jU^2+k^2$ gives $U\mid2\lambda k$. Here $\lambda\ne0$, as $j\ge1$, and $|z|/U=\sqrt{j+k^2/U^2}<B+1$ gives $|\lambda|<B+2$. Therefore $U\le2|\lambda|k<2B(B+2)<600000B^6 A^{18}$ in this case as well.

## Excluding residues of absolute value at most twelve

For $2\le |a|\le12$ we have $U\ge2048>2A^2$. Thus the estimates for an unsplit largest component give $U<6000A^{16}$ and $1\le L\le\min(8A^3,2U)$, also $L\not\equiv a\pmod2$. The pair of signs need not be searched. Indeed $s\equiv v=a-L\pmod {2U}$, and $Upr\equiv U\pmod{2U}$ because $p,r$ are odd. Define $w$ to be the least residue of $(v+1)/\Phi(v)$ modulo $2U$. Then $m\equiv U-\epsilon w\pmod{2U}$, and $0<m<U$ uniquely forces $m=|U-w|$ and $\epsilon=\operatorname{sgn}(U-w)$, excluding $w=0,U$. The estimate $Lm\le4U$ and the necessary congruence $a^2[m\Phi(a)+\epsilon(a+1)]^2\equiv1\pmod q$ finish the check. Across 3,660,032 initial $(a,U,L)$, the bounds on $m,L$ and orientation left 16,946 possibilities, and zero passed the last congruence. Hence $|a|\ge13$ for any even-level candidate with largest component unsplit. The exact check is implemented in checks/almost_perfect_small_unsplit_residues.py.
