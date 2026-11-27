# Consecutive prime gaps in the five-prime Chebyshev case

Suppose $n$ is a five-prime candidate. Its five distinct primes are at least seven, there are three positive and two negative signs, and $\sum_i\varepsilon_i n/p_i=1$. For each prime $p$, the required congruence is $n/p\equiv\varepsilon_p\pmod{p(p-\varepsilon_p)}$ and the forbidden shift $p+\varepsilon_p$ does not divide $n-1$.

**Theorem.** For the largest two prime factors $p<q$, let $h=q-p$. At every spread, $p<4h^6$. If their signs are opposite, $p<6h^4$. Additional bounds for every adjacent gap in the ordered interval appear below.

## Opposite signs

More generally, for any two primes $p<q$ of signs $s,-s$, set $X=n/(pq)$. The signed cofactor equation implies $Y=(hX-s)/(pq)$ is a positive integer. Modulo each of $p-s,q+s$ we have $(h+s)X\equiv s$ from the required cofactor congruences, and $pq\equiv s(h+s)$. Therefore
$$
\operatorname{lcm}(p-s,q+s)\mid (h+s)^2Y+s. \tag{1}
$$
Their gcd divides $h+2s$. For the two largest primes we have $X<p^3$ and $Y<hp$, since $hp^3+1<hp^2(p+h)$. Unless $s=-1,h=2$, the right side of (1) is positive and $h+2s\ne0$. Since $q\ge p+2$, we get
$$
p(p-1)< (p-s)(q+s)\le(h+2)\big((h+1)^2Y+1\big)
 \le(h+2)(h+1)^2hp < 5h^4p .
$$
The middle inequality uses $Y\le hp-1$, and the last uses $h\ge2$. Thus $p<6h^4$.

For $s=-1,h=2$, set $L=(pq-1)/2=(p+1)^2/2-1$. The required congruences at $p,q$ imply $X\equiv L\pmod p$, $X\equiv L\pmod q$ and $X\equiv L\equiv-1\pmod{p+1}$. The moduli are pairwise coprime. As $0<X<p^3$, $0<L<p(p+1)q$, and $p(p+1)q>p^3$, this forces $X=L$. Consequently $pq=2X+1$. In the remaining triple of signed coordinates $u_1,u_2,u_3$ the signed product is $-X$. Its signed reciprocal sum multiplied by $X$ is $\sum_{i=1}^3\varepsilon_i X/|u_i|=1$, by $pq=2X+1$ and the five-term cofactor equation. Hence its second elementary symmetric sum is $-1$, and $\prod_i(u_i+1)=\prod_i(u_i-1)$.

Put $R_i=|u_i-1|/2$, $F_i=|u_i+1|/2$, and $N=(n-1)/2$. We have $R_i\mid N$, $F_i\nmid N$, $\gcd(F_i,R_i)=1$ and $\prod F_i=\prod R_i$. For each $i$ select a prime $t_i$ with $v_{t_i}(F_i)>v_{t_i}(N)$. It must divide both other $R_j$, as a single $R_j$ cannot supply the needed valuation. Thus the three witnesses are distinct; at least one is an odd prime $t$. Two signed coordinates in the triple are $1\pmod t$, and the second symmetric sum $-1$ forces the third to be $-1\pmod t$. Its signed product then implies $X\equiv1\pmod t$. This gives $n-1=X(2X+1)-1\equiv2\pmod t$, contradicting $t\mid N$. This is the earlier exceptional-residual argument applied to the two largest primes.

## Both signs positive

They cannot both be negative: in that case the three positive reciprocal terms each exceed $1/p$ and the two negative reciprocals sum to at least $-2/p$, contradicting the signed reciprocal identity. Suppose both signs are positive. If $h>p$ we already have the claimed bound. Otherwise let $T=h^2(h^2-1)^2$ and let $L(Z)$ interpolate at $0,1,-h,1-h$ with respective values $1/h,1/(h+1),-1/h,1/(1-h)$. Then
$$
\begin{aligned}
 TL(Z)={}&-2(3h^2-1)Z^3-(h-1)(9h^2-h-4)Z^2\\
 &+(-h^4+10h^3-3h^2-4h+2)Z +h(h^2-1)^2 .
\end{aligned}
$$
For $Z\ge h\ge2$, we have $-2Z^3<L(Z)<0$. To check both signs, substitute $h=2+x$, $Z=2+x+y$ into $-TL(Z)$ and $2TZ^3+TL(Z)$. Both have positive constant and nonnegative polynomial coefficients, as checked exactly by the symbolic verifier.

Put $Q(Z)=Z(Z-1)(Z+h)(Z+h-1)$. If $r_i$ is one of the four interpolation nodes with value $s_i$, Lagrange interpolation yields
$$
\frac{X-L(p)}{Q(p)}
=\sum_i\frac{X-s_i}{(p-r_i)Q'(r_i)} .
$$
Writing $s_i=a_i/b_i$ in signed unreduced form as displayed, the required cofactor congruences give $(p-r_i)\mid b_iX-a_i$. At each node $b_iQ'(r_i)$ divides $T$. Therefore $T(X-L(p))/Q(p)$ is a positive integer. Since $X<p^3$ and $0<-L(p)<2p^3$, $p^3(p-1)<Q(p)<3Tp^3$. Thus $p<4h^6$. The opposite-sign result also implies $p<4h^6$ for $h\ge2$.

## Absolute gap between the two largest prime factors

The two largest prime factors differ by at least 26 for every five-prime candidate. To bound the enumeration for positive signs, the same coefficient substitution as above also gives $18h^2Z^3+TL(Z)>0$. Thus for $p\ge h$ the positive integer $T(X-L(p))/Q(p)$ gives
$$
p^3(p-1)< Q(p) < (T+18h^2)p^3.
$$
It follows that $p<1+T+18h^2$. This bound is automatic when $p<h$. For opposite signs use $p<6h^4$ and the negative-first twin exclusion above.

For each even $h$ from 2 through 24 these estimates give a finite range of $p$. Within that range take each pair of primes $p,q=p+h$. Set $X=n/(pq)$ and write $s,t$ for their signs. The two required congruences impose
$$
qX\equiv s\pmod{p(p-s)},\qquad pX\equiv t\pmod{q(q-t)}.
$$
If a coefficient is noninvertible, its corresponding right side is a unit, so no solution exists. Otherwise the generalized Chinese remainder theorem returns all possible $X$ modulo the least common multiple of the possibly overlapping moduli. Enumerate every representative with $0<X<p^3$. Test whether it is the product of three distinct primes in $[7,p)$ by deterministic trial division.

| Gap $h$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 | 24 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Cofactors counted with pair and signs | 1 | 3 | 4 | 4 | 5 | 11 | 4 | 7 | 5 | 6 | 2 | 7 |
| Products of three eligible primes | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

The sieve uses exact integers with checked congruences. In this range $p,q<192{,}000{,}000$, $p(p-s),q(q-t)<4\cdot10^{16}$ and their product is less than $1.6\cdot10^{33}$, within signed 128-bit arithmetic. Compile and run the certificate as follows.

```sh
g++ -std=c++17 -O2 checks/chebyshev_small_top_gaps.cpp -o /tmp/chebyshev-top-gaps
/tmp/chebyshev-top-gaps
```

## All four gaps in the ordered interval

Assume $7\le d<e<a<b<c<2d$ are primes, with negative signs at $d,e$ and positive signs at $a,b,c$. Put $A=abc$, $n=deA$. The signed reciprocal equation and the required shifts give $eA\equiv-1\pmod{d(d+1)}$ and $dA\equiv-1\pmod{e(e+1)}$. The argument uses the signed equation and required shifts only.

### The two negative primes

Set $t=e-d$, an even integer with $2\le t<d$. In the four moduli $d,d+1,d+t,d+t+1$, the divisibilities above give
$$
d\mid tA+1,\quad d+1\mid(t-1)A+1,\quad d+t\mid tA-1,\quad d+t+1\mid(t+1)A-1.
$$
Let $L_t(X)$ be the cubic with values $-1/t,-1/(t-1),1/t,1/(t+1)$ at the distinct points $r_i=0,-1,-t,-t-1$. Set $D=t^2(t-1)^2(t+1)^2$ and $U(X)=X(X+1)(X+t)(X+t+1)$. Then
$$
\frac{D(A-L_t(d))}{U(d)}\in\mathbb Z.
$$
Indeed, divide the Lagrange formula for $A-L_t(d)$ by $U(d)$. The term at $i$ is $(A-L_t(r_i))/[(d-r_i)U'(r_i)]$. The four divisibilities make this integral after multiplication by the denominator of $L_t(r_i)$ times $|U'(r_i)|$. Those multipliers are $t^2(t+1)$, $t(t-1)^2$, $t^2(t-1)$, $t(t+1)^2$, respectively, all divisors of $D$. This proves divisibility by the full product even when two of its factors share a divisor.

Writing $P=DL_t$, its coefficients in descending degree are
$$
6t^2-2,\quad 9t^3+10t^2-3t-4,\quad t^4+10t^3+3t^2-4t-2,\quad -t(t^2-1)^2 .
$$
All three nonconstant coefficients are positive for $t\ge2$, so $L_t(d)>-1/t$. Also $D(X+t)^3-P(X)$ has positive coefficients in $X$ for every $t\ge2$, as seen by writing its coefficients as polynomials in $t-2$ (verified by the accompanying exact symbolic check). Thus $L_t(d)<e^3<A$.

For the upper bound on $A$, let $z_p=2d/p-1>0$ for $p=a,b,c$. Then $8d^3/A=\prod(1+z_p)>1+\sum z_p=2d/e+2d/n$, hence $A<4d^2e$. Integrality of $A$ yields $A-L_t(d)<4d^2 e$. The positive integer above is at least one, so $d(d+1)e(e+1)<4D d^2e$ and hence
$$
\boxed{e+1<4t^2(t^2-1)^2<4t^6.}
$$
This excludes every bounded negative gap at all sufficiently large prime sizes. The reciprocal equation also gives $3de<c(d+e)$: one has $3/c\le 1/d+1/e+1/n$ and the integer $3de-c(d+e)$ is odd and $<1$. Consequently $2c-3d>3d(e-d)/(d+e)>e-d$. This transfers the gap to the real endpoint $3d/2$.

### The middle mixed pair

Put $v=a-e$, $j=2d-b$, $k=2d-c$ and $Q=dbc$. The signed equation gives
$$
\frac{j}{2db}+\frac{k}{2dc}=\frac{v}{ea}+\frac1n.
$$
The left side exceeds $(j+k)/(4d^2)$. The right side is below $v/d^2$, because $v(ea-d^2)bc>d$ and $n=deabc$. Thus $j+k<4v$.

Suppose $v=2$. The different positive odd integers $j>k$ have $j+k<8$, leaving $(3,1)$ and $(5,1)$. In the latter case one of $2d-5,2d-1$ is a multiple of 3, since $d\ne3$. In the former case the signed identity yields
$$
(4d-3)e(e+2)=2d(2d-3)(2d-1)+1 .
$$
Modulo $4d-3$ the right side multiplied by 8 equals $-1$: indeed $16d(2d-3)(2d-1)=(4d)(4d-6)(4d-2)$ equals $3(-3)(1)=-9$ modulo $4d-3$. This excludes $v=2$, so $v\ge4$.

Reducing the local congruences at $e,a$ gives $ea\mid vQ+1$. Hence $m=(vQ+1)/(ea)$ is a positive integer. Since $Q<4e^3$ and $a>e$, one has $m<4ve$. Set $L=\operatorname{lcm}(e+1,a-1)$. Each of the two shifts divides $(v-1)Q+1$: this follows from $L\mid n-1$, since $ea\equiv-(v-1)$ modulo each shift. Reducing $v((v-1)Q+1)=(v-1)mea+1$ modulo $L$ gives $L\mid1-m(v-1)^2$. This last integer is negative. As $\gcd(e+1,a-1)\mid v-2$,
$$
\frac{e^2}{v-2}< L\le m(v-1)^2-1 <4ve(v-1)^2.
$$
In particular
$$
\boxed{e<4v(v-1)^2(v-2)<4v^4.}
$$
The quartic argument extends the mixed-sign gap calculation for the two largest primes to the two middle primes in this interval, with a separate exclusion for the coincident shifts at $a=e+2$. These inequalities leave unbounded interior configurations with both gaps proportional to $d$.

### Pairs of positive primes

Let $x<y=x+h$ be any two positive-sign primes among $a,b,c$, and $C=n/(xy)$ the product of the remaining three. Then $x>h$ since $x>d$ and $y<2d$. Reflecting the four interpolation nodes for the negative pair gives $L_h^+(x)=L_h(-x-h)$. At $x=0,1,-h,1-h$ its values are respectively $1/h,1/(h+1),-1/h,-1/(h-1)$, exactly the residue targets from $x(x-1)\mid Cy-1$ and $y(y-1)\mid Cx-1$. Therefore
$$
\frac{h^2(h^2-1)^2(C-L_h^+(x))}{x(x-1)y(y-1)}\in\mathbb Z .
$$
Both $-L_h^+(x)$ and $(x+h)^3+L_h^+(x)$ are positive: multiply by $h^2(h^2-1)^2$ and substitute $x=h+u$, $h=2+v$. All coefficients of the resulting integer polynomials are positive where nonzero, including their constants. Thus $0<C-L_h^+(x)<16d^3$. Since $x(x-1)y(y-1)>d^4$, we obtain
$$
d<16h^2(h^2-1)^2<16h^6 .
$$
Hence all four consecutive prime gaps in the dyadic order diverge when the smallest prime grows: the middle transition has the fourth-root bound and each same-sign gap has a sixth-root bound.

Run `python checks/chebyshev_prime_gaps.py` with SymPy 1.14 to check the interpolation identities and the polynomial signs.

## An explicit endpoint gap from the signed reciprocal equation

Let five distinct odd integers, each at least seven, satisfy $d<e<a<b<c<2d$ and $1/a+1/b+1/c-1/d-1/e=1/n$, where $n=abcde$. Put $\Delta=2c-3d$, $\beta=e-d$, $\alpha_r=2r-3d$ for $r=a,b,c$, and $F=9\beta-2\sum_r\alpha_r=9(d+e)-4(a+b+c)$. Then
$$
d<6\Delta^3.
$$
If $F\ne0$, then $d<14\Delta^2$. In particular the square-root bound holds whenever $e-d\equiv0\pmod4$.

The identity
$$
\sum_{r=a,b,c}(1/r-1/c)+(1/d-1/e)=\Delta/(cd)+1/n
$$
has nonnegative left side. It implies $\Delta\ge1$, since $cd<n$ and $\Delta$ is odd. Bounding each term separately gives $c-r\le2\Delta$, because $c-r\le(r/d)\Delta+rc/n<2\Delta+1$. Similarly $\beta\le\Delta$. In particular $-3\Delta\le\alpha_r\le\Delta$, and $\Delta\ge3$ since $\beta\ge2$.

One exact division of each reciprocal gives
$$
\frac{d^2}{n}=\frac{F}{9}+\sum_r\frac{2\alpha_r^2}{9(3d+\alpha_r)}-\frac{\beta^2}{d+\beta}.
$$
The two nonnegative correction terms (the sum and the final fraction) have respective upper bounds $3\Delta^2/d$ and $\Delta^2/d$, because $3d+\alpha_r=2r>2d$. Thus their difference has absolute value at most $3\Delta^2/d$. Using $n>d^5$ and $d\ge7$ gives $|F|<28\Delta^2/d$. If $F\ne0$, its evenness implies $|F|\ge2$, proving $d<14\Delta^2$. This also gives $d<6\Delta^3$ since $\Delta\ge3$. As each $\alpha_r$ is odd, $\beta\equiv0\pmod4$ forces $F\equiv2\pmod4$.

It remains to consider $F=0$. Here $\sum\alpha_r=9\beta/2>0$, so each $\alpha_r>-2\Delta$ and $\beta\le2\Delta/3$. Also $\beta\equiv2\pmod4$. Set $B=2\sum_r\alpha_r^2-27\beta^2$. Each odd square is $1$ modulo eight, so $B\equiv10\pmod{16}$ and $|B|\ge6$. A second exact division gives
$$
\frac{d^3}{n}=\frac B{27}-\sum_r\frac{2\alpha_r^3}{27(3d+\alpha_r)}+\frac{\beta^3}{d+\beta}.
$$
Consequently
$$
|B|<\frac{27}{d^2}+\frac{24\Delta^3}{d}+\frac{8\Delta^3}{d}<\frac{36\Delta^3}{d}.
$$
The last inequality uses $d\ge7$, $\Delta\ge1$. Since $|B|\ge6$, this gives $d<6\Delta^3$ in the remaining case. All bounds hold at finite size and require only oddness, ordering and the signed reciprocal identity.

## Excluding a middle gap of at most 100

Suppose $7\le d<e<a<b<c<2d$ are odd integers and $n=deabc$. Assume
$$
\frac1a+\frac1b+\frac1c-\frac1d-\frac1e=\frac1n,
\qquad d+1\mid n-1 .
$$
Then $a-e\ge102$. This computer-assisted conclusion holds at every size and requires only the displayed hypotheses, so it applies to five-prime Chebyshev candidates in this ordering.

### The finite reduction

Put $v=a-e$, $j=2d-b$, $k=2d-c$. Then $v$ is positive and even, and $j>k$ are positive and odd. The reciprocal equation is
$$
\frac{j}{2db}+\frac{k}{2dc}=\frac{v}{ea}+\frac1n.
$$
The left side exceeds $(j+k)/(4d^2)$. The right side is less than $v/d^2$ since $v(ea-d^2)bc>d$. Consequently $j+k<4v$. Also $d>j+v$ follows from $d+v<e+v=a<b=2d-j$.

Set $m=j+k$, $u=jk$, $N=md-u$ and $C=(j+2)(k+2)$. Multiplying the reciprocal equation through by $n$ yields
$$
N\,e(e+v)=vdbc+1.\tag{1}
$$
Here $N=d(b+c)-bc>0$.

**The divisor for $d+1$.** Modulo $d+1$, one has $bc\equiv C$ and $eaC\equiv-1$ because $n\equiv1$. Multiply (1) by $C$ and reduce modulo $d+1$. The left side gives $m+u$ and the right side gives $C-vC^2$. As $C=u+2m+4$, this proves
$$
d+1\mid W,\qquad W=vC^2-m-4.
$$
Here $W>0$ since $C>m+4$. For fixed $v,j,k$, this bounds every possible $d$.

**The divisor for $N$.** Reducing modulo $N$ gives $md\equiv u$, $mb\equiv-j(j-k)$, and $mc\equiv k(j-k)$. Multiply the right side of (1) by $m^3$ and substitute these residues. This yields
$$
N\mid X,\qquad X=v\,[jk(j-k)]^2-m^3 .
$$
Both divisor tests use multiplication and reduction without cancelling nonunits.

### Exact verification

Run `python3 checks/chebyshev_middle_gap.py` with Python 3.8 or later. The script uses standard-library integer arithmetic throughout. It enumerates the even values $2\le v\le100$, then all odd $j>k>0$ with $j+k<4v$. For each triple, $W$ is even. All even divisors $d+1$ of $W$ occur exactly once as twice a divisor of $W/2$. The script factors $W/2$ by trial division. Its prime table is sufficient because the arithmetic mean bound gives $C<(2v+2)^2$, hence $W<100\cdot202^4$.

| Stage | Count |
| --- | ---: |
| Gap triples $(v,j,k)$ | 169,150 |
| Divisor choices with $d\ge7$, $d>j+v$, and $N\mid X$ | 73 |
| Choices giving an integer $Y=(vdbc+1)/N$ | 14 |
| Choices with $v^2+4Y$ a perfect square | 0 |

An integer solution would give $Y=e(e+v)$ and $v^2+4Y=(2e+v)^2$. Zero square discriminants exclude every tested width for all $d$. The computation leaves widths $v\ge102$ open.
