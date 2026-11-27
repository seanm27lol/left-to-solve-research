# Three coupled quotients in the almost-perfect equation

Assume $N=2^t$, $P=prs$ for distinct odd primes $p<r<s$, and $\Phi(x)=x^2+x+1$. The equation under study is
$$
(N-1)\Phi(p)\Phi(r)\Phi(s)=NP^2-1 .
$$
For each $x$, let $y,z$ be its complementary pair and put $C_x=Ny^2z^2$, $B_x=(N-1)\Phi(y)\Phi(z)$, $F_x=C_x-B_x$. Reducing the equation modulo $\Phi(x)$ gives $C_x\equiv x$. Hence
$$
D_x=(C_x-x)/\Phi(x),\quad B_x=D_xx^2+x-1,\quad F_x=D_x(x+1)+1,\quad C_x=xF_x+D_x.
$$
Here $x>N$ by the abundancy bound $1+1/x<N/(N-1)$. The equation $F_x x^2=B_x(x+1)+1$ gives $F_x>0$, and $D_x$ is odd, hence positive. If $D_x=1$, then $Ny^2z^2=(x+1)^2$, so $t$ is even. But in this case $3\mid N-1$ while $x^2+x-1$ is never zero modulo three.

## Reproducing the contributed exclusions

The supplied component certificate and spacing certificate both passed on the source bundle. The first certificate is included as `checks/almost_perfect_component_obstructions.py`. Its results concern the three **squared** odd primes at unrestricted sizes. Let $G=\gcd(D_p,D_r,D_s)$. We record the proof that at every $t\ge21$, neither $N-1$ nor $N+1$ divides $G$.

For $q=N-1$, the hypothesis $q\mid G$ forces each $x\equiv1\pmod q$. Oddness then gives successive lower bounds $2q+1,4q+1,6q+1$. The upper geometric sums must satisfy $\prod x/(x-1)\ge N/q$. Indeed $qP-N\prod(x-1)$ is an integer greater than $-\prod(x-1)/P^2>-1$. But the three lower bounds give $\prod x/(x-1)\le(1+1/(2q))(1+1/(4q))(1+1/(6q))<1+1/q$ for $q\ge4$.

For $M=N+1$ we need a local fact. For every prime power $\ell^j$ dividing both $M$ and $G$, all $x+1$ are multiples of $\ell^j$ for $\ell\ne3$, and of $3^{j-2}$ for $\ell=3,j\ge3$. Here is a short verification using the [three residue patterns](almost-perfect-common-quotients.md). For $\ell\ge5$ the polynomial for the all-distinct case evaluates to $-6$ at $N=-1$ and the polynomial for the two-equal case evaluates to $81$. Thus all three bases equal some $a$ modulo $\ell^j$. Then $a^3=-1$ and $\Phi(a)^3=1$. Hence $(a-1)^3=-8$ and $3(a-2)(a+1)=0$. The residue $a=2$ modulo $\ell$ would force $\ell\mid9$. Thus $a-2$ is a unit and $a=-1$ modulo $\ell^j$. Conversely, if $N,x$ are all $-1$ modulo $\ell^j$ the component identities give $\ell^j\mid G$. At three, multiplying the three cube equations $x^3=-P^2$ gives $P^3=-1$ modulo $3^j$. The formula $v_3(P^3+1)=v_3(P+1)+1$ gives $P\equiv-1\pmod{3^{j-1}}$. Apply the same formula to $x^3\equiv-1\pmod{3^{j-1}}$ to get the claimed bound.

Under $M\mid G$, put $L=M/9$ and $x=aL-1,bL-1,cL-1$ for the three bases in order. The coefficients are even positive integers whether or not $L$ is an integer. With $T=a+b+c$ and $K=9(ab+ac+bc)-abc$, the integer geometric envelope becomes
$$
0\le qP-N\prod(x-1)=KL^3-27TL^2+(2T+63)L-6.
$$
Thus $K>0$. Since $q=N-1=9L-2$, the lower abundancy bound $1+(1/a+1/b+1/c)/L<N/q$ gives $qK<2abc$. The coefficients are even and $K$ is a positive multiple of four. Consequently $abc>2q\ge4{,}194{,}302$. Also $10\le a\le26$ and $b<180$ follow from $a>9$ and $1/a+1/b+1/c>1/9$.

If $1/a+1/b>1/9$, the same two-term abundance comparison gives $q[9(a+b)-ab]<2ab$ and hence $ab>q$, impossible. At equality, $(a-9)(b-9)=81$ leaves $(10,90)$ and $(12,36)$. For each of these pairs, the certificate verifies the strict signs $Q(9M)>0>Q(10M)$ at every $L\ge8$ for
$$
Q(D)=D^2-(C_s+F_s)D+F_s(F_s-1).
$$
The component identities give $Q(D_s)=0$. It is the smaller root since $D_s<F_s<C_s$ and $Q(C_s)<0$. Therefore $9M<D_s<10M$, contradicting divisibility. In the remaining case $K>0$ gives $b<c<9ab/[ab-9(a+b)]$. Enumerating even coefficients gives 100 prefixes and 10,074 triples. The maximum $abc=3{,}806{,}960$ occurs at $(10,92,4138)$, contradicting the required lower bound. This computation bounds the coefficients and covers arbitrarily large $N$.

## Extensions and scope

* [Two smallest primes](almost-perfect-smallest-pair.md) shows that $N-1$ cannot divide both of the first two quotients, independently of the third. If the smallest prime equals $2N-1$, the two larger primes differ by at least $\sqrt{8N}$ even at arbitrary exponents.
* [Common shifts](almost-perfect-common-shifts.md) gives a uniform power saving for the part of $G$ shared with either $N-1$ or $N+1$.
* [Even-level splitting](almost-perfect-even-splitting.md) proves that each side $2^{t/2}P\pm1$ receives prime factors from at least two cyclotomic values, with a quantitative lower bound on the smaller portion.
* [Largest-prime gap](almost-perfect-largest-gap.md) bounds the level and the middle prime as functions of $s-r$. It also excludes every gap through 24 at $t\ge21$.
* [Common quotients](almost-perfect-common-quotients.md) gives one polynomial in $N$ divisible by $G$ at full prime-power precision.

These results leave open solutions with dispersed primes and small shared quotient divisors. The proof and the checks above do not rely on reproducing Shnoudi's bounded-component computations. [Shnoudi, Theorems 4.1, 7.8, 9.6](https://doi.org/10.5281/zenodo.23674490).
