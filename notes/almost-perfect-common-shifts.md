# A power-saving bound for common divisors at the two neighboring integers

Let $N=2^t$, $P=prs$, and $\Phi(x)=x^2+x+1$. Suppose $N<p<r<s$ are distinct odd primes and
$$
(N-1)\Phi(p)\Phi(r)\Phi(s)=NP^2-1.
$$
Put $M=N+1$, $L=\gcd(M,p+1,r+1,s+1)$ and $k=M/L$. Then
$$
M\le608k^7,\qquad L\le608^{1/7}M^{6/7}.
$$
The proof also applies to distinct odd integer bases larger than $N$ satisfying the displayed polynomial equation.

For the component quotients $D_x=(N(P/x)^2-x)/\Phi(x)$, the local lemma in the [component audit](almost-perfect-component-audit.md) yields
$$
G=\gcd(M,D_p,D_r,D_s)\le9L\le9\cdot608^{1/7}M^{6/7}.
$$
Indeed each prime power dividing $G$ divides all three shifted bases, except possibly two powers of 3. In particular, along a sequence of candidates with $t$ unbounded, neither $L$ nor $G$ can remain a positive fixed fraction of $N+1$.

## Bounding the coefficients

Write $p=aL-1$, $r=bL-1$, $s=cL-1$ and $q=N-1=kL-2$. Then $k<a<b<c$. We can assume $L>608k^6$. Let $A=a+b+c$ and $K=k(ab+ac+bc)-abc$. The finite geometric factors at $p,r,s$ imply
$$
H=\prod_x(1+1/x+1/x^2)=N/q-1/(qP^2)<1+1/q.
$$
Since $H<P/V$ with $V=(p-1)(r-1)(s-1)$, the integer $E=qP-NV$ is greater than $-V/P^2>-1$, hence nonnegative. Expansion gives
$$
E=KL^3-3kAL^2+(2A+7k)L-6 .
$$
The last three terms have negative sum since $A>3k$ and $L>608$. Thus $K>0$. Because $p<aL$, and similarly for $r,s$, the strict bound $H>1+(1/a+1/b+1/c)/L$ gives
$$
qK<2abc.
$$
From $1/a+1/b+1/c>1/k$, we have $a<3k$ and $b<2ka/(a-k)\le2k(k+1)\le4k^2$.

If $1/a+1/b>1/k$, the same abundancy comparison with two terms gives $q[k(a+b)-ab]<2ab<24k^3$, precluding $L>608k^6$. If $1/a+1/b<1/k$, then $K>0$ gives $c<kab/[ab-k(a+b)]\le kab<12k^4$, and $q<2abc<288k^7$, again impossible.

## The exact harmonic boundary

If $1/a+1/b=1/k$, put $u=a+b$. Then $ab=ku$ and $4k\le u\le4k^2$. For the lower bound use $ab\le u^2/4$. For the upper bound the positive integer divisors $a-k,b-k$ have product $k^2$, hence sum at most $k^2+1$, giving $u\le(k+1)^2$.

Put $C=Np^2r^2$, $F=C-q\Phi(p)\Phi(r)$. The component equation gives $C=sF+D_s$ and $F=D_s(s+1)+1$ with $D_s>0$. In particular $0<C/F-s<1/(s+1)$. Direct expansion gives
$$
C=(kL-1)(kuL^2-uL+1)^2,\qquad F=3k^2uL^3+(u^2-5ku)L^2+1\ge2k^2uL^3.
$$
Define $B(L)=9k^4uL^2-3k^2u(4k+u)L+18k^3+7k^2u-ku^2+u^3$. There is an integer division identity
$$
27k^3 C=B(L)F+r_0+r_1L+r_2L^2,
$$
where
$$
\begin{aligned}
r_0&=-(45k^3+7k^2u-ku^2+u^3),\\
r_1&=3k^2(9k^2+22ku+u^2),\\
r_2&=-u(27k^4+10k^3u+12k^2u^2-6ku^3+u^4).
\end{aligned}
$$
Since $k\le u/4$, the respective absolute values are at most $3u^3$, $22k^2u^2$, $4u^5$. Using the lower bound for $F$, $u\le4k^2$, and $s+1>L$, we find
$$
|27k^3s-B(L)|<
\frac{24k^2}{L^3}+\frac{44k^2}{L^2}+\frac{512k^6+27k^3}{L}
\le\frac{607k^6}{L}<1.
$$
Thus the integer $27k^3s-B(L)$ vanishes. Since $s\equiv-1\pmod L$, this forces $L\mid B(0)+27k^3=-r_0$. But $0<-r_0\le3u^3\le192k^6<L$. This contradiction proves the bound.

## The common divisor at the level minus one

Let $N=2^t$ and allow the odd part $M_0=p^{2i}r^{2j}s^{2h}$ to have arbitrary $i,j,h\ge1$. Suppose $(N-1)\sigma(M_0)=NM_0-1$. For $L=\gcd(N-1,p-1,r-1,s-1)$ and $k=(N-1)/L$ we again have
$$
N-1\le608k^7 .
$$
In the squarefree-root case this yields the same bound with $L=\gcd(N-1,D_p,D_r,D_s)$ because $x^2D_x\equiv1-x\pmod{N-1}$ and every base $x$ is coprime to $N-1$.

Write $N=kL+1$ and $p=aL+1$, $r=bL+1$, $s=cL+1$. Here $k<a<b<c$ by the single-prime lower abundancy bound and oddness of the bases. Again assume $L>608k^6$. As before, with $P=prs$, $V=(p-1)(r-1)(s-1)$, and $H=\sigma(M_0)/M_0$, the upper and lower envelopes are
$$
\prod_x (1+1/x+1/x^2)\le H<1+1/(kL)\le P/V.
$$
The last inequality follows because the integer $(N-1)P-NV$ exceeds $-V/M_0>-1$. If $a\ge4k$, then $P/V\le(1+1/(4kL))^3<1+1/(kL)$ for $kL\ge1$, a contradiction. Thus $a<4k$. Using
$$
1+1/(kL)\le(1+1/(aL))(1+1/(bL))^2
$$
and subtracting $1+1/(aL)$ shows that $b$ is at most $ka/(a-k)$ times $(1+1/(aL))(2+1/(bL))$. This last factor is at most $(5/4)(9/4)<3$, so $b<3k(k+1)\le6k^2$.

Put $T=ab-k(a+b)$ and $K=kab-Tc$. Direct expansion of the upper envelope yields
$$
0\le (N-1)P-NV=L[KL^2+k(a+b+c)L+k].
$$
For each $z=a,b,c$, we have $1/(zL+1)>1/(zL)-1/(z^2 L^2)$. If $T<0$, the lower envelope with just the terms at $a,b$ gives $1/a+1/b-1/k<2/(La^2)$. The left side is at least $1/(kab)$, so $L<2kb/a<12k^2$.

If $T=0$ then $u=a+b\le4k^2$ as before. The lower envelope forces $F=Np^2r^2-(N-1)\Phi(p)\Phi(r)>0$. But substituting $ab=ku$ gives
$$
F=-k^2uL^3+(u^2-5ku)L^2+(2u-8k)L+1<0.
$$
Indeed $F/(uL^2)\le-k^2L+4k^2+2/L+1/(uL^2)<0$.

Finally let $T>0$. The upper envelope gives
$$
c(T-k/L)\le kab+k(a+b)/L+k/L^2.
$$
As $T\ge1$ and $k/L<1/4$, this bounds $c$ by $kab(1+1/(aL))(1+1/(bL))/(1-k/L)<3kab$. In particular $c<72k^4$. If $K<0$, integrality gives $L\le k(a+b+c)+k/L<83k^5$. If $K>0$, the lower envelope with three terms gives $1/a+1/b+1/c-1/k<3/(La^2)$, whose left side is at least $1/(kabc)$. Hence $L<3kbc/a<9k^2b^2<324k^6$.

If $K=0$, then $1/a+1/b+1/c=1/k$. For each $x=zL+1$ one has
$$
1+1/x+1/x^2=1+1/(zL)-1/[zL(zL+1)^2].
$$
The sum of the three losses is at most $3/(a^3L^3)$. The cross term from $p,r$ in the product of the three factors is greater than $1/(4abL^2)$. Since $L>12b/a^2$, this gain exceeds the loss, forcing $H>1+1/(kL)$, the final contradiction.

## Fixed proportional overlap at arbitrary exponents on the plus side

If the odd part $M_0=p^{2e_p}r^{2e_r}s^{2e_s}$ has three distinct odd prime factors, all positive exponents may vary in the following conclusion:
$$
\frac{\gcd(N+1,p+1,r+1,s+1)}{N+1}\longrightarrow0
$$
along any sequence of candidates with $N\to\infty$. This extends the qualitative conclusion of the plus-side bound to higher exponents.

Use the same $k,L,a,b,c$ as in the plus-side argument, so $p=aL-1$. For a bounded sequence of $k$, pass to a subsequence on which $k$ is constant. The upper abundancy envelope still yields a nonnegative $E=(N-1)P-NV$, since $-V/M_0>-1$. The lower envelope still gives the same inequalities on $a,b,c$ and $K$. Thus $a,b$ are bounded and may also be fixed on a subsequence. Both cases $ab\ne k(a+b)$ have already given a bound on $L$ from these envelopes. It remains to exclude $L\to\infty$ on the harmonic boundary $ab=k(a+b)$.

Set $A=1/a$, $B=1/b$, $T=A+B=1/k$, and $z=1/L$. Write $U=N/(N-1)$, $H_x=\sigma(x^{2e_x})/x^{2e_x}$ for $x=p,r,s$, and $H_2=H_pH_r$. Define the polynomial
$$
H(A,i)=1+Az+2A^2z^2+(4-i)A^3z^3+(8-4i)A^4z^4.
$$
Then $H_p=H(A,i)+O(z^5)$, where $i=1$ if $e_p=1$, and $i=0$ otherwise. Indeed the infinite geometric sum is $(1-Az)/(1-2Az)$. The tail that starts at $p^{-3}$ when $e_p=1$ contributes $A^3z^3+4A^4z^4+O(z^5)$. For $e_p\ge2$ the omitted tail is $O(z^5)$ uniformly in $e_p$. Use $H(B,j)$ for $r$, and pass to a subsequence with $i,j$ fixed. Also $U=H(T,0)+O(z^5)$.

Let $w_i$ denote the coefficient of $z^i$ in $H(T,0)-H(A,i_p)H(B,i_r)$, with $i_p=i$ and $i_r=j$. Then $w_0=w_1=0$ and $w_2=3AB>0$. From the exact equation,
$$
U/H_2-1=H_s-1+1/[(N-1)M_0H_2].
$$
The right side is comparable to $1/s$ uniformly in $e_s$, so $s$ is comparable to $L^2$. Expanding $H_s-1=1/s+1/s^2+O(1/s^3)$ uniformly and using $M_0\ge p^2r^2s^2$ now gives
$$
s=U/(U-H_2)+O(1/s)+O(1/[(N-1)p^2r^2]).
$$
Division of the series gives $s=Q(L)+O(1/L)$ with $Q$ a quadratic polynomial having fixed rational coefficients. Its constant term is
$$
Q(0)=2T^2/w_2-(w_4+Tw_3)/w_2^2+w_3^2/w_2^3.
$$
In every case $Q(0)+1>0$. In fact the polynomial $w_2^3(Q(0)+1)$ is one of the following:

| $(i,j)$ | Polynomial |
|---|---|
| $(0,0)$ | $A^2B^2(4A^2+71AB+4B^2)$ |
| $(1,0)$ | $A^2(A^4+5A^3B+18A^2B^2+71AB^3+4B^4)$ |
| $(0,1)$ | The preceding polynomial with $A,B$ interchanged |
| $(1,1)$ | $A^6+5A^5B+18A^4B^2+73A^3B^3+18A^2B^4+5AB^5+B^6$ |

Choose a fixed positive integer $d$ clearing the coefficients of $Q$. Then $ds-dQ(L)$ is an integer tending to zero, so eventually $s=Q(L)$. Since $L\mid s+1$, this would force $L$ to divide the fixed positive integer $d(Q(0)+1)$. This rules out every bounded value of $k$ along a sequence with $N\to\infty$.

## Shared shifts for the two smallest primes

In the three-prime squarefree-root case, every sequence of candidates at unbounded levels also satisfies
$$
\frac{\gcd(N+1,p+1,r+1)}{N+1}\to0,\qquad
\frac{\gcd(N-1,p-1,r-1)}{N-1}\to0 .
$$
In particular, $\gcd(N-1,D_p,D_r)/(N-1)\to0$, with no condition on the quotient at the largest prime.

For the proof, take either sign and write $L$ for the corresponding gcd involving only $p,r$. Suppose the corresponding index $k=(N\pm1)/L$ stays bounded. Pass to a subsequence with fixed $k$ and $L\to\infty$. As in the three-prime common-shift argument, write the two smallest primes as $aL-1,bL-1$ on the plus side and $aL+1,bL+1$ on the minus side. The derivation bounding $a,b$ on both sides did not require $c$ to be integral: on the plus side $c=(s+1)/L$ can be real since $E\ge0$ still gives a positive real $K$ and therefore $a<3k$ and $b<4k^2$. On the minus side the upper Euler factors directly bound $a,b$. Thus pass to a further subsequence with fixed $a,b$.

Put $u=a+b$, $v=ab$ and $T=v-ku$. The two-factor lower abundancy bound excludes $T<0$ for sufficiently large $L$ on either side. If $T=0$, the minus side was already excluded, while on the plus side the harmonic division gives $s=Q(L)+O(1/L)$ with $Q(0)+1>0$.

For $T>0$ use $C=Np^2r^2$, $F=C-(N-1)\Phi(p)\Phi(r)$. By $C=sF+D_s$ we have $0<C/F-s<1/(s+1)=O(1/L)$. Polynomial division gives $C/F=Q(L)+O(1/L)$, where $Q$ is linear with rational coefficients. Its leading coefficient is $kv/T$ and its constant satisfies
$$
Q(0)+1=-3k(uT+kv)/T^2<0
$$
on the plus side, and
$$
Q(0)-1=k(uT+kv)/T^2>0
$$
on the minus side. Indeed the leading two coefficients of $C$ in degrees five and four are $kv^2$ and $-2kuv-v^2$ on the plus side and $kv^2$ and $2kuv+v^2$ on the minus side. The corresponding coefficients of $F$ in degrees four and three are $vT,3kv$ on the plus side and $vT,2uT-kv$ on the minus side.

For both $T>0$ and the harmonic plus side, eventual integrality gives $s=Q(L)$ by clearing the constant denominators in $Q$. The original equation now implies a rational polynomial in $L$,
$$
FQ(L)^2-(N-1)\Phi(p)\Phi(r)(Q(L)+1)-1,
$$
vanishes at infinitely many distinct integers $L$. Hence it is the zero polynomial. On the plus side $L=0$ gives $p=r=N=-1$ and the value $(Q(0)+1)^2$, strictly positive in each case. On the minus side $L=0$ gives $p=r=N=1$ and the value $Q(0)^2-1>0$. Both are contradictions.
