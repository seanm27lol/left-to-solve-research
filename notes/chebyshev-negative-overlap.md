# The middle gap, the lower three primes and the two negative shifts

Let $7\le d<e<a<b<c<2d$ be distinct odd integers satisfying the signed reciprocal equation
$$
1/a+1/b+1/c-1/d-1/e=1/(deabc).
$$
Write $v=a-e$, $h=e-d$, $g=\gcd(d+1,e+1)$, and $K=(d+1)/g$, $L=(e+1)/g$. Then
$$
d<6v(h+v),\qquad d<8K^2v(v+1).
$$
The first inequality forces $a-d>\sqrt{d/6}$. The second gives a square-root lower bound on the product of the middle gap and the denominator of $(e+1)/(d+1)$. The conclusions use no prime bound, primality test or local required shifts.

Put $j=2d-b$, $k=2d-c$, $m=j+k$, $u=jk$. Both $j,k$ are positive odd and $m$ is even. The signed equation can be written in either of the forms
$$
\frac{j}{2db}+\frac{k}{2dc}=\frac{v}{ea}+\frac1{deabc},
\qquad
(md-u)ea=v d(4d^2-2md+u)+1.
$$
The first gives $mea<4vd^2+4d/(bc)<4vd^2+1$. By integrality $mea\le4vd^2$, so in particular $m<4v$ since $ea>d^2$. The second gives
$$
(4v-m)d^2=m(ea-d^2)+2vmd-vu-u ea/d-1/d.
$$
Now $ea-d^2=d(2h+v)+h(h+v)<d(3h+v)$ since $a<2d$. Since $4v-m$ is a positive even integer, $2d^2<3md(h+v)<12vd(h+v)$.

For the index bound, put $J=4vK^2-mL^2$. The inequality $m e^2<m ea\le4vd^2$ and $L/K<e/d$ give $J>0$. By the exact signed equation,
$$
4vd^2-me^2=m ev+2vmd-vu-u ea/d-1/d<4mvd .
$$
Also $0<e/d-L/K=(e-d)/(d(d+1))<1/d$ and $e/d+L/K<4$. Consequently
$$
2\le J=K^2\left[4v-m(e/d)^2+m((e/d)^2-(L/K)^2)\right]
<4mK^2(v+1)/d<16vK^2(v+1)/d,
$$
where the first inequality uses evenness.

## Additional congruences from the required shifts

Now suppose $d+1,e+1\mid n-1$, where $n=deabc$. Set $C=(j+2)(k+2)$. Since $d=e=-1\pmod g$, the product congruence and signed equation give $abc=1$ and $ab+ac+bc=-1\pmod g$. Substituting $a=v-1$, $b=-(j+2)$ and $c=-(k+2)$ modulo $g$ yields
$$
(v-1)C\equiv1,\qquad C+1\equiv(v-1)(m+4)\pmod g.
$$
In particular
$$
g\mid(v-1)^2(m+4)-v,\qquad g\mid C(C+1)-(m+4).
$$
The first integer is positive for $v\ge2$ and, since $m<4v$, smaller than $4(v+1)^3$. Thus $g<4(v+1)^3$.

If the three positive shifts are required as well, $G=\gcd(a-1,b-1,c-1)$ divides $v^2$. Indeed $de=1$ and $d+e=2\pmod G$ by $n=1$ and the signed equation. Thus $(e-1)^2=0\pmod G$ and $e=a-v=1-v\pmod G$.

## A quadratic bound for the common negative shift

For every full Chebyshev candidate in this order one has
$$
\boxed{\gcd(d+1,e+1)<4v^2},\qquad d+1<4K v^2 .
$$
The previous exhaustive dyadic result gives $v\ge102$, and the top-pair result gives $t=c-b\ge26$ and $b<1+t^2(t^2-1)^2+18t^2<t^6$ for these two positive signs. The last inequality follows already for $t\ge4$. These and $n\equiv1\pmod3$ are the previously established facts used below.

Let $R=(v-1)S-C-1$, with $S=m+4\le4v+2$. The negative shifts give $g\mid R$. Now $R<(v-1)S<4v^2$ and $R\ge S(v-1-S/4)-1\ge-3S/2-1>-4v^2$. Thus if $R\ne0$ the bound follows immediately. If $R=0$ then $t^2=S^2-4C=S[S-4(v-1)]+4$. Since $t\ge26$, the even integer $S-4(v-1)$ is one of $2,4,6$. Hence $t^2$ equals $8v$, $16v+4$ or $24v+16$, respectively.

The first and third exceptional families in the preceding list actually vanish modulo three. Every candidate has $n\equiv1\pmod3$ and all bases prime greater than 3. The signed coordinates $a,b,c,-d,-e$ have product 1 modulo three, and by the signed equation their inverse sum is also 1. Thus exactly two of them are $-1\pmod3$ (the negative count is even and congruent to 2 modulo three).

* If $t^2=8v$, write $t=4w$, $v=2w^2$ and $j,k=2v-3\pm2w$. For $w=0\pmod3$ one has $a=e$, $b=c=-d$ modulo 3, so the negative count is either one or four. For $w\ne0\pmod3$, $v=2$ and the pair $j,k$ is $0,2$ modulo 3. Requiring all coordinates to be units gives $e=d=-1$ and then only one signed coordinate is $-1$.
* If $t^2=24v+16$, then $t=4w$ and $v=2(w^2-1)/3$, so $3\nmid w$. The pair $j,k=2v-1\pm2w$ equals $2v,2v+1$ in some order modulo three. If $v=0$ one has $a=e$, $d=1$ and the negative count is three. If $v=1$, then $e=1,d=-1$, which again gives three. For $v=2$, one of $b,c$ would vanish modulo three.

Consequently only $t^2=16v+4$ remains on $R=0$. Write $t=4w+2$; then $v=w(w+1)$, $m=4v-4$, and $C=4v(v-1)-1$. Thus
$$
g\mid (v-1)C-1=v(2v-3)(2v-1).
$$
Also $d+1\mid W=vC^2-S=v(2v-3)(2v+1)(2v-1)^2$ by the middle-gap reduction.

Suppose $g\ge4v^2$ and put $\lambda=\sqrt{v/(v-1)}$, $z=e/d$, $E=\lambda d-e$, and $b_0=u/m=v-2-5/[4(v-1)]$. The earlier bound $me^2<4vd^2$ gives $1<z<\lambda<1.005$ and
$$
4v^2\le g\le e-d<(\lambda-1)d<d/[2(v-1)].
$$
Also $0.98v<b_0<v$, $b_0>v-2.02$. The signed equation gives the exact formula
$$
E=\frac{v(z+2)-b_0[z^2+(z+1)v/d]-1/(md^2)}{\lambda+z}.
$$
Since $d>8(v-1)v^2$ and $v\ge102$, it gives $0.98v<E<1.02v$. For example on dividing its numerator by $v$ the lower bound is $3-1.005^2-2.005/400-1/10000$, and the upper bound is $3.005-0.98$. The denominator is between 2 and 2.01. All terminating decimals denote exact rationals.

In fact $E<v+1/2$. Squaring gives $\lambda>1+0.49/v$, and then $z=\lambda-E/d>1+0.48/v$. Consequently $b_0 z^2>b_0+0.96 b_0/v>v-1.08$. These estimates yield
$$
(v+1/2)(\lambda+z)-[v(z+2)-b_0z^2]
=v(\lambda-1)+(\lambda+z)/2+b_0z^2-v>0.49+1-1.08>0.
$$

Now $g$ divides the integer $\Theta=2(d+1)-(4v-3)(e-d)$. Rationalization using $(4v-3)^2v-(4v-1)^2(v-1)=1$ gives
$$
\Theta=2+(4v-3)E-\frac{d}{(v-1)[(4v-3)\lambda+4v-1]}.
$$
The last positive fraction is less than $530v$: use $d<t^6=(16v+4)^3<(16.04v)^3$, $v-1>0.99v$ and $(4v-3)\lambda+4v-1>7.96v$. Thus $\Theta<2+(4v-3)(v+1/2)<4v^2$. When $v\ge150$, the lower bound $\Theta>2+(4v-3)0.98v-530v>0$ gives the required contradiction.

For $102\le v<150$, the only values of $v=w(w+1)$ are 110 and 132. Enumerate the divisors $D$ of the displayed integer $W$ and set $d=D-1$. Keep odd $7\le d<t^6$ with $d>j+v$. Then the first gap gives $j=2w^2+4w-1$ and $k=2w^2-3$. Respectively 529 and 331 values of $D$ remain, and none gives an integer $(v d b c+1)/(md-u)=ea$. This excludes the last two exceptional values for all prime sizes and completes the proof. The accompanying verifier checks the identities, local obstructions, rational estimates and these final two lists.

[Exact verifier](../checks/chebyshev_negative_overlap.py) · [Top and middle gap prerequisites](chebyshev-prime-gaps.md).
