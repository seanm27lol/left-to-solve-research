# A joint restriction on the middle and top gaps

Suppose the five distinct odd integers in the Chebyshev interval satisfy $7\le d<e<a<b<c<2d$ and the signed reciprocal equation. Write $n=deabc$ and assume the required shifts $e+1,a-1$ divide $n-1$. Put $v=a-e$, $h=c-b$, $j=2d-b$, $k=2d-c$, $m=j+k$, $u=jk$, $M=md-u$, $Q=dbc$, $Y=ea$ and $g=\gcd(e+1,a-1)$. For $v>2$, $g\mid v-2$. If either $\gcd(j,k)=1$ or $v\nmid gm^3$, then
$$
d<\max\{48g v^2,18\sqrt{g v^5(v+h^2)}\}.
$$
For example, along any sequence in this family with $h=O(v^{3/4})$ this gives $d=O(v^{15/4})$. The exponents in the earlier separate bounds for these two gaps were $4$ for $v$ and $6$ for $h$.

The signed equation gives $MY=vQ+1$. Also $v<m<4v$. For the upper bound, use $j/(2db)+k/(2dc)=v/(ea)+1/n$, as in the existing middle-gap proof. For the lower bound, the left side is less than $m/(2da)$, whence $m>2dv/e>v$.

## Recovering the shifts before reconstructing the primes

Put $H=Y+v-1=(e+1)(a-1)$. Since $g$ is the gcd of two positive integers whose difference is $v-2$,
$$g^2=\gcd(H,(v-2)^2).$$
This follows at each prime by comparing the valuations of the two integers. Their least common multiple equals $H/g$. Since $n=YQ\equiv -(v-1)Q\pmod H$, both shifts hold exactly when
$$
H/g\mid (v-1)Q+1 .
$$
In particular $H/g$ divides $M(v-1)^2-1$, since modulo $H$ the relation $MY=vQ+1$ gives $v[(v-1)Q+1]\equiv1-M(v-1)^2$. Hence
$$Z=\frac{g[M(v-1)^2-1]}{H}$$
is a positive integer with $Z<gmv^2/d<4gv^3/d$. The inequality uses $M<md$ and $H>d^2$. These tests can be applied at integral $Y=(vQ+1)/M$ before the square test for $e$.

## Integral remainder

Let $S=MH=vQ+1+(v-1)M$. Define the signed integer
$$J=g(v-1)^2m^3-vZ(4md-2m^2+8u).$$
Using $Q=d(4d^2-2md+u)$ and $h^2=m^2-4u$, polynomial division gives
$$
m^3S-v(4md-2m^2+8u)M^2
 =m^3(v-1)M+m^3-vu h^2(3md-2u).
$$
Since $ZS=gM[M(v-1)^2-1]$, this gives the exact relation
$$
J=\frac{[g+Z(v-1)]m^3}{M}
  +\frac{Z[m^3-vu h^2(3md-2u)]}{M^2}.
$$
Here $M>2md/3$ because $u\le m^2/4$ and $d>j+v>3m/4$. Applying $m<4v$, $u/m<v$, $v<d$ and the bound on $Z$ gives
$$
|J|<\frac{24gv^2}{d}
 +\frac{96gv^6+36gv^4/d+27gv^5h^2}{d^2}
 <\frac{24gv^2}{d}+\frac{160gv^5(v+h^2)}{d^2}.
$$
If $J\ne0$ the claimed bound follows since $18^2>320$.

If $J=0$, its definition forces $v\mid gm^3$. It remains to treat $J=0$ when $j,k$ are coprime. The exact relation implies
$$m^3\mid Zvu h^2(3md-2u).$$
Every odd prime dividing $m$ is coprime to $uh(3md-2u)$ because $\gcd(j,k)=1$ and $h=j-k$. If $4\mid m$, then $h$ has 2-adic valuation one and $3md-2u$ has valuation one. If $m\equiv2\pmod4$, the 2-part of $m^3$ equals 8. Thus $m^3\mid8Zv$. Substitution of $Z<gmv^2/d$ now gives $d<8gv^3/m^2<8gv$, which is within the asserted bound.

The zero-remainder condition is particularly restrictive when $t=\gcd(j,k)>1$. Put $m'=m/t$, $h'=h/t$. Every prime dividing $t$ is coprime to $v,d$, by $MY=vQ+1$, and to $g$ since $g\mid H/g\mid M(v-1)^2-1$ and $t\mid M$. The formula for $Z$ then gives $\gcd(t,Z)=1$. From $J=0$ and $4md-2m^2+8u=2t(2m'd-t h'^2)$ it follows that
$$2m'd\equiv t h'^2\pmod {t^2}.$$
In particular $t\mid m'$. Each odd prime dividing $t$ is then coprime to $h'$ because $j/t,k/t$ are relatively prime. Dividing the last congruence by $t$ gives $\gcd(m/t^2,t)=1$. Thus the first bound also holds whenever $t^2\nmid m$, or when $t^2\mid m$ but $m/t^2$ shares a prime with $t$.

For arbitrary $t=\gcd(j,k)$, allowing one more term gives the unconditional bound
$$d<\max\{48gv^2,18\sqrt{g v^5(v+h^2)},8gv t^6\}.$$
Indeed write $j=t j'$, $k=t k'$, $m=t m'$, $u=t^2u'$, $h=t h'$. In the case $J=0$, the divisibility just proved gives
$$m'^3\mid Zvt^2u'h'^2(3m'd-2tu').$$
Every odd prime $\ell\mid m'$ is coprime to $u'h'$. If $v_\ell(m')>v_\ell(t)$ then the last factor has valuation exactly $v_\ell(t)$. If $v_\ell(m')\le v_\ell(t)$, then the $\ell$-part of $m'^3$ divides $t^3$. At 2, $t$ is odd and the argument above applies to $j',k'$. Thus $m'^3\mid 8Zv t^3$, or $m^3\mid 8Zv t^6$, proving the displayed bound. In particular the $O(v^{15/4})$ conclusion also holds when $t$ stays bounded and $h=O(v^{3/4})$.

## Certificate for every even middle gap at most 500

The signed identity and $d+1\mid n-1$ alone imply $a-e\ge502$ in this interval. The proof uses the two divisors in [the previous middle-gap reduction](chebyshev-prime-gaps.md). For $T=(j+2)(k+2)$,
$$d+1\mid W=vT^2-m-4,\qquad M\mid X=v[u(j-k)]^2-m^3.$$
For the first, $bc\equiv T$ and $YT\equiv-1\pmod{d+1}$. Multiply $MY=vQ+1$ by $T$ modulo $d+1$ to obtain $m+u\equiv T-vT^2$. For the second, $md\equiv u$, $mb\equiv-j(j-k)$ and $mc\equiv k(j-k)\pmod M$ show $m^3(vQ+1)\equiv-X\pmod M$. Also $\gcd(v,m,u)=1$, since a common prime would divide both $M$ and $v$ in $MY=vQ+1$.

The [integer verifier](../checks/chebyshev_middle_gap_500.cpp) enumerates positive even $2\le v\le500$ and positive odd $j>k$ with $v<m<4v$ and $\gcd(v,m,u)=1$. The integer $W$ is positive and even. Factoring $W/2$ enumerates every feasible odd $d$ as twice one of its divisors minus one. We retain $d\ge7$, $d>j+v$ and $M\mid X$. For every retained divisor the checker asserts $d<10^6$ before forming $Q$, protecting the subsequent 128-bit products. This assertion is tested on every divisor hit. The inequality $T<(2v+2)^2$ gives $W/2<500\cdot1002^4/2<341550071728321$. The first seven prime bases in Miller–Rabin determine primality throughout that range. The factor finder checks each returned proper divisor by an exact gcd. [Deterministic primality threshold](https://arxiv.org/pdf/1207.0063)

| Stage | Count |
| --- | ---: |
| Eligible gap triples | 18,627,549 |
| Divisor choices satisfying both divisor tests and the bounds on $d$ | 507 |
| Choices giving integral $Y$ | 49 |
| Choices with $\gcd(H,(v-2)^2)$ square | 31 |
| Choices satisfying $H/g\mid(v-1)Q+1$ | 0 |

Independently of the two shifts, an integral $Y=e(e+v)$ requires $v^2+4Y=(2e+v)^2$. The checker tests all 49 integral products and finds zero square discriminants. This establishes the assertion using only the signed identity and the shift at $d$.

Compile and run the checker with assertions enabled.

```sh
g++ -std=c++17 -O3 checks/chebyshev_middle_gap_500.cpp -o /tmp/check-cheb-middle
/tmp/check-cheb-middle
```

Larger middle gaps and the unrestricted five-prime question remain open.

[Symbolic check of the joint-gap identity](../checks/chebyshev_middle_product.py).
