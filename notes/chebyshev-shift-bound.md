# A bound on the common negative shifts in the five-prime Chebyshev problem

**Theorem.** Suppose $7\le d<e<a<b<c<2d$ are primes with negative signs at $d,e$ and positive signs at $a,b,c$ in the five-prime Chebyshev test. Then
$$
\gcd(d+1,e+1)\le\frac{d+1}{10}.
$$
The original one-ninth bound follows by excluding $(7,11,442)$. The stronger bound follows by excluding the last two families with $(d+1)/\gcd(d+1,e+1)=9$. For $k=(d+1)/\gcd(d+1,e+1)$, this proves $k\ge10$ without a prime-size cutoff. The full five-prime conjecture and the spread inequality $c>2d$ remain open in this work. [Local Chebyshev criterion](17-chebyshev.md) · [Original problem](https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials).

## Why the exceptional family suffices for the one-ninth bound

Assume $7\le d<e<a<b<c<2d$ are primes, $n=abcde$, $A=abc$, $B=ab+ac+bc$, and $Bde-A(d+e)=1$. Assume that $d+1,e+1,a-1,b-1,c-1$ all divide $n-1$. These conditions follow from the Chebyshev test in this sign order.

Set $g=\gcd(d+1,e+1)$, $k=(d+1)/g$, $\ell=(e+1)/g$, and $r=\ell-k$. Then $g$ is even, $\gcd(k,\ell)=1$, and $2\le k<\ell<2k$ by $d<e<2d$. We first treat $2\le k\le8$, then test equality at $k=9$.

Modulo $d$ the cofactor equation gives $eA\equiv-1$; modulo $d+1$ this follows from $d+1\mid n-1$. The two moduli are coprime. Likewise at $e$. Thus
$$
 eA\equiv-1\pmod{d(d+1)},\qquad dA\equiv-1\pmod{e(e+1)}.
$$
Since $d,e\equiv-1\pmod g$, we also have $A\equiv1\pmod g$. Put $X=(A-1)/g$. There is an integer $h$ such that
$$
 r^2X=k\ell(k+\ell)-2k^2\ell^2g+hde. \tag{1}
$$
For example, modulo $d$, we have $kg=1$, $e=r/k$, $A=-k/r$, hence $r^2 X=-k\ell r$. The first two terms on the right also give $-k\ell r$. Modulo $e$ the corresponding equalities are $\ell g=1$, $d=-r/\ell$, $A=\ell/r$ and $r^2X=k\ell r$. Since $d,e$ are distinct primes, their product divides the difference.

The required shifts also give $eX\equiv-\ell\pmod k$ and $dX\equiv-k\pmod\ell$ by substituting $A=1+gX$ in $eA+1,dA+1$. Together with (1), this yields
$$
 he^2\equiv\ell^3\pmod k,\qquad hd^2\equiv k^3\pmod\ell,\qquad
 k\ell(k+\ell)-2k^2\ell^2g+hde\equiv0\pmod{r^2}. \tag{2}
$$
The negative congruences and the primality of $d,e$ imply $\gcd(d,\ell r)=\gcd(e,kr)=1$.

There are two bounds for $A$. Applying the arithmetic–geometric mean inequality to $1/a,1/b,1/c$, whose sum is $(d+e+1/A)/(de)$, gives $A>[3de/(g(k+\ell))]^3$. For the upper bound, put $z_p=2d/p-1>0$ for $p=a,b,c$. Then $8d^3/A=\prod_p(1+z_p)>1+\sum_p z_p=2d/e+2d/n$, so $A<4d^2e$. For $d>1000$ put $x=k/1000>1/g$. In (1) the correction $hgde-r^2A=2k^2\ell^2g^2-k\ell(k+\ell)g-r^2$ is positive, since $k,\ell,g\ge2$ and $k\ell>r$. The bounds on $A$ therefore give
$$
 \frac{27r^2(k-x)^2(\ell-x)^2}{(k+\ell)^3}<h<
 4kr^2+\frac{2k^2\ell^2x}{(k-x)(\ell-x)}. \tag{3}
$$
For $2\le k\le8$, enumerate each coprime $k<\ell<2k$, each integer $h$ in (3), and each even residue $g$ modulo $2k\ell r^2$. This modulus includes the full periods of (2) and the two coprimality tests. Only $(k,\ell,h)=(7,11,442),(8,11,283)$ survive. For $d\le1000$, a separate check enumerates the 329 possible negative-prime pairs with $k\le8$, solves the two simultaneous congruences on $A$ by CRT, and examines all resulting products $e^3<A<4d^2e$. There are 106 products and none is a product of three distinct primes in $(e,2d)$. These calculations use exact integers and rational endpoints.

From (1) and the signed equation,
$$
 B=-1+\frac{(k+\ell)hg^2-2g(h+k\ell(k+\ell))}{r^2}.
$$
Every candidate also has $n\equiv1\pmod4$. For the signed coordinates $u=(a,b,c,-d,-e)$, the signed equation gives $e_4(u)=1$. If $r$ signed coordinates are $-1\pmod4$, then $(-1)^r(5-2r)\equiv1\pmod8$, so $r=2$ or $3$. A coordinate equal to $1\pmod4$ has a required shift divisible by 4. This proves the stated congruence.

Every candidate has $n\equiv1\pmod3$. Otherwise none of the five required shifts could be divisible by 3, so all five signed prime coordinates would equal $-1\pmod3$. Their fourth elementary symmetric sum would be $5\not\equiv1\pmod3$, contradicting the signed equation.

For $(k,\ell,h)=(8,11,283)$ let $g$ range over the 81 residues modulo 81. Require $3\nmid de$, integrality at 3 of $(A-1)/g$ and $B$ from the displayed formulas, and $Ade\equiv1\pmod3$. The survivors $(g,A,B)\bmod(81,9,9)$ are $(1,1,0),(28,7,3),(55,4,6)$. Each has $(A,B)\equiv(1,0)\pmod3$, forcing $a,b,c\equiv1\pmod3$. Expanding $a,b,c$ about 1 gives $B\equiv2A+1\pmod9$, which fails for all three rows. The denominator $r^2=9$ explains why residues modulo 81 suffice.

For $(k,\ell,h)=(7,11,442)$ the formulas give
$$
 d=7g-1,\quad e=11g-1,\quad
 A=(17017g^3-9907g^2+914g+8)/8,\quad
 B=(1989g^2-914g-4)/4.
$$
Thus excluding exactly this polynomial family proves $k\ge9$, equivalently $\gcd(d+1,e+1)\le(d+1)/9$, for every candidate in the stated order and interval.

The argument reproduces Sections 6 and 7 of *The remaining interval in the five-prime Chebyshev case* (November 26, 2026), with a smaller independent finite check sufficient for these seven values of $k$.

## The exceptional family

The remaining exceptional parameters force $d=7g-1$, $e=11g-1$ and
$$
 A=abc=(17017g^3-9907g^2+914g+8)/8,\qquad
 B=ab+ac+bc=(1989g^2-914g-4)/4 .
$$
These polynomials satisfy $Bde-A(d+e)=1$ identically. Write $S=a+b+c$, $n=Ade$ and define
$$
 R=(a-1)(b-1)(c-1)=A-B+S-1,\quad L=\operatorname{lcm}(a-1,b-1,c-1),\quad w=R/L.
$$
The three positive required shifts divide $n-1$. Consequently $J=n-1-77g^2R$ is divisible by $L$, and the integer $\kappa=J/L$ satisfies $\kappa R=wJ$. Direct expansion gives
$$
8R=17017g^3-13885g^2+2742g+8S+8,\qquad
8J=g(-616Sg+54587g^2-26359g+770).
$$

### The sixteen possibilities for the overlap

Since $g\mid n-1$ and $de\equiv1\pmod g$, we have $A\equiv1\pmod g$. The numerator of $(A-1)/g$ over denominator 8, for even $g\equiv0,2,4,6\pmod8$, is respectively $2,0,6,4\pmod8$. Thus $g\equiv2\pmod8$ and $d,e\equiv1\pmod4$. The primality of $7g-1$ and $11g-1$, both greater than three, forces $3\mid g$.

For the signed coordinates $(a,b,c,-d,-e)$ the fourth elementary symmetric sum equals 1. Replacing an odd coordinate by another congruent to it modulo 4 preserves this sum modulo 8, since its coefficient is a sum of four odd products. If $r$ coordinates are $-1\pmod4$, reduction therefore gives $(-1)^r(5-2r)\equiv1\pmod8$, or $r\in\{2,3\}$. Some coordinate is $1\pmod4$, so its required shift is divisible by 4 and $n\equiv1\pmod4$. The product of the five signed coordinates equals $n$, hence $r$ is even. The two negative coordinates already account for both occurrences, giving $a,b,c\equiv1\pmod4$.

Their pairwise product sum consequently satisfies $B\equiv3\pmod8$. With $t=g/2\equiv1\pmod4$ the family formula gives $B\equiv4-t\pmod8$, so $g\equiv2\pmod{16}$ and $g\equiv18\pmod{48}$. Write $a=1+4x,b=1+4y,c=1+4z$. Then
$$
2A-B+1=16(xy+xz+yz)+128xyz\equiv16\pmod{32},
$$
where the last residue follows by substituting $g=2t$, $t\equiv1\pmod8$, in the family formulas. At least two of $x,y,z$ are odd. The two smallest 2-adic valuations among the positive shifts are both 2, so $v_2(w)=4$.

Let $m$ be any odd divisor of two of the positive shifts. Then $m\mid n-1$ and $m\mid 2A-B+1$ because, for instance, $a,b\equiv1\pmod m$ implies $A\equiv c$, $B\equiv1+2c$. Introduce the integer polynomials
$$
 P=4(2A-B+1)=17017g^3-11896g^2+1828g+16,\qquad
 F=8(n-1)/g=1310309g^4-1069145g^3+265721g^2-25743g+770.
$$
The constant $P(0)=16$ gives $\gcd(m,g)=1$, hence $m\mid F$. The following polynomial identity applies to the entire modulus $m$, including prime powers:
$$
 UP+VF=64K,\qquad K=7\cdot11\cdot41\cdot11683657,
$$
with
$$
 U=7110817638925g^3-582543875991g^2-111642799613g+35208505871,
 \quad V=-92348281025g^2-3228450042g+2334186280 .
$$
The verifier checks this identity coefficient by coefficient and proves that each listed factor of $K$ is prime by trial division. Every such odd $m$ divides $K$.

An odd prime $\ell$ dividing all three positive shifts would give $A\equiv1$ and $B\equiv3\pmod\ell$. From $n\equiv1\pmod\ell$ and $Bde-A(d+e)=1$ we get $de\equiv1$ and $d+e\equiv2$. Thus $d\equiv e\equiv1\pmod\ell$. This would imply $\ell\mid11(d-1)-7(e-1)=-8$. Hence every odd prime in $w$ occurs in exactly two shifts, and its exponent in $w$ is at most one. We have $w=16H$ for $H\mid K$.

Each $\ell\mid H$ must also satisfy $P(g)=F(g)=0$ in $\mathbb F_\ell$. The monic gcd of the two polynomials gives the following complete lists. The verifier checks that the gcd equals the product of the indicated linear factors.

| Prime $\ell$ | Possible $g\bmod\ell$ |
|---:|---|
| 7 | 4 |
| 11 | 5 |
| 41 | 18, 29 |
| 11,683,657 | 5,633,197 |

### Why the parameter search is finite

From $S^2\ge3B$ we have $S>38g$ for $g\ge18$, since $4(3B-(38g)^2)=191g^2-2742g-12>0$. The interval $a,b,c<2d$ gives $S<42g$. In the formulas for $8(J-R)$ and $8(6J-11R)$ the coefficients of $S$ are negative. Substituting $42g$ for the first lower bound and $38g$ for the second upper bound gives
$$
8(J-R)>11698g^3-12474g^2-2308g-8>0,\qquad
8(6J-11R)<-113g^3-5419g^2-28886g-88<0 .
$$
It follows that $1<\lambda=\kappa/w=J/R<11/6$.

Define the integer
$$
 z=(54587w-17017\kappa)g+(13885\kappa-26359w)-616wS .
$$
Substituting $\kappa R=wJ$ and collecting terms gives
$$
 (77wg^2+\kappa)z=-E g-F_0,\qquad
 E=17017\kappa^2-265721\kappa w+59290w^2,\quad F_0=\kappa(25743w-13885\kappa).
$$
Here $F_0>0$. Also $(E+F_0)/w^2=3132\lambda^2-239978\lambda+59290$ is negative at 1 and decreasing up to $11/6$. Thus $E<0$ and $Eg+F_0<0$ for $g\ge1$. In particular $z$ is a **positive** integer. The polynomial $(-17017\lambda^2+265721\lambda-59290)/77$ is increasing on this interval. Evaluation at its upper endpoint yields
$$
 0<gz< -E/(77w)<(1213099/252)w<4814w .
$$
Both $g$ and $z$ are now bounded in terms of one of the sixteen possible $w$.

### The square test

The last identity is equivalent to the following quadratic in $\kappa$:
$$
 (17017g-13885)\kappa^2+
 \bigl[(-265721g+25743)w+z\bigr]\kappa+
 59290gw^2+77wg^2z=0 .
$$
Its leading coefficient is positive. An integer root forces the discriminant to be a nonnegative perfect square. For each divisor $H$ of $K$, combine $g\equiv18\pmod{48}$ with the appropriate residues in the table, enumerate that progression up to $g<4814w$, and test $1\le z\le\lfloor(4814w-1)/g\rfloor$. The full enumeration has 16 overlaps, 24 residue classes, 38,517 values of $g$ counted with their overlap, and 1,803,673 discriminants. None is a square. This excludes the exception for every even $g$. A second implementation in the same verifier enumerates an auxiliary integer first and independently finds zero square discriminants in 67,500 checks.

Run `python checks/chebyshev_7_11_family.py` from the repository root. The complete finite search uses integer arithmetic. The researcher supplied the exceptional-family proof and verifier from a separate model. The positive-overlap argument is credited to that contribution. This is a computer-assisted exclusion for the specified ordering and interval.

### Equality in the one-ninth bound

The same computation gives a further restriction when $k=9$. Above $d=2000$, use $x=9/2000$ in (3) and enumerate (2) as before. The two surviving pairs are $(\ell,h)=(13,562),(14,893)$. For $d\le2000$ there are 93 eligible negative-prime pairs with $k=9$. Their CRT classes contain 11 possible products in $e^3<A<4d^2e$, and none has the required prime factorization. Thus, at every prime size, the equality case $9g=d+1$ has at most the following two polynomial families. The two arguments in the companion note exclude both families.

| $(k,\ell,h)$ | $A$ | $B$ |
|---|---|---|
| $(9,13,562)$ | $(32877g^3-19871g^2+1568g+8)/8$ | $(3091g^2-1568g-4)/4$ |
| $(9,14,893)$ | $(112518g^3-52291g^2+3791g+25)/25$ | $(20539g^2-7582g-25)/25$ |

The [(9,13,562) proof](chebyshev-ninth-ratio.md#the-913562-family) tests 1,093,956 discriminants, and the [(9,14,893) proof](chebyshev-ninth-ratio.md#the-914893-family) tests 2,776,728. Neither admits a square. Since $k$ is an integer, $k\ge10$, proving the theorem.

## Reproduce the checks

Run these four commands from the repository root with Python 3.8 or later. All four certificates use the standard library.

```sh
python checks/chebyshev_small_shift_ratios.py
python checks/chebyshev_7_11_family.py
python checks/chebyshev_9_13_family.py
python checks/chebyshev_9_14_family.py
```
