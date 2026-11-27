# Excluding equality in the five-prime one-ninth bound

The [small-ratio reduction](chebyshev-shift-bound.md) leaves two triples when $9g=d+1$, with $g=\gcd(d+1,e+1)$. This note excludes both. Each proof applies the positive-shift overlap and integer remainder argument from the supplied $(7,11,442)$ proof to its own product and pair-sum polynomials. Throughout, $a,b,c$ have positive signs, $d,e$ have negative signs, and $7\le d<e<a<b<c<2d$.

## The 9,13,562 family

Suppose that five distinct primes satisfy $d<e<a<b<c<2d$, the signed cofactor equation, and all five required shift conditions. In this family $d=9g-1$, $e=13g-1$ with $g$ positive and even. Set $A=abc$, $B=ab+bc+ac$, $S=a+b+c$, and $n=Ade$. Substitution in the negative-shift parametrization at $(k,l,h)=(9,13,562)$ gives

$$
8A=32877g^3-19871g^2+1568g+8,\qquad
4B=3091g^2-1568g-4.
$$

These expressions satisfy $Bde-A(d+e)=1$. Since $g\mid n-1$ and $de\equiv1\pmod g$, $(A-1)/g$ is integral. Its displayed numerator modulo $8$ forces $g\equiv0\pmod8$ among even residues. Thus $g\ge8$, $d,e\equiv-1\pmod4$, and $4\mid n-1$.

### The overlap of positive shifts

Write $R=(a-1)(b-1)(c-1)=A-B+S-1$, $L=\mathrm{lcm}(a-1,b-1,c-1)$ and $w=R/L$. For the signed coordinates $(a,b,c,-d,-e)$ let $r$ count the entries congruent to $-1$ modulo 4. The fourth elementary symmetric sum is 1 by the signed equation. Modulo 8 it equals $(-1)^r(5-2r)$, since adding 4 to a coordinate changes that sum by 4 times the sum of four odd triples. Thus $r=2$ or $3$. The signed product equals $n\equiv1\pmod4$, so $r=2$. Both negatives $-d,-e$ are 1 modulo 4. Hence exactly two positive shifts have 2-adic valuation 1 and the third has valuation at least 2. This gives $v_2(w)=2$.

If $m$ divides two positive shifts, $A\equiv c$ and $B\equiv1+2c\pmod m$ after relabeling. Also $m\mid L\mid n-1$. Define
$$
P=4(2A-B+1)=32877g^3-22962g^2+3136g+16,\qquad
F=8(n-1)=3846609g^5-3048201g^4+653495g^3-53431g^2+1392g.
$$
Then $m\mid P,F$. The integer Bézout identity
$$UP+VF=2^4\cdot3^3\cdot1666729\cdot2236651$$
holds with coefficients
$$
\begin{aligned}
U={}&221609361437164935g^4-173715183736960086g^3
 +38473896617588464g^2-3263658701032482g+100653059283633,\\
V={}&-1894097106300555g^2+1306667654424393g-189245297914478 .
\end{aligned}
$$

An odd prime $p$ dividing all three positive shifts would give $A=1$, $B=3$, and $de=1$ in $\mathbb F_p$. The signed equation would then imply $d+e=2$, hence $d=e=1$ in that field. But $13(d-1)-9(e-1)=-8$. Thus no odd prime occurs in all three shifts, and any odd prime contributes to $w$ only its common power in one pair. Consequently
$$
w=4\cdot3^j H,\quad 0\le j\le3,\quad H\mid1666729\cdot2236651 .
$$
The two large constants are prime. For every indicated modulus dividing the odd part of $w$, the only common root of $P,F$ is listed below. Trial division and complete residue enumeration verify the entries.

| Modulus | 3 | 9 | 27 | 1666729 | 2236651 |
|---|---:|---:|---:|---:|---:|
| $g$ modulo that modulus | 2 | 8 | 17 | 868893 | 918968 |

Each of the 16 possible $w$ gives one class of $g$ modulo $2w$ by CRT with $g=0\pmod8$.

### Finite reduction

Set $J=n-1-117g^2R$ and $\kappa=J/L$. The positive required shifts give $L\mid n-1$, so $\kappa$ is an integer and $\kappa R=wJ$. Direct expansion gives
$$8J=g(-936Sg+103127g^2-54367g+1392).$$
We have $45g<S<54g$. The upper bound follows from $c<2d$ and the lower from $S^2\ge3B$ and $3B-(45g)^2=1173g^2/4-1176g-3>0$ for $g\ge8$. Using the upper bound in $8(J-R)$ yields a lower bound of $19706g^3-28314g^2-3744g-8>0$. Using the lower bound in $8(J-2R)$ yields an upper bound of $-4747g^3-2261g^2-8736g-16<0$. Hence $1<\lambda=\kappa/w<2$.

The equation $\kappa R=wJ$ yields the integer identity
$$
(117wg^2+\kappa)
\big[936wS-(103127w-32877\kappa)g-(26053\kappa-54367w)\big]
=Eg+F_0
$$
where $E=32877\kappa^2-653495\kappa w+162864w^2$ and $F_0=\kappa(53431w-26053\kappa)$. This identity follows by expansion. We have $E/w^2<4(32877)-653495+162864=-359123$ and $0<F_0/w^2<2(53431)$, so $Eg+F_0<0$. Writing $z$ for the negative of the square bracket gives a positive integer. Consequently
$$
gz<\frac{-E}{117w}<9000w .
$$
Indeed $-E/w^2=-32877\lambda^2+653495\lambda-162864$ is increasing on $(1,2)$ and equals $1012618<117\cdot9000$ at $2$.

Regrouping the identity as a quadratic equation in $\kappa$ gives
$$
(32877g-26053)\kappa^2 + [(-653495g+53431)w+z]\kappa
 +162864gw^2+117wg^2z=0 .
$$
Its discriminant must be a nonnegative square. For each of the 16 CRT classes, enumerate its positive $g<9000w$ and $1\le z\le\lfloor(9000w-1)/g\rfloor$. The complete search visits 71,999 values of $g$ counted by class and 1,093,956 discriminants. None is a square. This excludes the $(9,13,562)$ family at every parameter size. The finite bound follows from the hypotheses and uses no prior search in $d$.

The standard-library verifier additionally checks primality of the two support constants, completeness of the modular roots, the Bézout certificate, the polynomial remainder identity, and the reported counts.

[Run the exact verifier for this family](../checks/chebyshev_9_13_family.py).

## The 9,14,893 family

Write $d=9g-1$, $e=14g-1$, $n=Ade$, $S=a+b+c$ and $B=ab+ac+bc$. The shape equations give
$$
25A=112518g^3-52291g^2+3791g+25,\qquad
25B=20539g^2-7582g-25 .
$$
Let $R=(a-1)(b-1)(c-1)=A-B+S-1$, $L=\mathrm{lcm}(a-1,b-1,c-1)$, $w=R/L$, and $J=n-1-126g^2R$. Then $\kappa=J/L$ is an integer and $\kappa R=wJ$.

**Finite overlap support.** Every odd prime power dividing the gcd of two positive shifts divides $P=25(2A-B+1)$ and $n-1$. For primes above 5 it is coprime to $g$, since $P(0)=100$, and therefore divides $T=25(n-1)/g$. The certificate verifies an integer-polynomial identity $UP+VT=2^4\cdot3^2\cdot5^3\cdot47\cdot1237\cdot6451\cdot88861$. A prime dividing three positive shifts implies $de\equiv1$ from $L\mid n-1$ and $d+e\equiv2$ from $Bde-A(d+e)=1$, so $d\equiv e\equiv1$ modulo that prime. Since $14(d-1)-9(e-1)=-10$, triple overlap can only occur at 2 or 5. Consequently each listed prime above 5 occurs in $w$ at most once. If present, its required residue for $g$, in the order $47,1237,6451,88861$, is $33,797,3203,79288$. Direct polynomial evaluation over each field proves completeness of the list.

**Small primes.** With $x=a-1,y=b-1,z=c-1$, the quantity $2A-B+1=xy+xz+yz+2xyz$ is divisible by $w$, since $w$ divides each pair product. Also $w\mid L^2\mid(n-1)^2$, and the absence of a triple at 3 improves $v_3(w)\le v_3(n-1)$. Each positive shift is even, so $v_2(w)\ge2$. To bound the exponents at $p=2,3,5$, use $m=16,27,25$, respectively. Enumerate $g$ modulo $m\gcd(m,25)$, imposing evenness for $p=2$, $p\nmid Ade$, integrality at $p$ of $A,B,(A-1)/g$, $n\equiv1\pmod4$ or $n\equiv1\pmod3$ when applicable, and the necessary congruences $\gcd(m,9g)\mid eA+1$, $\gcd(m,14g)\mid dA+1$. Integrality of $(A-1)/g$ follows from $g\mid n-1$ and $de\equiv1\pmod g$. The preceding valuation bounds give the following allowed pairs of valuations and residues. Each line includes all possibilities; some residue classes can have more than one possible exponent.

| Prime | Exponent in $w$ | Allowed $g$ |
|---|---|---|
| 2 | 2 | $0\pmod2$ |
| 2 | 3 | $2\pmod4$ |
| 3 | 0 | $0,6,7\pmod9$ |
| 3 | 1 or 2 | $7\pmod9$ |
| 5 | 0 | $13,38,63,113\pmod{125}$ |
| 5 | 1 | $113\pmod{125}$ |

In particular $g$ is even and $g\equiv13\pmod{25}$, so $g\ge38$. This deals with all prime sizes without any preliminary search.

**Archimedean bounds.** We have $49g<S<54g$. The upper bound follows from $c<2d$. The lower bound follows from $S^2\ge3B$ and $25(3B-(49g)^2)=1592g^2-22746g-75>0$ for $g\ge38$. The identity $\lambda=\kappa/w=J/R$ and the linear dependence of $J,R$ on $S$ give $3/2<\lambda<11/6$. In detail, using $S<54g$ gives
$$
25(2J-3R)>42004g^3-60478g^2-31737g-75>0.
$$
Using $S>49g$ gives
$$
25(11R-6J)>4524g^3+35774g^2+119282g+275>0.
$$
Their positivity follows by substituting $g=38+t$, $t\ge0$.

**Integer remainder.** Set
$$
Q=126wg^2+\kappa,\quad C_3=359879w-112518\kappa,\quad C_2=-139484w+72830\kappa,
$$
$$
E=112518\kappa^2-1792877\kappa w+405216w^2,\qquad
F=\kappa(136334w-72830\kappa).
$$
Expanding $\kappa R=wJ$ gives $Q(3150wS-C_3g-C_2)=Eg+F$. For $3/2<\lambda<11/6$ we have $E<0$, $F>0$ and $E+F<0$. Thus $z=C_3g+C_2-3150wS$ is a positive integer, and $gz<-E/(126w)$. The quadratic $(-112518\lambda^2+1792877\lambda-405216)/126$ is increasing on the interval and takes the value $7510619/378<20000$ at $11/6$. This yields $0<gz<20000w$.

The resulting quadratic in $\kappa$ has coefficients
$$
112518g-72830,\qquad (-1792877g+136334)w+z,\qquad 405216gw^2+126wg^2z .
$$
The necessary overlap data generate 800 CRT progressions for $g$, counting classes with their value of $w$. Starting at $g\ge38$, the product bound leaves 153,593 parameter values with overlap class and 2,776,728 discriminants. Exact integer square root finds zero squares. This excludes the family for every even $g$.

[Run the exact verifier for this family](../checks/chebyshev_9_14_family.py).
