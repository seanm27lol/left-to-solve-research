# Elimination of the Chebyshev top-shift family (7,10,23)

This note continues the supplied top-shift overlap reduction. The starting parameterization and the residue classes are due to the supplied research. The argument here uses the three lower shifts to eliminate the exceptional family. It applies only to this family. The general interval problem still allows top index at least nine.

## Theorem

Let \(g\ge254\) satisfy \(g\equiv48,138,426,516\pmod{630}\), and put \(b=7g+1,\ c=10g+1\). There are no primes \(d<e<a<b<c<2d\) with
\[
 X=dea=(1610g^3-9409g^2-1167g+9)/9,\qquad
 Z=a(d+e)-de=(391g^2-2334g+9)/9
\]
and \(a-1,d+1,e+1\mid n-1\), where \(n=bcX\).

Together with the earlier classification of top indices at most eight, this gives \(\gcd(b-1,c-1)\le(b-1)/9\) throughout the remaining five-prime interval.

## 1. The three lower shifts

Write \(u_1=a,u_2=-d,u_3=-e\). Their elementary symmetric functions are \(S=a-d-e,-Z,X\). Define
\[
 R=(a-1)(d+1)(e+1)=X+Z+S-1,\quad
 L=\operatorname{lcm}(a-1,d+1,e+1),\quad w=R/L.
\]
Put \(t=g/3\), an even integer. The explicit family gives \(P(t)=2X+Z+1\), \(tF(t)=n-1\), where
\[
 P=9660t^3-18427t^2-1556t+4,\quad
 F=3042900t^4-5681340t^3-720099t^2-28618t-338.
\]
If a positive integer \(m\) divides two of the lower shifts, two of the \(u_i\) equal 1 modulo \(m\). Calling the remaining coordinate \(v\), we have \(X\equiv v\) and \(-Z\equiv1+2v\). Thus \(m\mid P(t)\), and \(m\mid n-1\) by hypothesis. For odd \(m\) this also gives \(m\mid F(t)\), since \(P(0)=4\) implies \(\gcd(m,t)=1\).

The integer Bézout identity
\[
 UP+VF=2\cdot23\cdot257\cdot29259726079
\]
holds with
\[
\begin{aligned}
U={}&-2769237917415900t^3+5354603308283040t^2+466269573740589t+19538197375049,\\
V={}&8791231483860t^2-17354576221277t-792176604159 .
\end{aligned}
\]
All three odd factors are distinct primes. The monic polynomial gcd of \(P,F\) over each residue field is respectively \(t+4,t+21,t+1421483446\). The verifier checks the identity, primality, and all three gcds.

No odd prime divides all three lower shifts. Indeed, if \(\ell\) did, \(X\equiv1,-Z\equiv3,bc\equiv1\pmod\ell\). The identity \(X(b+c)-Zbc=1\), verified by substitution of the family formulas, gives \(b+c\equiv-2\). Hence \((b+1)^2\equiv0\) and \(b\equiv c\equiv-1\). But \(10(b+1)-7(c+1)=6\), so \(\ell=3\), inconsistent with \(3\mid g\). For each odd prime dividing \(w\), its valuation in \(w\) is therefore the smaller of its two nonzero shift valuations. The Bézout identity bounds that valuation by one.

For the power of two, if \(4\mid g\) then \(4\mid t\) and \(P(t)\equiv4\pmod8\). In this case each pair gcd has valuation at most two. If \(g\equiv2\pmod4\), the formulas give \(X\equiv1+g-g^2\) and \(bc\equiv1+g\pmod8\), so \(n-1\equiv2g\equiv4\pmod8\). Here every individual shift has valuation at most two. In either case the two smallest valuations of the three even shifts are between one and two. Consequently
\[
 w=2^iH,\quad i\in\{2,3,4\},\qquad H\mid23\cdot257\cdot29259726079 .
\]
For each prime \(\ell\mid H\), the polynomial gcd above gives the single allowed residue \(g\equiv3t\pmod\ell\).

## 2. An integer remainder

Set \(J=n-1-70g^2R\). The lower required shifts imply \(L\mid n-1\), so \(\kappa=J/L\) is integral and \(\kappa R=wJ\). Direct expansions give
\[
\begin{aligned}
9R&=1610g^3-9018g^2-3501g+9S+9,\\
9J&=-630Sg^2+5037g^3-29248g^2-1014g.
\end{aligned}
\]
The ordering gives \(-8g<S<0\) since \(S>-d>-b\) and \(d+e>c>a\). For \(g\ge254\) the expansions yield
\[
174g^3<R<179g^3<J<1120g^3 .
\]
For example, the lower bound on \(R/g^3\) follows from \(1610/9-1002/254-397/254^2>174\), and the lower bound on \(J/g^3\) follows from \((5037-29248/254-1014/254^2)/9>179\). Hence \(1<\lambda=\kappa/w=J/R<7\).

Define integers
\[
\begin{aligned}
z&=630wS+(1610\kappa-5037w)g-9018\kappa+29248w,\\
E&=1610\kappa^2+240033\kappa w-70980w^2,\\
F_0&=-9018\kappa^2+28618\kappa w .
\end{aligned}
\]
Expanding \(\kappa R=wJ\) gives
\[
 (70wg^2+\kappa)z=Eg+F_0 .
\]
Since \(1<\lambda<7\), we have \(170000<E/w^2<1690000\) and \(-442000<F_0/w^2<201000\). Thus \(Eg+F_0>0\) and
\[
 0<gz< \frac{1690000+201000/254}{70}w <25000w.
\]
This bounds \(g\) because \(z\) is a positive integer, even when the largest allowed prime divides \(H\).

## 3. The finite certificate

Rearranging the integer remainder gives a quadratic with integer root \(\kappa\),
\[
 (1610g-9018)\kappa^2+[(240033g+28618)w-z]\kappa
       -70980gw^2-70wg^2z=0.
\]
Its discriminant must be a nonnegative perfect square. For every divisor \(H\) above and \(2^i=4,8,16\), the certificate combines each of the four initial classes modulo 630 with the one residue modulo each prime dividing \(H\). It checks exactly \(254\le g<25000w\) in each resulting progression and all \(1\le z\le\lfloor(25000w-1)/g\rfloor\). The search bound follows from the inequalities in Section 2.

Run `python3 verify_top_exception.py`. The output is

```
96 classes, 35540 parameters with multiplicity, 308878 discriminants, zero squares.
```

Thus no \(\kappa\) exists and the exceptional family is empty. The calculation uses only integer arithmetic from Python's standard library.
