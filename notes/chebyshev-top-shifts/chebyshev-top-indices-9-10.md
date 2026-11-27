# Further top-shift indices in the five-prime interval

With the hypotheses and definitions of the supplied top-shift overlap theorem, let \(K=(b-1)/g\), \(J=(c-1)/g\), where \(g=\gcd(b-1,c-1)\). Using the earlier classification for \(K\le8\) and the companion exclusion of its exceptional family, every candidate satisfies
\[
 K\ge11,\qquad \gcd(b-1,c-1)\le(b-1)/11 .
\]
This note proves the additional exclusions of \(K=9,10\). The same initial residue test also excludes \(K=12\). The case \(K=11\) and unbounded larger indices are left open.

## Top indices and the use of the full common shift

We use the supplied bounds \(K<J<3K/2\), \(\gcd(K,J)=1\), \((2K-J)g\ge1012\), and its formulas (2.6), (2.8) and (3.2). Write \(D=(J-K)^2\), \(W=2J-K\), and \(z_0\) for the top parameter. The function
\[
 U(g)=\frac{DKJ}{2W}
 +\frac{2KJ+D(2J^2-K^2)/(2W^2)}g+\frac{D}{Wg^2}
\]
is decreasing. Thus \(DJ^2/[4(3K-J)]< z_0 < U(g_0)\), where \(g_0=2\lceil506/(2K-J)\rceil\). The shifts give
\[
 K\mid z_0c^2+DJ,\qquad J\mid z_0b^2+DK .
\]
Also \(g\mid n-1\) and \(b,c\equiv1\pmod g\), so \(g\mid X-1\) for \(X=dea\). The exact top identity for \(X\) then gives an extra restriction without dividing a congruence,
\[
 D\mid z_0bc-KJ(K+J)-2K^2J^2g.
\]
To classify the index pairs, enumerate integer \(z_0\) in the displayed open interval, and all even classes \(g\bmod\operatorname{lcm}(2,KJ,D)\), using the three divisibility tests. The prime divisors of the period are at most 17 for the listed pairs, and \(b,c\) exceed 17 by the lower bound on \(g\), so classes with \(bc\) noncoprime to the period are impossible. The interval and the enumerated congruences are exact. The eligible \(J\) are 10, 11, 13 for \(K=9\); 11, 13 for \(K=10\); and 13, 17 for \(K=12\). The only survivors among all these indices have
\[
 (K,J,z_0)=(10,13,23),\quad g\ge146,\quad
 g\equiv30,66,300,966\pmod{1170}.
\]

## The remaining family of index ten

Here \(b=10g+1,c=13g+1\), and substitution in the top formulas gives
\[
 9X=2990g^3-33271g^2-2967g+9,\qquad
 9Z=529g^2-5934g+9,qquad Z=a(d+e)-de.
\]
Use the signed lower triple \((a,-d,-e)\) as in the companion note. Write \(S=a-d-e, R=(a-1)(d+1)(e+1)=X+Z+S-1\), \(L=\operatorname{lcm}(a-1,d+1,e+1)\), and \(w=R/L\). The three lower shifts divide \(n-1\).

For \(t=g/3\), which is an even integer in every surviving class, put
\[
\begin{aligned}
 P(t)&=2X+Z+1=17940t^3-66013t^2-3956t+4,\\
 F(t)&=(n-1)/t=10494900t^4-38308140t^3-3443859t^2-100342t-920 .
\end{aligned}
\]
Any pair gcd of the lower shifts divides \(P\) and \(tF\), as proved in the companion note. Its odd part is coprime to \(t\) since \(P(0)=4\), and hence divides \(F\). An integer Bézout identity is
\[
 UP+VF=16\cdot5\cdot193139\cdot1510363823 ,
\]
with
\[
\begin{aligned}
 U={}&-111293654758497900t^3+411000919835152140t^2
          +25049195928215469t+750637786674080,\\
 V={}&190245563689740t^2-708175480015043t-22102458180582 .
\end{aligned}
\]
All three odd factors are distinct primes. The monic polynomial gcds modulo these primes, in order, are \(t-2,t-62582,t-317669003\), verified by polynomial division. No odd prime can divide all three shifts. As in the companion proof, such a prime would force \(b\equiv c\equiv-1\), hence divide \(13(b+1)-10(c+1)=6\), whereas \(b,c\equiv1\pmod3\).

When \(4\mid t\), \(P\equiv4\pmod8\). When \(t\equiv2\pmod4\), \(P\equiv8\pmod{16}\). Every pair gcd of the three lower shifts therefore has 2-adic valuation at most three. The two smallest valuations of these even shifts each lie between one and three. We have proved
\[
 w=2^iH,\qquad 2\le i\le6,\qquad H\mid5\cdot193139\cdot1510363823,
\]
with one necessary residue \(g=3t\) modulo each prime dividing \(H\).

Define \(J_0=n-1-130g^2R\), and let \(h=J_0/L\), an integer. Then \(hR=wJ_0\), with
\[
\begin{aligned}
9R&=2990g^3-32742g^2-8901g+9S+9,\\
9J_0&=-1170Sg^2+9177g^3-101512g^2-2760g .
\end{aligned}
\]
As \(-11g<S<0\) and \(g\ge146\), the formulas give \(300g^3<R<333g^3<900g^3<J_0<2450g^3\). For the two lower bounds one may use \(2990/9-3638/146-1000/146^2>300\) and \((9177-101512/146-2760/146^2)/9>900\). Hence \(1<h/w<9\).

Set
\[
\begin{aligned}
 z&=1170wS+(2990h-9177w)g-32742h+101512w,\\
 E&=2990h^2+1147953hw-358800w^2,\\
 F_0&=-32742h^2+100342hw .
\end{aligned}
\]
Expansion of \(hR=wJ_0\) gives \((130wg^2+h)z=Eg+F_0\). Since \(1<h/w<9\), we have
\[
 790000<E/w^2<10250000,\qquad -2700000<F_0/w^2<904000 .
\]
Thus \(Eg+F_0>0\), and \(z\) is a positive integer with
\[
 gz<\frac{10250000+904000/146}{130}w<80000w .
\]
Rearrangement gives the necessary quadratic
\[
 (2990g-32742)h^2+[(1147953g+100342)w-z]h
        -358800gw^2-130wg^2z=0 .
\]
The finite calculation covers every compatible residue class of \(g\), including the overlap of 5 with the base period 1170. It tests \(146\le g<80000w\) and \(1\le z\le\lfloor(80000w-1)/g\rfloor\). Across 120 classes and 474,794 values of \(g\) counted with multiplicity, it tests 5,448,422 discriminants. None is a square. This eliminates the last index-ten family.

Run `python3 verify_top_indices_9_10.py` with `verify_top_exception.py` in the same directory. Both files use Python's standard library. The verifier checks the initial rational bounds and residue enumeration, the polynomial identities and prime support, and the full discriminant calculation.
