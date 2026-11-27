# Erdős 723: ternary dependency-code reduction for order 12

This note gives necessary conditions for a projective plane of order 12.
It does **not** construct such a plane or prove that none exists.  The
ternary-code and rank framework goes back to Hall--Wilkinson; the reductions
below specialize it to the exact order-12 target and were independently
audited.

Let (A) be the (157\times157) incidence matrix of a hypothetical plane,
with rows indexed by lines.  Then

\[
 AA^{\mathsf T}=12I+J,
 \qquad |\det A|=13\cdot 12^{78}.
\]

## Rank and minimum-distance trichotomy

Over \(\mathbf F_3\), the determinant valuation gives
\(\operatorname{rank} A\ge79\).  Row differences are orthogonal to every
row, giving the reverse bound.  Hence

\[
 \operatorname{rank}_{3}A=79,
 \qquad K:=\ker_{\mathbf F_3}(A^{\mathsf T})
 \text{ has dimension }78.
\]

The code (K) is self-orthogonal, so every weight is divisible by 3.
The usual signed-pair count gives (d(K)\ge18). The difference of two point
pencils is a word of weight 24, so

\[
 \boxed{d(K)\in\{18,21,24\}.}
\]

This is a trichotomy, not a proof that a weight-18 word exists.

## The weight-18 branch

If (x\in K) has weight (18), its signs split (9+9).  Equality in the
pair count forces each sign class to carry the unique (2-(9,3,1)) design,
namely \(\operatorname{AG}(2,3)\), and every opposite-sign pair lies alone on
its joining line.  Thus the support consists of two disjoint affine planes
of order (3).

For an outside point let (p\in\{0,1,2,3\}) be the number of internal affine
lines of either sign through it.  The two numbers agree.  If (N_p) counts
outside points of type (p), then for one integer (0\le t\le4),

\[
 \boxed{(N_0,N_1,N_2,N_3)=(31-t,96+3t,12-3t,t).}
\]

The (52) lines external to both affine subplanes and the (139) outside
points form a smaller exact design.  Its (52\times139) incidence matrix
(E) satisfies

\[
 EE^{\mathsf T}=12I_{52}+J_{52}.
\]

Equivalently, it is a pairwise-balanced design on (52) symbols with block
sizes (4,5,6,7), block counts (N_0,N_1,N_2,N_3), every symbol in (13)
blocks, and the sum of the corresponding (p)-values through each symbol
equal to (12).  This is a finite exact-cover target substantially smaller
than searching for all (157) lines directly.

For the integral lift (A^{\mathsf T}x=3z), the binary support of (z) is a
line-incidence codeword of weight (24) with intersection distribution

\[
 (n_0,n_2,n_4,n_6)=(31-t,96+3t,30-3t,t).
\]

It cannot be the symmetric difference of two lines, because the 18 selected
lines meet it in four points. Thus a weight-18 ternary dependency would
produce a concrete weight-24 binary hull word outside the line-difference
family. We avoid calling this simply "non-tame" without fixing that term's
precise convention.

## The weight-21 branch

Write the nonzero coefficients of (x\in K) as (a) plus signs and (b)
minus signs.  Counting about a supported line gives

\[
 a+2b\ge27,\qquad2a+b\ge27.
\]

Since (a,b) are multiples of (3), the only splits up to sign are
((6,15)) and ((9,12)).  Put (A^{\mathsf T}x=3z) and (s=a-b).  Then

\[
 \lVert z\rVert^2=28+s^2/9,
 \qquad \sum z_i=13s/3.
\]

The (6+15) split would give (\lVert z\rVert^2=37) and
\(|\sum z_i|=39), contradicting
\(\sum z_i^2\ge\sum|z_i|\ge|\sum z_i|\).  Therefore every weight-21 word
has split (9+12).  Orienting it with sum (-3) gives

\[
 \boxed{\lVert z\rVert^2=29,\quad\sum z_i=-13,\quad Az=4x-\mathbf1.}
\]

An exact integer dynamic program on the local types
((i,j)) (numbers of incident selected positive and negative lines) uses

\[
 \sum i=117,\quad\sum j=156,\quad
 \sum\binom i2=36,\quad\sum\binom j2=66,\quad\sum ij=108,
\]

together with (z=(i-j)/3), (\sum z=-13), (\sum z^2=29), and the
13-point lower bound for an odd set.  It leaves exactly six nonzero
multiplicity patterns:

Run the standard-library certificate with
`python3 scripts/verify_erdos723_ternary_code.py`.

| nonzero values of (z) | odd support |
|---|---:|
| \(-1^{19},1^2,2^2\) | 21 |
| \(-1^{20},1^5,2\) | 25 |
| \(-1^{21},1^8\) | 29 |
| \(-2,-1^{16},1,2^2\) | 17 |
| \(-2,-1^{17},1^4,2\) | 21 |
| \(-2^2,-1^{12},3\) | 13 |

The final row is impossible.  Its 13-point odd set must be a line.  The pair
budgets force one type \((9,0)\), twelve types \((0,3)\), two types
\((0,6)\), and 108 balanced types \((1,1)\).  The twelve \((0,3)\) points
on that line demand 36 incidences from the twelve selected negative lines,
but each such line can meet it only once.  Hence only the first five patterns
remain.

The pattern with odd support 17 is also impossible, by a geometric argument
independent of the local-type program. In fact no 17-point set (T) in an
order-12 plane can meet every line oddly. A line meeting (T) in
(k=7,9,11) points contains a point outside (T); the other twelve lines
through that point force at least (k+12>17) points. A 13-secant would make
the symmetric difference with (T) a four-point even set, also impossible
by taking the pencil through one of those four points. Thus intersections
have sizes only 1, 3, and 5. If (n_j) counts the (j)-secants, the design
equations give

\[
(n_1,n_3,n_5)=(135,12,10).
\]

Two 5-secants cannot meet outside (T), since their intersection pencil
would force at least (5+5+11=21) incidences. For (P\in T), let (h_P)
be the number of 5-secants through (P). Then

\[
\sum_P h_P=50,qquad
\sum_P\binom{h_P}{2}=45,qquad
\sum_P h_P^2=140.
\]

Cauchy's inequality gives (2500\le17\cdot140=2380), a contradiction.
Consequently only four weight-21 multiplicity patterns remain.

## The weight-24 minimum branch

Assume now that (d(K)=24). Fix two lines (L,M), their intersection
(P), and the canonical word (mathbf1_L-mathbf1_M). Shortening the
78-dimensional ternary hull on its 24-point support has dimension 55. Every
shortened word also vanishes at (P), so puncturing (L\cup M) gives a
self-orthogonal ternary code

\[
B=[132,55,\ge24]_3.
\]

The 132 coordinates split into the eleven other (P)-lines, with 12 points
per group. The 144 lines not through (P) become 11-point transversals, one
point from every group. Thus they form a transversal design
(mathrm{TD}(11,12)), equivalently nine mutually orthogonal Latin squares
of order 12. The group-sum equations are already generated by the transversal
blocks over (mathbf F_3): summing the twelve blocks through a point of a
group gives the sum of the other ten groups. Therefore the 144-by-132 block
matrix has ternary rank exactly 77 and (B) is its dual.

The canonical differences of the eleven groups form a 10-dimensional
subcode (W\subset B). Its weight-24 words are exactly the 110 ordered
group differences. If (B=W\oplus U), then (U) has dimension 45, is
self-orthogonal, and contains no pencil-difference word. The ternary Griesmer
bound rules out distance 61 for a length-132, dimension-45 code:

\[
61+21+7+3+41=133>132.
\]

Hence, for every pair (L,M), the d=24 branch forces a noncanonical
dependency supported away from (L\cup M), of one of the weights

\[
24,27,30,\ldots,60.
\]

This is a residual finite target, not a contradiction: rule out a
(mathrm{TD}(11,12)) with ternary block rank 77 and dual distance 24, or
force the noncanonical word below weight 24.

There is a second restriction on any noncanonical weight-24 word which does
not use the transversal-design decomposition. Write
$A^{\mathsf T}x=3z$. Up to replacing $x$ by $-x$, its sign split is one of
$(3,21),(6,18),(9,15),(12,12)$. The first two are impossible because the
identities

\[
 \|z\|^2=32+\frac{(a-b)^2}{9},\qquad
 \sum z_i=\frac{13(a-b)}3
\]

would respectively give $(\|z\|^2,|\sum z_i|)=(68,78)$ and $(48,52)$,
contrary to $\sum z_i^2\ge|\sum z_i|$.

If every coordinate of $z$ were even, the $(9,15)$ split would give
$z=2y$ with $\|y\|^2=9$ and $|\sum y_i|=13$, again impossible. In the
$(12,12)$ split one instead has

\[
 z=2y,\qquad \|y\|^2=8,\qquad \sum y_i=0,\qquad Ay=2x.
\]

If some $y_P=\pm1$, at most seven other points lie in the support of $y$.
One of the thirteen lines through $P$ is therefore tangent to that support,
and its line sum is $\pm1$, contradicting $Ay\in\{0,\pm2\}^{157}$. Hence
all nonzero coordinates of $y$ have absolute value at least two. Norm eight
and zero sum force $y=\pm2(e_P-e_Q)$, whence
$z=\pm4(e_P-e_Q)$. Since
$A^{\mathsf T}A(e_P-e_Q)=12(e_P-e_Q)=A^{\mathsf T}x$ and $A$ is
nonsingular over the rationals, $x$ is the corresponding point-pencil
difference.

Consequently every **noncanonical** weight-24 dependency has a nonzero
binary hull reduction $z\bmod2$. Its weight is divisible by four, is at
least the standard even-set lower bound 14, and is at most $\|z\|^2\le36$.
Thus its binary support has one of the six sizes

\[
 \boxed{16,20,24,28,32,36}.
\]

This is another finite residual target. It is recorded as an independently
derived restriction in the Hall--Wilkinson framework, not as a claim of
literature priority.

## Exact remaining obstruction

A full solution must now do at least one of the following:

1. eliminate the weight-24 minimum branch;
2. eliminate the four surviving weight-21 patterns; or
3. refute every one of the five weight-18 PBD/exact-cover cases (t=0,\ldots,4\).

The earlier 137-line completion theorem is independent: it proves that a
137-line seed would extend, while this note attacks what a full plane's
ternary dependency code would have to contain.
