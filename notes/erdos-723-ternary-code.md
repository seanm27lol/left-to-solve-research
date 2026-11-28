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

### A 105-point exact-cover reduction at weight 18

The weight-18 branch has a second exact finite formulation which retains the
geometry of the two affine planes. Label the nine positive selected lines by
the points of \(\operatorname{AG}(2,3)\). Their twelve internal triple points
are the twelve affine lines; call this set \(P\). Do the same for the nine
negative selected lines, obtaining \(N\). Finally, every positive/negative
pair meets at a distinct balanced point; call the resulting \(9\times9\) grid
\(G\). The congruence \(i-j\equiv0\pmod3\) at every point and the equality
cases in the pair count show that these

\[
 |P|+|N|+|G|=12+12+81=105
\]

points are distinct.

Consider one of the other 139 lines. If it contains \(a\) points of \(P\),
their corresponding affine lines must be mutually parallel: two nonparallel
affine lines share a selected positive line, so their two triple points already
lie on that selected line. Hence \(0\le a\le3\). The same argument on the
negative side, together with the fact that the line meets each of the nine
selected lines once, shows that it contains exactly \(a\) points of \(N\).
The remaining intersections form a perfect matching between the \(9-3a\)
unused positive and negative selected lines. Its trace on the 105 known points
therefore has size \(9-a\).

Up to the fixed affine-plane labels, all possible traces can be enumerated:

\[
\begin{array}{c|c|c}
a&\text{choices}&\text{count}\\ \hline
0&\text{a permutation of the }9\text{ grid rows}&9!=362880\\
1&12\cdot12\text{ choices of }P,N\text{ points, then }6!&103680\\
2&(4\binom32)^2\text{ choices, then }3!&864\\
3&4^2\text{ parallel-class choices}&16
\end{array}
\]

Thus there are exactly

\[
 \boxed{467440}
\]

candidate traces.

The eligible pairs among the known points are precisely:

* two \(P\)-points or two \(N\)-points from the same parallel class (24);
* a \(P\)-point and an \(N\)-point (144);
* a \(P\)-point and a grid point whose row is outside its affine triple
  (648), and symmetrically \(N\)-to-grid (648);
* two grid points in different rows and different columns (2592).

There are 4056 eligible pairs in total. Every one must occur in exactly one
selected trace. In addition, every \(P\)- or \(N\)-point occurs in ten traces,
every grid point in eleven, and the numbers of traces of the four types are

\[
 (M_0,M_1,M_2,M_3)=(31-t,96+3t,12-3t,t),\qquad0\le t\le4.
\]

The pair count closes exactly:

\[
 36M_0+28M_1+21M_2+15M_3=4056.
\]

Consequently, a weight-18 dependency forces an exact cover with 467440
explicit columns and 4165 exact constraints (4056 pair constraints, 105 degree
constraints, and four type counts). This is complementary to the 52-symbol
pairwise-balanced-design reduction: it retains all intersections already
determined by the two affine planes, while the 52-symbol formulation controls
the points outside their selected lines.

The standard-library verifier
`python3 scripts/verify_erdos723_weight18_traces.py` regenerates the affine
planes, all eligible pairs, and all 467440 columns. It also computes the
complete binary linear relaxation: the column span has rank 2642, and the
right-hand side lies in that span for every \(t=0,1,2,3,4\). Thus parity alone
cannot eliminate any case. An integer exact-cover obstruction, a stronger
modulus, or compatibility with the remaining 52 unknown points is essential.

This is a necessary-condition reduction, not a construction or a proof that
an order-12 plane does not exist. The affine-plane structure comes from the
Hall--Wilkinson ternary-code framework; this explicit trace formulation is
recorded as an independently derived specialization without a priority claim.

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

### Complete exclusion of weight 21

Restore the full line profiles. Since (Az=4x-\mathbf1), the sum of (z)
on a line is (3), (-5), or (-1), according as its coefficient in (x)
is (+1), (-1), or (0). There are respectively (9), (12), and
(136) lines of these classes.

For each multiplicity pattern, enumerate all profiles ((c_v)_{v\ne0})
with (sum_vc_v\le13) and (sum_vvc_v\in\{3,-5,-1\}). Point and
unique-pair counting require

\[
 \sum_Lc_v(L)=13n_v,\quad
 \sum_L\binom{c_v(L)}2=\binom{n_v}2,\quad
 \sum_Lc_v(L)c_w(L)=n_vn_w.
\]

For the patterns

\[
 -1^{19},1^2,2^2;\qquad -1^{20},1^5,2;\qquad
 -2,-1^{17},1^4,2,
\]

these exact systems have integer Farkas certificates. In the verifier's
constraint order (three line-class counts, incidences by sorted value,
equal-value pairs, then unequal-value pairs lexicographically), they are

\[
\begin{array}{c|c|c}
(-1^{19},1^2,2^2)&(4,0,4,-4,-4,-4,2,-4,4,3,2,4)&-68\\
(-1^{20},1^5,2)&(-3,45,45,-45,3,-45,18,-2,-45,12,27,45)&-92\\
(-2,-1^{17},1^4,2)&(21,-15,-15,-12,15,-21,-48,-48,-6,14,-48,0,48,48,6,12,48)&-276.
\end{array}
\]

Each certificate pairs nonnegatively with every admissible profile column
and negatively with the required right-hand side.

For the last pattern, (-1^{21},1^8), every positive selected line has
(z)-sum (3), so it contains at least three of the eight (+1)-points.
The nine positive lines use at least \(9\binom32=27\) of their
\(\binom82=28\) pairs. Pair uniqueness forces nine triples covering all but
one pair. At any of the six points outside the missing pair, all seven
incident pairs would be partitioned two at a time by the triples through
that point, impossible because seven is odd.

The standard-library verifier
`python3 scripts/verify_erdos723_weight21_profiles.py` checks the profile
enumeration and certificates. Hence

\[
 \boxed{\text{the ternary dependency code has no word of weight }21.}
\]

This closes the weight-21 branch only; it does not construct or rule out a
projective plane of order (12).

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

### Exact line-profile reduction at weight 24

The noncanonical weight-24 branch admits a finite reduction parallel to the
weight-21 endgame.  Let (x) have (a) coefficients (+1) and (b)
coefficients (-1), put (s=a-b), and write
(A^{\mathsf T}x=3z).  From (AA^{\mathsf T}=12I+J),

\[
 \|z\|^2=32+\frac{s^2}{9},\qquad
 \sum z_i=\frac{13s}{3},\qquad
 Az=4x+\frac{s}{3}\mathbf1.
\]

The only sign splits not already excluded are ((9,15)) and ((12,12)).
Orienting the first with (s=-6), these identities give respectively

\[
 (\sum z_i,\|z\|^2)=(-26,36),\qquad (0,32).
\]

For a noncanonical word the binary vector (z\bmod2) is a nonzero hull
word.  Its weight is divisible by four, is at least 14, and is at most
(\|z\|^2).  Exact integer enumeration therefore leaves 12 possible
multiplicity patterns in the ((9,15)) split and 32 in the balanced split.

For each pattern enumerate every line profile ((c_v)_{v\ne0}), with at
most 13 nonzero entries, whose weighted sum is the required line sum.  Those
line sums and class sizes are

\[
\begin{array}{c|c}
(9,15)&2^9,(-6)^{15},(-2)^{133},\\
(12,12)&4^{12},(-4)^{12},0^{133}.
\end{array}
\]

As before, point and unique-pair counting impose

\[
 \sum_Lc_v(L)=13n_v,\quad
 \sum_L\binom{c_v(L)}2=\binom{n_v}2,\quad
 \sum_Lc_v(L)c_w(L)=n_vn_w.
\]

Exact integer Farkas certificates make 38 of the 44 systems infeasible.
One more pattern has a direct pencil contradiction.  For
(z=(-2)^2,(-1)^{24},2), every positive selected line must contain the
unique (+2) point and no other nonzero point.  That point lies on nine
positive and three negative selected lines.  The two (-2) points lie on six
negative selected lines each, and the 24 points of value (-1) lie on three
each.  These incidences already account for all

\[
 \binom32+2\binom62+24\binom32=\binom{15}2
\]

pairs of negative selected lines.  Hence a negative selected line avoiding
the (+2) point meets the nine positive lines at nine distinct zero-points,
leaving four places.  A sum of (-6) in those places requires both (-2)
points and two (-1) points.  At most one line can contain both (-2)
points, whereas twelve negative selected lines avoid the (+2) point.

Consequently every noncanonical weight-24 word has, up to reversing all
signs where applicable, one of only five point-value multisets:

\[
\boxed{
\begin{gathered}
 -1^{31},1^5;\\
 -1^{15},1^{13},2;\qquad -1^{16},1^{16};\\
 -2,-1^{12},1^{12},2;\qquad -2,-1^{13},1^{15}.
\end{gathered}}
\]

Run `python3 scripts/verify_erdos723_weight24_profiles.py` beside the checked
certificate asset.  The verifier uses only Python integers and the standard
library: it regenerates all 44 norm/parity patterns and every admissible line
profile, checks all 38 Farkas vectors column by column, and checks the pencil
argument's finite arithmetic.

This is a necessary-condition reduction, not a realization theorem.  It
does not close the weight-24 branch or decide whether a projective plane of
order 12 exists.  The coding framework is due to Hall--Wilkinson; this exact
profile reduction is recorded as an independently derived specialization,
without a literature-priority claim.

### Double-pencil reduction for the two-special-point pattern

The fourth surviving multiset admits a further geometric reduction which is
not present in the line-profile linear program.  Suppose

\[
 z=-2,-1^{12},1^{12},2,
\]

and call the points of value \(2,-2\) respectively \(Q_+,Q_-\). At \(Q_+\),
let \(i,j\) be the numbers of selected positive and negative lines. Then
\(i-j=6\). Every positive selected line through \(Q_+\) has remaining
\(z\)-sum \(2\), and hence contains at least two of the twelve \(+1\)-points.
If one of those lines also contained \(Q_-\), it would require at least four
\(+1\)-points. The pencil lines are otherwise disjoint, so

\[
 12\ge 2i+2\mathbf1_{Q_-\text{ lies on such a line}}.
\]

It follows that \(i=6,j=0\), that \(Q_-\) is on none of those six lines, and
that each of the six lines contains exactly two \(+1\)-points and no other
nonzero point. Reversing signs gives the dual assertion at \(Q_-\): it lies
on exactly six negative selected lines, each containing exactly two
\(-1\)-points and no other nonzero point. In particular, \(Q_+Q_-\) is
unselected and contains no other nonzero point.

Write \(A,N\) for those two six-line pencils and \(B,M\) for the remaining
six positive and six negative selected lines. A \(+1\)-point lies on one
line of \(A\), no line of \(N\), and, if \(b,m\) count its incident lines in
\(B,M\), satisfies \(b-m=2\). Put \(r=\sum m\) over the twelve
\(+1\)-points. Then \(\sum b=24+r\). The six lines of \(B\) have only
\(\binom62=15\) pairs, whereas convexity gives

\[
 \sum_{z(P)=1}\binom{b_P}{2}\ge 12+2r.
\]

Consequently \(r\in\{0,1\}\). Line sums, and then sign reversal, make the
entire selected part explicit:

* if \(r=0\), all \(+1\)-points have local type \((i,j)=(3,0)\), all
  \(-1\)-points have type \((0,3)\), every line of \(B\) contains four
  \(+1\)-points, and every line of \(M\) contains four \(-1\)-points;
* if \(r=1\), eleven points of each sign retain those types, while the two
  exceptional types are \((4,1)\) and \((1,4)\). One line of \(B\) has
  profile \(1^{-},5^{+}\), the other five have four \(+1\)-points; the
  negative statement is symmetric.

At every zero-point the selected incidences form a balanced block
\((S_+,S_-)\) with \(|S_+|=|S_-|\le6\). Pair uniqueness turns the remaining
problem into a literal balanced-clique exact cover. In the \(r=0\) case
the blocks must cover 15 unused same-sign pairs on each side and all 144
opposite-sign pairs, with

\[
 \sum |S_+|=\sum |S_-|=114.
\]

For \(r=1\), the exceptional nonzero points have already used three extra
same-sign pairs on each side and eight opposite-sign pairs in total.  The
corresponding budgets are 12, 12, and 136, with half-incidence sum 112.
Thus no unspecified incidence remains in the **selected-line intersection**
subproblem: after choosing the two degree-two marked bipartite graphs and
the permitted nonzero selected-line blocks above, one must exactly cover the
residual edges by balanced cliques of size at most six.  This exact cover is
only necessary; an abstract cover need not extend to all 157 points and
lines of a plane.

Thus this survivor is reduced to two finite exact-cover shapes.  More
geometrically, the twelve \(+1\)-points are the marked intersections of six
\(A\)-rays with the six unselected rays from \(Q_-\), with degree two on
both sides; the \(-1\)-points give the sign-reversed degree-two bipartite
graph.  A completion must realize one of these two marked double pencils
while decomposing every remaining pair of selected lines at zero-points.
This is strictly stronger than the aggregate line profiles, but it is not a
contradiction and does not close the weight-24 branch.

Run `python3 scripts/verify_erdos723_weight24_double_pencil.py` for the exact
finite arithmetic used in this reduction.

## Exact remaining obstruction

A full solution must now do at least one of the following:

1. eliminate the weight-24 minimum branch; or
2. refute every one of the five weight-18 PBD/exact-cover cases (t=0,\ldots,4\).

The earlier 137-line completion theorem is independent: it proves that a
137-line seed would extend, while this note attacks what a full plane's
ternary dependency code would have to contain.
