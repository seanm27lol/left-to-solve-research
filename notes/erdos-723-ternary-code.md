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

## Exact remaining obstruction

A full solution must now do at least one of the following:

1. eliminate the weight-24 minimum branch;
2. eliminate the five surviving weight-21 patterns; or
3. refute every one of the five weight-18 PBD/exact-cover cases (t=0,\ldots,4\).

The earlier 137-line completion theorem is independent: it proves that a
137-line seed would extend, while this note attacks what a full plane's
ternary dependency code would have to contain.
