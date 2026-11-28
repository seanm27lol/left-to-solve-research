# The residual obstruction at 137 lines in order twelve

**Research by Sean Mahdavian (@seanm27lol) with OpenAI Codex assistance.**

This note continues the independently audited completion theorems for 138 and
139 partial lines.  It does not construct an order-twelve plane and does not
prove that none exists.

## Result

Let `S` be a family of 137 distinct 13-subsets of a fixed 157-point set, with
each two members meeting in exactly one point.  If no point has deficit one,
then the graph induced by the deficit-two points is connected.  Subject to the
published classification of connected graphs with least eigenvalue at least
minus two, it is the ordinary line graph of a connected simple graph `H`.
Moreover,

* `H` has at least 20 vertices;
* in the nonbipartite case `H` has exactly 20 vertices;
* in the bipartite case `H` has 20 or 21 vertices, and the 21-vertex case is
  impossible.

The apparent half-integral exceptions in the nonbipartite case cannot occur.
Neither the unbalanced nor the balanced 20-vertex bipartite cases can obstruct
completion.  Consequently every 137-line seed extends to a projective plane
of order twelve.  This is a completion theorem: it does not construct the
required 137-line seed and therefore does not settle existence of the plane.

## Deficits and the exact finite certificate

Write `r_x` for the number of old lines through a point and
`t_x = 13-r_x`.  Put `m=n_2`, where `n_t` is the number of points of deficit
`t`.  The standard pencil and residual-Gram calculations give

\[
 \sum_x t_x=260,\qquad \sum_x t_x(t_x-2)=120,
\]

and a point of deficit `a` has `12a` gap neighbors satisfying

\[
 \sum_{y\in N(x)}(t_y-2)=a(8-a).
\]

Thus every positive deficit is at most eight.  Let `E` be the number of gap
edges with one deficit-two and one heavier endpoint.  The sum of the light
vectors has squared norm `26m-E`.

The verifier enumerates all 127 deficit histograms, all locally possible
neighborhood profiles, and the equality of every cross-type edge count.  Of
101 locally consistent histograms, 72 give the required lower bound directly.
For each of the other 29, the file contains an exact rational dual vector.  It
checks, using `Fraction` arithmetic, that every feasible mixture has

\[
 E > \frac{494m-4m^2}{19},\qquad
 \frac{4m^2}{26m-E}>19.
\]

No numerical optimizer is trusted by the certificate.  The dual vectors were
discovered computationally, then written as small rational numbers and
verified against every column of the finite linear system.

For connectivity, suppose a smallest light component has `n` vertices.  If a
heavy point `y` has `T_y` light neighbors, let `c_y` be the number in this
component.  Cross-component light pairs are collinear and have four common
gap neighbors, all heavy.  Therefore

\[
 \sum_y(t_y-2)c_y=12n,\qquad
 \sum_yc_y(T_y-c_y)=4n(m-n).
\]

Using the largest locally allowed `T_y` gives an exact integer upper bound for
the left side after adding an arbitrary multiple of the first identity.  The
verifier checks 3,502 component sizes and finds a minimum contradiction slack
of 284.

Run:

```sh
python3 notes/erdos-723-137/verify_137_profiles.py
```

## Root graph and coordinates

The light Gram matrix is `2I + Adj(G)`, so its least eigenvalue is at least
minus two.  The light graph is connected, has more than 36 vertices, and has
minimum degree greater than four.  The
[Cameron--Goethals--Seidel--Shult classification](https://doi.org/10.1016/0021-8693(76)90162-9)
makes it a generalized line graph.  A cocktail-party
attachment would contain two nonadjacent vertices with identical open
neighborhoods.  They would have more than four common light neighbors, while
the pencil count permits exactly four common gap neighbors.  Hence `G=L(H)`
for a connected simple root graph `H`.

If the degrees of `H` are `k_i`, then

\[
 \sum_i k_i=2m,\qquad \sum_i k_i^2=26m-E.
\]

Cauchy--Schwarz and the certified strict inequality give `|V(H)|>19`.  The
unsigned edge vectors span `h` dimensions when `H` is nonbipartite and `h-1`
when it is bipartite, inside the 20-dimensional residual space.  This gives
the alternatives stated above.  For a 21-vertex bipartite root with part sizes
`a,b`, the edge vectors fill the residual space.  The vector having inner
product two with every edge has squared norm `4ab/21`; it would have to equal
the residual vector of squared norm 20.  This requires `(a-b)^2=21`, which is
impossible.

For a nonbipartite 20-vertex root, connectedness and an odd cycle imply that a
point vector `w` is either integral or strictly half-integral.  The residual
vector is the all-ones vector and

\[
 \sum_iw_i=\lVert w\rVert^2=t_x.
\]

Integral coordinates are binary because every integer `u` satisfies
`u(u-1)>=0`.  In the half-integral case write `w=z+(1/2)1`.  The displayed
identity gives `||z||^2=5`.  Since deficits are at most eight, the only
connected possibilities are:

* deficit five: five coordinates `-1/2` and fifteen coordinates `1/2`;
* deficit seven: four coordinates `-1/2`, one coordinate `3/2`, and fifteen
  coordinates `1/2`.

The other norm-five pattern for deficit seven contains a coordinate `-3/2`;
no root edge can meet that coordinate while keeping every edge sum in
`{0,1}`, contradicting connectedness.

The two displayed patterns are also impossible.  The vector sum on every old
line equals the all-ones vector, so every old line contains an even number of
strictly half-integral point vectors.  A deficit-five point lies on eight old
lines.  Those lines require eight distinct additional half-integral points,
whereas

\[
 15n_5+35n_7\leq\sum_x t_x(t_x-2)=120
\]

allows at most eight points of deficits five and seven in total.  If there is
no half-integral deficit-five point, a half-integral deficit-seven point and
its six old lines require at least seven such points, while `35n_7<=120`
gives `n_7<=3`.  Thus every point vector is integral, hence binary, in the
nonbipartite case.

## The unbalanced bipartite roots

Let a bipartite root have parts of sizes `a,b`, with `a+b=20`, and put
`d=a-b`.  Write `u` for the vector which is one on the first part and minus
one on the second.  The edge span is `u^perp`.  The projection and norm of the
residual sum vector permit a choice of the last coordinate for which that sum
vector is again the all-ones vector.

Every point vector then has the form

\[
 w=z+\alpha u,\qquad z\in\mathbb Z^{20}.
\]

If `d` is nonzero and `alpha=p/q` is reduced modulo the integers, the integral
sum and norm of `w` imply

\[
 q\mid d,\qquad q\mid20.
\]

Indeed `d alpha` is integral, and reducing
`q^2||w||^2=sum_i(qz_i+/-p)^2` modulo `q` gives `q|20`.  A denominator two is
excluded by the old-line parity argument above.  A denominator four would
make the twenty coordinates of `4w` odd, so their squared sum is `4 mod 8`,
whereas `16||w||^2` is zero modulo eight.

The only remaining nonintegral denominators are five or ten.  They force
`|d|=10`, so the root parts have sizes five and fifteen and its number `m` of
edges is at most 75.  The two deficit identities then leave only

\[
 (n_2,n_3,n_5)=(75,35,1),\qquad (n_2,n_3)=(70,40).
\]

For `m=70`, every light has twelve heavy gap neighbors, so the line graph is
12-regular.  Every root edge therefore has endpoint-degree sum 14.  A
connected bipartite root is semiregular, but 70 is not divisible by the
15-vertex part.  For `m=75`, the root must be `K_{5,15}`, whose line graph is
18-regular; the local deficit equation instead gives light degrees 12 or 14.
Both cases are impossible.

Therefore every unbalanced bipartite root either has integral point vectors,
which are binary, or is impossible.  Binary coordinates supply twenty new
lines exactly as in the 138- and 139-line arguments.

## The balanced bipartite root

It remains to treat a connected bipartite root with parts of size ten and
ten.  Put

\[
 u=(1^{10},-1^{10}),\qquad \lVert u\rVert^2=20.
\]

The edge vectors span `u^perp`.  Every point vector can be written

\[
 w=z+\alpha u,\qquad z\in\mathbb Z^{20}.
\]

Set `A=z dot u` and replace `z` by `z+ku`, and `alpha` by `alpha-k`, so that
`|A|<=10`.  Also put

\[
 B=\lVert z\rVert^2-\sum_i z_i=\sum_i z_i(z_i-1).
\]

The residual sum vector is the all-ones vector, so
`sum w_i=||w||^2=t`.  Since `sum u_i=0`, this gives

\[
 20\alpha^2+2A\alpha+B=0.
\]

The invariant signed scalar

\[
 a=w\mathbin{\cdot}u=A+20\alpha
\]

therefore satisfies

\[
 a^2=A^2-20B. \tag{1}
\]

The root has minimum degree at least four.  Indeed, a light point has 24 gap
neighbors and weighted heavy excess 12, so it has at least twelve light gap
neighbors.  For a root edge `ij`, this says
`deg_H(i)+deg_H(j)-2>=12`.  Each root degree is at most ten in a simple
`10+10` bipartite graph; hence both endpoints of every root edge have degree
at least four, and connectedness covers every root vertex.

Here `B` is a nonnegative even integer.  Equation (1), together with
`|A|<=10`, leaves only `B=0,2,4`.  Before restricting (1) to squares, its only
nonsquare positive values are

\[
 20,\quad24,\quad41,\quad60. \tag{2}
\]

All nonzero values `A^2-20B` have one common squarefree kernel.  Indeed, the
inner-product calculation below says that the product of the signed square
roots belonging to any two points is an integer.  The residual Gram matrix
has rank `157-137=20`; its frame identity `G^2=12G+tt^T`, projected to the
`u` direction, gives

\[
 \sum_x (A_x^2-20B_x)=240. \tag{3}
\]

Thus the kernel `41` is impossible.  The other nonsquare cases in (2) consist
respectively of twelve, ten, or four equal-magnitude nonzero scalar
coordinates.  The exact coordinate enumeration, together with minimum root
degree four, places the `20` and `24` cases at deficit six, and the `60` case
at deficit eight.  Their old-line degrees are therefore seven, seven, and
five.  The scalar sum on every old line is zero.  Globally there are equally
many signs of either kind, but a point's old lines are disjoint away from the
point and each needs an opposite sign.  This would require, respectively,
seven among only six, seven among only five, or five among only two available
opposite-sign points.  All nonsquare kernels are excluded.

We may consequently take the signed quantity `a` in (1) to be an integer.
Enumerating the coordinate counts in the two ten-element parts gives the
following complete algebraic list for deficits at most eight (some listed
patterns are harmless overapproximations of the root-edge restrictions):

* `B=0`: `z` is binary, `A` has the parity of `t`, `|A|<=t`, and `|a|=|A|`;
* `B=2`: `t` is five or seven, `|A|=7`, and `|a|=3`;
* `B=4`: `t` is five or seven, `|A|=9`, and `|a|=1`.

The verifier enumerates these coordinate counts rather than assuming the
list.

For two point vectors, direct expansion gives

\[
 w_x\mathbin{\cdot}w_y
 =z_x\mathbin{\cdot}z_y+
   \frac{a_xa_y-A_xA_y}{20}.
\]

All entries of the residual Gram matrix are integers.  Hence

\[
 a_xa_y\equiv A_xA_y\pmod {20} \tag{4}
\]

for every pair, including a point paired with itself.  Equation (3) now reads
`sum a_x^2=240`.

Not every `A_x` is divisible by five: otherwise (4) would make every `a_x`
divisible by five, contradicting (3).  Choose an `A_x` which is a unit modulo
five.  Equation (4) then fixes one common sign modulo five for every point.
Modulo four the same argument applies if some `A_x` is odd; if every `A_x`
is even, the displayed list gives `a_x` congruent to `A_x` modulo four
directly.  The Chinese remainder theorem therefore supplies one global
multiplier

\[
 r\in\{1,9,11,19\},\qquad a_x\equiv rA_x\pmod {20} \tag{5}
\]

for every point.  An independent exact compatibility-graph enumeration in
the verifier finds precisely the same four maximal classes.

If `r=1`, then `(a-A)/20=alpha` is integral, so every `w` is integral.  If
`r=19`, reflect every vector across `u^perp`.  This fixes all edge vectors and
all inner products and replaces `a` by `-a`; equation (5) again makes every
vector integral.  Reflection interchanges the cases `r=9` and `r=11`, so it
remains to consider `r=11`.

When `r=11` and `A` is even, (5) again makes the vector integral.  Every
nonintegral vector has odd `A`; the exact list above shows that it is strictly
half-integral and has deficit five or seven.  The half-integral classification
already used in the nonbipartite case applies verbatim: the only connected
patterns are five coordinates `-1/2` at deficit five, or four coordinates
`-1/2` and one coordinate `3/2` at deficit seven, with all remaining
coordinates `1/2`.

Every old line has integral vector sum, so it contains an even number of
strictly half-integral points.  A deficit-five point lies on eight disjoint
old lines and would require eight further half-integral points, but
`n_5+n_7<=8`.  Once deficit five is excluded, a deficit-seven point and its
six lines would require seven such points, but `n_7<=3`.  Thus this last case
also becomes integral.

Finally, an integral vector satisfying `sum w_i=||w||^2` is binary.  The
twenty coordinate columns therefore give the twenty missing lines, completing
the 137-line seed.

