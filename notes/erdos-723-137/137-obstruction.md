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
The unbalanced 20-vertex bipartite cases cannot obstruct completion either.
Consequently every 137-line seed extends to a plane unless its light graph is
the line graph of a connected bipartite graph with parts of size ten and ten.
This balanced root is the precise remaining obstruction below the completed
138-line case.

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
lines exactly as in the 138- and 139-line arguments.  The sole unresolved
case is a connected bipartite root with parts of size ten and ten.  In that
balanced case the edge span has an orthogonal direction which is also
orthogonal to the all-ones vector, so the preceding denominator argument does
not control its scalar coordinates.

