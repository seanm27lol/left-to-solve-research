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

If the remaining 20-vertex root is nonbipartite, the residual coordinates of
every point are binary except possibly for deficit-five and deficit-seven
points.  The exceptional coordinate patterns are completely determined:

* deficit five has five coordinates `-1/2` and fifteen coordinates `1/2`;
* deficit seven has four coordinates `-1/2`, one coordinate `3/2`, and fifteen
  coordinates `1/2`.

Consequently every 137-line seed extends to a plane unless either the root is
bipartite on 20 vertices or at least one of these two half-integral patterns
occurs.  This is the precise new obstruction below the completed 138-line
case.

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
possibilities are the two patterns stated above.  The other norm-five pattern
for deficit seven contains a coordinate `-3/2`; no root edge can meet that
coordinate while keeping every edge sum in `{0,1}`, contradicting
connectedness.

Binary coordinates supply twenty new lines exactly as in the 138- and
139-line arguments.  The unresolved work is therefore concrete: eliminate
the 20-vertex bipartite root, and eliminate the two half-integral patterns in
the nonbipartite root.

