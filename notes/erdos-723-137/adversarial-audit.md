# Adversarial audit of the 137-line completion theorem

This audit treats the result as a reduction, not as a solution of Erdős 723.

* **Exact scope.** The theorem assumes the existence of 137 distinct
  13-subsets on the same 157 points, with pairwise intersection exactly one.
  It proves that such a family extends to a full plane.  It neither constructs
  the family nor rules it out, so it does not settle Erdős 723 by itself.
* **Zero and deficit-one cases.** A point of deficit zero has zero residual
  vector and no gap neighbors.  A deficit-one point immediately supplies a
  new line and reduces to the independently audited 138-line completion
  theorem.  The finite certificate is used only after removing this case.
* **Profile enumeration.** A separate mixed-integer optimization recomputed
  the minimum light--heavy edge count for every locally consistent histogram.
  It found 94 feasible mixtures and the same strict effective-root bound in
  all of them.  The permanent verifier does not trust those floating-point
  answers.  Its 29 exact dual witnesses have denominators at most six, satisfy
  every dual inequality, and exceed the required rational threshold.
* **Connectivity.** The cut calculation was checked for every integer
  component size, including the endpoints `minDegree+1` and `floor(m/2)`.
  The multiplier range `-100..150` is only a finite list of certificates: for
  each cut, one member gives a strictly positive exact slack.  It is not an
  assumption on a prospective plane.
* **Graph classification.** The classification is applied only after
  connectedness, simplicity, the least-eigenvalue bound, and the more-than-36
  size condition are established.  The exclusion of a cocktail-party
  attachment uses open neighborhoods and the exact common-gap count four.
* **Dimension bookkeeping.** A bipartite root on 20 vertices is not excluded
  merely by the norm argument, because its edge span has codimension one in
  the residual space.  A bipartite root on 21 vertices does fill the residual
  space and is excluded by `(a-b)^2=21`.  For 20 vertices, the denominator
  argument removes every unequal pair of part sizes.  The balanced `10+10`
  case requires the separate scalar argument below.
* **Half-integral coordinates.** In 20 dimensions the parity argument from an
  odd number of coordinates does not by itself exclude strict half-integers.
  Completing the square gives `||z||^2=5`, and an exhaustive hand
  classification gives the two connected patterns in the note.  Old-line
  vector sums then force an even number of half-integral points on each old
  line.  The deficit identity bounds all possible supporting points and
  contradicts the pencil through either pattern.
* **Unbalanced bipartite arithmetic.** For `a!=b`, the fractional denominator
  divides both 20 and `a-b`.  Denominator four is excluded modulo eight and
  denominator two by the old-line argument.  Denominators five and ten force
  parts `5+15`; the two possible deficit profiles are checked directly from
  the two global identities, and their root degree sums are impossible.  The
  denominator argument deliberately does not cover `a=b=10`.
* **Balanced scalar normalization.** Replacing `z` by `z+ku` changes `A` by
  `20k` and leaves the vector `w` unchanged, so the normalization `|A|<=10`
  loses no cases.  The quantity `B=sum z_i(z_i-1)` is even and nonnegative;
  `A^2-20B>=0` therefore restricts it to `0,2,4`.  The exact verifier
  enumerates multiplicities of `-1,0,1,2` in both ten-element parts.  Its
  minimum-degree filter is only necessary, so using it cannot discard a
  genuine root.
* **Frame identity.** The equality `sum (A^2-20B)=240` uses that the residual
  Gram matrix has full residual rank `157-137=20`.  Without this rank fact,
  projecting the frame operator would not be justified.  The nonsquare
  kernels `5,6,15,41` are then exhausted exactly; no numerical square-root
  comparison is used.
* **Compatibility classes.** Pairwise integrality gives
  `a_x a_y = A_x A_y (mod 20)`.  The proof by signs modulo four and five is
  independent of the compatibility-graph computation.  The verifier's exact
  Bron--Kerbosch replay finds four maximal cliques, of sizes `15,15,17,17`,
  and checks that they are precisely the multipliers `1,9,11,19`.
* **Last half-integral branch.** Reflection is applied simultaneously to all
  point vectors and fixes the edge span, so it preserves every Gram entry.
  In the multiplier-eleven class the only nonintegral vectors are strictly
  half-integral at deficits five or seven.  The old-line parity argument is
  therefore the same argument already audited above, not an assumption that
  all fractional vectors have one common sign.

The result is a complete extension theorem for 137-line seeds.  It remains
conditional on such a seed and is not an existence or nonexistence proof for
a plane of order twelve.
