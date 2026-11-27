# Adversarial audit of the 137-line reduction

This audit treats the result as a reduction, not as a solution of Erdős 723.

* **Exact scope.** The theorem assumes the existence of 137 distinct
  13-subsets on the same 157 points, with pairwise intersection exactly one.
  It neither constructs that family nor rules it out.
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
  by the norm argument, because its edge span has codimension one in the
  residual space.  The note explicitly leaves this case open.  A bipartite
  root on 21 vertices does fill the residual space and is excluded by
  `(a-b)^2=21`.
* **Half-integral coordinates.** In 20 dimensions the parity argument that
  worked in odd residual dimension no longer excludes strict half-integers.
  Completing the square gives `||z||^2=5`, and an exhaustive hand
  classification of integer vectors of norm five gives precisely the listed
  deficit-five and deficit-seven patterns.  The disconnected `-3/2` pattern
  is removed separately.

No step in this audit turns the conditional 137-line result into an existence
or nonexistence proof for a plane of order twelve.
