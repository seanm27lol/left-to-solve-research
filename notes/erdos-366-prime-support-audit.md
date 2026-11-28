# Adversarial audit of the cubefull prime-support lemma

**Research by Sean Mahdavian (`@seanm27lol`) with OpenAI Codex assistance.**

The proved statement is only the necessary condition
`omega(n(n+1)) >= 3` for a positive consecutive cubefull pair.  It neither
produces a pair nor proves that no pair exists.

* The case `n=1` is separated: `1` satisfies the fullness predicate
  vacuously, but `2` does not, because `2^3` does not divide `2`.
* For `n>1`, both coprime endpoints have nonempty disjoint prime support.  If
  their union has at most two elements, each endpoint is a power of exactly
  one prime.  Cubefullness makes both positive exponents at least three.
* Exactly one base is two.  When the upper endpoint is the power of two,
  reduction modulo eight is used only after its exponent is known to be at
  least three.  It forces the odd-base exponent to be odd.  The alternating
  quotient is then both odd and greater than one, although it divides a power
  of two.
* When the lower endpoint is the power of two, an odd exponent on the odd
  base gives an odd geometric quotient greater than one.  For an even
  exponent `2c`, the two factors around `q^c` are powers of two differing by
  two.  The only such positive pair is `2,4`; because the original exponent
  is at least three and even, `c>=2`, so `q^c=3` is impossible.
* The elementary proof does not invoke Mihăilescu's theorem.  Yao Xu's Lean
  formalization of that theorem is cited only as an independent mathematical
  cross-check and is not imported into the pinned project.
* The statement about the Mordell coordinate concerns the point constructed
  from a genuine candidate by R3.  It is not asserted for an arbitrary
  solution of the Mordell equation without the reduction's local hypotheses.

No bounded computation or unverified factor table enters the lemma.
