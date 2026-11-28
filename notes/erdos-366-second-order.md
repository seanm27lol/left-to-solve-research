# Erdős 366: second-order congruences in the three-support residual families

This note sharpens the two power-of-two residual families in the exact
three-prime-support reduction. It is cutoff-free, but it does **not** prove
that either family is empty and does not settle
`Erdos366.erdos_366.variants.weaker`.

The first-order congruences and exact order restrictions are established in
[`erdos-366-three-support.md`](erdos-366-three-support.md). The second-order
expansions below were independently derived under Sean Mahdavian's
coordination with OpenAI Codex assistance; no literature-priority claim is
made.

## The Mersenne-type family

Assume

\[
 2^A-1=q^b r^c,
\]

where $A$ is an odd prime, $q,r$ are distinct odd primes, and $b,c\ge3$.
The primitive orders are $A$, so write

\[
 q=1+2Au,\qquad r=1+2Av,\qquad
 T=\frac{2^{A-1}-1}{A}.
\]

Fermat's theorem makes $T$ an integer. Define

\[
 S=\binom b2u^2+bcuv+\binom c2v^2.
\]

Expanding the product modulo $(2A)^3$ gives

\[
 q^b r^c-1\equiv2A(bu+cv)+(2A)^2S\pmod{(2A)^3}.
\]

But $q^b r^c-1=2^A-2=2AT$. Dividing the congruence by $2A$ yields
the exact second-order condition

\[
 \boxed{bu+cv+2AS\equiv T\pmod{4A^2}.}
\]

Its reduction modulo $2A$ is the previously recorded first-order
congruence.

There is also a global-search-independent size restriction. After ordering
$q<r$, their distinct positive multipliers give

\[
 q\ge2A+1,\qquad r\ge4A+1.
\]

Cubefullness therefore forces

\[
 2^A-1\ge(2A+1)^3(4A+1)^3.
\]

Exact integer comparison for the primes below $43$ shows that this is
impossible there. Hence every member of this residual family satisfies

\[
 \boxed{A\ge43.}
\]

This small bound is independent of the much larger global finite search.

## The Fermat-type family

Assume

\[
 2^A+1=q^b r^c,\qquad A=2^s,\qquad s\ge4.
\]

The quadratic-character refinement in the preceding note gives

\[
 q=1+4Au,\qquad r=1+4Av.
\]

With the same quadratic expression $S$, expansion modulo $(4A)^3$
and division by $4A$ gives

\[
 \boxed{bu+cv+4AS\equiv2^{A-s-2}\pmod{16A^2}.}
\]

Since $2^{A-s-2}$ is divisible by $4A$ for $s\ge4$, this reduces to the
earlier congruence $bu+cv\equiv0\pmod{4A}$.

The distinct multipliers now give $q\ge4A+1$ and $r\ge8A+1$, so

\[
 2^A+1\ge(4A+1)^3(8A+1)^3.
\]

This excludes $A=16,32$, leaving the uniform necessary bound

\[
 \boxed{A\ge64\quad(s\ge6).}
\]

## Verification and scope

Run

```sh
python3 scripts/verify_erdos366_second_order.py
```

The standard-library verifier checks the two binomial identities on an exact
integer grid and checks every relevant exponent below the two stated
thresholds. The finite loops audit only elementary arithmetic; the displayed
congruences are proved for all parameters by the binomial expansion above.

These are stronger necessary conditions for two already surviving families,
not an existence or nonexistence theorem for consecutive cubefull integers.
