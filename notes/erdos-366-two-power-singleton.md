# Erdős 366: a power-of-two singleton with four total supports

This note gives a cutoff-free classification in one unbounded part of the
exact weaker target.  It does **not** produce consecutive cubefull integers
or rule them out in general.

Assume that consecutive positive integers are cubefull, that together they
have exactly four prime divisors, and that one endpoint is (2^A), so (A\ge3).
The other
endpoint is odd and has exactly three prime divisors.  All three of their
exponents in that endpoint are at least three.

The proof uses the Bang--Zsigmondy theorem, Mihăilescu's theorem (Catalan's
conjecture), and Proposition 1 of M. A. Bennett and A. Levin, *The
Nagell--Ljunggren equation via Runge's method*, Monatsh. Math. 177 (2015),
15--31, doi:10.1007/s00605-015-0748-1.  The synthesis below was independently
derived with OpenAI Codex under Sean Mahdavian's coordination; no priority is
claimed for the classical inputs.

## The upper endpoint (2^A)

Suppose

\[
 2^A-1=q^b r^c s^d,
 \qquad b,c,d\ge3.
\]

For every divisor (m>1) of (A), Bang--Zsigmondy supplies a prime of exact
order (m), except when (m=6).  Distinct orders give distinct support
primes.  Hence

\[
 \tau(A)-1-\mathbf1_{6\mid A}\le3.
\]

If (6\nmid A), the elementary divisor-count classification gives

\[
 A\in\{p,p^2,p^3,pq\},
\]

where (p,q) are distinct primes in the last case.  If (6\mid A), the
same bound leaves only (A=6), and (2^6-1=3^2\cdot7) is not cubefull.

The remaining composite exponents are impossible.

* If (A=p^2), put
  \[
  F=\Phi_p(2)=2^p-1,
  \qquad G=\Phi_{p^2}(2)=\frac{2^{p^2}-1}{2^p-1}.
  \]
  Their gcd divides (p), while (F\equiv1\pmod p), so they are coprime.
  Since the two primitive-order blocks use only three supports, one block is
  a prime power whose exponent is at least three.  The possibility
  (F=u^e) contradicts Mihăilescu.  If (G=u^e), choose a prime
  (ell\mid e) and apply Bennett--Levin Proposition 1 to
  \[
  \frac{X^p-1}{X-1}=(u^{e/\ell})^\ell,
  \qquad X=2^p.
  \]
  None of its four exceptional solutions has power-of-two base, while its
  general alternative would require a prime divisor of (X) congruent to
  (1\pmod\ell).  The only base prime is (2), and the proposition makes
  (ell) odd outside its exceptions.  The case (p=2) is direct:
  (Phi_4(2)=5) has exponent one.

* If (A=p^3), the three pairwise coprime primitive blocks of orders
  (p,p^2,p^3) exhaust the three supports.  The top block is a prime power
  of exponent at least three, and the same Bennett--Levin argument, now with
  (X=2^{p^2}), excludes it.  For (p=2), the top block is
  (Phi_8(2)=17).

* If (A=pq), choose (p<q).  The block (Phi_p(2)=2^p-1) has one
  support prime.  If that prime is not (q), its final exponent is at least
  three and Mihăilescu excludes it.  If it is (q), Mihăilescu forces
  (2^p-1=q); LTE then gives
  \[
  v_q(2^{pq}-1)=v_q(2^p-1)+v_q(q)=2,
  \]
  contrary to cubefullness.  The only order-overlap exception with (p=2)
  is (q=3), already the failed exponent (A=6).

Thus

\[
 \boxed{2^A-1\text{ cubefull with three supports}\Longrightarrow
        A\text{ is an odd prime}.}
\]

This is an exponent classification, not an exclusion of the prime-exponent
family.

## The lower endpoint (2^A)

Suppose

\[
 2^A+1=q^b r^c s^d,
 \qquad b,c,d\ge3,
\]

and write (A=2^t u), with (u) odd.  Factor

\[
 2^A+1=\prod_{m\mid u}\Phi_{2^{t+1}m}(2).
\]

For (t\ge1), every divisor (m\mid u) contributes a distinct primitive
order, so (\tau(u)\le3).  Therefore

\[
 u\in\{1,p,p^2\}
\]

for an odd prime (p).  If (t=0), cubefullness at (3) and LTE give
(v_3(2^A+1)=1+v_3(A)\ge3), so (9\mid A).  The sole missing primitive
order is (6), and the support count leaves only (A=9,27).  Now
(2^9+1=3^3\cdot19), and LTE gives
(v_{19}(2^{27}+1)=v_{19}(2^9+1)=1).  Both fail.  Hence (t\ge1).

The three cases have the following exact form.  Put (x=2^{2^t}).

1. If (u=1), no further splitting is forced:
   (2^A+1=x+1) must itself have exactly three cubefull supports.

2. If (u=p), the two cyclotomic layers can overlap only at (p), because
   \[
   \gcd\!\left(x+1,\frac{x^p+1}{x+1}\right)\mid p.
   \]
   They must overlap.  Otherwise one coprime layer is a cubefull prime
   power, excluded by Mihăilescu for (x+1) and by Bennett--Levin at base
   (-x) for the quotient.  The possibility (x+1=p) gives total
   (p)-valuation two by LTE and also fails.  Consequently, after renaming
   the other two support primes,
   \[
   \boxed{x+1=p^a q^b,\qquad
   \frac{x^p+1}{x+1}=p r^c,}
   \]
   where (a\ge2) and (b,c\ge3).  The single factor of (p) in the
   quotient raises the final (p)-valuation to (a+1\ge3).

3. If (u=p^2), the three primitive-order classes already exhaust the
   three supports.  Thus (x+1) is a prime power.  Mihăilescu excludes a
   proper power; cubefullness then forces its prime to be the shared index
   prime.  Hence
   \[
   p=x+1=2^{2^t}+1
   \]
   is a Fermat prime, and for distinct primitive primes (q,r),
   \[
   \boxed{
   \frac{x^p+1}{x+1}=p q^b,\qquad
   \frac{x^{p^2}+1}{x^p+1}=p r^c,\qquad b,c\ge3.}
   \]
   LTE gives one factor of (p) in each displayed quotient, so
   (v_p(x^{p^2}+1)=3).  This is why cubefullness cannot be imposed on
   each cyclotomic layer separately.  The Fermat-prime-square branch is a
   genuine residual family, not an exception that the present tools remove.

Combining the cases,

\[
 \boxed{2^A+1\text{ cubefull with three supports}\Longrightarrow
 A=2^t,\ 2^tp,\text{ or }2^tp^2,}
\]

with (t\ge1), and the square case has exactly the Fermat-prime system
above.

In the first alternative (A=2^t), the standing condition (A\ge3) sharpens
this to (t\ge2).

## Two uniform checks

If the three final support exponents had a common divisor (g>1), the odd
endpoint would be a perfect (g)-th power.  Mihăilescu excludes both
(2^A-Y^g=1) and (Y^g-2^A=1); the sole (9-8) orientation has only one
odd support.  Thus their gcd is one.

For any odd support prime (\rho) with final exponent (e), order and LTE
give the corrected identity

\[
 \boxed{v_\rho(2^{\rho-1}-1)=e-v_\rho(A).}
\]

The subtraction matters precisely for support primes shared with an index,
including the Fermat prime (p) above.

## Exact scope

This theorem handles the (1+3) support split only when the singleton is a
power of two.  It leaves the prime-exponent minus family, all three plus
families displayed above, the (2+2) split, and every candidate with at
least five total prime supports.  It is therefore a partial result for
`Erdos366.erdos_366.variants.weaker`, not a proof or disproof of that target.

