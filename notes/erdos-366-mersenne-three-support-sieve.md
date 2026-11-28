# Erdős 366: a second-order sieve in the prime-exponent Mersenne branch

This note sharpens one residual family from the four-support singleton
classification. Suppose \(p\) is an odd prime and

\[
 2^p-1=q_1^{e_1}q_2^{e_2}q_3^{e_3},
 \qquad e_i\ge3,
\]

with distinct primes \(q_i\). Put

\[
 k_i=\frac{q_i-1}{2p},\qquad
 Q_p(2)=\frac{2^{p-1}-1}{p}.
\]

Then every \(k_i\) is an integer and the following exact second-order
congruence holds:

\[
 \boxed{
 Q_p(2)\equiv
 \sum_i e_i k_i+2p\left(
   \sum_i\binom{e_i}{2}k_i^2+
   \sum_{i<j}e_i e_jk_i k_j
 \right)\pmod{4p^2}.}
\]

Indeed, \(\operatorname{ord}_{q_i}(2)=p\), hence
\(q_i=1+2pk_i\). Expanding the product modulo \((2p)^3\) gives

\[
 \prod_i(1+2pk_i)^{e_i}
 \equiv1+2pS_1+4p^2S_2\pmod{8p^3},
\]

where

\[
 S_1=\sum_i e_i k_i,
 \qquad
 S_2=\sum_i\binom{e_i}{2}k_i^2+
       \sum_{i<j}e_i e_jk_i k_j.
\]

On the other hand, the definition of the Fermat quotient gives the exact
identity \(2^p-1=1+2pQ_p(2)\). Cancelling \(2p\) proves the displayed
congruence modulo \(4p^2\). Its reduction modulo \(2p\) is

\[
 \sum_i e_i k_i\equiv Q_p(2)\pmod {2p}.
\]

## Two further restrictions

Since \((q_i-1)/p<q_i\), LTE gives

\[
 \boxed{e_i=v_{q_i}(2^{q_i-1}-1).}
\]

Thus every support prime is a cubic base-two Wieferich prime. Also, \(2\)
has odd order \(p\) modulo \(q_i\), so \(2\) is a quadratic residue and

\[
 q_i\equiv\pm1\pmod8.
\]

For \(p\ge5\), reduction of the original factorization modulo \(16\)
therefore gives

\[
 \boxed{\prod_{e_i\text{ odd}}q_i\equiv-1\pmod{16}.}
\]

## Scope and attribution

These are cutoff-free necessary conditions, not an exclusion of the branch.
They turn the residual prime-exponent family into a simultaneous order,
cubic-Wieferich, Fermat-quotient, and parity sieve. Bang--Zsigmondy, LTE,
and the classical Fermat quotient retain their standard attribution. The
combined second-order specialization was independently derived under Sean
Mahdavian's coordination with OpenAI Codex assistance.

The arithmetic identities can be audited with

```sh
python3 scripts/verify_erdos366_mersenne_three_support.py
```

The verifier includes \(p=29\), for which
\(2^{29}-1=233\cdot1103\cdot2089\); this has the same three-support shape
but exponent one, so it is only an identity check and not a cubefull example.
