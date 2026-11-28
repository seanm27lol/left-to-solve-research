# Erdős 366: completion of the exponent-gcd classification in the 2+2 split

Consider the residual four-support configuration

\[
 E=2^a p^b,\qquad O=q^c r^d,\qquad |E-O|=1,
 \qquad a,b,c,d\ge 3,
\]

where \(p,q,r\) are distinct odd primes. Put

\[
 g=\gcd(a,b),\qquad h=\gcd(c,d).
\]

The existing 2+2 analysis proves that \(h\) is either \(1\) or an odd
prime, and that \(h>1\) forces \(g=1\). The complementary branch
\(h=1\) has the following cutoff-free classification.

## Theorem

If \(h=1\), then

\[
\boxed{
\begin{array}{ll}
 O=E-1: & g=1,\ \ell,\ \text{or }\ell^2\quad(\ell\text{ prime}),\\[2mm]
 O=E+1: & g=2^t\ \text{or }\ 2^t\ell
          \quad(t\ge0,\ \ell\text{ an odd prime}).
\end{array}}
\]

Thus, together with the earlier \(h\)-classification, every 2+2 candidate
falls into one of the following two gcd-level branches:

1. \(h\) is an odd prime, \(g=1\), and the previously derived exact
   cyclotomic systems apply;
2. \(h=1\), and \(g\) has one of the orientation-dependent shapes above.

## Proof

Write

\[
 Z=2^{a/g}p^{b/g}.
\]

Then \(E=Z^g\), and \(Z\) is an even composite integer divisible by both
\(2\) and \(p\).

### The orientation \(O=E-1\)

Here \(O=Z^g-1\). For every divisor \(m>1\) of \(g\), the
Bang--Zsigmondy theorem supplies a primitive prime divisor of \(Z^m-1\).
Neither exceptional case occurs: \(Z\ne2\), and for \(m=2\) the possible
exception would require \(Z+1\) to be a power of two, whereas \(Z+1>1\)
is odd.

Such a primitive prime has multiplicative order exactly \(m\) for base
\(Z\). Hence distinct divisors \(m>1\) give distinct prime divisors of
\(Z^g-1=O\). Since \(O\) has only the two prime supports \(q,r\),

\[
 \tau(g)-1\le2.
\]

The positive integers with at most three divisors are \(1\), a prime, and
the square of a prime. This proves the first line.

### The orientation \(O=E+1\)

Write \(g=2^t u\) with \(u\) odd. For every divisor \(m\mid u\), apply
Bang--Zsigmondy to

\[
 Z^{2^{t+1}m}-1.
\]

Again the exceptional cases are absent. A resulting primitive prime has
order exactly \(2^{t+1}m\), so it divides \(Z^{2^t m}+1\). Because
\(u/m\) is odd,

\[
 Z^{2^t m}+1\mid Z^{2^t u}+1=O.
\]

Distinct divisors \(m\mid u\) again produce distinct prime supports of
\(O\). Therefore \(\tau(u)\le2\), whence \(u=1\) or \(u\) is prime.
This proves the second line. ∎

## Scope and attribution

This is a necessary classification, not a solution of Erdős 366. It closes
the exponent-gcd bookkeeping left open in the \(h=1\) part of the 2+2
residual family. The primitive-divisor input is the classical theorem of
Bang and Zsigmondy. The orientation-dependent specialization was
independently derived under Sean Mahdavian's coordination with OpenAI Codex
assistance.

The elementary divisor-count deductions can be audited with

```sh
python3 scripts/verify_erdos366_two_plus_two_gcd.py
```
