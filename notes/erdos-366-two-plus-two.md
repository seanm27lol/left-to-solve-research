# Erdős 366: a cutoff-free reduction for the two-plus-two support split

This note treats a previously separate unbounded family in the search for
consecutive cubefull integers.  It does **not** produce such a pair or prove
that none exists.

Suppose two consecutive cubefull integers have the exact forms

\[
 E=2^a p^b,\qquad O=q^c r^d,qquad |E-O|=1,
\]

where (p,q,r) are distinct odd primes and (a,b,c,d\ge3).  Put

\[
 h=\gcd(c,d),\qquad Y=q^{c/h}r^{d/h}.
\]

Thus (O=Y^h), and the two exponents in (Y) are coprime.

The proof uses the Bang--Zsigmondy theorem and Preda Mihăilescu's theorem.
Those classical results retain their original credit.  The reduction below
was independently derived under Sean Mahdavian's coordination with OpenAI
Codex assistance; no literature-priority claim is made.

## The common exponent

The common exponent satisfies

\[
 \boxed{h=1\quad\text{or}\quad h=\ell
        \text{ for an odd prime }\ell.}
\]

First suppose that (h) is even.  If (O=E+1), set
(Z=Y^{h/2}).  Then

\[
 \frac{Z-1}{2}\frac{Z+1}{2}=2^{a-2}p^b.
\]

The two factors on the left are coprime consecutive integers greater than
one, so they must be (2^{a-2}) and (p^b) in some order.  The boundary
(a-2=1) forces the other factor to be (3), contradicting (b\ge3).
Otherwise they are consecutive nontrivial perfect powers.  Mihăilescu leaves
only (8,9), whose odd exponent is two rather than at least three.  If
(O=E-1), then (E=Y^h+1\equiv2\pmod8), contradicting (a\ge3).
Hence (h) is odd.

If this odd (h) were composite, choose two distinct divisors (m>1) of
(h).  In the upper-odd orientation, Bang--Zsigmondy supplies distinct odd
prime divisors of exact orders (m) in (Y^h-1).  In the lower-odd
orientation it supplies distinct primes of exact orders (2m), which divide
(Y^h+1) because (h/m) is odd.  The order-two and base-two/order-six
exceptions do not apply to these indices and the odd base (Y).  Either
orientation would give the even endpoint at least two odd support primes,
although it has only (p).  Thus a nontrivial (h) is an odd prime.

## Exact residual system when (h=\ell)

The unique primitive odd support must be (p).  It cannot divide the first
linear factor, so the factorization is forced:

\[
\begin{array}{rcll}
Y^\ell=E+1&:&Y-1=2^a,&\Phi_\ell(Y)=p^b,\\
Y^\ell=E-1&:&Y+1=2^a,&\Phi_{2\ell}(Y)=p^b.
\end{array}
\]

Moreover,

\[
 \boxed{\gcd(a,b)=1.}
\]

Indeed, a common divisor greater than one would make both consecutive
endpoints nontrivial perfect powers; Mihăilescu's (8,9) pair has the wrong
support pattern.

The primitive order gives (p\equiv1\pmod\ell) in the upper-odd case and
(p\equiv1\pmod{2\ell}) in the lower-odd case.  Substitution of
(Y\equiv1) or (-1\pmod{2^a}) in the cyclotomic quotient gives

\[
 \boxed{p^b\equiv\ell\pmod{2^a}.}
\]

Finally LTE, together with ((p-1)/\operatorname{ord}_p(Y)<p), gives the
exact Wieferich-type condition

\[
 \boxed{b=v_p\!\left(Y^{p-1}-1\right).}
\]

Thus (p) is a cubic base-(Y) Wieferich witness.

## Necessary shapes of the power-of-two exponent

The root (Y=q^u r^v) has exactly two prime supports, with
(gcd(u,v)=1).  A second Bang--Zsigmondy count therefore gives:

* if (Y=2^a+1), then
  
  \[
   \boxed{a=2^t,\quad a=2^t s\text{ with }s\text{ an odd prime},
          \quad\text{or}\quad a=9;}
  \]

* if (Y=2^a-1), then

  \[
   \boxed{a\text{ is prime, a prime square, or }a=6.}
  \]

For the plus sign, write (a=2^t w) with (w) odd.  The primitive orders
(2^{t+1}m), (m\mid w), give (	au(w)\le2), except that the order-six
exception at (t=0) also permits (w=9).  For the minus sign, the count is
(	au(a)-1-\mathbf1_{6\mid a}\le2), which gives precisely the stated
list.

These classifications and the displayed cyclotomic equations are necessary,
not sufficient.  The case (h=1) and every residual prime-power equation
remain open, as do support patterns with more than four primes.  This is a
partial result for `Erdos366.erdos_366.variants.weaker`.
