# Almost-perfect numbers and squares of squares

## Almost-perfect numbers other than powers of two

Does a positive integer other than a power of two satisfy 1+σ(n)=2n, with σ the sum of positive divisors? This is exactly the formal predicate, including at zero. Every power of two qualifies. Antalan and Dris derive the odd-square part and an upper bound on the power of two in terms of the square root. Kishore treats the odd case with five distinct prime divisors. [Catalog](https://lefttosolve.com/p/AlmostPerfectNumbers.exists_almost_perfect_not_power_of_two) · [Antalan–Dris](https://arxiv.org/abs/1602.04248) · [Kishore](https://doi.org/10.1090/S0025-5718-1978-0485658-X).

**Restricted result.** There is no non-power-of-two solution with at most one distinct odd prime divisor. There is no solution with exactly two distinct odd prime divisors and two-adic valuation from 0 to 11 inclusive. The second statement covers arbitrary odd prime exponents and sizes. The proof below for two-adic valuation 1 can be checked by hand. The remainder uses the exact finite search in `the accompanying verification scripts`. No priority claim is made for these exclusions.

Write n=2^a b with b odd, and t=2^(a+1)−1. From σ(2^a)σ(b)=2n−1 we get
$$
t(\sigma(b)-b)=b-1.
$$
The right side in the original multiplicative identity is odd, so σ(b) is odd and b is a square. Suppose b>1. If p is a prime divisor of b, then σ(b)−b ≥ b/p, so t<p. Since p is odd and t+1 is even, actually p>t+1. If b=p^A for a single odd prime, substitution of σ(b)−b=(b−1)/(p−1) would give p=t+1, a contradiction.

For two odd primes, b=p^A q^B with p<q and A,B positive even integers. Define
$$
F=t(t+1)-(p-t-1)(q-t-1),\qquad C=t+(p-1)(q-1).
$$
Multiplying the divisor-sum identity by (p−1)(q−1) and expanding gives
$$
F p^Aq^B=t p^{A+1}+t q^{B+1}-C.
$$
The right side is positive, since (tq^{B+1}>t+(p-1)(q-1)). Thus F≥1, and the positive factors p−t−1 and q−t−1 have product strictly below t(t+1). There are finitely many candidate pairs of primes for each fixed a.

For a=1, t=3. The inequality (p−4)(q−4)<12 leaves just (5,7),(5,11),(5,13). For every such pair,
$$
\frac{\sigma(b)}{b}\ \ge\ (1+1/5+1/25)(1+1/13+1/169)
=\frac{5673}{4225}>\frac43.
$$
But the defining equation implies σ(b)/b=4/3−1/(3b), which is impossible.

For the full computation, dividing the expanded identity by p^A q^B gives (F<t p/q^B+t q/p^A). Hence (F p^A<2tq) or (Fq^B<2tp). Enumerate all even powers satisfying the first bound and use
$$
q^B=\frac{t p^{A+1}-C}{F p^A-tq}.
$$
The swapped case treats the second bound. A positive exact quotient must be a positive even power of q. The numerator is positive for all candidates: F>0 gives q<(t+1)^2<p², t≥3 whenever candidate pairs exist, and then (t+(p-1)(q-1)<t+p^3<t p^3). Thus zero denominators can be discarded, and swapping p,q also preserves positivity. The implementation iterates primes and all bounded even exponents using integers and tests divisibility exactly. The counts of candidate pairs for a=0 through 11 are 0, 3, 6, 70, 93, 540, 1,957, 12,146, 19,068, 90,501, 336,851, and 1,370,021. All 1,831,256 pairs were eliminated.

**Two routes.** (1) The exact identity supplies a finite test for every fixed two-adic valuation and two-prime odd support. For a bound uniform in a, control the divisibility $Fp^A-tq\mid tp^{A+1}-C$ and its symmetric counterpart as the Mersenne-type parameter t varies. The hyperbolic prime-pair bound alone grows with t. (2) For arbitrary prime support use the product $\sigma(b)/b=\prod_{p^e\Vert b}(1+p^{-1}+\cdots+p^{-e})=1+1/t-1/(tb)$ to branch on small odd primes, bounding the contribution of unspecified primes by p/(p−1), as in the odd near-perfect abundance estimates of Kishore. At any finite branching stage the number of further factors is unbounded. No uniform prime-support bound or contradiction follows.

## A three-by-three magic square of distinct squares

Does a 3×3 magic square of nine distinct positive integer squares exist, with all eight lines sharing a sum? Rome and Yamagishi proved in 2025 that all orders at least 4 admit magic squares of distinct squares. Bremner gives geometric reductions for order 3. [Catalog](https://lefttosolve.com/p/MagicSquares.exists_magic_square_squares) · [Rome–Yamagishi](https://doi.org/10.1007/s40993-025-00671-5) · [Bremner, On squares of squares](https://matwbn.icm.edu.pl/ksiazki/aa/aa88/aa8837.pdf).

**Restricted result.** In a primitive solution, the square root e of the center must have at least two distinct prime factors, both congruent to 1 modulo 4. The no-prime-power argument reproduces a previously recorded valuation obstruction. A more recent online project reports a stronger exclusion of all two-prime centers. We do not rely on that stronger claim. [Known prime-power obstruction, §5](https://github.com/uwe-schwarz/magic-squares-of-squares/blob/main/research/prime-support/hourglass-sunit.md) · [Unrefereed two-prime report](https://labs.ofertiber.com/magic-square/research?doc=research%2Fautonomous-20260909%2FPROOF.md).

Divide the nine roots by their gcd. Every 3×3 magic square is determined by its center c and two signed offsets u,v. Its entries are c and the pairs c±u, c±v, c±(u+v), c±(u−v). For example, its rows can be written (c−u, c+u+v, c−v), (c+u−v,c,c−u+v), (c+v,c−u−v,c+u). Thus c=e² and each opposite root pair satisfies x²+y²=2e². If 2 divides e, reducing modulo 4 forces every x,y even. If p≡3 mod 4 divides e, reducing modulo p gives p|x,y because −1 is a quadratic nonresidue. Both violate primitivity. If e=1 there are no distinct positive opposite pairs.

Suppose therefore e=p^k, where p≡1 mod 4 is a prime, k≥1. Write p=π times its conjugate in the Gaussian integers. Unique factorization shows that for an opposite pair, up to a unit and conjugation,
$$
x+iy=(1+i)p^{k-j}\pi^{2j},\qquad 0\le j\le k.
$$
Indeed the exponents of π and its conjugate in the representation sum to 2k. The positive offset (|x^2-y^2|/2) equals
$$
d_j=p^{2(k-j)}|\operatorname{Im}(\pi^{4j})|,\qquad 1\le j\le k;
$$
j=0 is the repeated-center pair. The imaginary factor is nonzero modulo p, since otherwise π divides $\pi^{4j}-\bar\pi^{4j}$ and therefore divides $\bar\pi^{4j}$, impossible. Thus the d_j have the pairwise distinct valuations 2(k−j). Any exact additive relation amongst three signed integers with different p-adic valuations is impossible, since its smallest valuation would be unique. In a magic square the signed offsets satisfy u+v−(u+v)=0, with three distinct absolute values because all entries are distinct. This contradiction excludes all prime-power center roots.

**Two routes.** (1) For several primes $p^k\Vert e$, simultaneously record the two Gaussian exponents above each p for each of the four offsets. The two equations for u±v force a repeated minimum in every applicable valuation. Use those necessary conditions to restrict the patterns, then compare the actual Gaussian integers. A distinct offset can share a valuation at any single p when other split primes are present, so the one-prime contradiction no longer closes the argument. (2) In Bremner's reduction the square gives three rational points in 2E(Q) with equally spaced x-coordinates on (E:y^2=x(x^2-v^2)). Conversely, provided the usual distinctness and positivity inequalities hold, such a triple clears denominators to a square of the required kind. A descent could sieve the possible configurations on the quadratic twists, or a search could produce an explicit triple. Solving a fixed twist or producing points in E(Q) alone does not control all twists and the divisibility-by-two condition.
