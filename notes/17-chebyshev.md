# A local criterion for the Chebyshev primality question

**Partial result.** Let D_m(x)=2T_m(x/2), the Dickson polynomial with parameter 1. The question asks whether ∑_{x=0}^{n−1}D_{n−1}(x)≡−1 (mod n) is equivalent to primality. The original answer proves the prime direction. We give a necessary and sufficient criterion for any composite counterexample, prove that every such integer is odd, squarefree, and has at least five prime factors, and supply an exhaustive bounded check.

For p odd and m≥1, in F_p one has

    ∑_{x∈F_p} D_m(x) = −[p−1 divides m] + [p+1 divides m].

Indeed let A=F_p^× and B={z∈F_{p²}^×:z^{p+1}=1}. Each x∈F_p has precisely two preimages under z↦z+z⁻¹ from the disjoint union of these groups: the roots of z²−xz+1 are either both in A, or nonrational and interchanged by Frobenius and in B. A repeated root z=±1 appears once in each group. Since D_m(z+z⁻¹)=z^m+z⁻ᵐ, and inversion permutes both groups, the desired sum is the sum of z^m over both cyclic groups. The cyclic sum equals its group order when that order divides m and zero otherwise. Their orders are p−1 and p+1, giving the identity.

Write n=pq and m=n−1. Since D_m has integer coefficients (use D_0=2, D_1=x, D_{m+1}=xD_m−D_{m−1}), the n-term sum modulo p equals q times the p-term sum. If p² divides n this vanishes, including for p=2. If n is even and has an odd prime divisor p, then neither p−1 nor p+1 divides the odd m, again giving zero modulo p. The only even solution is 2. For odd squarefree n, the Chinese remainder theorem gives an exact criterion. For every p|n exactly one of p−1,p+1 must divide n−1. Define ε_p=1 for the p−1 case and ε_p=−1 for the p+1 case. The remaining condition at p is q≡ε_p (mod p). Equivalently, there must be a sign ε_p with

    q≡ε_p (mod p(p−ε_p))  and  p+ε_p does not divide n−1.

Here p≡ε_p (mod p−ε_p), so p−ε_p divides n−1 iff q≡ε_p (mod p−ε_p). Each odd prime passes by taking q=1 and ε_p=1.

For a composite take the largest prime p. If there are at most three prime factors, then 1<q≤(p−2)²<p(p−1)−1 for p≥5. Neither sign congruence is possible. For four distinct odd primes p_i, the signed integer W=∑_i ε_i n/p_i is 1 modulo every p_i, hence modulo n. But |W|/n≤1/3+1/5+1/7+1/11<0.77, forcing W=1 (because n≥1155). This is impossible by parity: W is a sum of four odd terms. The same argument excludes six and eight prime factors, since the sum of reciprocal first eight odd primes is about 0.999, bounded below 1−1/n for the relevant n. Thus the first candidate cases have five or seven factors.

**Computational audit.** The local finite-field sum was compared with direct polynomial recurrence for nine odd primes up to 29 over all 250 exponents 1 through 250. The global factor test was compared with direct n-term sums for every integer 2 through 274. A second program exhaustively enumerates squarefree odd composites with four or more factors, already excluding smaller counts algebraically. Prefixes are in strictly increasing prime order and discarded only if the remaining minimum possible product exceeds the bound. For fixed prefix product Q and last prime P, the divisibility above gives P≤sqrt(Q+1)+2 and P≤cuberoot(n)+2. For two prior primes a,b, it jumps between the four exact CRT classes of P satisfying P·Q/a≡±1 mod a and P·Q/b≡±1 mod b. It then checks every surviving prime against the full local criterion. Through 1,000,000,000,000 the search checked 40,103,813 terminal prefixes and 4,259,311 CRT-compatible last-integer candidates and found no composite. Code: chebyshev_search.cpp. This finite search and the local characterization leave the existence of a composite open.

[Catalog](https://lefttosolve.com/p/mse-2615963) · [Original statement and earlier partial answer](https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials) · [Author’s collected Conjecture 1.51](https://vixra.org/pdf/1801.0341v7.pdf) · [Dickson identities](https://numberdb.org/T117) · [Chou, Gomez-Calderon and Mullen (1988), finite-field value sets](https://doi.org/10.1016/0022-314X(88)90006-6). Related work on distinct image residues asks a different counting question. The sum here counts each field input once, including repeated output values.

## A congruence obstruction for the number of prime factors

Let an odd squarefree candidate have an odd number $r$ of prime factors. With the signs from the local criterion above, put $W=\sum_{p\mid n}\varepsilon_p n/p$. We have $W\equiv1\pmod n$. Both $n$ and $W$ are odd, so $W\equiv1\pmod{2n}$. Thus $W=1$ whenever
$$
\sum_{p\mid n}\frac1p+\frac1n<2.
$$
This holds for every odd $r\le1411$. To verify the numerical cutoff, replace the factors by the first $r$ odd primes, which maximizes each term and the reciprocal product. The exact rational check in the linked program tests every prefix through the first crossing at 1,412 primes. Only the cases $r=5,7$ are needed below, for which summing through 19 already suffices.

Suppose $W=1$, $q\ge3$, $n\equiv-1\pmod q$, and every $p\mid n$ is $1$ or $-1$ modulo $q$. Then
$$
r\equiv1\pmod{q^2}.
$$
Indeed $q\nmid n-1$. A prime $p\equiv1\pmod q$ cannot have $p-1\mid n-1$, so its sign is $-1$. A prime $p\equiv-1\pmod q$ has sign $+1$ by the same argument. Set $b_p=-\varepsilon_p p$. Every $b_p$ is $1$ modulo $q$. Their product is $-n$ because it equals $\pm n$ and is $1$ modulo $q$. Hence
$$
1=W=\sum_{p\mid n}\prod_{p'\ne p} b_{p'}
\equiv r+(r-1)\sum_{p\mid n}(b_p-1)\pmod{q^2}.
$$
Reduction modulo $q$ first gives $r\equiv1\pmod q$. The sum on the right is also divisible by $q$, proving the claim.

**Five or seven prime factors force $n\equiv1\pmod{12}$ and $\gcd(n,15)=1$.** Taking $q=4$ excludes $n\equiv3\pmod4$ for both factor counts. Consequently $3$ cannot divide $n$, since both $3-1$ and $3+1$ would divide $n-1$. If $n\equiv-1\pmod3$, taking $q=3$ would require $r\equiv1\pmod9$. This excludes both counts again. Thus $n\equiv1\pmod{12}$. Both $5-1$ and $5+1$ now divide $n-1$, excluding the factor 5.

### Which signs can occur for five or seven factors?

Let $u_i=\varepsilon_i p_i$ and $S=\prod_i\varepsilon_i$. The equation $W=1$ says that $e_{r-1}(u_1,\ldots,u_r)=S$, where $e_{r-1}$ is the sum of products omitting one factor at a time. Write $b_j$ for the number of $u_i$ congruent to $-1$ modulo $j$, for $j=3,4$. Then the following are necessary conditions.

| Number of primes | Product of signs $S$ | $b_3$ | $b_4$ | $n\bmod48$ |
|---:|---:|---:|---:|---|
| 5 | $+1$ | 2 | 2 | $1,13,25,37$ |
| 7 | $-1$ | 3 | 3 | $1,25$ |
| 7 | $-1$ | 3 | 7 | $13,37$ |

To see the sign condition, write $u_i=1+2a_i$. Modulo 4 the symmetric sum equals $r+2(r-1)\sum_i a_i\equiv r$, as $r$ is odd. Thus $S=+1$ for five and $S=-1$ for seven. Since $n\equiv1\pmod{12}$ and each $p_i$ is coprime to 6, reduction of $W$ modulo 3 gives $r-2b_3\equiv1\pmod3$, while $(-1)^{b_3}=S$. These give the values of $b_3$ in the table.

Modulo 8 the same expansion gives
$$
 S\equiv r+2(r-1)\sum_i a_i+4(r-2)\sum_{i<j}a_i a_j\pmod8.
$$
The two sums have parities $b_4$ and $\binom{b_4}{2}$. Also $(-1)^{b_4}=S$ by reduction of $\prod_i u_i=Sn$ modulo 4. For five primes these conditions force $b_4=2$. For seven they give $b_4=3$ or $7$.

For the last column one can exhaust the 16 units modulo 48, allowing repeated residues. For each unordered residue list take $P=\prod_i u_i$, set $n=SP$ modulo 48, and require $n\equiv1\pmod{12}$, $e_{r-1}(u)\equiv S\pmod{48}$, and $\gcd(48,u_i-1)\mid n-1$ for every $i$. The last test follows from $p_i-\varepsilon_i\mid n-1$. Integer representatives in the symmetric sum avoid division modulo 48. The enumeration gives exactly the displayed residue patterns. Whether any surviving residue pattern contains a composite satisfying the original test remains open. [Reproduce the residue enumeration](../checks/chebyshev_residues.py)

## Finite completion of a prescribed prime prefix

For five or seven factors write the known smallest $r-2$ primes as $p_1,\ldots,p_{r-2}$, with product $A$, and denote the last two by $x<y$. Fix prefix signs and let $T=\sum_i\varepsilon_i A/p_i$. It is nonzero because precisely one summand survives modulo each $p_i$. For signs $s=\varepsilon_x$ and $t=\varepsilon_y$, the equation $W=1$ becomes
$$
Txy+sAy+tAx=1.
$$
Taking absolute values and dividing by $y$ gives $|T|x\le2A+1/y<2A+1$. Thus the integer $x$ satisfies $x\le\lfloor 2A/|T|\rfloor$ and
$$
y=\frac{1-tAx}{Tx+sA}.
$$
A zero denominator cannot produce a solution because $Ax>1$. This exhausts every possible completion without a bound on $n$ or $y$. Each candidate is tested for primality and for the original local conditions at *all* factors. Prefix signs with $\gcd(A,p_i-\varepsilon_i)>1$ are impossible since that common prime would divide $n$ and $n-1$.

| Factor count | Prescribed prefix | Prefixes checked | Composite solutions |
|---|---|---:|---:|
| 5 | Third-smallest prime at most 313 | 37,820 | 0 |
| 7 | Fifth-smallest prime at most 67 | 4,368 | 0 |

As an independent check, the program factors $(Tx+sA)(Ty+tA)=T+stA^2$ for sample prefixes and compares all odd integral pairs with the scan before primality or local filtering. The comparison covers 208 signed systems and 14 integral pairs. The small signed equation $-5\cdot7+3\cdot7+3\cdot5=1$ ensures the comparison includes actual solutions. The full Chebyshev primality equivalence remains open in this work. [Reproducible completion search and exact arithmetic checks](../checks/chebyshev_completions.py) · [Original conjecture](https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials)

## The two smallest primes with negative signs

In the remaining order $7\le d<e<a<b<c<2d$, with negative signs at $d,e$, every five-prime candidate satisfies $10\gcd(d+1,e+1)\le d+1$. The reduction uses the signed cofactor equation and the required shifts. The bound holds for all prime sizes. [Proof and exact certificates](chebyshev-shift-bound.md).

The five-prime follow-up gives a lower bound on the top prime gap for every sign order and excludes the tenth negative-shift ratio in the remaining interval. [Prime gaps](chebyshev-prime-gaps.md) · [Tenth ratio](chebyshev-ratio-ten.md).

[Factor-count theorem and sign restriction](chebyshev-even-factor-count.md) excludes every even factor count through 2,451,594. For the five-prime interval $d<e<a<b<c<2d$, [the joint-shift reduction and finite certificate](chebyshev-joint-shifts.md) give $a-e\ge502$, and [the common negative-shift bound](chebyshev-negative-overlap.md) gives $\gcd(d+1,e+1)<4(a-e)^2$ at every size.
