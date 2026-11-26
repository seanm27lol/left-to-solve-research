# Four squares with the root 7 excluded

**Answer.** Every nonnegative integer is a sum of four squares of nonnegative integers, none equal to 7. Zero summands are allowed. The exact Left to Solve entry is `OeisA241898.conjecture_2`. Its API marked it open with no solution at the time of this check. [Catalog](https://lefttosolve.com/p/OeisA241898.conjecture_2) · [OEIS source](https://github.com/oeis/oeisdata/blob/main/seq/A241/A241898.seq).

**Literature.** In 2025 Wonjun Chae, Yun-Seong Ji, Kisuk Kim, Kyoungmin Kim, Byeong-Kweon Oh, and Jongheun Yoon determined the minimum number of summands required when a fixed square is forbidden. Their classification gives $M(7)=4$ and $I(7)=\varnothing$. These statements give the answer for every positive integer, and four zeroes work for zero. Zedan Soorya's 13 November 2026 comment in the OEIS entry explicitly records this consequence. [Chae et al., introduction and §3](https://arxiv.org/html/2504.03467v1).

**Independent counting proof.** Write $r_s(m)$ for the number of signed, ordered representations of $m$ as a sum of $s$ integer squares. If $4\mid n$, Lagrange's theorem at $n/4$ provides four roots whose doubles represent $n$ and avoid 7. For $4\nmid n$, Jacobi's formula gives $r_4(n)=8\sum_{d\mid n,4\nmid d}d\ge8n$. For $n>49$, at most $8r_3(n-49)$ of these representations use 7 or −7. The factor eight accounts for the position and sign of the forbidden entry. [Adiga, Jacobi's two-square and four-square theorems](https://journals.math.tku.edu.tw/index.php/TKJM/article/download/4423/1477).

For $m>0$, Jacobi's two-square theorem gives

$$
r_2(m)\le4\prod_{\substack{p^e\Vert m\\p\equiv1\bmod4}}(e+1)\le8m^{1/4}.
$$

For $p\ge17$, use $e+1\le2^e\le p^{e/4}$. For $p=5$ and $p=13$, the respective bounds are $(3/2)5^{e/4}$ and $(4/3)13^{e/4}$. Check $e=0,1,2$ directly. For $e\ge2$, the ratio of successive left sides is $(e+2)/(e+1)\le4/3<5^{1/4}$. The two exceptional constants multiply to 2. Jacobi's product bound itself follows at once from $r_2(m)/4=\sum_{d\mid m}\chi_4(d)$: primes congruent to 3 contribute either zero or one, and 2 contributes one.

As $r_2(0)=1$, summing over the third root gives $r_3(N)\le(2\sqrt N+1)8N^{1/4}\le24N^{3/4}$ for $N\ge1$. Whenever $n\ge24^4$, $24(n-49)^{3/4}<n$. Thus the bad representations are fewer than the total. Take absolute values in any remaining representation.

For $0\le n<331776=24^4$, an exact integer bitset calculation starts with the set $\{0\}$ and adds one allowed square in each of four rounds, discarding sums beyond the interval. The successive cardinalities are 575, 75,089, 276,478 and 331,776. The final equality proves that every number in the interval is represented. The complete finite certificate follows.

~~~python
from math import isqrt

N = 24**4
mask = (1 << N) - 1
allowed = [j*j for j in range(isqrt(N - 1) + 1) if j != 7]
bits = 1
for _ in range(4):
    next_bits = 0
    for square in allowed:
        next_bits |= (bits << square) & mask
    bits = next_bits
assert bits == mask
~~~

The published classification and the independent computation both address the exact four-square statement. The neighboring catalog entry about the maximum possible smallest positive root concerns a separate conjecture.
