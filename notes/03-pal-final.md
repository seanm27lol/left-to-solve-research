# A complete palindrome classification

Let $F(w)$ concatenate a nonempty word $w$, its prefix one symbol shorter, and all remaining nonempty prefixes in decreasing order. The question on OEIS A056142 concerns decimal digits. The following classification works over every alphabet.

**Theorem.** If $|w|\le2$, every word works. If $|w|=3$, exactly the words $aba$ work. For $|w|\ge4$, $F(w)$ is a palindrome exactly when all letters of $w$ are equal.

For instance, $121$ gives $121121$ and refutes the source's threshold of three. Wasserman recorded the outcomes at lengths three, four and five in 2005. Adams-Watters observed in 2006 that at most two distinct symbols can occur. The argument below rules out every nonconstant word of length at least four.

**A forced binary word.** Put $T_j=j(j+1)/2$. Define $s_1=0$, $s_2=1$, and require the block at $T_{j-1}+1,\ldots,T_j$ to be $s_j,s_{j-1},\ldots,s_1$. Positions one and two impose tautologies and every later position refers strictly backwards. If $F(w)$ is a palindrome, it equals its reverse, which lists reversed prefixes in increasing order. Its first $n=|w|$ symbols are $w$ and satisfy this recursion. Equal first two symbols force a constant word. Otherwise rename them zero and one. Then $w=s_1\cdots s_n$ and the reverse of $F(w)$ is the full prefix $s_1\cdots s_{T_n}$. Its equality with $F(w)$ forces

$$
D_n:\qquad s_{n+i}=s_i\quad(1\le i\le n-1)
$$

by comparison with the two longest prefixes at the beginning of $F(w)$.

**Descent.** Suppose $p\ge4$ is the smallest shift for which $D_p$ holds. The first 31 symbols, grouped below only for readability, follow immediately by the triangular-block rule:

$$
\mathtt{0100100010}\ \mathtt{1001001001}\ \mathtt{0001001000}\ \mathtt{0}.
$$

For $p=4,\ldots,15$, the first mismatch offsets are, respectively,

$$
1,\ 2,\ 2,\ 4,\ 1,\ 8,\ 1,\ 2,\ 8,\ 1,\ 2,\ 11.
$$

All are at most $p-1$. Thus $p\ge16$. Choose the least $j$ with $T_j\ge p$ and put $\delta=T_j-p$, $\ell=\delta+j+1$. Then $j\ge6$, $0\le\delta\le j-1$, and $7\le\ell\le2j\le T_{j-1}<p$. Positions $p+\delta+1,\ldots,p+\ell$ are exactly the $(j+1)$st triangular block. Property $D_p$ copies its reversed prefix onto positions $\delta+1,\ldots,\ell$. This gives $s_r=s_{\ell+1-r}$ for all $1\le r\le j+1$. Since $\delta\le j-1$, these mirrored intervals cover the entire prefix, which is therefore palindromic.

Take the largest $k$ with $T_k<\ell$ and put $u=\ell-T_k$, so $1\le u\le k+1$. Reflecting the complete reversed $k$th triangular block in this palindromic prefix gives $s_{u+i}=s_i$ for $1\le i\le k$. Since $u-1\le k$, property $D_u$ holds. Now $u<p$, so minimality gives $u\le3$. At shifts $1,2,3$ the longest matching prefixes have lengths $0,1,4$ respectively, directly from the displayed word. Thus $k\le4$ and $\ell\le T_4+3=13$. The displayed word has precisely three palindromic prefixes through length 13, of lengths $1,3,6$. This contradicts $7\le\ell$.

The impossibility of $D_n$ for $n\ge4$ rules out every nonconstant word in that range. Direct substitution settles lengths one, two and three, and constant words always work. The same reflection argument also shows that $1,3,6$ are the only palindromic prefix lengths of the infinite word $s$.

[Original problem and early observations](https://oeis.org/A056142) · [Catalog entry](https://lefttosolve.com/p/oeis-a056142).
