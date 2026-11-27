# Completion of a 139-block configuration of order twelve

**Research by Sean Mahdavian (@seanm27lol) with OpenAI Codex assistance.** The profile enumeration, the incidence argument and its independent audit were developed in the @seanm27lol research workspace.

**Theorem.** A family of 139 distinct 13-element subsets of 157 points, with every two blocks meeting in exactly one point, extends on the same points to a projective plane of order 12. Consequently, existence of such a family is equivalent to existence of an order-12 plane.

The initial family is assumed in the extension theorem. Constructing it or proving its nonexistence remains the unresolved existence problem. This is a paper proof, with a short integer enumeration. It uses the generalized-line-graph theorem. The question of historical priority for this numerical embedding bound is open in this note.

The elementary extensions from 140, 141 and 142 lines and their Lean formalization under @seanm27lol and collaborators (Codex-assisted) are recorded in [the research repository](https://github.com/seanm27lol/left-to-solve-research/commit/4100242ec70236d9ba325564392f6c75f363acb8). For families already having 143 through 156 lines, the distinct existing work of @ian139, @dk8827 and @Baseball6438 is documented in upstream [#3312](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3312), [#4661](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4661) and [#4747](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4747). The argument below treats the next case of 139 blocks.

**Reproducibility.** Run the [profile verifier](./verify_139_profiles.py) with Python 3. It uses only the standard library. The [ternary pencil inequalities](./code/TernaryPencil.lean) have a separate Lean formalization with the standard axioms. The full embedding theorem below is a paper proof.

## 1. Residual Gram matrix

Let $A$ be the $139$ by $157$ incidence matrix of the old blocks. For a point x let $r_x$ be its degree and let $t_x=13-r_x$. The union of $x$ and the lines through it covers $1+12r_x$ points, so $r_x\le 13$. Call distinct points adjacent in the gap graph when no old block joins them. Each x has $12t_x$ gap neighbors.

If $t_x=1$, the twelve points missed by its pencil together with x give a new line. A block through x meets it at x. Each other block meets the twelve pencil lines in twelve distinct points, so its thirteenth point is the unique new-line point. The previously proved extensions from 140 onward then finish. Assume below that every positive $t_x$ is at least two. A point of deficit two is light, and one of greater deficit is heavy.

Write J for an all-ones matrix of the indicated dimensions and let $K=12I+J$ on the points. Since $AA^{\mathsf T}=12I+J$ and each row sums to 13,
$K^{-1}=(I-J/169)/12$ and $AK^{-1}A^{\mathsf T}=I$. Thus

$$
Q=K-A^{\mathsf T}A
=K^{1/2}\bigl(I-K^{-1/2}A^{\mathsf T}AK^{-1/2}\bigr)K^{1/2}
$$

is positive semidefinite of rank 157−139=18. Take vectors $v_x$ spanning Euclidean 18-space with Gram matrix $Q$. Their squared norms are $t_x$. Distinct vectors have inner product one across a gap and zero otherwise. Zero vectors represent full points.

Put $s=(\sum_x v_x)/13$. Each row of Q sums to $13t_x$; also $\sum_x t_x=13\cdot18=234$. Hence $v_x\cdot s=t_x$ and $\lVert s\rVert^2=18$. For any old line L, $\sum_{x\in L}v_x=s$. Indeed $AQ=\mathbf{1}t^{\mathsf T}$ follows by expanding $A(12I+J)$ and $(AA^{\mathsf T})A$, and equality of all inner products gives the vector identity.

The sum of deficits on an old line is 18: summing degrees on it counts the line itself 13 times and every other block once, giving 139+12. In particular $\sum_x t_x r_x=139\cdot18$. Combining this with $\sum_x t_x=234$ gives $\sum_x t_x(t_x-2)=72$. For a point of deficit a, the sum of deficits of its gap neighbors is a(30−a): sum deficits across the 13−a pencil lines and remove their repeated center. No full point is a gap neighbor. Therefore

$$
\sum_{y\text{ gap-neighbor of }x}(t_y-2)=a(6-a).
$$

For positive a this gives a≤6.

For two distinct points of deficits a,b, the number of their common gap neighbors is ab when they are collinear and 12−a−b+ab otherwise. To see this, look at the pencil coverage at each point (size 1+12r). For a gap pair their two covered sets intersect in the (13−a)(13−b) distinct pairwise line intersections. For a collinear pair their common covered set consists of the 13 common-line points and (12−a)(12−b) other intersections. Subtract their union from 157. In particular adjacent light points have 12 common gap neighbors, and nonadjacent distinct light points have four.

## 2. Exact finite deficit enumeration

Let $n_t$ count points of deficit $t$ for $t=2,3,4,5,6$, and put $m=n_2$. The preceding identities give

$$
3n_3+8n_4+15n_5+24n_6=72,\qquad
2m+3n_3+4n_4+5n_5+6n_6=234.
$$

They allow 23 nonnegative histograms. For each type a that occurs, let $g_t$ count neighbors of the different types of a point of deficit a. Enumerate the nonnegative vectors with $g_t\le n_t-\mathbf{1}_{t=a}$, $\sum_tg_t=12a$ and $\sum_t(t-2)g_t=a(6-a)$. When a is odd require

$$
n_3+n_5-1-g_3-g_5\ge13-a.
$$

Every old line has even deficit sum. Each pencil line through an odd point needs another odd point, and these other points are distinct. Reject a histogram if any occupied type has no neighbor vector.

Two deficit-six points have exclusively light neighbors, 72 each, and must be collinear. Their common gap count is 36, so m≥108 whenever $n_6\ge2$. Count the light-heavy gap edges, say E, from the two sides. For each heavy type multiply its population by the smallest and the largest possible $g_2$ for that type. Sum these bounds over all heavy types. Independently light points give m times the minimum and maximum of $g_3+g_4+g_5+g_6$ for $a=2$. Intersect the two integer intervals, rejecting empty intersections.

The Gram norm of the sum of the m light vectors is 26m−E, since each light has 24 gap neighbors. Its inner product with s is 2m. Cauchy–Schwarz gives 4m²≤18(26m−E). The [profile verifier](./verify_139_profiles.py) checks every histogram and every allowed vector. Nine histograms survive before this last inequality, with the following bounds. The ratio uses the lower bound on E.

| $(m,n_3,n_4,n_5,n_6)$ | Bounds on $E$ | $4m^2/(26m-E_{\min})$ |
|---|---:|---:|
| (108,0,0,0,3) | 216 | 18 |
| (102,0,6,0,1) | 336–342 | 3468/193 |
| (99,0,9,0,0) | 396 | 18 |
| (92,11,3,1,0) | 528–541 | 4232/233 >18 |
| (91,14,0,2,0) | 544–548 | 16562/911 >18 |
| (90,16,0,0,1) | 552 | 2700/149 >18 |
| (87,16,3,0,0) | 584–606 | 15138/839 >18 |
| (86,19,0,1,0) | 568–606 | 7396/417 |
| (81,24,0,0,0) | 648 | 18 |

Five profiles remain and their five displayed ratios all exceed 17.

## 3. Connectivity and the line graph

Let G be the gap graph induced by light points. On the first three surviving profiles each light point has at most four heavy neighbors because their individual excesses t−2 are at least two, summing to eight. Thus its light degree is at least 20. In the component of a fixed light x, each of its at least 20 neighbors has at least 20−1−12=7 neighbors two steps from x. Every one of the latter points can account for at most four such walks. The component contains at least 1+20+35=56 vertices. Two components cannot fit, since m≤108.

For m=81, every light has eight heavy neighbors, and every heavy has 27 light neighbors (its excess nine is accounted for by nine other heavy points). If a component has size n<m, let $c_i$ count the lights in this component adjacent to the $i$th heavy point. Then $\sum_i c_i=8n$. Every light in this component and light outside it share four heavy neighbors, since they have no common light neighbor. Consequently

$$
4n(81-n)=\sum_{i=1}^{24} c_i(27-c_i)
\le 216n-(8n)^2/24=(8/3)n(81-n),
$$

a contradiction.

For m=86 let e be the unique deficit-five point. It has 55 light neighbors: its excess five occurs at five deficit-three neighbors, leaving 55 of its 60 neighbors light. Each deficit-three point has 27 or 29 light neighbors according as it misses e in the gap graph or is adjacent to e (its excess nine is supplied by nine triples, or e and six triples). In a smallest proper component of n≤43 lights let b of them be adjacent to e. The 19 triple points have altogether 8n−3b gap incidences to that component. Counting four common heavy neighbors for every cross-component light pair and applying Cauchy–Schwarz gives

$$
4n(86-n)\le29(8n-3b)-(8n-3b)^2/19+b(55-b).
$$

This fails for 1≤n≤43 and 0≤b≤n. Multiplying the difference, left minus right, by 19 gives 2128n−12n²+(608−48n)b+28b². Here 2128−12n≥1612 and 608−48n≥−1456, so the difference is positive.

The principal light submatrix of Q is $2I+\operatorname{Adj}(G)$. It is positive semidefinite, so G has least eigenvalue at least −2. It is connected and has at least 81 vertices. The Cameron–Goethals–Seidel–Shult theorem implies that G is a generalized line graph, since every connected exception has at most 36 vertices. If a cocktail-party attachment is nonempty, its matched nonadjacent pair has identical neighborhoods. Their number of common light neighbors would be their light degree, at least 16 in every profile (light points spend eight units of excess on heavy neighbors). This contradicts the common-gap bound four. Hence G is the ordinary line graph of a connected simple graph H with isolated vertices removed.

The cited classification and the definition of generalized line graphs are available in [Cameron, Goethals, Seidel and Shult (1976)](https://doi.org/10.1016/0021-8693(76)90162-9), [Acharya and Jiang, introduction and Definition 2.1](https://doi.org/10.1017/S0963548325100278), and the [Cambridge monograph excerpt](https://assets.cambridge.org/97805218/36630/excerpt/9780521836630_excerpt.pdf).

## 4. The non-bipartite embedding

For edge $ij$ of $H$, the vectors $e_i+e_j$ have exactly the light Gram matrix. Their span has dimension $h=|V(H)|$ if H is non-bipartite, and h−1 otherwise: a perpendicular vector must change sign on every edge. Hence h≤18 in the first case and h≤19 in the second.

If $k_i$ are the degrees in $H$, then $\sum_i k_i=2m$ and $\sum_i k_i^2=26m-E$. The latter follows by summing $k_i+k_j$ over edges $ij$, whose line-graph degrees are $k_i+k_j-2$. Consequently h≥4m²/(26m−E)>17 by Section 2.

In the non-bipartite case h=18, and the equality of Gram matrices permits an orthogonal choice of coordinates in the residual space in which all light vectors are $e_i+e_j$. As $s\cdot(e_i+e_j)=2$ on each edge and these vectors span the space, s=(1,…,1). For each point vector w the sums $w_i+w_j$ on edges are integers, because its inner products with all light vectors are integers. Connectivity and an odd cycle imply all coordinates of w are integers or all are half-integers with odd numerator. The latter would make $4\lVert w\rVert^2$ congruent to 18 modulo 8 (odd squares are 1 modulo 8), impossible for an integer norm squared. Thus w is integral. From $s\cdot w=\lVert w\rVert^2$, $\sum_i w_i(w_i-1)=0$, so every coordinate is zero or one.

Each of the 18 coordinates now gives one new block, consisting of the points with that coordinate one. From $\sum_x v_x=13s$ each has exactly 13 points. Distinct points share exactly one coordinate if their pair was missing, and zero otherwise. Each old line contains exactly one point in each new block, since its vector sum is s. With the old blocks, this gives 157 blocks and every pair of points lies on exactly one of them. In particular the new blocks are distinct. Each point lies on 13 blocks and any two blocks meet by standard pair counting (the other blocks meeting any given line total 13·12=156). This is a plane of order 12.

## 5. Bipartite roots

If H is bipartite with h≤19 then m≤90. The first three profiles have larger m. For m=86 this forces h=19 because a bipartite graph on 18 vertices has at most 81 edges. Each light is adjacent to either eight triple points or to e and five triple points, giving its light degree 16 or 18. Thus $k_i+k_j$ is even on every edge, and all $k_i$ have the same parity. They cannot all be odd, since 86 is the degree sum on each bipartite side and the two side sizes add to 19. If all are even, the only side sizes with product at least 86 are (8,11) and (9,10); either permits at most 80 edges when all degrees must be even. This eliminates the case.

For m=81 the line graph is 16-regular, so $k_i+k_j=18$ on every edge. In a connected bipartite graph this makes H semiregular, with constant degrees on each side, both divisors of 81. The only pair summing to 18 is 9 and 9. Hence $H=K_{9,9}$.

## 6. The 9 by 9 grid

Write the light vectors $v_{ij}$ as $e_i+f_j$ for $1\le i,j\le 9$ ($e$ and $f$ refer to disjoint sets of orthonormal basis vectors). The span has dimension 17. Choose an isometry on the full residual 18-space extending this identification. Its one-dimensional orthogonal complement is spanned by $u=\sum_i e_i-\sum_j f_j$, with $\lVert u\rVert^2=18$. The conditions $s\cdot v_{ij}=2$ determine the projection of s as the all-ones vector; this already has $\lVert s\rVert^2=18$. Thus s is the all-ones vector in these coordinates.

The 24 heavy vectors have norm squared three and have exactly 27 light neighbors each. For a heavy w, its grid of inner products $w\cdot v_{ij}$ consists of 27 ones among 81 binary entries and has the form $a_i+b_j$. Such a nonconstant binary grid depends on the row only or the column only. If two rows differ, their difference is a constant ±1, so one consists entirely of ones and the other of zeros; then all columns agree. If all rows agree, dependence is on columns alone. Hence its marks comprise exactly three rows or three columns.

Let $z_w$ be the sum of the corresponding three $e_i$ or the corresponding three $f_j$. It has the same grid inner products as w and the same norm. Thus $w=z_w$ or $w$ is its orthogonal reflection across $u^\perp$. As $z_w\cdot u=3$ for a row triple and −3 for a column triple, its reflection equals $z_w-u/3$ or $z_w+u/3$, respectively.

For each reflected row triple assign the ternary symbol −1 and for each reflected column triple assign +1; all other points get zero. On every old line these symbols sum to zero modulo three: subtract the integer vector sum of all the unreflected-coordinate representatives from its actual sum s. The resulting multiple of u/3 is an integer vector, hence the signed coefficient is divisible by three. Reflecting the entire coordinate system across $u^\perp$ fixes the lights and s and exchanges the two choices for every heavy vector. The heavy triples complementary to the first support therefore give a second ternary word with the same orthogonality property.

A nonzero such word supported on points of degree ten has weight at least 14. Write P and M for the numbers of plus and minus coordinates. If P>0, fix a plus point. Through it pass ten old lines. On each either there is another point with negative symbol or there are at least two further positive symbols. All these other points are disjoint across its ten lines. Consequently 20≤P−1+2M. Similarly if M>0 then 20≤M−1+2P. When both signs occur, addition gives P+M≥14. A monochromatic support needs at least 21 points. Thus the two complementary supports cannot both be nonempty since all 24 heavy points together have fewer than 28 elements.

It follows that all heavy triples are unreflected, or all are reflected. One global reflection in the latter case makes every point vector binary. The final construction in Section 4 completes the configuration to a plane.
