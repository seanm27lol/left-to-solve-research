# Completion of 139 lines in order twelve

**Theorem.** Let 139 distinct 13-subsets of a 157-set meet pairwise in exactly one point. A further 13-subset meets each of them exactly once. If every old point has degree different from 12, all eighteen missing lines can be constructed at once. Together with the 140-through-156 extensions this makes a 139-line seed sufficient for an order-twelve projective plane. This theorem does not construct a seed.

The ingredients are an exact enumeration of 23 integer histograms, the Cameron–Goethals–Seidel–Shult classification, and an analysis of the exceptional bipartite case that survives the classification. The theorem on small least eigenvalue is available in Brouwer–Haemers, *Spectra of Graphs*, Theorem 8.4.1, https://homepages.cwi.nl/~aeb/math/ipm/ipm.pdf. The assertions below about 139 lines are research arguments by Sean Mahdavian with OpenAI Codex. No claim of historical priority is made.

## The missing Gram matrix

Write A for the 139 by 157 binary incidence matrix, r_x for a column sum, and t_x=13-r_x for its deficit. A pencil has pairwise disjoint lines off its center, hence r_x≤13. If r_x=12, take x and the twelve points missed by its pencil. Every line outside the pencil meets its twelve members in distinct points away from x and contains exactly one of those twelve missed points. This gives the required new line. Assume henceforth that every positive deficit is at least two.

Put G=12I+J−AᵀA. Its diagonal entries are t_x and its off-diagonal entries are 1 for a pair on no old line, called a gap, and 0 otherwise. The matrix is positive semidefinite of rank 18. Indeed AAᵀ=12I+J and A1=13·1. For K=12I+J of size 157, K⁻¹=(I−J/169)/12. Therefore AK⁻¹Aᵀ=I, and G=K¹ᐟ²(I−UᵀU)K¹ᐟ² for U=AK⁻¹ᐟ². Thus the points have real Gram vectors of squared length t_x in dimension 18. Points of deficit zero are orthogonal to all points.

Direct multiplication gives G1=13t, GAᵀ=t·1ᵀ, and G²=12G+ttᵀ. Write U(x) for the gap neighbors of x. For t=t_x this gives |U(x)|=12t, and ∑_{y∈U(x)}t_y=t(30−t). For the latter identity, each old line has deficit sum 18 by GAᵀ=t·1ᵀ together with the usual line-degree count (an old line meets all 138 others once, so its degree sum is 13+138=151). Consequently Gt=30t by applying G² to an old line vector. For two distinct deficits t,s their common gap-neighbor count is ts for a joined pair and 12−t−s+ts for a gap pair. All positive deficits satisfy t≤6, since their 12t gap neighbors have deficits at least 2. Also ∑t_x=234 and ∑t_x(t_x−2)=72. The second identity follows from ∑r_x(r_x−1)=139·138 and ∑r_x=139·13.

## Five possible histograms

A light has deficit two, and a heavy has larger deficit. The following are necessary profiles, with columns ordered by deficit. The final column lists degrees in the gap graph induced on the light points, with multiplicities.

| t=0 | t=2 | t=3 | t=4 | t=5 | t=6 | Light degrees |
|---:|---:|---:|---:|---:|---:|:--|
|46|108|0|0|0|3|108 of 22|
|48|102|0|6|0|1|72 of 21, 30 of 20|
|49|99|0|9|0|0|99 of 20|
|51|86|19|0|1|0|55 of 18, 31 of 16|
|52|81|24|0|0|0|81 of 16|

Here is the finite certificate for completeness. Write P_s for the number at deficit s. Enumerate nonnegative P₃,P₄,P₅,P₆ with ∑s(s−2)P_s=72, then recover P₂ and P₀ from ∑sP_s=234 and ∑P_s=157. There are 23 possible histograms. Enumerate all possible old line types b_s from ∑b_s=13, ∑s b_s=18, and 0≤b_s≤P_s. For each type t actually present, the counts g_s of its gap neighbors satisfy ∑g_s=12t, ∑(s−2)g_s=t(6−t), g₀=0 and 0≤g_s≤P_s−[s=t]. Keep g only when some multiset of 13−t possible old line types, each containing a t point, has total coordinate P_s−g_s+(12−t)[s=t] at every s>2. This counts every joined point once except the center, counted 13−t times. The other two coordinates are already determined by the size and weight of each line. Every t actually present needs a surviving g. For each t,s the intervals P_t[min g_s,max g_s] and P_s[min g_t,max g_t] must overlap by symmetry of gaps. The accompanying Python verifier performs every one of these finite tests, with rational or integer arithmetic only.

The light degrees in the table follow from the neighbor-deficit sum. For the second row a deficit-six point has 72 neighbors, all light. A light seeing it has two gap neighbors of deficit four and the other lights have four. For the fourth row the deficit-five point meets five deficit-three and 55 light points in gaps. A light seeing it meets five more heavies, and every other light meets eight. In the other three rows the neighbor-deficit sum determines the counts directly.

## The light graph is a line graph

Let B be the light adjacency matrix. The principal submatrix S=2I+B is positive semidefinite of rank at most 18. Here is a uniform check that the light graph is connected in every row. With N lights, d their degrees, set T=2N, Q=4N+∑d, a=2+(∑d)/N, b=2+min d. If there were at least two components, the two top eigenvalues λ,μ of S would satisfy λ≥a and μ≥b by the all-ones Rayleigh quotient globally and on each component. Cauchy–Schwarz on at most 16 remaining nonzero eigenvalues would give
(T−λ−μ)²≤16(Q−λ²−μ²).
The difference of these sides is increasing in λ,μ throughout λ≥a, μ≥b: the derivative with respect to λ is 34λ+2μ−2T>0, and likewise for μ. In the five rows its values at (a,b) are respectively 1728, 17808/17, 1188, 1201/1849 and 324. These are strictly positive.

CGSS now applies since every row has more than 36 light vertices. A connected graph of smallest eigenvalue at least −2 with more than 36 vertices is a generalized line graph. A nontrivial cocktail-party attachment in a generalized line graph has a pair of nonadjacent vertices with identical open neighborhoods. Such a pair here would have at least 16 common light neighbors, whereas nonadjacent lights have only 4 common gap neighbors in total. Therefore B is the line graph of an ordinary connected simple graph H, with isolated root vertices omitted. Each light corresponds to one edge of H. Its Gram vector can be represented by e_u+e_v for that edge, since these vectors have precisely the Gram matrix S.

Let m=|V(H)| and k_u be the degrees in H. A star is a clique of lights and its members touch 11 distinct old lines each, so 11k_u≤139 and k_u≤12. On each edge uv, k_u+k_v=d(uv)+2≥18, giving k_u≥6. The unsigned incidence rank is m if H is nonbipartite, m−1 otherwise: a vector orthogonal to every edge has coordinates alternating by sign along all edges, and an odd cycle forces every coordinate zero. In particular m≤19. In the first four rows some edge has endpoint degree sum at least 20, impossible in a bipartite graph on at most 19 vertices. In the nonbipartite case m=18: by Cauchy–Schwarz,
m≥(2N)²/∑_{uv∈E(H)}(d(uv)+2),
using ∑k_u²=∑_{uv}(k_u+k_v). The ratios in all five rows exceed 17, and the rank upper bound is 18. In the last row H can also be bipartite. All edge degree sums are 18, so its two parts have constant degrees k and 18−k, both in [6,12] and both divisors of 81. They must be 9 and 9, giving H=K₉,₉.

## Reconstructing the missing lines when H is nonbipartite

In this case the edge vectors span all of ℝ¹⁸, so the other point vectors have coordinates in this same representation by Gram isometry. For any heavy vector w, each w_u+w_v on an edge is 0 or 1. Along an odd cycle the coordinates are integers or half-integers, and connectivity makes the fractional part the same everywhere. If they were strict half-integers then 4‖w‖², a multiple of 4, would be a sum of 18 odd squares and hence 2 modulo 4. Thus w is integral. If w_u≤−1, its at least six neighbors have coordinates at least 1, giving ‖w‖²≥7. If w_u≥2, each neighbor has coordinate at most −1. Both contradict t_x≤6. Thus every heavy vector is binary. The zero and light vectors are already binary.

Append to A the 18 rows of this coordinate matrix, obtaining a square binary matrix N with NᵀN=12I+J. Every column sums to 13 since the appended vector has t_x ones. As N is nonsingular, NᵀN1=169·1 implies N1=13·1. Both row and column sums are 13, so NJ=JN and NNᵀ=12I+J by similarity. The augmented rows are the lines of a complete plane.

## Reconstructing the bipartite case

The remaining possibility has 81 lights and 24 heavies of deficit three. Identify the lights with cells of a 9 by 9 grid. An edge is represented in ℝ¹⁸ by the sum of a row and a column basis vector. The orthogonal complement of the edge span is generated by the unit vector h=(1,…,1,−1,…,−1)/√18. The Gram dimension is 18, so extend the isometry into these coordinates for all the heavies.

A heavy has nine heavy gap neighbors and 27 light gap neighbors, from the neighbor formula. On the grid its marked cells (light gap neighbors) have indicator function equal to a row coordinate plus a column coordinate. Both coordinate lists cannot vary: every difference within either list is integral, so if both were nonconstant the range of their sums would be at least two. Thus the 27 marked cells form three whole rows or three whole columns. Two distinct heavies cannot give the same triple, since they would have 27 common light neighbors and the maximum total from the common-neighbor formula is 15.

Each light is adjacent to eight heavies. If r_i counts the row triples containing row i and c_j the column triples containing column j, then r_i+c_j=8 gives constant values r,c. Two cells in different rows in the same column have 12 common gap neighbors, seven of them lights. Thus each row pair belongs to 5−c row triples. Counting row pairs in row triples gives 36(5−c)=3·(3r)=9r. With r+c=8 this yields r=c=4 and exactly 12 triples on each side.

A heavy's indicator on the grid is represented by the canonical binary vector w of its row or column triple. The true vector and w have the same projection onto the light span. This projection has squared norm 3−9/18=5/2, so the true vector differs from its projection by ±h/√2. For a row triple and a column triple the dot product of their projections is 1/2 (their canonical vectors have disjoint support, with opposite h-coordinates). Consequently when such a pair lies together on an old line, their perpendicular coordinates have opposite signs.

Each heavy lies on ten old lines and is joined to fourteen of the other 23 heavies. Its old lines each contain an even number of heavies by their deficit sum 18. There are thus at least eight lines through it with exactly two heavies: each line needs at least one companion, and the fourteen companions permit at most two lines with three or more companions. Such a two-heavy line also contains six lights, necessarily a matching of six grid cells. A row-heavy on that line must be marked on precisely the three unused rows, and a column-heavy likewise for the three unused columns. Distinct triples therefore force one heavy of each kind. The heavy's at least eight partners on these lines are all distinct, and all have perpendicular sign opposite to its own. Any two row-heavies must share a partner among the twelve column-heavies, since each has at least eight partners. All row-heavies consequently have one common sign, and every column-heavy has the opposite sign. Reflecting in the light span if necessary makes these signs exactly the canonical signs for every triple. All vectors are now binary. The preceding square-incidence argument completes the plane.
