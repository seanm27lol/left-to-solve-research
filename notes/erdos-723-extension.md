# Erdős 723, order 12: the 143-line extension step

Let $S$ be a collection of $b$ distinct 13-element subsets of a fixed 157-element point set. Suppose that any two distinct members, called lines, intersect in exactly one point. If $143\le b<157$, one can add a 13-element line meeting every old line exactly once. This proves the mathematical statement of [the catalog's H2](https://lefttosolve.com/p/Erdos723.erdos_723.variants.eq_12.R1.H2).

This is a known consequence of Stephen Dow's general embedding theorem. Its threshold for order $q$ is $q^2-2\sqrt{q+3}+6$; for $q=12$ this is less than $143$. The proof below is a direct specialization using elementary counting. [Dow, *Discrete Mathematics* 45 (1983), 199–207](https://doi.org/10.1016/0012-365X(83)90036-5).

## Point deficits

Write $\delta=157-b$, $r_x$ for the number of lines containing $x$, and $t_x=13-r_x$. The $r_x$ lines have pairwise disjoint 12-point complements of $x$, so $r_x\le13$. Counting incidences and ordered pairs of distinct intersecting lines gives
$$
\sum_x r_x=13b,\qquad \sum_x r_x(r_x-1)=b(b-1).
$$
Consequently
$$
\sum_x t_x=13\delta,\qquad \sum_x t_x(t_x-1)=\delta(\delta-1),\qquad
\sum_x t_x(t_x-2)=\delta(\delta-14).
$$

If $t_x=1$, the 12 lines through $x$ cover $1+12^2=145$ points. Form $B$ from $x$ and the 12 uncovered points. Each line through $x$ meets $B$ only there. A line missing $x$ meets the 12 lines through $x$ in 12 distinct points, leaving exactly one of its 13 points in $B$. Thus $B$ is an admissible new line. This applies at every $1\le\delta<14$, as the last deficit sum is negative while the only integer $t\ge0$ with $t(t-2)<0$ is 1.

## The boundary at 143 lines

Assume $\delta=14$ and there is no point of deficit one. Then each $t_x(t_x-2)$ is nonnegative and the sum is zero. Hence every deficit is 0 or 2. Exactly 91 points have deficit two because $2\cdot91=13\cdot14$. These points each belong to 11 lines.

On these 91 points form a graph $D$ with $x,y$ adjacent if no old line contains them both. For each $x$, the points covered by the lines through $x$ form a set $C_x$ of size $1+12\cdot11=133$. Every point of deficit zero is joined to all others by old lines, so every point outside $C_x$ belongs to $D$. It follows that $D$ is 24-regular.

For $x,y$ adjacent in $D$, the 11 lines through $x$ meet the 11 through $y$ in 121 distinct points. These are exactly $C_x\cap C_y$. Thus $x,y$ have $157-2\cdot133+121=12$ common neighbors. If $x,y$ are distinct and nonadjacent in $D$, they share one old line. The intersection $C_x\cap C_y$ then comprises its 13 points and the distinct intersections of the ten other lines through each of $x,y$. Thus these vertices have $157-2\cdot133+13+100=4$ common neighbors.

Fix $x$ and restrict $D$ to its 24 neighbors. This induced graph is 12-regular. Three pairwise nonadjacent vertices in it would have three neighborhood sets of size 12, with pairwise intersections of size at most 3 because $x$ is already a common neighbor outside the induced graph. Their union would have size at least $36-3\cdot3=27$, which is impossible. Hence the complement $J$ of this induced graph is triangle-free and 11-regular on 24 vertices.

Choose an edge $ab$ in $J$. The sets $A=N_J(a)$ and $B=N_J(b)$ are disjoint independent 11-sets, leaving two vertices outside their union. Each vertex of $A$ has at least nine neighbors in $B$ and conversely, because its own side is independent and only two vertices are outside. If an exterior vertex $z$ had a neighbor on each side, triangle-freeness would permit it at most two neighbors in each side and one among the other exterior vertices. This contradicts degree eleven. So $z$ misses an entire side, yielding an independent 12-set of $J$.

These 12 vertices, together with $x$, give a clique of 13 vertices in $D$. Its points lie on pairwise disjoint collections of eleven old lines, accounting for all $13\cdot11=143$ old lines. Thus this clique is an admissible new line.

## Consequence for the open problem

Iteration completes any configuration of 143 lines with these properties to a plane of 157 lines. At 157 lines all points have degree 13, so any two points are on one of the lines by counting. Conversely, any order-12 plane gives a 143-line configuration by deleting 14 lines. The existence or impossibility of the 143-line seed, the catalog's H1, remains to be proved. The argument here gives a paper proof of H2. No Lean certificate is supplied.

## Smaller seeds: 140, 141 and 142 lines

The same one-line extension conclusion holds for these three smaller sizes. In particular a 140-line seed is equivalent to a full order-12 plane. We make no priority claim for these specialized bounds.

For an old line $B$, summing $r_x$ over its points counts itself 13 times and every other line once. Hence $\sum_{x\in B}t_x=\delta$. For a point $x$ of deficit $a>0$, let $U(x)$ be the points not on any old line through $x$. The pencil at $x$ covers $1+12(13-a)$ points. Its lines have no additional intersections, so
$$
|U(x)|=12a,\qquad \sum_{y\in U(x)}t_y=a(\delta+12-a).
$$
Full points never belong to any $U(x)$. In the graph of noncollinear points of positive deficit (the gap graph), the common-neighbor count for two distinct vertices with deficits $a,c$ is $12-a-c+ac$ for adjacent vertices and $ac$ for nonadjacent vertices. This follows by the same computation as in the 143-line proof, using $(13-a)(13-c)$ or $13+(12-a)(12-c)$ for the common pencil coverage.

At $b=142$, $\delta=15$. If deficit one is absent, every odd-deficit point has $t\ge3$ and contributes at least three to $\sum t(t-2)=15$. There are at most five such points, each on at most ten lines. Each of the 142 lines must contain one, by its odd deficit sum. This is impossible.

### The 141-line case

Now $\delta=16$ and $\sum t(t-2)=32$. Assume no deficit one. Suppose there is an odd deficit. If there is a deficit-three point then each of its ten lines needs another odd point since every line has even deficit sum. These ten further points are distinct. Yet at most $\lfloor32/3\rfloor=10$ odd points exist in total. If the smallest odd deficit is at least five, it must equal five (a deficit of seven costs 35). At most two such points exist, and the eight lines through one cannot each contain another. Thus all deficits are even. From $\sum t(t-2)=32$ the deficits above two consist either of four fours or of a six and a four. In the latter case there are 99 deficit-two points. Each has 24 uncovered neighbors with deficit sum 52. The required excess of four above their baseline 48 forces each one to have the unique deficit-six neighbor. That neighbor has only 72 neighbors. Hence the only possible pattern is four deficit-four points, called heavy, and 96 deficit-two points, called light. Every heavy point has 48 neighbors of total deficit 96, all light. Every light point has exactly two heavy neighbors.

We first recognize the graph induced by the light points. Fix a light point $x$. Its 22 light neighbors induce a graph $B_x$. Among all 24 neighbors, each light neighbor has 12 neighbors by the common-neighbor formula. Three pairwise nonadjacent light neighbors would give three such 12-sets inside 24, with pairwise overlaps of at most three, which is impossible. Thus the complement of $B_x$ is triangle-free. Its minimum degree is at least $21-12=9$. It is bipartite: on a shortest odd cycle of length $l\ge5$, any off-cycle vertex has at most two cycle neighbors, since otherwise an odd arc among its consecutive cycle neighbors closes to a shorter odd cycle (all arcs have length at least two). The cycle itself has no chords. Counting incidences with the cycle therefore gives $9l\le 2\cdot22$, impossible for $l\ge5$.

Each side of this bipartition is a clique in $B_x$ of size at most 11, since a light clique of 13 points including $x$ would touch $13\cdot11>141$ different old lines. Hence both sides have size eleven. Each light neighbor has at most two edges to the opposite side in $B_x$, since it has ten within its own side and at most 12 total. A clique meeting both sides therefore has size at most four. It follows that precisely two light cliques of size 12 contain $x$, and each adjacent pair of light points lies in a unique such clique.

Define the vertices of a new graph $H$ to be the light 12-cliques, and its edges to be the light points, each joining its two cliques. This is simple: two distinct 12-cliques cannot share two light points. Its 96 edges and 12-regularity give 16 vertices. Two light points are neighbors in the gap graph exactly when their edges in $H$ share an endpoint.

Fix a heavy point $e$. Mark the 48 edges in $H$ corresponding to its gap neighbors. Let $a_u$ count marked edges at $u$. For each edge $uv$, the common-neighbor count of $e$ with its light point is 14 if marked, 8 otherwise. All such common neighbors are light. Consequently
$$
a_u+a_v=16\quad\text{on marked edges},\qquad a_u+a_v=8\quad\text{on all other edges}.
$$
The graph $H$ is connected and every edge lies in a triangle, by its degree 12 on 16 vertices. On every edge $a_u\equiv-a_v\pmod8$. It follows from a triangle that $2a_u\equiv0\pmod8$, and by connectedness all the residues are the same. If they are all four modulo eight, the degree sum 96 forces some $a_u=12$. Then the light clique $u$ and $e$ form 13 pairwise noncollinear points touching exactly $12\cdot11+9=141$ distinct old lines. This is a new line.

If the residues are all zero modulo eight, exactly four vertices have $a_u=0$ and twelve have $a_u=8$. Every unmarked edge meets the set of four zeros. Of the nine old lines through $e$, at most three contain another heavy point, because there are only three other heavy points and a pair is on at most one line. Choose one through $e$ alone among the heavy points. Its deficit sum 16 requires six light points. They are collinear to $e$, giving six unmarked edges in $H$. They are also pairwise collinear and therefore define a matching. Six disjoint edges cannot all meet four vertices. This eliminates the last case.

### The 140-line case

Here $\delta=17$ and $\sum t(t-2)=51$. If there is no deficit-one point, all odd deficits are at least three. Every old line contains some odd deficit, and each such point belongs to at most ten lines. There are at least 14 such points; their number is odd because $\sum t=221$ is odd, and is at most $51/3=17$. It cannot be 15: above the baseline cost $15\cdot3=45$ the remaining six units cannot pay for an even deficit at least four (cost at least eight), or upgrade an odd deficit to at least five (extra cost at least twelve). Hence exactly 17 points have deficit three, and all other deficits are zero or two.

Each deficit-three point has 36 gap neighbors with deficit sum 78, hence exactly six of the other 16 deficit-three points are gap neighbors. The number of collinear pairs of such points is therefore $17\cdot10/2=85$. Every old line contains one, three or five of these points by its deficit sum of 17. Write $b_3,b_5$ for the line counts with three and five. Their 170 point-line incidences across 140 lines imply $b_3+2b_5=15$. Counting the 85 collinear pairs gives $3b_3+10b_5=85$. This would give $b_5=10$ and $b_3=-5$, a contradiction.

[Kernel-checked local graph lemmas](../lean/research/Erdos723Local.lean) prove the 24-vertex neighborhood assertion used above. The incidence-to-graph construction still needs a Lean formalization before the catalog can accept H2.
