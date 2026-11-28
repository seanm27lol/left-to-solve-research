# Completion of 138 partial lines in order twelve

**Research by Sean Mahdavian (@seanm27lol) with OpenAI Codex assistance.**

**Theorem.** Every family of 138 distinct 13-subsets of 157 points, in which every two subsets have exactly one point in common, extends on the same points to a projective plane of order 12.

Thus constructing such a seed would settle the order-12 existence question affirmatively. The proof assumes the seed. It gives a paper reduction of Erdős 723's order-12 case and does not settle existence. The argument uses the [139-line extension theorem](./139-extension.md), the published classification of connected graphs of least eigenvalue at least $-2$, and an [exact integer verifier](./verify_138_profiles.py).

## 1. Deficits and candidate profiles

Write $A$ for the old lines' incidence matrix, $r_x$ for the number through $x$, and $t_x=13-r_x$ for its deficit. Distinct points form a gap when no old line joins them. All deficits are nonnegative by pencil size. If $t_x=1$, the point $x$ and the twelve points missed by its pencil form a new 13-point line meeting every old line exactly once. This construction reaches 139, so the preceding theorem applies. In the rest of the proof all positive deficits are at least two.

We use the matrix identities of the preceding theorem with 138 rows instead of 139. In detail, $AA^{\mathsf T}=12I+J$, where $J$ denotes an all-ones matrix of the indicated dimensions. For $K=12I+J$ on the points we have $AK^{-1}A^{\mathsf T}=I$ since $K^{-1}=(I-J/169)/12$. The residual $K-A^{\mathsf T}A$ is therefore positive semidefinite of rank 19. Choose vectors $v_x$ spanning $\mathbb R^{19}$ with this Gram matrix. Their squared norms are $t_x$, and two distinct vectors have inner product one for a gap pair and zero otherwise. For $s=(\sum_x v_x)/13$ we have

$$
\lVert s\rVert^2=19,\qquad s\cdot v_x=t_x,\qquad
\sum_{x\in L} v_x=s\quad\text{for each old line }L.
$$

Indeed the rows of the residual sum to $13t_x$, and left-multiplication by $A$ gives $\mathbf 1t^{\mathsf T}$.

Every old line has deficit sum $19$ because the degrees of its 13 points sum to $138+12$. Summing the deficits over a pencil and subtracting the repeated center gives

$$
\sum_x t_x=247,\qquad \sum_x t_x(t_x-2)=95,\qquad
|N(x)|=12t_x,\qquad \sum_{y\in N(x)}(t_y-2)=t_x(7-t_x),
$$

where $N(x)$ is the set of gap neighbors. For the second identity, use $\sum_x(13-t_x)t_x=138\cdot19$. Full points have no gap neighbors, so the last identity forces $t_x\le7$. As in the 139-line proof, distinct joined points of deficits $a,b$ have $ab$ common gap neighbors. This follows by counting the union of the two pencils. Their common covered points are the 13 points of their common line and $(12-a)(12-b)$ intersections off that line.

Call deficit-two points light and points of greater deficit heavy. Let $n_t$ be the population of type $t$, $m=n_2$, and $E$ the total number of gap pairs with one light and one heavy. The exact verifier carries out the following finite enumeration.

1. Enumerate all nonnegative heavy populations satisfying $\sum_{t=3}^7 t(t-2)n_t=95$. Recover $m$ from $2m+\sum_{t=3}^7tn_t=247$ and reject populations of total size exceeding 157.
2. At each type $t$ that occurs, enumerate the neighbor counts $g_j$ satisfying $0\le g_j\le n_j-\mathbf1_{t=j}$, $\sum_jg_j=12t$ and $\sum_j(j-2)g_j=t(7-t)$. Reject a population if any occupied type has no allowed vector. For each pair of types $t,j$, the intervals for the two counts $n_tg_j$ and $n_jg_t$ must overlap. These intervals use minima and maxima over their respective choices of neighbor vector.
3. Compute the lower bound $E_0$ for $E$ by taking the larger of $m\min(24-g_2)$ over light neighborhoods and $\sum_{t>2}n_t\min(g_2)$ over the respective heavy neighborhoods. The sum of the light vectors has squared norm $26m-E$ and inner product $2m$ with $s$. Thus Cauchy–Schwarz requires $4m^2/(26m-E_0)\le19$.

There are 48 initial histograms and 39 after these necessary tests. In each of the 39, $m>36$, the minimum allowed light degree exceeds four, and

$$
\frac{4m^2}{26m-E_0}\ge\frac{529}{29}>18.
$$

## 2. The light graph is connected

Let $G$ be the graph of light points with gap edges. If $G$ were disconnected, its smallest component would have a size $n$ satisfying $1+\min g_2\le n\le m/2$, where the minimum is over light neighborhoods. For each heavy point $y$, let $T_y$ be its number of light gap neighbors and $c_y$ the number in this component. Each light in the component contributes $2(7-2)=10$ units of heavy-neighbor excess. Any pair of lights from opposite sides is joined by an old line and has exactly four common gap neighbors, necessarily heavy. Consequently

$$
\sum_y(t_y-2)c_y=10n,\qquad \sum_yc_y(T_y-c_y)=4n(m-n).
$$

Let $T_t$ be the largest allowed $g_2$ for a point of type $t$. For every integer $u$, the two equalities imply

$$
4n(m-n)\le 10nu+\sum_{t>2}n_t
\max_{0\le c\le\min(n,T_t)}\{c(T_t-c)-u(t-2)c\}.
$$

The maximum is over integers. This is an upper bound because $T_y\le T_{t_y}$ and $c_y\ge0$. The verifier uses the smallest of these upper bounds for $-20\le u\le50$. Across all 1,270 population-and-component-size pairs the left side exceeds the bound by at least 796. The finite range for $u$ supplies a contradiction for every pair; it imposes no restriction on a prospective plane. This proves connectivity.

## 3. Integer coordinates of the residual Gram representation

As $2I+\operatorname{Adj}(G)$ is a principal Gram submatrix, the least eigenvalue of $G$ is at least $-2$. By the Cameron–Goethals–Seidel–Shult theorem the connected graph $G$ on more than 36 vertices is a generalized line graph. A nonempty cocktail-party attachment would supply distinct nonadjacent lights with identical neighborhoods. Their common light-neighbor count would exceed four, since the minimum light degree exceeds four. The pencil count bounds their total common gap neighbors by four. Thus $G$ is the ordinary line graph of a connected simple graph $H$ without isolated vertices. For the classification and the precise generalization of line graphs, see [Cameron, Goethals, Seidel and Shult](https://doi.org/10.1016/0021-8693(76)90162-9) and [Acharya and Jiang, introduction and Definition 2.1](https://doi.org/10.1017/S0963548325100278).

The light vectors have the same Gram matrix as the unsigned edge vectors $e_i+e_j$ for edges $ij$ of $H$, so their spans are isometric. Put $h=|V(H)|$. If $k_i$ are the degrees of $H$, then $\sum k_i=2m$ and $\sum k_i^2=26m-E$ by counting the degrees in its line graph. Thus $h\ge4m^2/(26m-E)>18$. The edge vectors span $h$ dimensions in the nonbipartite case and $h-1$ in the bipartite case, since vectors perpendicular to all edges have coordinates alternating in sign along edges.

If $H$ is nonbipartite, $h=19$. Identify the light vectors isometrically with their edge representatives. They span the residual space and satisfy $s\cdot(e_i+e_j)=2$, hence $s=\mathbf1$. For any point vector $w$, its edge-coordinate sums $w_i+w_j$ are integers. Following an odd cycle and using connectivity shows the coordinates are all integers or all strict half-integers. In the latter case $4\lVert w\rVert^2$ would be a sum of 19 odd squares, which is odd, contrary to integrality of $\lVert w\rVert^2$.

If $H$ is bipartite, let its part sizes be $a,b>0$. Now $h=a+b$ is 19 or 20. Write $u$ for the vector equal to $1$ on the first part and $-1$ on the second. The edge vectors span $u^\perp$. The unique vector in that span with dot product two with every edge is the projection of $\mathbf 1$ onto $u^\perp$. Its squared norm is $h-(a-b)^2/h=4ab/h$. If $h=20$ the edges already span the 19-dimensional residual space, so this norm must equal $\lVert s\rVert^2=19$. That would give $(a-b)^2=20$, impossible.

Therefore $h=19$. Extend the edge-space isometry to the full 19-dimensional residual space. The image of $s$ has the same projection and norm as $\mathbf 1$, so a reflection across $u^\perp$, if necessary, makes $s=\mathbf 1$. For each point vector $w$, integer edge sums and connectivity imply that its coordinates have the form $z_i+u_i\alpha$ for integers $z_i$ and some real $\alpha$. Since $s\cdot w=t_x$ is an integer, $(a-b)\alpha$ is an integer. The part sizes sum to 19 and are both positive, so $0<|a-b|<19$. Write $\alpha=p/q$ in lowest terms with $q>0$; then $q\mid |a-b|$. Multiplying the integer squared norm of $w$ by $q^2$ and reducing modulo $q$ gives $19p^2\equiv0\pmod q$, so $q\mid19$. Since 19 is prime, $q=1$.

In both cases every vector $w$ is integral and $s=\mathbf1$. The identity $s\cdot w=\lVert w\rVert^2$ implies $\sum_i w_i(w_i-1)=0$, forcing every coordinate to be zero or one. The 19 coordinates give the 19 new lines. Each contains 13 points by $\sum_xv_x=13s$. Each meets each old line once since $\sum_{x\in L}v_x=s$. A pair of points belongs to one new line exactly when the pair was missing. All 157 lines are distinct, and every point lies on 13 lines. Counting the other lines through the 13 points of any line gives $13\cdot12=156$, so all pairs of lines meet. This completes the plane.
