# The four-clique-free case of Erdős 151 through threshold eleven

For a finite graph $G$, call a set *free* if it contains no maximal clique of $G$ with at least two vertices. Its complement is a clique transversal. Let $H(n)$ be the least independence number among triangle-free graphs on $n$ vertices.

**Theorem.** If $G$ is $K_4$-free on $n$ vertices and $H(n)\le11$, then $G$ has a free set of at least $H(n)$ vertices.

The Left to Solve proof by @princek0 handles $H(n)\le9$. We use its more general weighted neighborhood inequality and argument reducing to a minimal edge-Ramsey core. The cases $H(n)=10,11$ below are mathematical deductions from those lemmas. The candidate Lean proof covers $H(n)=10$. The argument for $H(n)=11$ below is a paper proof. The unrestricted problem remains open. [Existing verified proof and lemmas](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/proofs/Erdos151.erdos_151.variants.cliqueFree_four.R2.H1.lean) · [Problem](https://lefttosolve.com/p/Erdos151.erdos_151.variants.cliqueFree_four).

## The core inequality

Write $h=H(n)$ and $D=h-1$. Any open neighborhood is free, since its center extends every clique it contains. A degree at least $h$ settles the problem. Otherwise the previously verified core reduction either gives the required conclusion already or supplies $C\subseteq G$ on the same vertex set, with every vertex of positive core degree having degree at least eight. It also supplies a vertex $v$, a set $S=N_C(v)$ with $8\le d=|S|\le D$, and an outsider set $A$ disjoint from $S\cup\{v\}$. Put $a=|A|$ and let $c$ be the number of $G$-edges from $S$ to $A$. The conclusion of the weighted neighborhood inequality is
$$
  2n+d^2+2d+c\le2a+2Dd+2.
$$
Each $x\in A$ is individually safe: its neighbors in $S$ are independent in $G$, and every edge from $x$ to $S$ belongs to a triangle of $G$. Hence adjoining any independent subset of $A$ to $S$ preserves freeness. This is the statement of the public lemmas `Erdos151Research.bound_of_core_case` and `Erdos151.WeightedNeighborhood.safe_outsider_bound`, together with the free-neighborhood argument; the core and the graph need not have the same edge set.

More generally, mark those vertices of $A$ with a neighbor in $S$. For $T\subseteq A$ suppose:

* $T$ contains at most one marked vertex.
* $G[T]$ contains no triangle and every edge of $G[T]$ extends to a triangle in $G[A]$.

Then $S\cup T$ is free. A triangle with two vertices from $T$ and one from $S$ needs two marked vertices. A triangle with one vertex from $T$ is ruled out by individual safety. An edge in $S$ extends via $v$, an edge between $S$ and $T$ extends by safety, and an edge in $T$ extends by assumption. $G$ has no cliques of order four.

## Threshold ten

The triangle-free circulant on $\mathbb{Z}/38\mathbb{Z}$ with unsigned connection distances $1,3,5,12,19$ has independence number at most nine. The accompanying verifier exhausts the independent-set decision problem. Restricting this graph shows $h=10$ implies $n\ge39$. For $D=9$ the core degree $d$ is 8 or 9.

* If $d=8$, the inequality gives $a\ge n-33\ge6$. Any four vertices of $A$ contain two nonadjacent vertices, since $G$ is $K_4$-free. They can be adjoined to $S$.
* If $d=9$, the inequality gives $2a\ge 2n-65$. One safe outsider suffices.

Indeed $n\ge37$ suffices for this extension; the circulant gives a little room in the first inequality.

## Threshold eleven

The published 46-vertex triangle-free graph with independence number ten gives $h=11\Rightarrow n\ge47$ by restriction. The companion verifier independently checks its adjacency list. [Exoo, Theorem 1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p68/pdf/) · [Adjacency list](https://cs.indstate.edu/ge/RAMSEY/g.3.11.46).

Now $D=10$. For $d=10$, the inequality gives $2a\ge2n-82$, leaving a safe outsider. For $d=9$, it gives $2a\ge2n-83$, leaving at least four outsiders and hence a nonadjacent pair. It remains to handle $d=8$. In that case,
$$
a\ge6,\qquad c\le2a-12.
$$
It suffices to find three suitable outsiders.

If $G[A]$ has an independent triple, the extension follows from individual safety. Otherwise write $F=G[A]$, so $F$ is $K_4$-free and $\alpha(F)\le2$. Then $a\le8$ by $R(3,4)=9$. For completeness, any triangle-free graph on nine vertices has an independent four. If a vertex has degree at least four, take its neighborhood. If any vertex has degree at most two, its six or more nonneighbors contain an independent triple by $R(3,3)=6$. The remaining possibility, a 3-regular graph on nine vertices, contradicts the handshaking lemma.

If $a=6$, then $c=0$. If some $y\in A$ has three neighbors in $F$, choose any three of them. They induce no triangle, as $G$ is $K_4$-free, and any edge among them extends via $y$. Otherwise $\Delta(F)\le2$. A triangle-free $F$ has an independent triple by $R(3,3)=6$. If $F$ has a triangle then it is a component; take two of its vertices and one outsider from another component. This triple meets the two extension conditions.

Finally let $a=7$ or $8$. Within $F$, the other vertices nonadjacent to any given vertex form a clique, since $\alpha(F)\le2$. This clique has size at most three, so every vertex of $F$ has degree at least $a-4\ge3$. The number of marked vertices is at most $c$, hence there are at least $12-a$ unmarked vertices. The sum of their degrees is at least
$$
(12-a)(a-4)>a.
$$
Count incidences by their other endpoints. Some $y$ has at least two unmarked neighbors. Select two such neighbors and a third neighbor of $y$. As in the six-vertex case, their triple is triangle-free and any edge extends via $y$. At most one selected neighbor is marked. It follows that $S$ together with this triple is free and has eleven vertices.

The program independently checks the two Ramsey witnesses and, as a separate audit of the last argument, exhausts the small labelled $K_4$-free graphs of independence number at most two. It checks 2,812, 13,842 and 17,640 graphs on six, seven and eight vertices, respectively. This gives no conclusion for $H(n)\ge12$.

[Reproduce the finite graph checks](../checks/erdos151_threshold_eleven.py) · [Dated threshold-ten Lean source in the author's fork](https://github.com/seanm27lol/open-math-agents/commit/d93667354188ea834c58997e743372b31dcebd88).

The threshold-ten proof was filed from @seanm27lol's GitHub fork as [Left to Solve submission #9158](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9158). The checker verdict is recorded on that pull request.
