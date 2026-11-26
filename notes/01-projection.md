# The higher-rank eigenvalue inequality

**Statement.** Let $A\succeq0$ be real symmetric of size $n$ and $D=\operatorname{diag}(A)$ the diagonal matrix of its diagonal entries. Write $H=A-kD$, with eigenvalues $\lambda_1\ge\cdots\ge\lambda_n$, where $1\le k\le n$ is integral. Then

$$
\sum_{i=m}^{n-m(k-1)}\lambda_i\le 0
$$

for every integer $m\ge1$ for which the block is nonempty, equivalently $mk\le n$. Taking $m=1$ answers the main question. The source asks specifically about extending this to $m>1$. Its author and another commenter reported having a proof for $m=1$; neither posted a proof for the extension in that thread. The following is a proof developed for this search. Global priority and independent expert review are undetermined.

**Elementary route for the original question.** For any rank-$d=n-k+1$ orthogonal projection $P=UU^T$, let $u_i^T$ be the rows of the isometry $U$. Delete any zero rows. With $p_i=\|u_i\|^2\le1$, the matrix $E=\sum u_i u_i^T/p_i\succeq\sum u_i u_i^T=I_d$ has trace at most $n$. Its largest eigenvalue is at most $n-d+1=k$. The normalized Gram matrix with rows $u_i^T/\sqrt{p_i}$ has the same nonzero eigenvalues as $E$. Consequently $P\preceq k\operatorname{diag}(P)$, also on the removed zero rows. Thus $\operatorname{tr}(PH)=\operatorname{tr}(A(P-k\operatorname{diag}P))\le0$. Maximizing over rank-$d$ projections gives the claimed leading sum by Ky Fan.

**Proof of the higher-$m$ extension.** For $k=1$, $H$ has zero trace and each lower tail of an ordered mean-zero list has nonpositive sum. For $k>1$ with $n=mk$, the block consists of $\lambda_m$. Delete every zero diagonal entry of $A$ together with its zero row and column (positivity gives $|a_{ij}|^2\le a_{ii}a_{jj}$). If $h$ coordinates survive, $C=D^{-1/2}AD^{-1/2}\succeq0$ on them and $\operatorname{tr}C=h\le n=mk$. Thus fewer than $m$ eigenvalues of $C$ are strictly greater than $k$. Congruence preserves positive inertia, and restoring zeros preserves its count, giving $\lambda_m(H)\le0$. This also covers $A=0$.

It remains to treat $n>mk$ and $k>1$. Set $s=n-m(k-1)>m$ and $r=s-m+1$. The identity $n=s+m(k-1)<ks$ will be used. Given any $s$-dimensional subspace $S\subset\mathbb R^n$ and its projector $P_S$, we construct a matrix $Q$ such that

$$
0\preceq Q\preceq P_S,\qquad \operatorname{tr}(Q)=r,\qquad Q\preceq k\operatorname{diag}(Q). \tag{1}
$$


First take $S$ in general position. Namely, let $U\in\mathbb R^{n\times s}$ have orthonormal columns spanning $S$, and assume every $s\times s$ row submatrix is nonsingular. Every row $u_i^T$ then satisfies $0<\|u_i\|^2<1$: zero is excluded by nonsingularity, and equality to one puts the $i$th coordinate vector in $S$, making the $n-1\ge s$ other rows orthogonal to a nonzero vector. Over positive definite $T\preceq I_s$, minimize

$$
F(T)=\sum_{i=1}^n\log q_i-k\log\det T,\qquad q_i=u_i^T T u_i.
$$

Increasing the scale decreases $F$ whenever feasible, since $F(cT)-F(T)=(n-ks)\log c$. We may restrict to $\lambda_{\max}(T)=1$. A minimizer of that normalized problem is also a global minimizer on the full feasible set, since scaling any feasible matrix up to maximum eigenvalue one can only decrease its objective. To show an interior-of-the-positive-cone minimizer exists, let $I$ index the $s$ smallest $q_i$. Define $a=\min_I\det(U_I)^2>0$ and $b=\min_I\lambda_{\min}(U_I^T U_I)>0$ over all such sized subsets. Hadamard's inequality applied to $U_I T U_I^T$ gives $\prod_{i\in I}q_i\ge a\det T$. Also $\sum_{i\in I}q_i\ge b\operatorname{tr} T\ge b$, so every $i\notin I$ has $q_i\ge b/s$. It follows that $F(T)\ge\log(a(b/s)^{n-s})+(1-k)\log\det T\longrightarrow+\infty$ at the singular boundary. Compactness after setting a positive lower bound on the determinant proves existence.

At a minimizer put $B=\sum_i u_i u_i^T/q_i$ and $G=B-kT^{-1}$, the gradient for the trace inner product. The direction $-vv^T$ is feasible for a sufficiently short step for each $v$, so $G\preceq0$. For $v$ in the eigenspace sum $V$ of $T$ for eigenvalues less than one, $+vv^T$ is also locally feasible. Therefore $v^TGv=0$, and $Gv=0$ by semidefiniteness. The operator $E=T^{1/2}BT^{1/2}\preceq kI$ equals $kI$ on $V$. Further $B\succ I$, because $q_i\le\|u_i\|^2<1$ and $\sum_i u_i u_i^T=I$. Thus every unit vector in $V^\perp$, on which $T=I$, has $v^TEv>1$. Since $\lambda_{\max}(T)=1$, $V^\perp\ne0$. Writing $b_0=\dim V$ and observing $\operatorname{tr}E=\sum_i q_i/q_i=n$, we have

$$
n>kb_0+(s-b_0),\quad b_0<\frac{n-s}{k-1}=m,\quad \operatorname{tr}T\ge s-b_0\ge r.
$$

Set $X=UTU^T$; its diagonal is $q$. The matrix $Y=\operatorname{diag}(q)^{-1/2}UT^{1/2}$ has $Y^TY=E\preceq kI$, so $YY^T\preceq kI$. Conjugation gives $X\preceq k\operatorname{diag}X$. Also $X\preceq P_S$. The rescaling $Q=rX/\operatorname{tr}X$ proves (1).

Every $S$ is a limit of the generic subspaces used above: perturb a full-rank basis to avoid the finitely many zero-minor hypersurfaces and orthonormalize by right multiplication by an invertible matrix. Orthogonal projectors converge. The corresponding $Q$'s are contractions, so a convergent subsequence and the closed inequalities in (1) prove (1) for arbitrary $S$.

Finally take $S$ spanned by top $s$ eigenvectors of $H$. Positivity of $A$ and (1) give $\operatorname{tr}(QH)=\operatorname{tr}(A(Q-k\operatorname{diag}Q))\le0$. In an eigenbasis of $H|_S$, the diagonal weights of $Q$ have sum $r$ and lie in $[0,1]$. The smallest possible weighted sum is the sum of the bottom $r$ among those $s$ eigenvalues. Therefore $\lambda_m+\cdots+\lambda_s\le\operatorname{tr}(QH)\le0$, as asserted.

**Checks and provenance.** The proof permits singular and zero matrices, eigenvalue multiplicities, zero rows, and coordinate or otherwise nongeneric top eigenspaces. The special argument at $n=mk$ avoids using strict coercivity where $n=ks$. The easy bound for $m=1$ alone cannot control interior sums since those sums need not be convex in $A$. Compare the frame normalization variational construction with radial isotropic position in Hardt and Moitra's work; that paper supplies context only and is not invoked as a proof of (1).

[Catalog](https://lefttosolve.com/p/mo-334087) · [Original and comments](https://mathoverflow.net/questions/334087/sum-of-eigenvalues-is-nonpositive) · [Ky Fan's principle, Overton–Womersley](https://doi.org/10.1137/0613006) · [Hardt–Moitra, radial isotropic position](https://proceedings.mlr.press/v30/Hardt13.html).

Numerical audit with fixed random seed 334087: 14,448 ordered-block sums for trace-one PSD matrices in dimensions 2 to 24, with several ranks and inserted zero rows. The largest observed violation was $1.85\times10^{-15}$, consistent with floating-point roundoff; none exceeded $10^{-12}$. The proof above does not use the experiment.

More closely related, Nikhil Bansal's [Theorem 2.5](https://theoryofcomputing.org/articles/v020a006/v020a006.pdf), citing Bansal–Garg, supplies covariance matrices supported on a prescribed subspace with $U\preceq k\operatorname{diag}(U)$, diagonal entries at most one, and guaranteed trace at least $s-n/k$ when positive. For the variational step here the needed cap is $U\preceq P_S$ and the target trace is $s-m+1$. The statement of that theorem does not directly provide these conditions.
