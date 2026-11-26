# Spectral bounds and matrix reconstruction

## MO 334154. Exact spectral ellipse for a nearest-neighbor cyclic Markov chain

**Target.** For an $n$-cycle ($n\ge3$) whose steps from $i$ go backward and forward with probabilities $a_i,b_i>0$, $a_i+b_i=1$, set $p=(2n)^{-1}\log(\prod_i a_i/\prod_i b_i)$. For $p\ne0$, all eigenvalues $z$ of its transition matrix satisfy $(\Re z)^2+(\Im z/\tanh p)^2\le1$.

**Literature resolution and derivation.** Set $R=M-I$. It has nonnegative off-diagonal rates, column sums zero, maximum escape rate $1$, and cycle affinity $F=2n|p|$ after choosing the favorable orientation. For a nonreal eigenvalue $\lambda=z-1$, Theorem 1, equations (3)–(4), of Kolchinsky, Ohga and Ito gives for the same angle $\theta=\pi\omega/n$ in $(0,\pi/2)$

$$
|\Im z|\le(1-\Re z)\tanh |p|\cot\theta,\qquad
|\Im z|\le(1+\Re z)\tanh |p|\tan\theta .
$$

Both right sides are nonnegative since $|z|\le1$. Multiplication cancels the unknown winding angle and gives the ellipse exactly. A real eigenvalue already lies in $[-1,1]$. If $p=0$, the equal products give detailed balance by constructing the positive reversible measure successively along the cycle. Diagonal similarity to a symmetric matrix then puts the spectrum on the limiting line segment. Uniform $a_i=a,b_i=b$ yields $z_j=\cos(2\pi j/n)\pm i(a-b)\sin(2\pi j/n)$ and $a-b=\tanh p$, checking sharpness. Bounding $|\Im z|$ alone leaves a rectangle and does not prove this result. This is an application of a known theorem: the 2019 paper conjectured the ellipse; the 2026 proof supplies the two inequalities. The 2025 edge-force bound uses a different force parameter and by itself does not suffice.

[Catalog](https://lefttosolve.com/p/mo-334154) · [Original](https://mathoverflow.net/questions/334154/eigenvalues-of-cyclic-stochastic-matrices) · [Uhl–Seifert, 2019](https://arxiv.org/abs/1907.04260) · [Kolchinsky, Ohga & Ito, Theorem 1](https://arxiv.org/pdf/2605.15884) · [PRL DOI](https://doi.org/10.1103/dhmz-wlwh).

## MO 255146. Eigenvalues of a leading Sylvester–Kac block

**Target.** For the matrix *displayed* in the source, the upper off-diagonal entries are $n-i$ and lower ones $i$ at edge $(i,i+1)$, $1\le i<n$. Determine or bound the spectrum of its first $r$ rows and columns, $1<r\le n/2$. The full displayed matrix has extreme eigenvalues $\pm(n-1)$; the prose's $\pm n$ uses a different size convention.

**Exact formula.** Put $N=n-1$ and $P_j(t)=\det(tI-J_j)$ for the first $j$ rows. A terminal-row determinant expansion gives $P_0=1,P_1=t$,

$$
P_{j+1}=tP_j-j(n-j)P_{j-1}.
$$

Thus $P_r(t)=r![z^r](1+z)^{(N+t)/2}(1-z)^{(N-t)/2}$. Indeed its exponential generating function $G$ satisfies $(1-z^2)G'=(t-Nz)G$ with $G(0)=1$, which gives this coefficient by comparison. Equivalently the eigenvalues are the values $t=N-2x$ at the zeros of the binary Krawtchouk polynomial of degree $r$ (normalization does not alter the roots). Positive diagonal similarity turns the matrix into a symmetric path with edge weights $w_i=\sqrt{i(n-i)}$. All roots are real, simple by the two-term eigenvector propagation at a boundary, and symmetric by alternating signs. For $r=2$ the formula gives $\pm\sqrt{n-1}$.

**Separate extremal route, including the asymptotic asked in comments.** The weights increase to the midpoint. Entrywise comparison of nonnegative matrices against the uniform path, and then restriction to the last $L$ vertices, give for $2\le L\le r$

$$
2\sqrt{(r-L+1)(n-r+L-1)}\cos\frac{\pi}{L+1}
\le\rho(J_r)\le2\sqrt{(r-1)(n-r+1)}\cos\frac{\pi}{r+1}.
$$

A comparison uses a nonnegative path eigenvector, so increasing an edge increases its Rayleigh quotient; the uniform path eigenvalue follows from a sine vector. Every eigenvalue lies in $[-\rho,\rho]$. For $r/n\to\gamma\in(0,1/2]$, take $L=\lfloor\sqrt{r}\rfloor$ (eventually $\ge2$) to squeeze $\rho/n\to2\sqrt{\gamma(1-\gamma)}$. This supplies the constant asked about in a source comment. The polynomial identification is classical.

[Catalog](https://lefttosolve.com/p/mo-255146) · [Question and asymptotic comment](https://mathoverflow.net/questions/255146/eigenvalues-of-leading-principal-submatrix-of-the-clement-kac-sylvester-tridiago) · [NIST DLMF §18.22, table 18.22.1](https://dlmf.nist.gov/18.22).

## MO 453931. Multiparameter continuity of eigenvalues

For the concrete real symmetric matrix $A_{ij}=x_i+x_j$, let $e=(1,\ldots,1)^T$, $s=e^Tx$, $q=x^Tx$. Then $A=xe^T+ex^T$, vanishes on $\{x,e\}^\perp$, sends $e$ to $s e+n x$ and $x$ to $q e+s x$. If $x,e$ are independent the two remaining eigenvalues are $s\pm\sqrt{nq}$, manifestly continuous, together with $n-2$ zeros. In the dependent case $x=ce$ the spectrum is $2nc,0,\ldots,0$; for $n=1$ it consists only of $2x_1$.

More generally the ordered eigenvalues of a Hermitian matrix are 1-Lipschitz in operator norm by the min–max principle: every unit Rayleigh quotient changes by at most $\|A-B\|$. Composition works for parameter domains of any dimension. For possibly non-Hermitian matrices with everywhere-real spectrum, or monic polynomials with only real roots, sorting the real roots still gives continuous labels: for a convergent sequence of coefficients, the Cauchy root bound makes every ordered list bounded, and the elementary symmetric polynomials identify each subsequential limit with the unique sorted list of limit roots, counting multiplicity. General complex roots need not have continuous labels over two real parameters: for $z^2-(u+iv)$ on a disk containing the unit circle there is no continuous choice since any such choice on the circle would have winding number $1/2$. The original comments already explain the ordered-root continuity approach. The formula above gives a direct solution for the specified matrix.

[Catalog](https://lefttosolve.com/p/mo-453931) · [Question and comments](https://mathoverflow.net/questions/453931/functional-continuity-of-eigenvalues) · [Kato, Perturbation Theory, doi](https://doi.org/10.1007/978-3-642-66282-9).

## MO 465882. Compressing a positive semidefinite matrix to its nonzero spectrum

Write $r=k-n$ for the known rank, and let the columns of $Q\in\mathbb R^{k\times r}$ be any orthonormal basis for the orthogonal complement of the supplied nullspace. If $Z$ is an orthonormal basis of the nullspace, the orthogonal similarity $[Q,Z]^TL[Q,Z]=\operatorname{diag}(Q^TLQ,0_n)$ proves that $C=Q^TLQ$ has exactly the $r$ positive eigenvalues with multiplicities. Obtain $Q$ from a complete QR of a nullspace basis if appropriate. A source commenter already suggested block diagonalization. For the large-nullity example, a directly useful alternative is a Gaussian range finder: draw $\Omega$ of size $k\times(r+p)$ with $p\ge0$, form $Y=L\Omega$ using the factorization $L V=A(A^TV)+B^T(BV)$, and extract $r$ orthonormal range directions by rank-revealing QR or SVD. Indeed, in an eigendecomposition $L=U\Lambda U^T$ with $\Lambda>0$, $U^T\Omega$ is Gaussian of row rank $r$ almost surely, hence $\operatorname{range}(Y)=\operatorname{range}(L)$ in exact arithmetic. Form $C=Q^TA A^T Q+Q^TB^TBQ$ from the factors. If the Gram matrix would lose precision, compute singular values of $[A^T Q; BQ]$ directly and square them. Exact rank compression is guaranteed in exact arithmetic; sensitivity for tiny positive eigenvalues depends on the gap and accuracy of the subspace. A simple check in finite precision is the normwise residual $\|LQ-QC\|$ together with orthogonality and a rank threshold appropriate for the input. For dense explicit $L$, forming $L\Omega$ and $LQ$ costs $O(k^2(r+p))$ operations, followed by small dense linear algebra; a quoted run time is machine- and representation-dependent.

[Catalog](https://lefttosolve.com/p/mo-465882) · [Question and comments](https://mathoverflow.net/questions/465882/given-a-low-rank-symmetric-positive-semidefinite-matrix-and-a-basis-of-its-nulls) · [Halko, Martinsson and Tropp, SIAM Review](https://doi.org/10.1137/090771806).

## MO 193467. Are upper and lower product majorizations sufficient?

The answer depends on the definition of majorization, an issue also noticed in the source comments. For *ordinary* majorization (equal total sums), if $a,b$ are decreasing positive lists, the two required majorizations force $\sum a_i b_i=\sum a_i b_{n+1-i}$. Their difference is $\sum_{i\le\lfloor n/2\rfloor}(a_i-a_{n+1-i})(b_i-b_{n+1-i})$. If both lists are nonconstant the first term is strictly positive and all terms are nonnegative. Therefore one list must be constant. The two endpoints then have the same sorted spectrum, forcing the candidate spectrum to be that list product. A scalar and a diagonal matrix realize it. This literal condition is thus sufficient for a degenerate reason; it is not necessary in general.

For *weak* majorization (top partial sums, no equality of totals), take $a=b=(2,1)$ and $c=(3,3/2)$. Its top sums are between those of $(2,2)$ and $(4,1)$ but its product is $9/2$ rather than $4$, which violates determinants. Even the natural stronger *log-majorization* bounds with the determinant fixed are insufficient. In base-2 logs choose $\log_2 a=(4,3,2)$, $\log_2 b=(5,1,0)$, $\log_2 c=(7,6,2)$. The sorted lower and upper log endpoints are $(7,4,4)$ and $(9,4,2)$; all three have sum 15, and the candidate's first two partial sums $7,13$ lie between $7,11$ and $9,13$ componentwise. Yet $A\preceq16I$ implies $B^{1/2}AB^{1/2}\preceq16B$. Thus the second eigenvalue of $AB$, which is similar to this symmetric matrix, cannot exceed $16\cdot2=32$, whereas the candidate's second eigenvalue is $64$. This explicit obstruction does not require the general multiplicative Horn characterization.

[Catalog](https://lefttosolve.com/p/mo-193467) · [Question and comments](https://mathoverflow.net/questions/193467/existence-of-a-matrix-product-from-its-eigenvalues) · [Fulton, Eigenvalues, invariant factors, highest weights, and Schubert calculus](https://arxiv.org/abs/math/9908012).

## MO 416877. Recovering eigenvalue powers from one indexed compound matrix

Suppose $1\le p<n$ and $C_p(A)$, the indexed matrix of the $p$th exterior power, is invertible. Then $A$ is invertible. If another matrix $B$ has the same compound, $T=A^{-1}B$ has $\bigwedge^p T=I$. Every $p$-plane is invariant under $T$, because the wedge of a basis is fixed and the span is recovered as the vectors whose wedge with that basis wedge vanishes. Every line is an intersection of $p$-planes containing it: for any vector off the line, extend both to a basis and use the span of the line and $p-1$ of the other $n-2$ basis vectors. Thus $T$ preserves every line; testing coordinate lines and the lines through $e_i+e_j$ gives $T=cI$. Now $c^p=1$, so $A$ and $B$ have the same eigenvalue $p$th powers, with multiplicities over an algebraic closure.

Explicit recovery also follows. From the indexed exterior operator one obtains $A(L)$ for each line $L$ by intersecting the images of the $p$-planes through it; in fact the finite family of coordinate planes in a basis extending $L$ suffices. The images of the coordinate lines and of the lines through $e_i+e_j$ determine all column ratios and hence a representative $B$ of the projective class of $A$, over the input field. A nonzero entry of $C_p(B)$ and the corresponding entry of $C_p(A)$ determine the missing scalar's $p$th power as their quotient. Multiply the eigenvalue $p$th powers of $B$ by that scalar power. This avoids root extraction in the ground field. The source already has an answer using the Plücker-coordinate idea. Its printed statement omits $p<n$: when $p=n\ge2$, the compound records only the determinant, and $I_n$ and $\operatorname{diag}(2,1/2,1,\ldots,1)$ give different requested powers over $\mathbb R$ despite equal determinant. For $n=p=1$ the datum is $A$ itself. Thus the unrestricted yes/no question has a counterexample, with a positive theorem for every proper compound. The eigenvalues of an unindexed compound alone are a different reconstruction problem.

[Catalog](https://lefttosolve.com/p/mo-416877) · [Original and posted answers](https://mathoverflow.net/questions/416877/).
