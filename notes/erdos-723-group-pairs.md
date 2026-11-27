# A forbidden four-direction configuration for an affine plane of order 12

**Partial result for Erdős 723, order 12.** Let \(G\) be any group of order 12. No affine plane of order 12 can contain four coordinate directions which, after identifying its points with \(G\times G\) and relabeling each direction, are
\[
x,\qquad y,\qquad xy,\qquad f(x)y.
\]
Here \(f\) can be any function. The other nine directions of the putative plane are entirely unrestricted. In Latin-square language, no pair of squares developed in this form can belong to a complete collection of eleven mutually orthogonal Latin squares of order 12. We make no priority claim for this finite exclusion.

The order-12 problem asks whether there is any projective plane of that order. Deleting a projective line produces an affine plane with 144 points and thirteen directions of twelve parallel lines apiece. Taking two directions as rows and columns gives the Latin-square formulation. The exclusion below leaves open configurations outside the displayed class. An affine plane has not been shown to contain a pair of this form. [Exact Lean question](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/723.lean) · [Original problem](https://www.erdosproblems.com/723).

## Normalized transversals

Write 1 for the identity of \(G\). Orthogonality of the four coordinate maps requires that \(f\) and \(x\mapsto f(x)x^{-1}\) both be permutations. Indeed, fixing \(xy=a\) leaves \(f(x)y=f(x)x^{-1}a\). Left multiplication of the fourth coordinate by \(f(1)^{-1}\) allows us to assume \(f(1)=1\). Let \(\mathcal F\) be the finite set of all such normalized maps.

Every further affine line meets each of the first four directions in all twelve labels. In row \(x\) its column has the form \(g(x)^{-1}h\), uniquely with \(g(1)=1\), where \(h\) is its column in the identity row. The column and third-coordinate tests force \(g\in\mathcal F\), and the fourth-coordinate test says \(x\mapsto f(x)g(x)^{-1}\) is a permutation. Thus, for every pair of distinct rows \(i,j\), the two quantities \(f(i)^{-1}f(j)\) and \(g(i)^{-1}g(j)\) differ.

For each surviving \(g\) let \(m_g\) be the number of its twelve column translates which are actual additional lines of the plane. These nonnegative integers may be individually different; there is no assumption that translations preserve the plane.

Fix a pair of rows \(i,j\) in one chosen order. For each
\[
d\notin\{1,i^{-1}j,f(i)^{-1}f(j)\}
\]
there are exactly twelve pairs of cells, one in each of the two rows, whose columns satisfy \(y_i y_j^{-1}=d\). None is joined by one of the first four directions. Thus each must be joined by exactly one further line. A translate associated to \(g\) joins exactly one of these pairs if \(g(i)^{-1}g(j)=d\), and none otherwise. Consequently
\[
\sum_{g:\,g(i)^{-1}g(j)=d}m_g=12.
\]
There are \(\binom{12}{2}\cdot9=594\) equations. An empty left-hand side eliminates the candidate instantly.

## Exhaustion and the exceptional orbit

To enumerate \(\mathcal F\), the verifier builds each normalized permutation in order and discards a prefix only when one of its two required permutation properties is violated. The change
\[
f'(\alpha(x))=\alpha\big(f(t)^{-1}f(tx)\big)
\]
for \(t\in G\) and a group automorphism \(\alpha\) preserves the four-direction structure up to relabeling. The verifier can also check all maps without using this reduction.

| Group | Normalized maps | Orbits checked | Orbits with all 594 left sides nonempty |
|---|---:|---:|---:|
| cyclic group of order 12 | 0 | 0 | 0 |
| \(C_3\times C_2\times C_2\) | 16,512 | 149 | 1 |
| dihedral group of order 12 | 6,336 | 72 | 0 |
| dicyclic group of order 12 | 0 | 0 | 0 |
| alternating group \(A_4\) | 3,840 | 21 | 0 |

These exhaust the groups of order 12. If there are four Sylow 3-subgroups, conjugation on them is transitive, with point stabilizers of order three. Their cores are trivial, so the group embeds in \(S_4\) with index two and is \(A_4\). Otherwise the Sylow 3-subgroup is normal, and the group is its semidirect product with a Sylow 2-subgroup of order four. The latter is cyclic or a Klein four-group and acts trivially or by inversion, giving the four remaining entries of the table.

The exceptional orbit contains 12 normalized maps. For its representative there are 48 possible normalized transversals. Group the 594 equations by the size \(k\) of their left-hand supports, and weight each equation as follows.

| \(k\) | 4 | 5 | 6 | 7 | 8 | 12 |
|---|---:|---:|---:|---:|---:|---:|
| Number of equations | 252 | 108 | 120 | 36 | 72 | 6 |
| Weight | −1 | 1 | 0 | 0 | 1 | 4 |

The weighted right-hand side is \(12(-252+108+72+4\cdot6)=-576\). On the left the coefficients of the 48 variables are 0 (30 variables), 3 (12 variables), or 60 (6 variables). Their nonnegativity gives a contradiction, even for nonnegative real line multiplicities. The integer verifier checks the support counts and every coefficient directly.

The historical constructions of five mutually orthogonal squares provide useful comparison examples. The literature also rules out collineation groups larger than three for an entire projective plane of order 12. The calculation here prescribes four coordinate directions only. [Bose, Chakravarti and Knuth](https://doi.org/10.1080/00401706.1960.10489916) · [Akiyama, Suetake and Tanaka](https://doi.org/10.1002/jcd.21869).

Run the standard-library verifier with Python 3.10 or newer:

```sh
python3 checks/erdos723_group_pairs.py --all-maps
```

The final option repeats the line-cover checks separately for all 26,688 normalized maps, including all twelve exceptional maps.
