# Erdős 1160, the eventual sum variant

Let \(g(n)\) count isomorphism classes of groups of order \(n\), and set \(F(x)=\sum_{1\le n\le x}g(n)\). The [site target](https://lefttosolve.com/p/Erdos1160.erdos_1160.variants.sum) asks whether
\[
  F(2^m-1)\le g(2^m)
\]
for all sufficiently large \(m\). The exact Lean binder is `∀ᶠ m : ℕ in atTop`. The suggested onset \(m=7\) belongs to the commentary and does not appear in the target. [Pinned upstream declaration](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f/FormalConjectures/ErdosProblems/1160.lean).

## Deduction from Su and Xia

Theorem 1.1 of Ning Su and Binzhou Xia's [October 2026 preprint](https://arxiv.org/abs/2610.11092) gives, uniformly on \(2^m\le x<2^{m+1}\),
\[
  F(x)=g(2^m)\left(1+O(2^{-cm^2})\right)
\]
for an absolute \(c>0\). At \(x=2^m\), subtracting \(g(2^m)\) gives \(F(2^m-1)=O(2^{-cm^2}g(2^m))\). The cyclic group of order \(2^m\) ensures \(g(2^m)>0\). The implicit constant times \(2^{-cm^2}\) is eventually less than 1, proving the strict inequality throughout some final interval of exponents. This is an existing mathematical consequence. The quantitative concentration theorem would still require a Lean proof for the website to accept this route.

## Independent deduction using Li and Qiao

Yinan Li and Youming Qiao's [concurrent preprint](https://arxiv.org/abs/2610.14509) states that the fraction of class-two 2-groups among all finite groups of order at most \(x\) tends to one. It also gives, for \(a_m=g(2^m)\),
\[
  \log_2 a_m=\tfrac{2}{27}m^3-\tfrac49m^2+O(m).
\]
Subtracting the preceding level gives \(\log_2(a_m/a_{m-1})=\tfrac29m^2+O(m)\). Thus \(a_m\) eventually increases and \(m a_{m-1}=o(a_m)\). Accounting separately for the fixed initial segment yields \(\sum_{j<m}a_j=o(a_m)\). At \(x=2^m\), the class-two 2-groups form a subset of all the 2-groups counted by \(\sum_{j\le m} a_j\). Their density therefore implies \(\sum_{j\le m}a_j/F(2^m)\to1\). Hence \(F(2^m)\sim a_m\), implying the same eventual strict inequality.

These deductions check the implication from each preprint. They do not independently verify either preprint's full enumeration argument, provide an explicit onset for the inequality, or prove the stronger pointwise Erdős–Higman conjecture at every exponent.

## Exact status of the formal gap

Version 3, Corollary 15.11 of Li and Qiao already states the normalization
needed here:

\[
 \frac{F(2^m-1)}{g(2^m)}\longrightarrow0,
\]

and explicitly draws the eventual strict inequality.  Thus the remaining
Lean gap is not an asymptotic manipulation; it is the paper's group-enumeration
theorem itself.  Public searches found no Lean formalization of that input.
Mathematical credit for the solved asymptotic target belongs to Yinan Li and
Youming Qiao.

The two small formal interfaces have now been discharged in
[`lean/research/Erdos1160Density.lean`](../lean/research/Erdos1160Density.lean):

1. `Erdos1160.g_pos` proves `0 < Erdos1160.g n` for positive `n` by exhibiting the cyclic group
   `Multiplicative (ZMod n)` in the finite isomorphism-class table already used
   by the prepared direct-product proof;
2. `Erdos1160Density.strict_from_previous_ratio` proves the generic order-limit lemma which turns
   `Tendsto (fun m => ((sum_{1 <= n < 2^m} g n : Nat) : Real) /
   g (2^m)) atTop (nhds 0)` and eventual positivity into the exact eventual
   strict inequality. `Erdos1160.variants.sum_strict_of_previous_ratio`
   specializes it to the exact pinned catalog definition.

These lemmas were compiled with Lean against pinned Formal Conjectures commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The finite-table encoding is
adapted, with attribution, from Left to Solve PR 754 by @kamaleshanantha.
This is genuine kernel-checked progress, but it does not substitute for
Corollary 15.11. Until that enumeration theorem is formalized, the catalog
target has a published mathematical proof but not an end-to-end
kernel-checked proof in the pinned environment.
