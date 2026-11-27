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
