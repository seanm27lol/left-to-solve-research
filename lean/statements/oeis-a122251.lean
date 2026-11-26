import Mathlib

/-!
# OEIS A122251

Source: https://oeis.org/A122251
At index n the Hankel matrix has size n+1 and both indices start at zero.
Rat.num is the signed numerator after reduction. Natural division expresses
the floors in the source exponent, including the j=0 term.
-/

namespace OMA.S_oeis_a122251

open scoped BigOperators

def hankel (p n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j => 1 / (1 + (p : ℚ) * ((i.val : ℚ) + (j.val : ℚ)))

def exponent (p n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), (k + 1) / p ^ j

theorem main :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      (hankel p n).det.num = ((p : ℤ) ^ 2) ^ (exponent p n) := by
  sorry

end OMA.S_oeis_a122251
