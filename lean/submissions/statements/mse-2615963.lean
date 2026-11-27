import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Int.ModEq

/-!
# A congruence involving Chebyshev polynomials

Source: https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials
Question by Pedja. Lean formalization: @seanm27lol with Codex.

Mathlib's rescaled first-kind polynomial `Polynomial.Chebyshev.C` satisfies
`C m (2x) = 2 T m (x)` by `Polynomial.Chebyshev.C_comp_two_mul_X`.
Thus its integer value at `k` is exactly the source's `2 T m (k/2)`.
-/

namespace OMA.S_mse_2615963

theorem main : ∀ n : ℕ, 1 < n →
    (n.Prime ↔ Int.ModEq (n : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ))
      (-1)) := by
  sorry

end OMA.S_mse_2615963
