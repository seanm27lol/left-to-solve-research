import OMAStatements.S_mse_2615963
import Mathlib.Data.Nat.Squarefree

/-!
# A congruence involving Chebyshev polynomials

The forward direction follows from the power sums of a monic polynomial over
a prime field. The reverse direction separates the square-divisor and parity
obstructions from the remaining case of an odd squarefree composite.
-/

namespace OMA.R_mse_2615963_R1

def H1 : Prop := ∀ p : ℕ, p.Prime →
  Int.ModEq (p : ℤ)
    (∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ ((p : ℤ) - 1)).eval (k : ℤ)) (-1)

def H2 : Prop := ∀ n : ℕ, 1 < n →
  Int.ModEq (n : ℤ)
    (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1) →
  n = 2 ∨ Odd n ∧ Squarefree n

def H3 : Prop := ∀ n : ℕ, 1 < n → Odd n → Squarefree n → ¬n.Prime →
  ¬ Int.ModEq (n : ℤ)
    (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mse_2615963.main := by
  intro h1 h2 h3 n hn
  refine ⟨h1 n, ?_⟩
  intro h
  rcases h2 n hn h with rfl | ⟨ho, hsq⟩
  · exact Nat.prime_two
  · by_contra hc
    exact h3 n hn ho hsq hc h

end OMA.R_mse_2615963_R1
