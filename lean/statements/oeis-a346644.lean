import Mathlib

/-!
# OEIS A346644: denominators of arithmetic means of positive divisors

Source: https://oeis.org/A346644
The conjecture asks whether a witness exists for every positive denominator.
The sequence records the least such k. Rat.den gives the reduced positive denominator.
-/

namespace OMA.S_oeis_a346644

open scoped BigOperators

def divisorMean (k : ℕ) : ℚ :=
  ((∑ d ∈ k.divisors, d : ℕ) : ℚ) / (k.divisors.card : ℚ)

theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ (divisorMean k).den = n := by
  sorry

end OMA.S_oeis_a346644
