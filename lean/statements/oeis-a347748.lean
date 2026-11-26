import Mathlib

/-!
# OEIS A347748

Source: https://oeis.org/A347748
Each factorization uses positive factors, and each integer is counted once.
The half-open interval selects the positive integers with exactly n decimal digits.
-/

namespace OMA.S_oeis_a347748

def hasPairEndingIn (m digit : ℕ) : Bool :=
  decide ((m.divisors.filter (fun a => a % 10 = digit ∧ (m / a) % 10 = digit)).Nonempty)

def term (n : ℕ) : ℕ :=
  ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter fun m =>
    hasPairEndingIn m 4 = true ∧ hasPairEndingIn m 6 = true).card

theorem main :
    Filter.Tendsto (fun n : ℕ => (term n : ℝ) / (term (n - 1) : ℝ))
      Filter.atTop (nhds 10) := by
  sorry

end OMA.S_oeis_a347748
