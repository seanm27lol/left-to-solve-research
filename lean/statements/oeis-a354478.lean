import Mathlib

/-!
# OEIS A354478

Source: https://oeis.org/A354478
The signed first-kind Stirling number is the unsigned Mathlib value multiplied
by the sign (-1)^(n-k). The two OEIS entries are the reduced numerator and
denominator of this rational sum. Their quotient is the target sequence.
-/

namespace OMA.S_oeis_a354478

open scoped BigOperators

def signedStirling (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n - k) * (n.stirlingFirst k : ℤ)

def rowSum (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (1 : ℚ) / (signedStirling n (j + 1) : ℚ)

theorem main :
    Filter.Tendsto (fun n : ℕ => ((rowSum n).num : ℝ) / ((rowSum n).den : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a354478
