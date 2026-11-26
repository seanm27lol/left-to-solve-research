import Mathlib

/-!
# OEIS A309417: iterations of subtraction of the decimal digit sum

Source: https://oeis.org/A309417
At every positive state the digit sum is positive and at most the state, so
an initial state x reaches zero within x steps. The recursion takes x units of fuel.
-/

namespace OMA.S_oeis_a309417

def countSteps : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, x + 1 =>
      1 + countSteps fuel ((x + 1) - (Nat.digits 10 (x + 1)).sum)

def term (n : ℕ) : ℕ := countSteps (10 ^ n) (10 ^ n)

theorem main :
    Filter.Tendsto (fun n : ℕ => (term (n + 1) : ℝ) / (term n : ℝ))
      Filter.atTop (nhds 10) := by
  sorry

end OMA.S_oeis_a309417
