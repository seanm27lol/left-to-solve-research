import Mathlib

/-!
# OEIS A379181: consecutive-term growth for equal digit mean and mode

Source: https://oeis.org/A379181
The source counts a unique mode and includes zero among one-digit integers.
Exact equality of mean and mode is expressed by clearing the positive digit count.
-/

namespace OMA.S_oeis_a379181

def digitWord (k : ℕ) : List ℕ :=
  if k = 0 then [0] else (Nat.digits 10 k).reverse

def uniqueMode (w : List ℕ) (m : ℕ) : Bool :=
  (List.range 10).all fun d => (d == m) || decide (w.count d < w.count m)

def qualifies (w : List ℕ) : Bool :=
  (List.range 10).any fun m => uniqueMode w m && (w.sum == m * w.length)

def term (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter fun k =>
    (digitWord k).length = n ∧ qualifies (digitWord k) = true).card

theorem main :
    Filter.Tendsto (fun n : ℕ => (term (n + 1) : ℝ) / (term n : ℝ))
      Filter.atTop (nhds 10) := by
  sorry

end OMA.S_oeis_a379181
