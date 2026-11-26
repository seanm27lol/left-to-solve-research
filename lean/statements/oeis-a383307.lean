import Mathlib

/-!
# OEIS A383307: consecutive-term growth for equal digit range and mode

Source: https://oeis.org/A383307
Zero is a one-digit integer. The source compares the range to the unique mode.
Real division at the one zero term has no effect on the limit at infinity.
-/

namespace OMA.S_oeis_a383307

def digitWord (k : ℕ) : List ℕ :=
  if k = 0 then [0] else (Nat.digits 10 k).reverse

def uniqueMode (w : List ℕ) (m : ℕ) : Bool :=
  (List.range 10).all fun d => (d == m) || decide (w.count d < w.count m)

def qualifies (w : List ℕ) : Bool :=
  let largest := w.max?.getD 0
  let smallest := w.min?.getD 0
  uniqueMode w (largest - smallest)

def term (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter fun k =>
    (digitWord k).length = n ∧ qualifies (digitWord k) = true).card

theorem main :
    Filter.Tendsto (fun n : ℕ => (term (n + 1) : ℝ) / (term n : ℝ))
      Filter.atTop (nhds 10) := by
  sorry

end OMA.S_oeis_a383307
