import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# OEIS A071052: zero cells in Rule 150

Rule 150 starts with one on-cell. Each new bit is the XOR of the three
neighboring bits. We number each row from its left edge: a fixed physical
cell's index increases by one at each time step. Thus the parents of index
`i` have indices `i-2`, `i-1`, and `i` in the preceding row. The finite
row at time `n` has indices `0, ..., 2*n`.

Source: https://oeis.org/A071052 and https://oeis.org/A071036
-/

namespace OMA.S_oeis_a071052

/-- Cell state at time `n` and index `i`, including off-cells outside the row. -/
def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => xor (xor (cell n (i - 2)) (cell n (i - 1))) (cell n i)

/-- Count the off-cells in the length-`2*n+1` row at time `n`. -/
def zeroCount (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2*n + 1), if cell n i then 0 else 1

theorem main : ∀ n : ℕ, zeroCount (2*n) = zeroCount n + 2*n := by
  sorry

end OMA.S_oeis_a071052
