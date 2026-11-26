import Mathlib

/-!
# OEIS A047946

Source: https://oeis.org/A047946
The integer arithmetic retains the signs in both recurrence signatures.
The parameter n is positive and k runs through all nonnegative integers.
-/

namespace OMA.S_oeis_a047946

def coefficient (n : ℕ) : ℤ :=
  5 * (n.fib : ℤ) ^ 2 + 3 * (-1 : ℤ) ^ n

def fibSquare (n k : ℕ) : ℤ := ((n * k).fib : ℤ) ^ 2

theorem main :
    ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      fibSquare n (k + 3) =
        if n % 2 = 1 then
          coefficient n * fibSquare n (k + 2) +
          coefficient n * fibSquare n (k + 1) - fibSquare n k
        else
          coefficient n * fibSquare n (k + 2) -
          coefficient n * fibSquare n (k + 1) + fibSquare n k := by
  sorry

end OMA.S_oeis_a047946
