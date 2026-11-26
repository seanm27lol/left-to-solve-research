import Mathlib

/-!
# OEIS A056142: palindromes formed by concatenating decimal prefixes

Source: https://oeis.org/A056142
The source conjecture explicitly includes three-digit inputs. A digit string is
written most significant digit first, and the final empty prefix is omitted.
-/

namespace OMA.S_oeis_a056142

def decimalWord (n : ℕ) : List ℕ :=
  (Nat.digits 10 n).reverse

def prefixWord (w : List ℕ) : List ℕ :=
  (List.range w.length).flatMap (fun j => w.take (w.length - j))

theorem main :
    ∀ n : ℕ, 3 ≤ (decimalWord n).length →
      (prefixWord (decimalWord n)).reverse = prefixWord (decimalWord n) →
      ∀ x ∈ decimalWord n, ∀ y ∈ decimalWord n, x = y := by
  sorry

end OMA.S_oeis_a056142
