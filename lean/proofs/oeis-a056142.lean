import OMAStatements.S_oeis_a056142

/-!
# Refutation of the threshold-three conjecture in A056142

David Wasserman recorded the three-digit case on OEIS in 2005. For the
explicit witness 121, the concatenation is 121121 and the digits 1 and 2 differ.
-/

open OMA.S_oeis_a056142

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a056142.main) := by
  intro h
  have h12 : (1 : ℕ) = 2 :=
    h 121 (by decide) (by decide) 1 (by decide) 2 (by decide)
  exact (by decide : (1 : ℕ) ≠ 2) h12
