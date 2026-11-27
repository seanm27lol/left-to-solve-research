import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1

/-! The 143-line seed of @ian139's upstream reduction #3312 can be found
by constructing a 142-line seed and proving it always extends by one line.

Source of the extension argument: @seanm27lol and collaborators, with Codex,
`notes/erdos-723-extension.md` at research commit
79d441ee30269027e2b9d52023925b9d32a88432. -/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1

/-- Existence of an intersecting 142-line seed. -/
def H1 : Prop :=
  ∃ S : Finset (Finset (Fin 157)), S.card = 142 ∧ (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

/-- Extension of every 142-line seed by one line on the same point set. -/
def H2 : Prop :=
  ∀ S : Finset (Finset (Fin 157)), S.card = 142 →
    (∀ b ∈ S, b.card = 13) →
    (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      (∀ b ∈ T, b.card = 13) ∧
      ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

theorem main :
    H1 → H2 → OMA.R_Erdos723_erdos_723_variants_eq_12_R1.H1 := by
  rintro ⟨S, hs, sizes, meets⟩ extend
  obtain ⟨T, _, ht, tsizes, tmeets⟩ := extend S hs sizes meets
  exact ⟨T, by omega, tsizes, tmeets⟩

end OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1
