import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1

/-!
A 140-line seed and three successive one-line extensions suffice for the
143-line seed in @ian139's upstream reduction #3312. The smaller seed is an
existence problem. The separate extension hypothesis has an unconditional
Lean proof by @seanm27lol and collaborators, with Codex assistance.

Source of the specialized arguments: notes/erdos-723-extension.md at
seanm27lol/left-to-solve-research commit
79d441ee30269027e2b9d52023925b9d32a88432. The first formalization of the
142-line extension was recorded at ad3eedbbb3b968621f9a1d4743e07566ddf851ff.
-/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1

/-- Existence of an intersecting 140-line seed. -/
def H1 : Prop :=
  ∃ S : Finset (Finset (Fin 157)), S.card = 140 ∧ (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

/-- Extension on the same point set for every seed of 140, 141 or 142 lines. -/
def H2 : Prop :=
  ∀ S : Finset (Finset (Fin 157)), 140 ≤ S.card → S.card < 143 →
    (∀ b ∈ S, b.card = 13) →
    (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      (∀ b ∈ T, b.card = 13) ∧
      ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

theorem main :
    H1 → H2 → OMA.R_Erdos723_erdos_723_variants_eq_12_R1.H1 := by
  rintro ⟨S, sz, sizes, meets⟩ extend
  obtain ⟨A, _, a, asizes, ameets⟩ := extend S (by omega) (by omega) sizes meets
  obtain ⟨B, _, b, bsizes, bmeets⟩ := extend A (by omega) (by omega) asizes ameets
  obtain ⟨C, _, c, csizes, cmeets⟩ := extend B (by omega) (by omega) bsizes bmeets
  exact ⟨C, by omega, csizes, cmeets⟩

end OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1
