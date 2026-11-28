import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# A 137-block seed suffices if two residual extension cases hold

We reduce the 139-block existence hypothesis in @advancedsuperintelligence's
#13941, which follows the reductions of @ian139 and @seanm27lol. The new
geometric step constructs the missing line at any point of degree twelve,
so the unresolved extension hypothesis concerns only configurations having
no such point. Iterating at sizes 137 and 138 obtains the required seed.

The degree-twelve construction and Lean helpers are adapted from the work of
@seanm27lol and collaborators with Codex, in research revision
ad3eedbbb3b968621f9a1d4743e07566ddf851ff and Erdos723SmallSeeds.lean.
The 137- and 138-line paper arguments and their sources are in research PR #7,
revision dbcd0730e39a4e5ca157172dc97cbf43b613f4d4. This reduction by
@seanm27lol with Codex leaves the initial seed and the residual extension
hypothesis open in Lean.
-/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1_H1_R1

open Finset

private theorem meet_card {S : Finset (Finset (Fin 157))} (hs : ((∀ b ∈ S, b.card = 13) ∧ ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c)) {l m : Finset (Fin 157)}
    (hl : l ∈ S) (hm : m ∈ S) (hne : l ≠ m) : (l ∩ m).card = 1 := by
  obtain ⟨x,hx,uniq⟩ := hs.2 l hl m hm hne
  apply card_eq_one.mpr
  exact ⟨x, by ext y; simpa using (show (y ∈ l ∧ y ∈ m) ↔ y = x from
    ⟨uniq y, fun h => h ▸ hx⟩)⟩

private theorem extend_at {S : Finset (Finset (Fin 157))} (hs : ((∀ b ∈ S, b.card = 13) ∧ ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c)) (p : Fin 157) (hr : (S.filter (p ∈ ·)).card = 12) :
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧ ((∀ b ∈ T, b.card = 13) ∧ ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) := by
  classical
  let pencil := S.filter (p ∈ ·)
  have pencilCard : pencil.card = 12 := hr
  have disj : ∀ l ∈ pencil, ∀ m ∈ pencil, l ≠ m → Disjoint (l.erase p) (m.erase p) := by
    intro l hl m hm ne
    obtain ⟨ll,pl⟩ := mem_filter.mp hl
    obtain ⟨mm,pm⟩ := mem_filter.mp hm
    obtain ⟨_,_,un⟩ := hs.2 l ll m mm ne
    apply disjoint_left.mpr
    intro q hq hq'
    exact (mem_erase.mp hq).1 ((un q ⟨(mem_erase.mp hq).2,(mem_erase.mp hq').2⟩).trans
      (un p ⟨pl,pm⟩).symm)
  let joined := pencil.biUnion (fun a => a.erase p)
  let newLine := (univ : Finset (Fin 157)) \ joined
  have joinCard : joined.card = 144 := by
    change (pencil.biUnion (fun a => a.erase p)).card = _
    rw [card_biUnion (fun a ha b hb hab => disj a ha b hb hab)]
    have sizes (a : Finset (Fin 157)) (ha : a ∈ pencil) : (a.erase p).card = 12 := by
      obtain ⟨ha',hp⟩ := mem_filter.mp ha
      rw [card_erase_of_mem hp, hs.1 _ ha']
    rw [sum_congr rfl sizes, sum_const, pencilCard]; rfl
  have newCard : newLine.card = 13 := by
    change (univ \ joined).card = _
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, joinCard]
  have hits (l : Finset (Fin 157)) (hl : l ∈ S) : (newLine ∩ l).card = 1 := by
    by_cases hp : p ∈ l
    · have equ : newLine ∩ l = {p} := by
        ext x
        simp only [newLine,joined,mem_inter,mem_sdiff,mem_univ,true_and,
          mem_biUnion,mem_erase,mem_singleton]
        constructor
        · rintro ⟨nx,hx⟩
          by_contra ne
          exact nx ⟨l,mem_filter.mpr ⟨hl,hp⟩,ne,hx⟩
        · rintro rfl
          exact ⟨fun ⟨_,_,h,_⟩ => h rfl,hp⟩
      rw [equ,card_singleton]
    · have trace : joined ∩ l = pencil.biUnion (fun a => (a.erase p) ∩ l) := by
        ext x
        simp only [joined,mem_biUnion,mem_inter]
        aesop
      have counts (a : Finset (Fin 157)) (ha : a ∈ pencil) : ((a.erase p) ∩ l).card = 1 := by
        obtain ⟨ha',pa⟩ := mem_filter.mp ha
        have eq : (a.erase p) ∩ l = a ∩ l := by
          ext x
          simp only [mem_inter,mem_erase]
          aesop
        rw [eq]; exact meet_card hs ha' hl (by rintro rfl; exact hp pa)
      have cover : (joined ∩ l).card = 12 := by
        rw [trace,card_biUnion (fun a ha b hb ne =>
          (disj a ha b hb ne).mono inter_subset_left inter_subset_left),
          sum_congr rfl counts,sum_const,pencilCard]; rfl
      have rem : newLine ∩ l = l \ joined := by ext x; simp [newLine,and_comm]
      rw [rem,card_sdiff,hs.1 _ hl,cover]
  have fresh : newLine ∉ S := by
    intro h
    have eq := hits newLine h
    rw [inter_self,newCard] at eq
    contradiction
  have newMeets {a b : Finset (Fin 157)} (h : (a ∩ b).card = 1) :
      ∃! x, x ∈ a ∧ x ∈ b := by
    obtain ⟨x,hx⟩ := card_eq_one.mp h
    have key (y : Fin 157) : (y ∈ a ∧ y ∈ b) ↔ y = x := by
      rw [← mem_inter,hx,mem_singleton]
    exact ⟨x,(key x).mpr rfl,fun y hy => (key y).mp hy⟩
  refine ⟨insert newLine S,subset_insert _ _,card_insert_of_notMem fresh,?_,?_⟩
  · intro l hl
    rcases mem_insert.mp hl with rfl | h
    · exact newCard
    · exact hs.1 _ h
  · intro l hl m hm ne
    rcases mem_insert.mp hl with rfl | hl <;> rcases mem_insert.mp hm with rfl | hm
    · exact (ne rfl).elim
    · exact newMeets (hits _ hm)
    · exact newMeets (by rw [inter_comm]; exact hits _ hl)
    · exact hs.2 _ hl _ hm ne

/-- Construct 137 lines of the order-twelve plane on a fixed 157-point set. -/
def H1 : Prop :=
  ∃ S : Finset (Finset (Fin 157)), S.card = 137 ∧ ((∀ b ∈ S, b.card = 13) ∧ ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c)

/-- Extend a 137- or 138-block family when each point avoids degree twelve. -/
def H2 : Prop :=
  ∀ S : Finset (Finset (Fin 157)), (S.card = 137 ∨ S.card = 138) →
    ((∀ b ∈ S, b.card = 13) ∧ ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    (∀ p : Fin 157, (S.filter (p ∈ ·)).card ≠ 12) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      ((∀ b ∈ T, b.card = 13) ∧ ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c)

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1.H1 := by
  classical
  rintro ⟨S, hS, validS⟩ residual
  have advance (U : Finset (Finset (Fin 157))) (size : U.card = 137 ∨ U.card = 138)
      (hU : ((∀ b ∈ U, b.card = 13) ∧ ∀ b ∈ U, ∀ c ∈ U, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c)) :
      ∃ T : Finset (Finset (Fin 157)), U ⊆ T ∧ T.card = U.card + 1 ∧
        ((∀ b ∈ T, b.card = 13) ∧ ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) := by
    by_cases h : ∃ p : Fin 157, (U.filter (p ∈ ·)).card = 12
    · obtain ⟨p, hp⟩ := h
      exact extend_at hU p hp
    · exact residual U size hU (fun p hp => h ⟨p, hp⟩)
  obtain ⟨U, _, hsizeU, validU⟩ := advance S (Or.inl hS) validS
  have hu : U.card = 138 := by omega
  obtain ⟨T, _, hsizeT, validT⟩ := advance U (Or.inr hu) validU
  exact ⟨T, by omega, validT⟩

end OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1_H1_R1
