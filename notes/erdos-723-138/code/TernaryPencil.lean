import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Ternary pencil count for partial planes with ten covered lines per support point. -/
namespace PlaneTwelve.Ternary
open Finset

variable {V : Type*} [DecidableEq V]

/-- Two distinct blocks have at most one common point. -/
def LinearBlocks (S : Finset (Finset V)) : Prop :=
  ∀ L ∈ S, ∀ M ∈ S, L ≠ M → ∀ x ∈ L, x ∈ M → ∀ y ∈ L, y ∈ M → x = y

/-- Counts in the two sign classes agree modulo three on every block. -/
def Balanced (S : Finset (Finset V)) (A B : Finset V) : Prop :=
  ∀ L ∈ S, (L ∩ A).card % 3 = (L ∩ B).card % 3

private theorem erased_sum_bound {S : Finset (Finset V)} (hlin : LinearBlocks S)
    (x : V) (U : Finset V) :
    (∑ L ∈ S.filter (x ∈ ·), (L ∩ U.erase x).card) ≤ (U.erase x).card := by
  classical
  let F := S.filter (x ∈ ·)
  have hd : (F : Set (Finset V)).PairwiseDisjoint (fun L => L ∩ U.erase x) := by
    intro L hL M hM hne
    obtain ⟨ls,xl⟩ := mem_filter.mp hL
    obtain ⟨ms,xm⟩ := mem_filter.mp hM
    refine disjoint_left.mpr ?_
    intro y hy hz
    obtain ⟨yl, yu⟩ := mem_inter.mp hy
    exact (mem_erase.mp yu).1 (hlin L ls M ms hne y yl (mem_inter.mp hz).1 x xl xm)
  calc
    _ = (F.biUnion fun L => L ∩ U.erase x).card := (card_biUnion hd).symm
    _ ≤ _ := card_le_card (fun y hy => by
      obtain ⟨L,_,h⟩ := mem_biUnion.mp hy
      exact (mem_inter.mp h).2)

/-- At a positive support point, each line needs either two further positive
points or one negative point. No other point is counted on two such lines. -/
theorem pencil_charge {S : Finset (Finset V)} {A B : Finset V}
    (hlin : LinearBlocks S) (hab : Disjoint A B) (hbal : Balanced S A B)
    {x : V} (hx : x ∈ A) :
    2*(S.filter (x ∈ ·)).card ≤ A.card - 1 + 2*B.card := by
  classical
  have hxb : x ∉ B := fun hb => disjoint_left.mp hab hx hb
  let F := S.filter (x ∈ ·)
  have hline (L : Finset V) (hL : L ∈ F) :
      2 ≤ (L ∩ A.erase x).card + 2*(L ∩ B.erase x).card := by
    obtain ⟨ls,xl⟩ := mem_filter.mp hL
    have h := hbal L ls
    have xx : x ∈ L ∩ A := mem_inter.mpr ⟨xl,hx⟩
    have he : L ∩ A.erase x = (L ∩ A).erase x := by ext y; simp; tauto
    rw [he,card_erase_of_mem xx,erase_eq_of_notMem hxb]
    have hp := card_pos.mpr ⟨x,xx⟩
    omega
  have ha := erased_sum_bound hlin x A
  have hb := erased_sum_bound hlin x B
  rw [card_erase_of_mem hx] at ha
  rw [erase_eq_of_notMem hxb] at hb
  change 2*F.card ≤ _
  calc
    2*F.card = ∑ _ ∈ F, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ L ∈ F, ((L ∩ A.erase x).card + 2*(L ∩ B.erase x).card) := sum_le_sum hline
    _ = (∑ L ∈ F, (L ∩ A.erase x).card) + 2*∑ L ∈ F, (L ∩ B).card := by
      simp only [erase_eq_of_notMem hxb, sum_add_distrib, mul_sum]
    _ ≤ _ := by
      change (∑ L ∈ S.filter (x ∈ ·), (L ∩ A.erase x).card) +
        2*∑ L ∈ S.filter (x ∈ ·), (L ∩ B).card ≤ _
      omega

/-- A nonzero balanced ternary word with degree at least ten throughout its
support has weight at least fourteen. No assumption on other points' degrees. -/
theorem weight_ge_fourteen {S : Finset (Finset V)} {A B : Finset V}
    (hlin : LinearBlocks S) (hab : Disjoint A B) (hbal : Balanced S A B)
    (hnz : (A ∪ B).Nonempty)
    (hdeg : ∀ x ∈ A ∪ B, 10 ≤ (S.filter (x ∈ ·)).card) :
    14 ≤ (A ∪ B).card := by
  classical
  have hbal' : Balanced S B A := fun L hL => (hbal L hL).symm
  have hplus (nA : A.Nonempty) : 21 ≤ A.card + 2*B.card := by
    obtain ⟨x,hx⟩ := nA
    have hh := pencil_charge hlin hab hbal hx
    have hd := hdeg x (mem_union_left B hx)
    have hp := card_pos.mpr ⟨x,hx⟩
    omega
  have hminus (nB : B.Nonempty) : 21 ≤ B.card + 2*A.card := by
    obtain ⟨x,hx⟩ := nB
    have hh := pencil_charge hlin hab.symm hbal' hx
    have hd := hdeg x (mem_union_right A hx)
    have hp := card_pos.mpr ⟨x,hx⟩
    omega
  rw [card_union_of_disjoint hab]
  obtain ⟨x,hx⟩ := hnz
  rcases mem_union.mp hx with xp | xm
  · have h := hplus ⟨x,xp⟩
    by_cases b : B.Nonempty
    · have := hminus b; omega
    · have := not_nonempty_iff_eq_empty.mp b; simp_all; omega
  · have h := hminus ⟨x,xm⟩
    by_cases a : A.Nonempty
    · have := hplus a; omega
    · have := not_nonempty_iff_eq_empty.mp a; simp_all; omega

/-- Two nonzero such words cannot have disjoint supports in a set of size 24. -/
theorem no_disjoint_pair_in_24 {S : Finset (Finset V)} (hlin : LinearBlocks S)
    {T A B C D : Finset V} (hT : T.card ≤ 24)
    (deg : ∀ x ∈ T, 10 ≤ (S.filter (x ∈ ·)).card)
    (ab : Disjoint A B) (cd : Disjoint C D) (bal : Balanced S A B) (bal' : Balanced S C D)
    (n : (A ∪ B).Nonempty) (n' : (C ∪ D).Nonempty)
    (ht : A ∪ B ⊆ T) (hu : C ∪ D ⊆ T) (hd : Disjoint (A ∪ B) (C ∪ D)) : False := by
  have h := weight_ge_fourteen hlin ab bal n (fun x hx => deg x (ht hx))
  have h' := weight_ge_fourteen hlin cd bal' n' (fun x hx => deg x (hu hx))
  have c := card_le_card (union_subset ht hu)
  rw [card_union_of_disjoint hd] at c
  omega

section Words
variable [Fintype V]

/-- Ternary words orthogonal to each original incidence vector. -/
def Orthogonal (S : Finset (Finset V)) (f : V → ZMod 3) : Prop :=
  ∀ L ∈ S, ∑ x ∈ L, f x = 0

def wordSupport (f : V → ZMod 3) : Finset V := univ.filter (fun x => f x ≠ 0)

private def level (f : V → ZMod 3) (k : ZMod 3) : Finset V := univ.filter (fun x => f x = k)

private theorem decompose_val : ∀ t : ZMod 3,
    t = (if t=1 then 1 else 0) - (if t= -1 then 1 else 0) := by decide

private theorem support_levels (f : V → ZMod 3) :
    wordSupport f = level f 1 ∪ level f (-1) := by
  have h : ∀ t : ZMod 3, t ≠ 0 ↔ t = 1 ∨ t = -1 := by decide
  ext x
  simp [wordSupport,level,h]

omit [DecidableEq V] in
private theorem disjoint_levels (f : V → ZMod 3) : Disjoint (level f 1) (level f (-1)) := by
  refine disjoint_left.mpr ?_
  intro x hx hy
  have a : f x = 1 := (mem_filter.mp hx).2
  have b : f x = -1 := (mem_filter.mp hy).2
  exact (by decide : (1 : ZMod 3) ≠ -1) (a.symm.trans b)

private theorem balanced_levels {S : Finset (Finset V)} {f : V → ZMod 3}
    (h : Orthogonal S f) : Balanced S (level f 1) (level f (-1)) := by
  intro L hL
  have counts (k : ZMod 3) :
      (∑ x ∈ L, (if f x = k then (1 : ZMod 3) else 0)) = ((L ∩ level f k).card : ZMod 3) := by
    have hh : L.filter (fun x => f x = k) = L ∩ level f k := by ext x; simp [level]
    rw [← sum_filter, hh]
    simp
  have h0 := h L hL
  rw [sum_congr rfl (fun x _ => decompose_val (f x)),sum_sub_distrib,counts,counts] at h0
  exact (ZMod.natCast_eq_natCast_iff' _ _ 3).mp (sub_eq_zero.mp h0)

theorem orthogonal_weight_ge_fourteen {S : Finset (Finset V)} (hlin : LinearBlocks S)
    {f : V → ZMod 3} (hf : Orthogonal S f) (hnz : (wordSupport f).Nonempty)
    (hdeg : ∀ x ∈ wordSupport f, 10 ≤ (S.filter (x ∈ ·)).card) : 14 ≤ (wordSupport f).card := by
  rw [support_levels] at hnz hdeg ⊢
  exact weight_ge_fourteen hlin (disjoint_levels _) (balanced_levels hf) hnz hdeg

theorem no_disjoint_orthogonal_in_24 {S : Finset (Finset V)} (hlin : LinearBlocks S)
    {T : Finset V} (hT : T.card ≤ 24) (deg : ∀ x ∈ T, 10 ≤ (S.filter (x ∈ ·)).card)
    {f g : V → ZMod 3} (hf : Orthogonal S f) (hg : Orthogonal S g)
    (nf : (wordSupport f).Nonempty) (ng : (wordSupport g).Nonempty)
    (tf : wordSupport f ⊆ T) (tg : wordSupport g ⊆ T)
    (hd : Disjoint (wordSupport f) (wordSupport g)) : False := by
  have a := orthogonal_weight_ge_fourteen hlin hf nf (fun x hx => deg x (tf hx))
  have b := orthogonal_weight_ge_fourteen hlin hg ng (fun x hx => deg x (tg hx))
  have c := card_le_card (union_subset tf tg)
  rw [card_union_of_disjoint hd] at c
  omega
end Words
end PlaneTwelve.Ternary
#print axioms PlaneTwelve.Ternary.weight_ge_fourteen
#print axioms PlaneTwelve.Ternary.no_disjoint_pair_in_24

#print axioms PlaneTwelve.Ternary.no_disjoint_orthogonal_in_24
