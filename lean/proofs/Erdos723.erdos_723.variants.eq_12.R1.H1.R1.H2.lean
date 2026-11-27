import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.BooleanAlgebra

/-!
A family of 142 pairwise singly intersecting 13-subsets on 157 points extends
to 143 such subsets. The parity argument is from the order-12 research notes
of @seanm27lol and collaborators. The seed problem still asks for an example.
-/

namespace PlaneTwelve.Seed
open Finset

abbrev P := Fin 157
abbrev Block := Finset P
abbrev Valid (S : Finset Block) :=
  (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

private def deg (S : Finset Block) (x : P) : ℕ := (S.filter (x ∈ ·)).card

private theorem countWeights (S : Finset Block) (w : P → ℤ) :
    (∑ x : P, (deg S x : ℤ) * w x) = ∑ L ∈ S, ∑ x ∈ L, w x := by
  classical
  have key (x : P) : (deg S x : ℤ) * w x = ∑ L ∈ S, if x ∈ L then w x else 0 := by
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    rfl
  simp_rw [key]
  rw [sum_comm]
  simp

private theorem meet_card {S : Finset Block} (hs : Valid S) {l m : Block}
    (hl : l ∈ S) (hm : m ∈ S) (hne : l ≠ m) : (l ∩ m).card = 1 := by
  obtain ⟨x,hx,uniq⟩ := hs.2 l hl m hm hne
  apply card_eq_one.mpr
  exact ⟨x, by ext y; simpa using (show (y ∈ l ∧ y ∈ m) ↔ y = x from
    ⟨uniq y, fun h => h ▸ hx⟩)⟩

private theorem onLine {S : Finset Block} (hs : Valid S) {L : Block} (hl : L ∈ S) :
    (∑ x ∈ L, (deg S x : ℤ)) = S.card + 12 := by
  classical
  have key := countWeights S (fun x => if x ∈ L then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter, sum_const, nsmul_eq_mul, mul_one] at key
  rw [key, ← sum_erase_add _ _ hl]
  have aux : (∑ M ∈ S.erase L, ((M ∩ L).card : ℤ)) = (S.erase L).card := by
    apply Eq.trans (sum_congr rfl (g := fun _ : Block => (1 : ℤ)) ?_)
    · simp
    · intro M hM
      obtain ⟨ne,mem⟩ := mem_erase.mp hM
      exact_mod_cast meet_card hs mem hl ne
  rw [aux, inter_self, hs.1 _ hl]
  have := card_erase_add_one hl
  omega

private theorem degree_twelve {S : Finset Block} (hs : Valid S) (hc : S.card = 142) :
    ∃ x, deg S x = 12 := by
  classical
  by_contra! hn
  have h₁ := countWeights S (fun _ => (1 : ℤ))
  simp only [mul_one, sum_const, nsmul_eq_mul] at h₁
  have cardL (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  rw [sum_congr rfl cardL] at h₁
  simp [hc] at h₁
  have h₂ := countWeights S (fun x => (deg S x : ℤ))
  have constant (l : Block) (hl : l ∈ S) : (∑ x ∈ l, (deg S x : ℤ)) = 154 := by
    rw [onLine hs hl, hc]; norm_num
  rw [sum_congr rfl constant] at h₂
  simp [hc] at h₂
  let weight (x : P) : ℤ := if Even (deg S x) then 1 else 0
  have per (l : Block) (hl : l ∈ S) : (1 : ℤ) ≤ ∑ x ∈ l, weight x := by
    have parity : Even (∑ x ∈ l, deg S x) := by
      have v : ∑ x ∈ l, deg S x = 154 := by
        apply Int.ofNat_inj.mp
        simpa only [Nat.cast_sum, Nat.cast_ofNat] using constant l hl
      rw [v]; decide
    have h := (Finset.even_sum_iff_even_card_odd _).mp parity
    by_contra! bad
    have oddall : ∀ x ∈ l, Odd (deg S x) := by
      intro x hx
      by_contra! nn
      have we : weight x = 1 := if_pos (Nat.not_odd_iff_even.mp nn)
      have bound := Finset.single_le_sum (f := weight)
        (fun i (_ : i ∈ l) => by dsimp [weight]; split <;> decide) hx
      omega
    have same : l.filter (fun x => Odd (deg S x)) = l := filter_eq_self.mpr oddall
    rw [same, hs.1 l hl] at h
    exact (by decide : ¬ Even 13) h
  have total := sum_le_sum per
  rw [← countWeights] at total
  simp only [sum_const, hc, nsmul_eq_mul, mul_one, Nat.cast_ofNat] at total
  have cost (x : P) :
      (deg S x : ℤ) * weight x ≤ 5 * ((deg S x : ℤ)^2 - 24 * deg S x + 143) := by
    have hx := hn x
    let r : ℤ := deg S x
    change r * weight x ≤ 5 * (r^2 - 24*r + 143)
    by_cases hii : Even (deg S x)
    · rw [show weight x = 1 from if_pos hii, mul_one]
      obtain ⟨j,hj⟩ := hii
      have sep : r ≤ 10 ∨ 14 ≤ r := by dsimp [r]; omega
      rcases sep with low | high
      · have prod : 0 ≤ (10-r)*(14-r) := mul_nonneg (by omega) (by omega)
        nlinarith
      · nlinarith [sq_nonneg (r-14)]
    · rw [show weight x = 0 from if_neg hii, mul_zero]
      have sep : r ≤ 11 ∨ 13 ≤ r := by dsimp [r]; omega
      rcases sep with low | high
      · have prod : 0 ≤ (13-r)*(11-r) := mul_nonneg (by omega) (by omega)
        nlinarith
      · have prod : 0 ≤ (r-13)*(r-11) := mul_nonneg (by omega) (by omega)
        nlinarith
  have cap := sum_le_sum (fun x (_ : x ∈ (univ : Finset P)) => cost x)
  simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,← mul_sum, sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul, pow_two] at cap
  omega

/-- The complement of all pencil lines with their common point removed is a
new line whenever that point lies on exactly twelve old lines. -/
private theorem extend_at {S : Finset Block} (hs : Valid S) (p : P) (hr : deg S p = 12) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
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
  let newLine := (univ : Finset P) \ joined
  have joinCard : joined.card = 144 := by
    change (pencil.biUnion (fun a => a.erase p)).card = _
    rw [card_biUnion (fun a ha b hb hab => disj a ha b hb hab)]
    have sizes (a : Block) (ha : a ∈ pencil) : (a.erase p).card = 12 := by
      obtain ⟨ha',hp⟩ := mem_filter.mp ha
      rw [card_erase_of_mem hp, hs.1 _ ha']
    rw [sum_congr rfl sizes, sum_const, pencilCard]; rfl
  have newCard : newLine.card = 13 := by
    change (univ \ joined).card = _
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, joinCard]
  have hits (l : Block) (hl : l ∈ S) : (newLine ∩ l).card = 1 := by
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
      have counts (a : Block) (ha : a ∈ pencil) : ((a.erase p) ∩ l).card = 1 := by
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
  have newMeets {a b : Block} (h : (a ∩ b).card = 1) :
      ∃! x, x ∈ a ∧ x ∈ b := by
    obtain ⟨x,hx⟩ := card_eq_one.mp h
    have key (y : P) : (y ∈ a ∧ y ∈ b) ↔ y = x := by
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

/-- Every 142-line seed in the variables and incidence relation of the
catalog extends by one line. -/
theorem extend_142 (S : Finset Block) (hc : S.card = 142) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
  obtain ⟨p,hp⟩ := degree_twelve hs hc
  exact extend_at hs p hp


end PlaneTwelve.Seed


theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1.H2 := by
  intro S count size meet
  exact PlaneTwelve.Seed.extend_142 S count ⟨size, meet⟩
