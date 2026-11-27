import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Extending intersecting 13-point block families of sizes 140, 141 and 142

Original Lean proofs by @seanm27lol and collaborators, with Codex assistance,
for the three one-line extensions in reduction R1.H1.R1 of Erdős 723, order
12. The 143-line parent seed is due to @ian139 (upstream PR #3312).
The smaller seed's existence remains open.

The counting arguments for all three sizes were recorded in
seanm27lol/left-to-solve-research at commit
79d441ee30269027e2b9d52023925b9d32a88432, notes/erdos-723-extension.md.
The initial 142-line formalization was published at
ad3eedbbb3b968621f9a1d4743e07566ddf851ff.
Mathlib's Andrásfai–Erdős–Sós theorem supplies the bipartition in the local
22-vertex graph. All incidence and extension steps are proved below.

At 140 and 142 lines a point of degree 12 provides a new line. At 141 lines
without such a point, the degrees are 9, 11 and 13 with multiplicities
4, 96 and 57. The adjacency graph of the 96 degree-11 points is recognized
as the line graph of a graph on 16 vertices. Marking its edges by a
degree-9 point gives a 12-clique which, together with that point, meets
all 141 old lines exactly once.
-/

namespace PlaneTwelve.Seed
open Finset

abbrev P := Fin 157
abbrev Block := Finset P
abbrev Valid (S : Finset Block) :=
  (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

def deg (S : Finset Block) (x : P) : ℕ := (S.filter (x ∈ ·)).card

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


private def pencil (S : Finset Block) (p : P) := S.filter (p ∈ ·)
private def neighbors (S : Finset Block) (p : P) := (pencil S p).biUnion (fun L => L.erase p)

private theorem pencil_disjoint {S : Finset Block} (hs : Valid S) (p : P) :
    ((pencil S p : Finset Block) : Set Block).PairwiseDisjoint (fun L => L.erase p) := by
  intro l hl m hm ne
  obtain ⟨ls,pl⟩ := mem_filter.mp hl
  obtain ⟨ms,pm⟩ := mem_filter.mp hm
  obtain ⟨_,_,uni⟩ := hs.2 _ ls _ ms ne
  refine disjoint_left.mpr ?_
  intro q hq hq'
  exact (mem_erase.mp hq).1 ((uni q ⟨(mem_erase.mp hq).2,(mem_erase.mp hq').2⟩).trans
    (uni p ⟨pl,pm⟩).symm)

private theorem neighborhood_size {S : Finset Block} (hs : Valid S) (p : P) :
    (neighbors S p).card = deg S p * 12 := by
  rw [neighbors,card_biUnion (pencil_disjoint hs p)]
  have sizes (l : Block) (hl : l ∈ pencil S p) : (l.erase p).card = 12 := by
    have h := mem_filter.mp hl
    rw [card_erase_of_mem h.2,hs.1 _ h.1]
  rw [sum_congr rfl sizes, sum_const,nsmul_eq_mul]; rfl

private theorem degree_cap {S : Finset Block} (hs : Valid S) (p : P) : deg S p ≤ 13 := by
  have h := card_le_univ (neighbors S p)
  rw [neighborhood_size hs, Fintype.card_fin] at h
  omega

private def marks (d : ℕ) : ℤ := if Even d then 1 else 0
private def score (d : ℕ) : ℤ := (13-(d:ℤ))*(11-d)
private def surplus (d : ℕ) : ℤ := score d - 3*marks d

private theorem scoreTable (r : Fin 14) (h : r.val ≠ 12) :
    0 ≤ surplus r ∧ (surplus r = 0 ∨ 8 ≤ surplus r) ∧
    (surplus r = 0 → (r.val = 10 ∨ r.val = 11 ∨ r.val = 13)) ∧
    (r.val : ℤ)*marks r ≤ 10*marks r := by
  revert r
  decide

private theorem oneEvenPerLine {S : Finset Block} (hs : Valid S) {L : Block} (hl : L ∈ S)
    (hp : Even (∑ x ∈ L, deg S x)) : 1 ≤ ∑ x ∈ L, marks (deg S x) := by
  classical
  have h := (Finset.even_sum_iff_even_card_odd _).mp hp
  by_contra! bad
  have odds : ∀ x ∈ L, Odd (deg S x) := by
    intro x hx
    by_contra! nn
    have we : marks (deg S x) = 1 := if_pos (Nat.not_odd_iff_even.mp nn)
    have bound := single_le_sum (f := fun x => marks (deg S x))
      (fun i (_ : i ∈ L) => by dsimp [marks]; split <;> decide) hx
    omega
  rw [filter_eq_self.mpr odds,hs.1 _ hl] at h
  exact (by decide : ¬ Even 13) h

private theorem deg_classes140 {S : Finset Block} (hs : Valid S) (sz : S.card = 140)
    (no : ∀ x, deg S x ≠ 12) :
    (∑ x : P, marks (deg S x)) = 17 ∧
    ∀ x, deg S x = 10 ∨ deg S x = 11 ∨ deg S x = 13 := by
  classical
  have h₁ := countWeights S (fun _ => (1:ℤ))
  have cardL (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at h₁
  rw [sum_congr rfl cardL] at h₁
  simp [sz] at h₁
  have h₂ := countWeights S (fun x => (deg S x : ℤ))
  have ld (l : Block) (hl : l ∈ S) : (∑ x ∈ l, (deg S x : ℤ)) = 152 := by
    rw [onLine hs hl, sz]; norm_num
  rw [sum_congr rfl ld] at h₂
  simp [sz] at h₂
  let o := (univ : Finset P).filter (fun x => Even (deg S x))
  have oc : (∑ x : P, marks (deg S x)) = (o.card : ℤ) := by
    simp only [marks,← sum_filter,sum_const,nsmul_eq_mul,mul_one]; rfl
  have markEquiv (l : Block) (hl : l ∈ S) : 1 ≤ ∑ x ∈ l, marks (deg S x) := by
    have p : Even (∑ x ∈ l, deg S x) := by
      have v : ∑ x ∈ l, deg S x = 152 := by exact_mod_cast ld l hl
      rw [v]; decide
    exact oneEvenPerLine hs hl p
  have tbl (x : P) : 0 ≤ surplus (deg S x) ∧
      (surplus (deg S x) = 0 ∨ 8 ≤ surplus (deg S x)) ∧
      (surplus (deg S x) = 0 → deg S x = 10 ∨ deg S x = 11 ∨ deg S x = 13) ∧
      (deg S x : ℤ)*marks (deg S x) ≤ 10*marks (deg S x) :=
    scoreTable ⟨deg S x,by have := degree_cap hs x; omega⟩ (no x)
  have need := sum_le_sum markEquiv
  rw [← countWeights] at need
  simp only [sum_const,sz,nsmul_eq_mul,mul_one,Nat.cast_ofNat] at need
  have lim := sum_le_sum (fun x (_ : x ∈ (univ : Finset P)) => (tbl x).2.2.2)
  rw [← mul_sum,oc] at lim
  have sumScore : (∑ x : P, score (deg S x)) = 51 := by
    have e (x : P) : score (deg S x) = (deg S x : ℤ)*(deg S x) - 24*deg S x+143 := by
      dsimp [score]; ring
    simp only [e,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,h₁,h₂]; rfl
  have excess : (∑ x : P, surplus (deg S x)) = 51-3*(o.card:ℤ) := by
    simp only [surplus,sum_sub_distrib,← mul_sum,sumScore,oc]
  have small (x : P) : surplus (deg S x) ≤ 51-3*(o.card:ℤ) := by
    rw [← excess]
    exact single_le_sum (fun y _ => (tbl y).1) (mem_univ x)
  have nn := (tbl (0 : P)).1
  have q := small 0
  have co : o.card = 14 ∨ o.card = 15 ∨ o.card = 16 ∨ o.card = 17 := by omega
  have parityOdd : Even ((univ : Finset P).filter fun x => Odd (deg S x)).card := by
    apply (Finset.even_sum_iff_even_card_odd _).mp
    have v : ∑ x : P, deg S x = 1820 := by exact_mod_cast h₁
    rw [v]; decide
  have parts := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun x => Even (deg S x))
  simp only [Nat.not_even_iff_odd, card_univ,Fintype.card_fin] at parts
  change o.card + _ = _ at parts
  obtain ⟨k,hk⟩ := parityOdd
  have opts : o.card = 15 ∨ o.card = 17 := by omega
  have co17 : o.card = 17 := by
    rcases opts with bad | good
    · have zeros (x : P) (_ : x ∈ (univ : Finset P)) : surplus (deg S x) = 0 := by
        have c := small x
        have a := (tbl x).2.1
        omega
      rw [sum_congr rfl zeros,bad] at excess; norm_num at excess
    · exact good
  refine ⟨by rw [oc,co17]; rfl, fun x => ?_⟩
  apply (tbl x).2.2.1
  have ub := small x
  have lb := (tbl x).1
  omega


private theorem neighbors_mem {S : Finset Block} {p q : P} :
    q ∈ neighbors S p ↔ q ≠ p ∧ ∃ L ∈ S, p ∈ L ∧ q ∈ L := by
  simp only [neighbors, pencil, mem_biUnion, mem_erase, mem_filter]
  tauto

private theorem neighbor_symm {S : Finset Block} {p q : P} :
    q ∈ neighbors S p ↔ p ∈ neighbors S q := by
  rw [neighbors_mem,neighbors_mem,ne_comm]; aesop

private theorem full_joins {S : Finset Block} (hs : Valid S) {p q : P}
    (h : deg S p = 13) (ne : q ≠ p) : q ∈ neighbors S p := by
  have eq : neighbors S p = univ.erase p := by
    apply eq_of_subset_of_card_le
    · intro x hx; exact mem_erase.mpr ⟨(neighbors_mem.mp hx).1,mem_univ _⟩
    · rw [neighborhood_size hs,h,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
  rw [eq]; exact mem_erase.mpr ⟨ne,mem_univ _⟩

private theorem pencilSum {S : Finset Block} (hs : Valid S) (p : P) (f : P → ℤ) :
    (∑ x ∈ neighbors S p, f x) + (deg S p : ℤ)*f p =
      ∑ L ∈ pencil S p, ∑ x ∈ L, f x := by
  have cst : (deg S p : ℤ)*f p = ∑ _L ∈ pencil S p, f p := by rw [sum_const,nsmul_eq_mul]; rfl
  rw [neighbors,sum_biUnion (pencil_disjoint hs p),cst,← sum_add_distrib]
  exact sum_congr rfl fun L hL => sum_erase_add L _ (mem_filter.mp hL).2

private theorem degree_twelve_140 {S : Finset Block} (hs : Valid S) (sz : S.card = 140) :
    ∃ x, deg S x = 12 := by
  classical
  by_contra! no
  obtain ⟨heavyCount,cls⟩ := deg_classes140 hs sz no
  let m (x : P) := marks (deg S x)
  let h (L : Block) := ∑ x ∈ L, m x
  have incidence (x : P) : (deg S x : ℤ)*m x = 10*m x := by
    rcases cls x with a | a | a <;> norm_num [m,a,marks,Nat.even_iff]
  have lineDegrees (L : Block) (hl : L ∈ S) : (∑ x ∈ L, (deg S x : ℤ)) = 152 := by
    rw [onLine hs hl,sz]; rfl
  have countsTotal := countWeights S (fun _ => (1:ℤ))
  have cardL (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at countsTotal
  rw [sum_congr rfl cardL] at countsTotal
  simp [sz] at countsTotal
  have lineBounds (L : Block) (hl : L ∈ S) : 1 ≤ h L ∧ h L ≤ 5 := by
    constructor
    · apply oneEvenPerLine hs hl
      have v : ∑ x ∈ L, deg S x = 152 := by exact_mod_cast lineDegrees L hl
      rw [v]; decide
    · have cost (x : P) (_ : x ∈ L) : 3*m x ≤ 13-(deg S x : ℤ) := by
        rcases cls x with a | a | a <;> norm_num [m,a,marks,Nat.even_iff]
      have t := sum_le_sum cost
      rw [← mul_sum, sum_sub_distrib, lineDegrees L hl, sum_const, hs.1 _ hl] at t
      change 3*h L ≤ _ at t
      norm_num at t; omega
  have pencilHeavy (p : P) (hp : deg S p = 10) : (∑ L ∈ pencil S p, h L) = 20 := by
    let N := neighbors S p
    let A := (univ : Finset P) \ N
    have np : N.card = 120 := by rw [show N = neighbors S p from rfl,neighborhood_size hs,hp]
    have ap : A.card = 37 := by
      rw [show A = univ \ N from rfl,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,np]
    have per (x : P) (hx : x ∈ A) : (deg S x : ℤ) + m x = 11 := by
      rcases cls x with hd | hd | hd
      · norm_num [m,hd,marks,Nat.even_iff]
      · norm_num [m,hd,marks,Nat.even_iff]
      · have xp : p ≠ x := by intro eq; subst x; omega
        exact ((mem_sdiff.mp hx).2 (neighbor_symm.mp (full_joins hs hd xp))).elim
    have sD := pencilSum hs p (fun y => (deg S y : ℤ))
    have sumD : (∑ L ∈ pencil S p, ∑ y ∈ L, (deg S y : ℤ)) = 1520 := by
      have ld (L : Block) (hL : L ∈ pencil S p) : (∑ y ∈ L, (deg S y : ℤ)) = 152 := lineDegrees L (mem_filter.mp hL).1
      rw [sum_congr rfl ld,sum_const]
      change (deg S p) • (152:ℤ) = 1520
      rw [hp]; rfl
    rw [sumD,hp] at sD
    have sepD := sum_sdiff (f := fun x => (deg S x : ℤ)) (subset_univ N)
    have sepM := sum_sdiff (f := m) (subset_univ N)
    change (∑ x ∈ A, (deg S x : ℤ)) + (∑ x ∈ N, (deg S x : ℤ)) = _ at sepD
    change (∑ x ∈ A, m x) + (∑ x ∈ N, m x) = _ at sepM
    change (∑ x ∈ N, (deg S x : ℤ)) + _ = _ at sD
    rw [countsTotal] at sepD
    have totM : (∑ x : P, m x) = 17 := heavyCount
    rw [totM] at sepM
    have mix : (∑ x ∈ A, ((deg S x : ℤ) + m x)) = 407 := by
      rw [sum_congr rfl per, sum_const, ap]; rfl
    rw [sum_add_distrib] at mix
    have hSum := pencilSum hs p m
    change (∑ x ∈ N, m x) + (deg S p : ℤ)*m p = ∑ L ∈ pencil S p, h L at hSum
    rw [hp] at hSum
    have mv : m p = 1 := by norm_num [m,marks,hp,Nat.even_iff]
    rw [mv] at hSum
    omega
  have totalLines : (∑ L ∈ S, h L) = 170 := by
    change (∑ L ∈ S, ∑ x ∈ L, m x) = _
    rw [← countWeights,sum_congr rfl (fun x _ => incidence x),← mul_sum]
    change 10*(∑ x : P, marks (deg S x)) = _
    rw [heavyCount]; rfl
  have totalSq : (∑ L ∈ S, h L * h L) = 340 := by
    have weightSq (L : Block) : h L*h L = ∑ x : P, if x ∈ L then m x*h L else 0 := by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, ← sum_mul]
    rw [sum_congr rfl (fun L _ => weightSq L),sum_comm]
    have row (p : P) (_ : p ∈ (univ : Finset P)) :
        (∑ L ∈ S, if p ∈ L then m p*h L else 0) = 20*m p := by
      rw [← sum_filter, ← mul_sum]
      change m p*(∑ L ∈ pencil S p, h L) = 20*m p
      rcases cls p with hd | hd | hd
      · rw [pencilHeavy p hd,mul_comm]
      · norm_num [m,hd,marks,Nat.even_iff]
      · norm_num [m,hd,marks,Nat.even_iff]
    rw [sum_congr rfl row,← mul_sum]
    change 20*(∑ x : P, marks (deg S x)) = _
    rw [heavyCount]; rfl
  have chord (L : Block) (hl : L ∈ S) : h L * h L ≤ 6*h L-5 := by
    have ⟨a,b⟩ := lineBounds L hl
    nlinarith [mul_nonneg (show 0 ≤ h L-1 by omega) (show 0 ≤ 5-h L by omega)]
  have con := sum_le_sum chord
  rw [sum_sub_distrib,← mul_sum,totalLines,totalSq,sum_const,sz] at con
  norm_num at con

theorem extend_140 (S : Finset Block) (sz : S.card = 140) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
  obtain ⟨p,hp⟩ := degree_twelve_140 hs sz
  exact extend_at hs p hp

private theorem score_sum141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141) :
    (∑ x : P, score (deg S x)) = 32 := by
  have h₁ := countWeights S (fun _ => (1:ℤ))
  have size (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at h₁
  rw [sum_congr rfl size] at h₁
  simp [sz] at h₁
  have h₂ := countWeights S (fun x => (deg S x : ℤ))
  have ld (l : Block) (hl : l ∈ S) : (∑ x ∈ l, (deg S x : ℤ)) = 153 := by
    rw [onLine hs hl, sz]; norm_num
  rw [sum_congr rfl ld] at h₂
  simp [sz] at h₂
  have e (x : P) : score (deg S x) = (deg S x : ℤ)*(deg S x)-24*deg S x+143 := by
    dsimp [score]; ring
  simp only [e,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul,h₁,h₂]; rfl

/-- With 141 lines, the absence of a degree-twelve point forces every point
degree to be odd. -/
theorem odd_degrees_141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) : ∀ x, Odd (deg S x) := by
  classical
  intro p
  by_contra! noOdd
  have pe := Nat.not_odd_iff_even.mp noOdd
  have tab : ∀ i : Fin 14, i.val ≠ 12 →
      0 ≤ score i ∧ (Even i.val → 3 ≤ score i ∧ 33 ≤ score i + 3*(i.val:ℤ)) := by decide
  have fact (x : P) : 0 ≤ score (deg S x) ∧
      (Even (deg S x) → 3 ≤ score (deg S x) ∧ 33 ≤ score (deg S x) + 3*(deg S x:ℤ)) :=
    tab ⟨deg S x,by have := degree_cap hs x; omega⟩ (no x)
  have lineNeighbor (l : Block) (hl : l ∈ pencil S p) : ∃ y ∈ l.erase p, Even (deg S y) := by
    obtain ⟨ls,pl⟩ := mem_filter.mp hl
    by_contra! failing
    have odds : ∀ y ∈ l.erase p, Odd (deg S y) := fun y hy => Nat.not_even_iff_odd.mp (failing y hy)
    have erased : Even (∑ x ∈ l.erase p, deg S x) := by
      apply (Finset.even_sum_iff_even_card_odd _).mpr
      rw [filter_eq_self.mpr odds,card_erase_of_mem pl, hs.1 _ ls]
      decide
    have v : ∑ x ∈ l, deg S x = 153 := by
      have s := onLine hs ls
      rw [sz] at s
      norm_num at s
      exact_mod_cast s
    have ev := erased.add pe
    rw [sum_erase_add _ _ pl,v] at ev
    exact (by decide : ¬Even 153) ev
  have lineBound (l : Block) (hl : l ∈ pencil S p) : (3:ℤ) ≤ ∑ x ∈ l.erase p, score (deg S x) := by
    obtain ⟨y,hy,he⟩ := lineNeighbor l hl
    have hit := ((fact y).2 he).1
    exact hit.trans (single_le_sum (fun x _ => (fact x).1) hy)
  have low := sum_le_sum lineBound
  rw [← sum_biUnion (pencil_disjoint hs p),sum_const,nsmul_eq_mul] at low
  change (deg S p:ℤ)*3 ≤ ∑ x ∈ neighbors S p, score (deg S x) at low
  have self : p ∉ neighbors S p := fun h => (neighbors_mem.mp h).1 rfl
  have addcap := sum_le_sum_of_subset_of_nonneg (f := fun x => score (deg S x))
    (subset_univ (insert p (neighbors S p))) (fun x _ _ => (fact x).1)
  rw [sum_insert self,score_sum141 hs sz] at addcap
  have strong := ((fact p).2 pe).2
  omega

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

/-- Either there is an immediate pencil completion, or the degrees of the
141-line configuration have one uniquely determined distribution. -/
theorem degree_counts_141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) :
    (∀ x, deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13) ∧
    ((univ : Finset P).filter (fun x => deg S x = 9)).card = 4 ∧
    ((univ : Finset P).filter (fun x => deg S x = 11)).card = 96 ∧
    ((univ : Finset P).filter (fun x => deg S x = 13)).card = 57 := by
  classical
  let cls (k : ℕ) := (univ : Finset P).filter (fun x => deg S x = k)
  let mark (k : ℕ) (x : P) := if deg S x = k then (1:ℤ) else 0
  have totals (k : ℕ) : (∑ x : P, mark k x) = (cls k).card := by
    simp only [mark,←sum_filter,sum_const,nsmul_eq_mul,mul_one]; rfl
  have rtable : ∀ r : Fin 14, Odd r.val →
    0 ≤ score r ∧ (score r ≤ 32 → r.val=7 ∨ r.val=9 ∨ r.val=11 ∨ r.val=13) := by decide
  have tab (x : P) : 0 ≤ score (deg S x) ∧ (score (deg S x) ≤ 32 →
      deg S x = 7 ∨ deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13) :=
    rtable ⟨deg S x,by have := degree_cap hs x; omega⟩ (odd_degrees_141 hs sz no x)
  have kinds (x : P) : deg S x = 7 ∨ deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13 := by
    apply (tab x).2
    rw [← score_sum141 hs sz]
    exact single_le_sum (fun y _ => (tab y).1) (mem_univ x)
  have sMark (x : P) (_ : x ∈ (univ : Finset P)) : score (deg S x) =
      24*mark 7 x + 8*mark 9 x := by
    rcases kinds x with h|h|h|h <;> norm_num [score,mark,h]
  have sEq := sum_congr rfl sMark
  rw [score_sum141 hs sz,sum_add_distrib,←mul_sum,←mul_sum,totals,totals] at sEq
  have defs (x : P) (_ : x ∈ (univ : Finset P)) : 13-(deg S x : ℤ) =
      6*mark 7 x + 4*mark 9 x + 2*mark 11 x := by
    rcases kinds x with h|h|h|h <;> norm_num [mark,h]
  have h₁ := countWeights S (fun _ => (1:ℤ))
  have size (l : Block) (hl : l ∈ S) : (l.card : ℤ) = 13 := by exact_mod_cast hs.1 l hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at h₁
  rw [sum_congr rfl size] at h₁
  simp [sz] at h₁
  have dEq := sum_congr rfl defs
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,totals,h₁] at dEq
  have dz : (cls 7).card = 0 := by
    by_contra! nonzero
    have k7 : (cls 7).card = 1 := by omega
    have k9 : (cls 9).card = 1 := by omega
    have k11 : (cls 11).card = 99 := by omega
    obtain ⟨z,hz⟩ := card_eq_one.mp k7
    have nz : deg S z = 7 := (mem_filter.mp (show z ∈ cls 7 by rw [hz]; simp)).2
    have lightMiss (p : P) (hp : p ∈ cls 11) : p ∈ univ \ neighbors S z := by
      have dp := (mem_filter.mp hp).2
      refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
      intro near
      let N := neighbors S p
      let A := univ \ N
      have cN : N.card = 132 := by rw [show N = neighbors S p from rfl,neighborhood_size hs,dp]
      have cA : A.card = 25 := by
        rw [show A = univ \ N from rfl,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,cN]
      have aKinds (x : P) (hx : x ∈ A) : deg S x = 9 ∨ deg S x = 11 := by
        rcases kinds x with t|t|t|t
        · have xz : x=z := by
            have mem : x ∈ cls 7 := mem_filter.mpr ⟨mem_univ _,t⟩
            rwa [hz,mem_singleton] at mem
          subst x
          exact ((mem_sdiff.mp hx).2 (neighbor_symm.mp near)).elim
        · exact Or.inl t
        · exact Or.inr t
        · have ne : p ≠ x := by intro eq; subst x; omega
          exact ((mem_sdiff.mp hx).2 (neighbor_symm.mp (full_joins hs t ne))).elim
      have per (x : P) (hx : x ∈ A) : (deg S x : ℤ) =
          11-2*mark 9 x := by rcases aKinds x hx with t|t <;> norm_num [mark,t]
      have sD := pencilSum hs p (fun y => (deg S y : ℤ))
      have singleL (L : Block) (hL : L ∈ pencil S p) :
          (∑ x ∈ L, (deg S x : ℤ)) = 153 := by
        rw [onLine hs (mem_filter.mp hL).1,sz]; norm_num
      rw [sum_congr rfl singleL, sum_const] at sD
      change (∑ x ∈ N, (deg S x:ℤ)) + (deg S p:ℤ)*(deg S p) = (deg S p) • (153:ℤ) at sD
      rw [dp] at sD
      have sep := sum_sdiff (f := fun x => (deg S x:ℤ)) (subset_univ N)
      change (∑ x ∈ A, (deg S x:ℤ)) + (∑ x ∈ N, (deg S x:ℤ)) = _ at sep
      rw [h₁] at sep
      have sumA := sum_congr rfl per
      rw [sum_sub_distrib,sum_const,cA,←mul_sum] at sumA
      have upper := sum_le_sum_of_subset_of_nonneg (f := mark 9) (subset_univ A)
        (fun x _ _ => by dsimp [mark]; split <;> decide)
      rw [totals,k9] at upper
      norm_num at upper sumA sD
      omega
    have num := card_le_card (show cls 11 ⊆ univ \ neighbors S z from lightMiss)
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,
      neighborhood_size hs,nz,k11] at num
    omega
  have eqs : (cls 9).card = 4 ∧ (cls 11).card = 96 := by omega
  have no7 (x : P) : deg S x ≠ 7 := by
    intro bad
    have hx : x ∈ cls 7 := mem_filter.mpr ⟨mem_univ _,bad⟩
    have pos := card_pos.mpr (show (cls 7).Nonempty from ⟨x,hx⟩)
    omega
  have all (x : P) (_ : x ∈ (univ : Finset P)) : (1:ℤ) = mark 9 x + mark 11 x + mark 13 x := by
    rcases (kinds x).resolve_left (no7 x) with t|t|t <;> norm_num [mark,t]
  have count := sum_congr rfl all
  simp only [sum_add_distrib,totals,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at count
  exact ⟨fun x => (kinds x).resolve_left (no7 x),eqs.1,eqs.2,
    (show (cls 13).card = 57 by omega)⟩


end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private def gap (S : Finset Block) (p : P) := univ \ insert p (neighbors S p)

private theorem gap_mem {S : Finset Block} {p q : P} :
    q ∈ gap S p ↔ q ≠ p ∧ q ∉ neighbors S p := by simp [gap]

private theorem gap_symm {S : Finset Block} {p q : P} :
    q ∈ gap S p ↔ p ∈ gap S q := by rw [gap_mem,gap_mem,ne_comm,neighbor_symm]

private theorem self_neigh (S : Finset Block) (p : P) : p ∉ neighbors S p :=
  fun h => (neighbors_mem.mp h).1 rfl

private theorem gap_size {S : Finset Block} (hs : Valid S) (p : P) :
    (gap S p).card = 12*(13-deg S p) := by
  rw [gap,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,
    card_insert_of_notMem (self_neigh _ _),neighborhood_size hs]
  have hb := degree_cap hs p
  omega

private theorem gap_on_block {S : Finset Block} (hs : Valid S) (q : P) {L : Block} (hl : L ∈ S) :
    (L ∩ gap S q).card = if q ∈ L then 0 else 13-deg S q := by
  classical
  by_cases hq : q ∈ L
  · rw [if_pos hq]
    apply card_eq_zero.mpr
    refine eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    obtain ⟨xl,xg⟩ := mem_inter.mp hx
    have xm := gap_mem.mp xg
    exact xm.2 (neighbors_mem.mpr ⟨xm.1,L,hl,hq,xl⟩)
  · rw [if_neg hq]
    have tr : neighbors S q ∩ L = (pencil S q).biUnion (fun a => (a.erase q) ∩ L) := by
      ext x; simp only [neighbors,mem_inter,mem_biUnion]; aesop
    have ct (a : Block) (ha : a ∈ pencil S q) : ((a.erase q) ∩ L).card = 1 := by
      have ⟨as,qa⟩ := mem_filter.mp ha
      have eq : (a.erase q) ∩ L = a ∩ L := by ext x; simp only [mem_inter,mem_erase]; aesop
      rw [eq]; exact meet_card hs as hl (by rintro rfl; exact hq qa)
    have c : (neighbors S q ∩ L).card = deg S q := by
      rw [tr,card_biUnion (fun a ha b hb ne => (pencil_disjoint hs q ha hb ne).mono
        inter_subset_left inter_subset_left),sum_congr rfl ct,sum_const]; simp [deg,pencil]
    have eq : L ∩ gap S q = L \ neighbors S q := by
      ext x; simp only [gap_mem,mem_inter,mem_sdiff]; aesop
    rw [eq,card_sdiff,hs.1 _ hl,c]

private def weight (A : Finset P) (x : P) : ℤ := if x ∈ A then 1 else 0

private theorem sum_weight (W A : Finset P) :
    (∑ x ∈ W, weight A x) = (W ∩ A).card := by
  simp only [weight,←sum_filter,filter_mem_eq_inter,sum_const,nsmul_eq_mul,mul_one]

private theorem common_gaps {S : Finset Block} (hs : Valid S) {p q : P} (qp : q ≠ p) :
    ((gap S p ∩ gap S q).card : ℤ) =
      if q ∈ gap S p then (12-(deg S p:ℤ))*(13-deg S q) + deg S p - 1
      else (13-(deg S p:ℤ))*(13-deg S q) := by
  classical
  let g := gap S q
  let I := (pencil S p).filter (q ∈ ·)
  have fcard : (I.card:ℤ) = if q ∈ gap S p then 0 else 1 := by
    by_cases h : q ∈ gap S p
    · rw [if_pos h]
      have em : I = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr ?_
        intro L hL
        have ⟨ls,ql⟩ := mem_filter.mp hL
        have ⟨ls',pl⟩ := mem_filter.mp ls
        exact (gap_mem.mp h).2 (neighbors_mem.mpr ⟨qp,L,ls',pl,ql⟩)
      rw [em]; rfl
    · rw [if_neg h]
      have joined : q ∈ neighbors S p := by
        by_contra n; exact h (gap_mem.mpr ⟨qp,n⟩)
      obtain ⟨_,L,ls,pl,ql⟩ := neighbors_mem.mp joined
      have one : I.card = 1 := by
        apply card_eq_one.mpr
        refine ⟨L,?_⟩
        ext M
        simp only [I,pencil,mem_filter,mem_singleton]
        constructor
        · rintro ⟨⟨ms,pm⟩,qm⟩
          by_contra ne
          obtain ⟨_,_,uniq⟩ := hs.2 M ms L ls ne
          exact qp ((uniq q ⟨qm,ql⟩).trans (uniq p ⟨pm,pl⟩).symm)
        · rintro rfl; exact ⟨⟨ls,pl⟩,ql⟩
      exact_mod_cast one
  have partition := sum_sdiff (f := weight g) (subset_univ (insert p (neighbors S p)))
  change (∑ x ∈ gap S p, weight g x) + _ = _ at partition
  rw [sum_insert (self_neigh _ _),sum_weight,sum_weight,sum_weight,univ_inter] at partition
  have pc := pencilSum hs p (weight g)
  rw [sum_weight] at pc
  have kg : (13-deg S q:ℕ) = 13-(deg S q : ℤ) := by
    rw [Nat.cast_sub (degree_cap hs q)]; rfl
  have geom (L : Block) (hl : L ∈ pencil S p) :
      (∑ x ∈ L, weight g x) =
      (if q ∈ L then (0:ℤ) else 13-deg S q) := by
    rw [sum_weight]
    change ((L ∩ gap S q).card:ℤ) = _
    rw [gap_on_block hs q (mem_filter.mp hl).1]
    split <;> simp [*]
  rw [sum_congr rfl geom,sum_ite, sum_const_zero,zero_add,sum_const,nsmul_eq_mul] at pc
  let other := (pencil S p).filter (fun L => q ∉ L)
  have two := card_filter_add_card_filter_not (s := pencil S p) (fun L => q ∈ L)
  change I.card + other.card = deg S p at two
  have ocast : (other.card:ℤ) = (deg S p:ℤ) - I.card := by omega
  change _ = (other.card:ℤ) * (13 - (deg S q:ℤ)) at pc
  rw [ocast,fcard] at pc
  have ord : (g.card:ℤ) = 12*(13-(deg S q:ℤ)) := by
    change ((gap S q).card:ℤ) = _
    rw [gap_size hs,Nat.cast_mul,kg]; rfl
  rw [ord] at partition
  have ww : weight g p = if q ∈ gap S p then 1 else 0 := by simp [weight,g,gap_symm (p:=q) (q:=p)]
  rw [ww] at pc partition
  change ((gap S p ∩ g).card:ℤ) = _
  split <;> rename_i h
  · simp only [if_pos h] at pc partition
    nlinarith only [pc,partition]
  · simp only [if_neg h] at pc partition
    nlinarith only [pc,partition]

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private def light (S : Finset Block) : Finset P := univ.filter (fun x => deg S x = 11)
private def heavy (S : Finset Block) : Finset P := univ.filter (fun x => deg S x = 9)

private theorem mlight {S : Finset Block} {x : P} : x ∈ light S ↔ deg S x = 11 := by simp [light]
private theorem mheavy {S : Finset Block} {x : P} : x ∈ heavy S ↔ deg S x = 9 := by simp [heavy]

private theorem breakdown141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) (p : P) (d : deg S p = 9 ∨ deg S p = 11) :
    (gap S p ∩ heavy S).card = (if deg S p = 9 then 0 else 2) ∧
    (gap S p ∩ light S).card = (if deg S p = 9 then 48 else 22) := by
  classical
  obtain ⟨kinds,_,_,_⟩ := degree_counts_141 hs sz no
  have all (x : P) (hx : x ∈ gap S p) : deg S x = 9 ∨ deg S x = 11 := by
    have g := gap_mem.mp hx
    rcases kinds x with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (g.2 (neighbor_symm.mp (full_joins hs h g.1.symm))).elim
  have degreeSum := countWeights S (fun _ => (1:ℤ))
  have sizes (L : Block) (hl : L ∈ S) : (L.card:ℤ) = 13 := by exact_mod_cast hs.1 L hl
  simp only [mul_one,sum_const,nsmul_eq_mul] at degreeSum
  rw [sum_congr rfl sizes] at degreeSum; simp [sz] at degreeSum
  have lds (L : Block) (hl : L ∈ pencil S p) : (∑ x ∈ L, (deg S x:ℤ)) = 153 := by
    rw [onLine hs (mem_filter.mp hl).1,sz]; norm_num
  have ps := pencilSum hs p (fun y => (deg S y:ℤ))
  rw [sum_congr rfl lds,sum_const] at ps
  change _ = deg S p • (153:ℤ) at ps
  have partition := sum_sdiff (f := fun x => (deg S x:ℤ)) (subset_univ (insert p (neighbors S p)))
  change (∑ x ∈ gap S p, (deg S x:ℤ)) + _ = _ at partition
  rw [degreeSum, sum_insert (self_neigh _ _)] at partition
  have val (x : P) (hx : x ∈ gap S p) : (deg S x:ℤ) =
      11 - 2*weight (heavy S) x := by
    rcases all x hx with h|h <;> simp [weight,mheavy,h]
  have per (x : P) (hx : x ∈ gap S p) :
      weight (heavy S) x + weight (light S) x = 1 := by
    rcases all x hx with h|h <;> simp [weight,mheavy,mlight,h]
  have sumval := sum_congr rfl val
  have sumper := sum_congr rfl per
  rw [sum_add_distrib,sum_weight,sum_weight,sum_const,gap_size hs] at sumper
  rw [sum_sub_distrib,←mul_sum,sum_weight,sum_const,gap_size hs] at sumval
  rcases d with low|high
  · rw [low] at ps partition sumper sumval ⊢
    norm_num at ps partition sumper sumval
    constructor <;> split <;> omega
  · rw [high] at ps partition sumper sumval ⊢
    norm_num at ps partition sumper sumval
    constructor <;> split <;> omega

private theorem extendingClique {S : Finset Block} (hs : Valid S) (C : Block)
    (size : C.card = 13) (uncov : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → y ∈ gap S x)
    (allDeg : (∑ x ∈ C, (deg S x:ℤ)) = S.card) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card+1 ∧ Valid T := by
  classical
  have leOne (L : Block) (hl : L ∈ S) : (L ∩ C).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra h
    have g := gap_mem.mp (uncov x (mem_inter.mp hx).2 y (mem_inter.mp hy).2 h)
    exact g.2 (neighbors_mem.mpr ⟨Ne.symm h,L,hl,(mem_inter.mp hx).1,(mem_inter.mp hy).1⟩)
  have dsum := countWeights S (weight C)
  simp only [weight,mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,univ_inter,
    sum_const,nsmul_eq_mul] at dsum
  rw [allDeg] at dsum
  have dif (L : Block) (hl : L ∈ S) : 0 ≤ 1-((L ∩ C).card:ℤ) := by
    have := leOne L hl; omega
  have zero : ∑ L ∈ S, (1-((L ∩ C).card:ℤ)) = 0 := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,←dsum,sub_self]
  have exact1 (L : Block) (hl : L ∈ S) : (L ∩ C).card = 1 := by
    have := (sum_eq_zero_iff_of_nonneg dif).mp zero L hl
    omega
  have fresh : C ∉ S := by
    intro hh; have t := exact1 C hh
    rw [inter_self,size] at t; contradiction
  have single {a b : Block} (h : (a ∩ b).card = 1) : ∃! x, x ∈ a ∧ x ∈ b := by
    obtain ⟨x,hx⟩ := card_eq_one.mp h
    have key (y : P) : (y ∈ a ∧ y ∈ b) ↔ y = x := by rw [← mem_inter,hx,mem_singleton]
    exact ⟨x,(key x).mpr rfl,fun y hy => (key y).mp hy⟩
  refine ⟨insert C S, subset_insert _ _, card_insert_of_notMem fresh, ?_, ?_⟩
  · intro L hl; rcases mem_insert.mp hl with rfl|h
    · exact size
    · exact hs.1 L h
  · intro a ha b hb ne
    rcases mem_insert.mp ha with hA | ha'
    · subst a
      rcases mem_insert.mp hb with hbE | hb'
      · exact (ne hbE.symm).elim
      · exact single (by rw [inter_comm]; exact exact1 _ hb')
    · rcases mem_insert.mp hb with hB | hb'
      · subst b; exact single (exact1 _ ha')
      · exact hs.2 _ ha' _ hb' ne

end PlaneTwelve.Seed

/-!
# The 22 light neighbors at a point in a partial plane of order twelve

The local graph in the 141-line case has two distinguished cliques.  The
numerical coloring implication uses Mathlib's Andrásfai–Erdős–Sós theorem.
-/

namespace PlaneTwelve

open Finset SimpleGraph

/-- Three twelve-element neighborhoods in a common twenty-four-element set
cannot have all three pairwise intersections of size at most three. -/
theorem triangleFreeOfNeighborhoodCounts {V X : Type*} [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) (U : Finset X) (f : V → Finset X) (size : U.card = 24)
    (subset : ∀ x, f x ⊆ U) (degree : ∀ x, (f x).card = 12)
    (overlap : ∀ x y, Gᶜ.Adj x y → (f x ∩ f y).card ≤ 3) :
    Gᶜ.CliqueFree 3 := by
  intro s hs
  obtain ⟨x,y,z,xy,xz,yz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  have h₁ := card_union_add_card_inter (f x) (f y)
  have h₂ := card_union_add_card_inter (f x ∪ f y) (f z)
  have h₃ := card_union_le (f x ∩ f z) (f y ∩ f z)
  have h₄ := card_le_card (union_subset (union_subset (subset x) (subset y)) (subset z))
  rw [Finset.union_inter_distrib_right] at h₂
  have := overlap x y xy
  have := overlap y z yz
  have := overlap x z xz
  have := degree x
  have := degree y
  have := degree z
  omega

private theorem boundOffSide {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A K : Finset V)
    (ac : G.IsClique (A : Set V)) (kc : G.IsClique (K : Set V))
    (ca : A.card = 11) (upper : ∀ x, G.degree x ≤ 12)
    {x : V} (xa : x ∈ A) (xk : x ∈ K) :
    (K \ A).card ≤ 2 := by
  classical
  have dis : Disjoint (A.erase x) (K \ A) := by
    apply Finset.disjoint_left.mpr
    intro y ha hk
    exact (mem_sdiff.mp hk).2 (mem_of_mem_erase ha)
  have sub : A.erase x ∪ (K \ A) ⊆ G.neighborFinset x := by
    intro y hy
    apply (G.mem_neighborFinset x y).mpr
    rcases mem_union.mp hy with h | h
    · exact ac xa (mem_erase.mp h).2 (mem_erase.mp h).1.symm
    · have hyA := (mem_sdiff.mp h).2
      exact kc xk (mem_sdiff.mp h).1 (by rintro rfl; exact hyA xa)
  have h := card_le_card sub
  rw [card_union_of_disjoint dis, card_erase_of_mem xa, ca,
    G.card_neighborFinset_eq_degree] at h
  have := upper x
  omega

/-- Every clique with at least five vertices lies on one of the two sides.
In particular the only cliques of size eleven are the two sides. -/
theorem lightNeighborhoodCliques {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : Fintype.card V = 22)
    (triangle : Gᶜ.CliqueFree 3) (upper : ∀ x, G.degree x ≤ 12)
    (cliqueBound : ∀ K : Finset V, G.IsClique (K : Set V) → K.card ≤ 11) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = univ ∧
      A.card = 11 ∧ B.card = 11 ∧ G.IsClique (A : Set V) ∧ G.IsClique (B : Set V) ∧
      (∀ K : Finset V, G.IsClique (K : Set V) → 5 ≤ K.card → K ⊆ A ∨ K ⊆ B) ∧
      (∀ K : Finset V, G.IsClique (K : Set V) → K.card = 11 → K = A ∨ K = B) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have min : 9 ≤ Gᶜ.minDegree := by
    apply Gᶜ.le_minDegree_of_forall_le_degree
    intro x
    rw [SimpleGraph.degree_compl, order]
    have := upper x
    omega
  obtain ⟨C⟩ := SimpleGraph.colorable_of_cliqueFree_lt_minDegree
    (G := Gᶜ) (r := 2) triangle (by rw [order]; omega)
  let A : Finset V := univ.filter (fun x => C x = 0)
  let B : Finset V := univ \ A
  have ma (x : V) : x ∈ A ↔ C x = 0 := by simp [A]
  have mb (x : V) : x ∈ B ↔ C x ≠ 0 := by simp [B,ma]
  have side {x y : V} (h : C x = C y) (ne : x ≠ y) : G.Adj x y := by
    by_contra hxy
    exact C.valid (show Gᶜ.Adj x y from ⟨ne,hxy⟩) h
  have ac : G.IsClique (A : Set V) := by
    intro x hx y hy ne
    exact side (((ma _).mp hx).trans ((ma _).mp hy).symm) ne
  have bc : G.IsClique (B : Set V) := by
    intro x hx y hy ne
    have h₁ := (mb _).mp hx
    have h₂ := (mb _).mp hy
    apply side _ ne
    exact Fin.ext (by omega)
  have dis : Disjoint A B := Finset.disjoint_sdiff
  have union : A ∪ B = univ := by simp [B]
  have both := card_union_of_disjoint dis
  rw [union, card_univ, order] at both
  have ubA := cliqueBound A ac
  have ubB := cliqueBound B bc
  have ca : A.card = 11 := by omega
  have cb : B.card = 11 := by omega
  have cover (K : Finset V) (kc : G.IsClique (K : Set V)) (large : 5 ≤ K.card) :
      K ⊆ A ∨ K ⊆ B := by
    classical
    by_contra! fails
    obtain ⟨x,xk,nxa⟩ := Finset.not_subset.mp fails.1
    obtain ⟨y,yk,nyb⟩ := Finset.not_subset.mp fails.2
    have xb : x ∈ B := mem_sdiff.mpr ⟨mem_univ _,nxa⟩
    have ya : y ∈ A := by simpa [B] using nyb
    have offA := boundOffSide G A K ac kc ca upper ya yk
    have offB := boundOffSide G B K bc kc cb upper xb xk
    have split : K \ A ∪ (K \ B) = K := by
      ext z
      by_cases hz : z ∈ A <;> simp [B, hz]
    have h := card_union_le (K \ A) (K \ B)
    rw [split] at h
    omega
  refine ⟨A,B,dis,union,ca,cb,ac,bc,cover,?_⟩
  intro K kc size
  rcases cover K kc (by omega) with h|h
  · exact Or.inl (eq_of_subset_of_card_le h (by omega))
  · exact Or.inr (eq_of_subset_of_card_le h (by omega))

/-- Lift the two sides of an induced neighborhood to 12-cliques in the
whole graph. Every 12-clique through the fixed point is one of these two. -/
theorem liftLightPencil {L : Type*} [Fintype L] [DecidableEq L]
    (G : SimpleGraph L) [DecidableRel G.Adj] (x : L)
    (order : Fintype.card (G.neighborSet x) = 22)
    (triangle : (G.induce (G.neighborSet x))ᶜ.CliqueFree 3)
    (upper : ∀ y, (G.induce (G.neighborSet x)).degree y ≤ 12)
    (bound : ∀ K : Finset (G.neighborSet x),
      (G.induce (G.neighborSet x)).IsClique K → K.card ≤ 11) :
    ∃ A B : Finset L, G.IsNClique 12 A ∧ G.IsNClique 12 B ∧
      A ∩ B = {x} ∧ A ∪ B = insert x (G.neighborFinset x) ∧
      ∀ K : Finset L, G.IsNClique 12 K → x ∈ K → K = A ∨ K = B := by
  classical
  obtain ⟨s,t,dis,su,sc,tc,sk,tk,_,maximal⟩ :=
    lightNeighborhoodCliques (G.induce (G.neighborSet x)) order triangle upper bound
  let e : G.neighborSet x ↪ L := Function.Embedding.subtype _
  let S := s.map e
  let T := t.map e
  have neighbor {U : Finset (G.neighborSet x)} {y : L} (hy : y ∈ U.map e) :
      G.Adj x y := U.property_of_mem_map_subtype hy
  have make (U : Finset (G.neighborSet x)) (uc : U.card = 11)
      (uk : (G.induce (G.neighborSet x)).IsClique (U : Set (G.neighborSet x))) :
      G.IsNClique 12 (insert x (U.map e)) := by
    have nx : x ∉ U.map e := fun hx => (neighbor hx).ne rfl
    refine ⟨?_,by rw [card_insert_of_notMem nx,card_map,uc]⟩
    rw [coe_insert, G.isClique_insert]
    refine ⟨?_,fun y hy _ => neighbor hy⟩
    rw [coe_map]
    exact (G.isClique_induce_iff.mp uk)
  have di : Disjoint S T := by simpa [S,T] using dis
  have un : S ∪ T = G.neighborFinset x := by
    change s.map e ∪ t.map e = _
    rw [← map_union, su]
    ext y
    exact ⟨fun h => (G.mem_neighborFinset _ _).mpr (neighbor h),
      fun h => mem_map.mpr ⟨⟨y,(G.mem_neighborFinset _ _).mp h⟩,mem_univ _,rfl⟩⟩
  refine ⟨insert x S,insert x T,make s sc sk,make t tc tk,?_,?_,?_⟩
  · ext y
    by_cases h : y = x
    · simp [h]
    · have : ¬(y ∈ S ∧ y ∈ T) := fun w => disjoint_left.mp di w.1 w.2
      simp [h,this]
  · simp [un]
  · intro K k12 hx
    let E := K.erase x
    let D := E.subtype (G.Adj x)
    have pre : ∀ y ∈ E, G.Adj x y := by
      intro y hy
      exact k12.1 hx (mem_of_mem_erase hy) (mem_erase.mp hy).1.symm
    have recover : D.map e = E := subtype_map_of_mem pre
    have eleven : G.IsNClique 11 E := k12.erase_of_mem hx
    have ind : (G.induce (G.neighborSet x)).IsNClique 11 D :=
      (G.isNClique_induce_iff _ _ _).mpr (by
        change G.IsNClique 11 (D.map e)
        rw [recover]; exact eleven)
    have which := maximal D ind.1 ind.2
    have back : insert x E = K := insert_erase hx
    rcases which with eq | eq
    · left; rw [← back, ← recover,eq]
    · right; rw [← back, ← recover,eq]

/-- The 12-cliques of the light graph are the vertices of the auxiliary
graph. Each light point has two ends, distinct cliques intersect in at most
one light, and sharing a clique is exactly adjacency for distinct lights. -/
theorem lightCliqueIncidences {L : Type*} [Fintype L] [DecidableEq L]
    (G : SimpleGraph L) [DecidableRel G.Adj]
    (pencil : ∀ x, ∃ A B : Finset L, G.IsNClique 12 A ∧ G.IsNClique 12 B ∧
      A ∩ B = {x} ∧ A ∪ B = insert x (G.neighborFinset x) ∧
      ∀ K : Finset L, G.IsNClique 12 K → x ∈ K → K = A ∨ K = B) :
    let V := ↥(G.cliqueFinset 12)
    let C : V → Finset L := fun i => i.val
    (∀ u, (C u).card = 12) ∧
    (∀ x, (univ.filter (fun u => x ∈ C u)).card = 2) ∧
    (∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) ∧
    (∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ u, x ∈ C u ∧ y ∈ C u) := by
  classical
  dsimp only
  refine ⟨fun u => (SimpleGraph.mem_cliqueFinset_iff.mp u.property).2,?_,?_,?_⟩
  · intro x
    obtain ⟨A,B,as,bs,inter,_,unique⟩ := pencil x
    let a : ↥(G.cliqueFinset 12) := ⟨A,SimpleGraph.mem_cliqueFinset_iff.mpr as⟩
    let b : ↥(G.cliqueFinset 12) := ⟨B,SimpleGraph.mem_cliqueFinset_iff.mpr bs⟩
    have dist : A ≠ B := by
      rintro rfl
      rw [inter_self] at inter
      have c := as.2
      rw [inter,card_singleton] at c
      omega
    have ab : a ≠ b := fun h => dist (congrArg Subtype.val h)
    have both : x ∈ A ∧ x ∈ B := mem_inter.mp (by rw [inter]; simp)
    have eq : univ.filter (fun u : ↥(G.cliqueFinset 12) => x ∈ u.val) = {a,b} := by
      ext u
      simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      constructor
      · intro hx
        exact (unique _ (SimpleGraph.mem_cliqueFinset_iff.mp u.property) hx).imp
          (fun h => Subtype.ext h) (fun h => Subtype.ext h)
      · rintro (rfl|rfl)
        · exact both.1
        · exact both.2
    rw [eq,card_pair ab]
  · intro u v neq
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨A,B,_,_,inter,_,unique⟩ := pencil x
    have U := unique u.val (SimpleGraph.mem_cliqueFinset_iff.mp u.property) (mem_inter.mp hx).1
    have V := unique v.val (SimpleGraph.mem_cliqueFinset_iff.mp v.property) (mem_inter.mp hx).2
    have yU := (mem_inter.mp hy).1
    have yV := (mem_inter.mp hy).2
    rcases U with uA|uB <;> rcases V with vA|vB
    · exact (neq (Subtype.ext (uA.trans vA.symm))).elim
    · have yh : y ∈ A ∩ B := mem_inter.mpr ⟨uA ▸ yU,vB ▸ yV⟩
      simpa [inter,eq_comm] using yh
    · have yh : y ∈ A ∩ B := mem_inter.mpr ⟨vA ▸ yV,uB ▸ yU⟩
      simpa [inter,eq_comm] using yh
    · exact (neq (Subtype.ext (uB.trans vB.symm))).elim
  · intro x y
    constructor
    · intro h
      obtain ⟨A,B,as,bs,inter,union,_⟩ := pencil x
      have both : x ∈ A ∧ x ∈ B := mem_inter.mp (by rw [inter]; simp)
      have either : y ∈ A ∪ B := by
        rw [union]
        exact mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr h)
      refine ⟨h.ne,?_⟩
      rcases mem_union.mp either with ha|hb
      · exact ⟨⟨A,SimpleGraph.mem_cliqueFinset_iff.mpr as⟩,both.1,ha⟩
      · exact ⟨⟨B,SimpleGraph.mem_cliqueFinset_iff.mpr bs⟩,both.2,hb⟩
    · rintro ⟨ne,u,hu,hv⟩
      exact (SimpleGraph.mem_cliqueFinset_iff.mp u.property).1 hu hv ne

/-- Convert the gap and pencil counts in an actual 141-line configuration
into the complete local-clique incidence structure. Here `i` includes light
points into the ambient point set, and `pencil` records their old lines. -/
theorem reconstructLightCliques {L P O : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq P] [DecidableEq O] (G : SimpleGraph L) [DecidableRel G.Adj]
    (i : L ↪ P) (U : L → Finset P) (gap : ∀ x y, G.Adj x y ↔ i y ∈ U x)
    (size : ∀ x, (U x).card = 24) (order : ∀ x, G.degree x = 22)
    (adjacent : ∀ x y, G.Adj x y → (U x ∩ U y).card = 12)
    (collinear : ∀ x y, x ≠ y → ¬G.Adj x y → (U x ∩ U y).card ≤ 4)
    (old : Finset O) (pencil : L → Finset O) (oldSize : old.card = 141)
    (oldSub : ∀ x, pencil x ⊆ old) (lineDeg : ∀ x, (pencil x).card = 11)
    (noJoin : ∀ x y, G.Adj x y → Disjoint (pencil x) (pencil y)) :
    let V := ↥(G.cliqueFinset 12)
    let C : V → Finset L := fun j => j.val
    (∀ u, (C u).card = 12) ∧
    (∀ x, (univ.filter (fun u => x ∈ C u)).card = 2) ∧
    (∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) ∧
    (∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ u, x ∈ C u ∧ y ∈ C u) := by
  classical
  apply lightCliqueIncidences G
  intro x
  let N := G.neighborSet x
  let I := G.induce N
  let embed : N ↪ P := (Function.Embedding.subtype _).trans i
  let F (y : N) := U x ∩ U y.val
  have hx (y : N) : G.Adj x y.val := y.property
  have fsize (y : N) : (F y).card = 12 := adjacent _ _ (hx y)
  have tr : Iᶜ.CliqueFree 3 := by
    apply triangleFreeOfNeighborhoodCounts I (U x) F (size x) (fun _ => inter_subset_left) fsize
    intro y z neg
    have yz : y.val ≠ z.val := fun he => neg.1 (Subtype.ext he)
    have bound := collinear _ _ yz (fun h => neg.2 (show I.Adj y z from h))
    have self : i x ∉ U x := fun h => ((gap x x).mpr h).ne rfl
    have outside : i x ∉ F y ∩ F z :=
      fun h => self (mem_inter.mp (mem_inter.mp h).1).1
    have inc : insert (i x) (F y ∩ F z) ⊆ U y.val ∩ U z.val := by
      intro p hp
      rcases mem_insert.mp hp with rfl|hm
      · exact mem_inter.mpr ⟨(gap _ _).mp (hx y).symm,(gap _ _).mp (hx z).symm⟩
      · exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hm).1).2,
                             (mem_inter.mp (mem_inter.mp hm).2).2⟩
    have le := card_le_card inc
    rw [card_insert_of_notMem outside] at le
    omega
  have du (y : N) : I.degree y ≤ 12 := by
    have inc : (I.neighborFinset y).map embed ⊆ F y := by
      intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hp
      have yz : G.Adj y.val z.val := (I.mem_neighborFinset y z).mp hz
      exact mem_inter.mpr ⟨(gap _ _).mp (hx z),(gap _ _).mp yz⟩
    have le := card_le_card inc
    rwa [card_map,I.card_neighborFinset_eq_degree,fsize] at le
  have cap (K : Finset N) (hc : I.IsClique K) : K.card ≤ 11 := by
    let S := K.map (Function.Embedding.subtype _)
    have nx : x ∉ S := fun h => (K.property_of_mem_map_subtype h : G.Adj x x).ne rfl
    have cs : G.IsClique (S : Set L) := by
      rw [Finset.coe_map]; exact (G.isClique_induce_iff.mp hc)
    have ci : G.IsClique ((insert x S : Finset L) : Set L) := by
      rw [coe_insert,G.isClique_insert]
      exact ⟨cs,fun y hy _ => K.property_of_mem_map_subtype hy⟩
    let T := insert x S
    have inc : T.biUnion pencil ⊆ old := by
      intro o h
      obtain ⟨v,_,hv⟩ := mem_biUnion.mp h
      exact oldSub v hv
    have pd : (T : Set L).PairwiseDisjoint pencil :=
      fun _ h _ h' ne => noJoin _ _ (ci h h' ne)
    have le := card_le_card inc
    rw [card_biUnion pd,oldSize] at le
    simp only [lineDeg,Finset.sum_const,smul_eq_mul] at le
    have cardT : T.card = K.card + 1 := by rw [show T = insert x S from rfl,
      card_insert_of_notMem nx,card_map]
    rw [cardT] at le
    omega
  apply liftLightPencil G x _ tr du cap
  simpa [SimpleGraph.degree,SimpleGraph.neighborFinset] using order x

end PlaneTwelve

namespace PlaneTwelve.Seed

open Finset

private def lightGraph (S : Finset Block) : SimpleGraph ↥(light S) where
  Adj x y := y.val ∈ gap S x.val
  symm := ⟨fun _ _ h => gap_symm.mp h⟩
  loopless := ⟨fun _ h => (gap_mem.mp h).1 rfl⟩

private instance (S : Finset Block) : DecidableRel (lightGraph S).Adj :=
  fun x y => inferInstanceAs (Decidable (y.val ∈ gap S x.val))

private theorem lightGraph_adj {S : Finset Block} (x y : ↥(light S)) :
    (lightGraph S).Adj x y ↔ y.val ∈ gap S x.val := Iff.rfl

private theorem light_clique_geometry {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) :
    let V := ↥((lightGraph S).cliqueFinset 12)
    let C : V → Finset ↥(light S) := fun u => u.val
    (∀ u, (C u).card = 12) ∧
    (∀ x, (univ.filter (fun u => x ∈ C u)).card = 2) ∧
    (∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) ∧
    (∀ x y, (lightGraph S).Adj x y ↔ x ≠ y ∧ ∃ u, x ∈ C u ∧ y ∈ C u) := by
  classical
  let G := lightGraph S
  let i : ↥(light S) ↪ P := Function.Embedding.subtype _
  have ld (x : ↥(light S)) : deg S x.val = 11 := mlight.mp x.property
  have sz24 (x : ↥(light S)) : (gap S x.val).card = 24 := by rw [gap_size hs,ld]
  have d22 (x : ↥(light S)) : G.degree x = 22 := by
    have mapped : (G.neighborFinset x).map i = gap S x.val ∩ light S := by
      ext y
      constructor
      · intro h
        obtain ⟨z,hz,rfl⟩ := mem_map.mp h
        exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mp hz,z.property⟩
      · intro h
        obtain ⟨hg,hl⟩ := mem_inter.mp h
        exact mem_map.mpr ⟨⟨y,hl⟩,(G.mem_neighborFinset _ _).mpr hg,rfl⟩
    have counts := (breakdown141 hs sz no x.val (Or.inr (ld x))).2
    simp [ld x] at counts
    rw [← counts, ← mapped,card_map,G.card_neighborFinset_eq_degree]
  have adjcount (x y : ↥(light S)) (h : G.Adj x y) :
      (gap S x.val ∩ gap S y.val).card = 12 := by
    have hg : y.val ∈ gap S x.val := h
    have v := common_gaps hs (gap_mem.mp hg).1
    rw [if_pos hg,ld x,ld y] at v
    omega
  have nonadjcount (x y : ↥(light S)) (h : x ≠ y) (ha : ¬G.Adj x y) :
      (gap S x.val ∩ gap S y.val).card ≤ 4 := by
    have hg : y.val ∉ gap S x.val := ha
    have v := common_gaps hs (show y.val ≠ x.val from fun eq => h (Subtype.ext eq.symm))
    rw [if_neg hg,ld x,ld y] at v
    omega
  have noJoin (x y : ↥(light S)) (h : G.Adj x y) :
      Disjoint (pencil S x.val) (pencil S y.val) := by
    apply disjoint_left.mpr
    intro b hb hb'
    obtain ⟨sb,xb⟩ := mem_filter.mp hb
    obtain ⟨_,yb⟩ := mem_filter.mp hb'
    obtain ⟨ne,absent⟩ := gap_mem.mp (show y.val ∈ gap S x.val from h)
    exact absent (neighbors_mem.mpr ⟨ne,b,sb,xb,yb⟩)
  exact PlaneTwelve.reconstructLightCliques G i (fun x => gap S x.val)
    (fun _ _ => Iff.rfl) sz24 d22 adjcount nonadjcount S (fun x => pencil S x.val) sz
    (fun x => filter_subset _ _) ld noJoin

end PlaneTwelve.Seed

/-!
The final marked-edge argument in the 141-line extension proof.
The graph on 16 vertices has degree 12. The two endpoint weights sum to 8
on an unmarked edge and to 16 on a marked one. Six disjoint unmarked edges
force a vertex of weight 12.
-/

namespace PlaneTwelve.MarkedMatching
open Finset

theorem full_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → Finset V) (order : Fintype.card V = 16) (degree : ∀ x, (N x).card = 12)
    (w : V → ℕ) (bound : ∀ x, w x ≤ 12) (total : ∑ x, w x = 96)
    (edge : ∀ x y, y ∈ N x → w x+w y = 8 ∨ w x+w y = 16)
    (matching : Fin 6 × Bool → V) (injective : Function.Injective matching)
    (unmarked : ∀ i, w (matching (i,false)) + w (matching (i,true)) = 8) :
    ∃ x, w x = 12 := by
  classical
  have common (x y : V) : (N x ∩ N y).Nonempty := by
    apply card_pos.mp
    have a := card_union_add_card_inter (N x) (N y)
    have b := card_le_univ (N x ∪ N y)
    rw [degree,degree] at a
    omega
  have residues (x y : V) : w x % 8 = w y % 8 := by
    obtain ⟨z,hz⟩ := common x y
    have a := edge _ _ (mem_inter.mp hz).1
    have b := edge _ _ (mem_inter.mp hz).2
    omega
  have ne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v := Classical.choice ne
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < (N v).card by rw [degree]; decide)
  have law := edge _ _ hu
  have equ := residues u v
  have opts : w v % 8 = 0 ∨ w v % 8 = 4 := by omega
  by_contra! no
  rcases opts with zero | four
  · have values (x : V) : w x = 0 ∨ w x = 8 := by have := bound x; have := residues x v; omega
    let Z := (univ : Finset V).filter (fun x => w x = 0)
    have pieces (x : V) (_ : x ∈ (univ : Finset V)) :
        w x + (if w x = 0 then 8 else 0) = 8 := by
      rcases values x with h|h <;> simp [h]
    have card := sum_congr rfl pieces
    rw [sum_add_distrib,total,← sum_filter,sum_const,sum_const,card_univ,order] at card
    change 96 + Z.card • 8 = 16 • (8:ℕ) at card
    have cn : 96 + Z.card * 8 = 128 := by
      simpa using card
    have sz : Z.card = 4 := by omega
    let side (i : Fin 6) := decide (w (matching (i,false)) ≠ 0)
    have hits (i : Fin 6) : matching (i,side i) ∈ Z := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      by_cases z : w (matching (i,false)) = 0
      · simp [side,z]
      · have law := unmarked i
        have val := values (matching (i,false))
        have vtrue : w (matching (i,true)) = 0 := by omega
        simpa [side,z] using vtrue
    let pick (i : Fin 6) : Z := ⟨matching (i,side i),hits i⟩
    have inj : Function.Injective pick := by
      intro i j h
      have heq : matching (i,side i) = matching (j,side j) := congrArg Subtype.val h
      exact congrArg Prod.fst (injective heq)
    have hc := Fintype.card_le_of_injective pick inj
    rw [Fintype.card_fin, Fintype.card_coe, sz] at hc
    omega
  · have val (x : V) (_ : x ∈ (univ : Finset V)) : w x = 4 := by
      have e := residues x v
      have b := bound x
      have n := no x
      omega
    rw [sum_congr rfl val,sum_const,card_univ,order] at total
    contradiction

end PlaneTwelve.MarkedMatching

namespace PlaneTwelve.LightCliques
open Finset

variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

def ends (C : V → Finset L) (x : L) : Finset V := univ.filter (x ∈ C ·)

def neighbors (C : V → Finset L) (u : V) : Finset V :=
  (univ.erase u).filter fun v => (C u ∩ C v).Nonempty

def weight (C : V → Finset L) (M : Finset L) (u : V) : ℕ := (C u ∩ M).card

omit [Fintype L] in
/-- Count the incidences between the selected cliques and selected lights. -/
private theorem incidences (C : V → Finset L) (S : Finset V) (T : Finset L) :
    ∑ u ∈ S, (C u ∩ T).card = ∑ x ∈ T, (ends C x ∩ S).card := by
  classical
  have a (u : V) : T.bipartiteAbove (fun u x => x ∈ C u) u = C u ∩ T := by
    ext x; simp [bipartiteAbove, and_comm]
  have b (x : L) : S.bipartiteBelow (fun u x => x ∈ C u) x = ends C x ∩ S := by
    ext u; simp [bipartiteBelow, ends, and_comm]
  simpa only [a,b] using
    (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := S) (t := T) (fun u x => x ∈ C u))

theorem order (C : V → Finset L) (lightOrder : Fintype.card L = 96)
    (size : ∀ u, (C u).card = 12) (two : ∀ x, (ends C x).card = 2) :
    Fintype.card V = 16 := by
  have h := incidences C univ univ
  simp [size,two,lightOrder] at h
  omega

omit [Fintype L] in
theorem total_weight (C : V → Finset L) (M : Finset L) (sz : M.card = 48)
    (two : ∀ x, (ends C x).card = 2) : ∑ u, weight C M u = 96 := by
  simpa [weight,two,sz] using incidences C univ M

omit [Fintype L] [Fintype V] [DecidableEq V] in
theorem weight_bound (C : V → Finset L) (M : Finset L) (size : ∀ u, (C u).card = 12)
    (u : V) : weight C M u ≤ 12 := by
  simpa [weight,size] using (card_le_card (inter_subset_left (s₁ := C u) (s₂ := M)))

omit [Fintype L] in
theorem degree (C : V → Finset L) (size : ∀ u, (C u).card = 12)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1) (u : V) :
    (neighbors C u).card = 12 := by
  classical
  have ht (x : L) (hx : x ∈ C u) : (ends C x ∩ univ.erase u).card = 1 := by
    have e : ends C x ∩ univ.erase u = (ends C x).erase u := by ext v; simp [and_comm]
    rw [e, card_erase_of_mem (by simpa [ends] using hx), two]
  have hi := incidences C (univ.erase u) (C u)
  rw [sum_congr rfl ht] at hi
  simp [size] at hi
  have line (v : V) (hv : v ∈ univ.erase u) :
      (C v ∩ C u).card = if (C u ∩ C v).Nonempty then 1 else 0 := by
    have ub := linear v u (mem_erase.mp hv).1
    rw [inter_comm] at ub ⊢
    by_cases h : (C u ∩ C v).Nonempty
    · have := card_pos.mpr h; simp [h]; omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  rw [sum_congr rfl line, ← sum_filter] at hi
  simpa [neighbors] using hi

omit [Fintype L] in
theorem endpoints {C : V → Finset L} (two : ∀ x, (ends C x).card = 2)
    (x : L) : ∃ u v, u ≠ v ∧ ∀ z, x ∈ C z ↔ z = u ∨ z = v := by
  obtain ⟨u,v,h,he⟩ := card_eq_two.mp (two x)
  refine ⟨u,v,h,fun z => ?_⟩
  have e := Finset.ext_iff.mp he z
  simpa [ends] using e

omit [Fintype L] in
theorem neighbor_edge {C : V → Finset L} {u v : V} (h : v ∈ neighbors C u) :
    u ≠ v ∧ ∃ x, x ∈ C u ∧ x ∈ C v := by
  obtain ⟨hn,x,hx⟩ := mem_filter.mp h
  exact ⟨(mem_erase.mp hn).1.symm,x,mem_inter.mp hx⟩

omit [Fintype L] in
/-- The marked neighbors of the light x are precisely the other marked lights
on one of its two cliques. Counting them gives the endpoint degree law. -/
theorem endpoint_weights (C : V → Finset L) (M : Finset L) (adj : L → L → Prop)
    [DecidableRel adj]
    (graph : ∀ x y, adj x y ↔ x ≠ y ∧ ∃ z, x ∈ C z ∧ y ∈ C z)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1)
    (markCounts : ∀ x, (M.filter (adj x)).card = if x ∈ M then 14 else 8)
    {u v : V} (ne : u ≠ v) {x : L} (hu : x ∈ C u) (hv : x ∈ C v) :
    weight C M u + weight C M v = if x ∈ M then 16 else 8 := by
  classical
  have uniq (z : V) (hz : x ∈ C z) : z = u ∨ z = v := by
    have sub : ({u,v} : Finset V) ⊆ ends C x := by
      intro w hw
      rcases (show w = u ∨ w = v by simpa using hw) with rfl | rfl
      · simpa [ends] using hu
      · simpa [ends] using hv
    have eq := eq_of_subset_of_card_le sub (by simp [two,ne])
    have hz' : z ∈ ends C x := by simpa [ends] using hz
    rw [← eq] at hz'; simpa using hz'
  let U := (C u ∩ M).erase x
  let W := (C v ∩ M).erase x
  have dis : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    obtain ⟨hyx, hyu, _⟩ := (show y ≠ x ∧ y ∈ C u ∧ y ∈ M by simpa [U] using hy)
    have hyv : y ∈ C v := (mem_inter.mp (mem_erase.mp hz).2).1
    exact hyx (card_le_one.mp (linear _ _ ne) _ (mem_inter.mpr ⟨hyu,hyv⟩)
      _ (mem_inter.mpr ⟨hu,hv⟩))
  have cover : U ∪ W = M.filter (adj x) := by
    ext y
    simp only [U,W,mem_union,mem_filter,mem_erase,mem_inter,graph]
    constructor
    · rintro (⟨ny,yu,ym⟩|⟨ny,yv,ym⟩)
      · exact ⟨ym,ny.symm,u,hu,yu⟩
      · exact ⟨ym,ny.symm,v,hv,yv⟩
    · rintro ⟨ym,ny,z,zx,zy⟩
      rcases uniq z zx with rfl|rfl
      · exact Or.inl ⟨ny.symm,zy,ym⟩
      · exact Or.inr ⟨ny.symm,zy,ym⟩
  have eq := card_union_of_disjoint dis
  rw [cover,markCounts] at eq
  dsimp [U,W] at eq
  by_cases hx : x ∈ M
  · rw [if_pos hx, card_erase_of_mem (mem_inter.mpr ⟨hu,hx⟩),card_erase_of_mem (mem_inter.mpr ⟨hv,hx⟩)] at eq
    have a := card_pos.mpr (show (C u ∩ M).Nonempty from ⟨x,mem_inter.mpr ⟨hu,hx⟩⟩)
    have b := card_pos.mpr (show (C v ∩ M).Nonempty from ⟨x,mem_inter.mpr ⟨hv,hx⟩⟩)
    simp [weight,hx]; omega
  · simpa [weight,hx] using eq.symm

end PlaneTwelve.LightCliques

namespace PlaneTwelve.LightCliques
open Finset
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

omit [Fintype L] in
/-- Six pairwise nonadjacent unmarked lights give the six disjoint unmarked
edges required by the marked matching argument. -/
theorem matching (C : V → Finset L) (M : Finset L) (adj : L → L → Prop)
    [DecidableRel adj]
    (graph : ∀ x y, adj x y ↔ x ≠ y ∧ ∃ z, x ∈ C z ∧ y ∈ C z)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1)
    (markCounts : ∀ x, (M.filter (adj x)).card = if x ∈ M then 14 else 8)
    (light : Fin 6 → L) (inj : Function.Injective light)
    (unmarked : ∀ i, light i ∉ M)
    (independent : ∀ i j, i ≠ j → ¬adj (light i) (light j)) :
    ∃ pick : Fin 6 × Bool → V, Function.Injective pick ∧
      ∀ i, weight C M (pick (i,false)) + weight C M (pick (i,true)) = 8 := by
  classical
  choose u v ne hv using fun i => endpoints two (light i)
  let pick : Fin 6 × Bool → V := fun ⟨i,b⟩ => if b then v i else u i
  have inc (i : Fin 6) (b : Bool) : light i ∈ C (pick (i,b)) := by
    apply (hv i _).mpr
    cases b <;> simp [pick]
  refine ⟨pick,?_,?_⟩
  · rintro ⟨i,a⟩ ⟨j,b⟩ he
    have ij : i = j := by
      by_contra ni
      exact independent i j ni ((graph _ _).mpr ⟨fun h => ni (inj h), _, inc i a, he ▸ inc j b⟩)
    subst j
    cases a <;> cases b
    · rfl
    · exact (ne i he).elim
    · exact (ne i he.symm).elim
    · rfl
  · intro i
    have h := endpoint_weights C M adj graph two linear markCounts (ne i)
      ((hv i _).mpr (Or.inl rfl)) ((hv i _).mpr (Or.inr rfl))
    simpa [pick,unmarked] using h

end PlaneTwelve.LightCliques

namespace PlaneTwelve.LightCliques
open Finset

/-- A heavy point and the six unmarked lights on one old line force an
entire 12-clique adjacent to that heavy point. -/
theorem saturated_clique {L V : Type*} [Fintype L] [Fintype V]
    [DecidableEq L] [DecidableEq V] (C : V → Finset L) (M : Finset L)
    (adj : L → L → Prop) [DecidableRel adj] (lightOrder : Fintype.card L = 96)
    (size : ∀ u, (C u).card = 12) (markedCount : M.card = 48)
    (graph : ∀ x y, adj x y ↔ x ≠ y ∧ ∃ z, x ∈ C z ∧ y ∈ C z)
    (two : ∀ x, (ends C x).card = 2)
    (linear : ∀ u v, u ≠ v → (C u ∩ C v).card ≤ 1)
    (markCounts : ∀ x, (M.filter (adj x)).card = if x ∈ M then 14 else 8)
    (light : Fin 6 → L) (inj : Function.Injective light)
    (unmarked : ∀ i, light i ∉ M)
    (independent : ∀ i j, i ≠ j → ¬adj (light i) (light j)) :
    ∃ u, C u ⊆ M := by
  classical
  obtain ⟨pick, hi, hm⟩ := matching C M adj graph two linear markCounts light inj unmarked independent
  obtain ⟨u,full⟩ := PlaneTwelve.MarkedMatching.full_vertex
    (neighbors C) (order C lightOrder size two) (degree C size two linear)
    (weight C M) (weight_bound C M size) (total_weight C M markedCount two)
    (fun u v h => by
      obtain ⟨ne,x,hu,hv⟩ := neighbor_edge h
      have h := endpoint_weights C M adj graph two linear markCounts ne hu hv
      by_cases hx : x ∈ M
      · exact Or.inr (by simpa [hx] using h)
      · exact Or.inl (by simpa [hx] using h)) pick hi hm
  refine ⟨u,?_⟩
  have e : C u ∩ M = C u := eq_of_subset_of_card_le inter_subset_left (by
    change (C u).card ≤ weight C M u; rw [size,full])
  exact fun x h => (mem_inter.mp (show x ∈ C u ∩ M from e.symm ▸ h)).2

end PlaneTwelve.LightCliques


namespace PlaneTwelve.Seed
open Finset

/-- A heavy point lies on a line with no other heavy point. The six light
points on that line are mutually collinear and are collinear to the heavy
point. -/
theorem six_unmarked_141 {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (kinds : ∀ x, deg S x = 9 ∨ deg S x = 11 ∨ deg S x = 13)
    (heavyCard : ((univ : Finset P).filter (fun x => deg S x = 9)).card = 4)
    {e : P} (heavy : deg S e = 9) :
    ∃ light : Fin 6 → P, Function.Injective light ∧
      (∀ i, deg S (light i) = 11 ∧ light i ∈ neighbors S e) ∧
      ∀ i j, i ≠ j → light j ∈ neighbors S (light i) := by
  classical
  let H := (univ : Finset P).filter (fun x => deg S x = 9)
  have he : e ∈ H := mem_filter.mpr ⟨mem_univ _,heavy⟩
  have good : ∃ l ∈ pencil S e, ∀ x ∈ l, deg S x = 9 → x = e := by
    by_contra! no
    let F := pencil S e
    have other (l : F) : ∃ x, x ∈ l.val ∧ deg S x = 9 ∧ x ≠ e := no l.val l.property
    choose p pm ph pn using other
    let f (l : F) : H.erase e := ⟨p l,mem_erase.mpr ⟨pn l,mem_filter.mpr ⟨mem_univ _,ph l⟩⟩⟩
    have inj : Function.Injective f := by
      intro l m eqn
      have eqp : p l = p m := congrArg Subtype.val eqn
      by_contra hne
      have dne : l.val ≠ m.val := fun h => hne (Subtype.ext h)
      have dis := pencil_disjoint hs e l.property m.property dne
      exact disjoint_left.mp dis (mem_erase.mpr ⟨pn l,pm l⟩) (mem_erase.mpr ⟨pn l,eqp ▸ pm m⟩)
    have fewer := Fintype.card_le_of_injective f inj
    rw [Fintype.card_coe,Fintype.card_coe,card_erase_of_mem he] at fewer
    change deg S e ≤ H.card - 1 at fewer
    change H.card = 4 at heavyCard
    omega
  obtain ⟨l,hl,alone⟩ := good
  obtain ⟨ls,el⟩ := mem_filter.mp hl
  let T := l.filter (fun x => deg S x = 11)
  have r (x : P) (hx : x ∈ l) :
      (deg S x : ℤ) = 13 - (if x = e then 4 else 0) - (if deg S x = 11 then 2 else 0) := by
    rcases kinds x with h|h|h
    · have := alone x hx h; subst x; norm_num [heavy]
    · have ne : x ≠ e := fun heq => by subst x; omega
      norm_num [ne,h]
    · have ne : x ≠ e := fun heq => by subst x; omega
      norm_num [ne,h]
  have count := sum_congr rfl r
  rw [onLine hs ls,sz,sum_sub_distrib,sum_sub_distrib,sum_const,hs.1 l ls] at count
  simp only [sum_ite_eq',if_pos el,← sum_filter,sum_const,nsmul_eq_mul] at count
  have six : T.card = 6 := by dsimp [T]; omega
  have cardT : Fintype.card T = 6 := by simpa using six
  let light (i : Fin 6) := ((Fintype.equivFinOfCardEq cardT).symm i).val
  have lt (i : Fin 6) : light i ∈ T := ((Fintype.equivFinOfCardEq cardT).symm i).property
  have inj : Function.Injective light := by
    intro i j h
    exact (Fintype.equivFinOfCardEq cardT).symm.injective (Subtype.ext h)
  refine ⟨light,inj,?_,?_⟩
  · intro i
    obtain ⟨ll,dl⟩ := mem_filter.mp (lt i)
    refine ⟨dl,neighbors_mem.mpr ⟨?_,l,ls,el,ll⟩⟩
    intro heq; rw [heq,heavy] at dl; contradiction
  · intro i j ne
    exact neighbors_mem.mpr ⟨fun h => ne (inj h).symm,l,ls,(mem_filter.mp (lt i)).1,
      (mem_filter.mp (lt j)).1⟩

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

private theorem sixOnLine {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) (e : P) (he : e ∈ heavy S) :
    ∃ f : Fin 6 → ↑(light S), Function.Injective f ∧
      (∀ i, (f i).val ∉ gap S e) ∧
      (∀ i j, i ≠ j → (f j).val ∉ gap S (f i).val) := by
  have ⟨kinds,heavyCard,_,_⟩ := degree_counts_141 hs sz no
  obtain ⟨point,inject,members,pairs⟩ :=
    six_unmarked_141 hs sz kinds heavyCard (mheavy.mp he)
  let f (i : Fin 6) : ↑(light S) := ⟨point i, mlight.mpr (members i).1⟩
  refine ⟨f,fun i j eqn => inject (congrArg Subtype.val eqn),?_,?_⟩
  · intro i hg
    exact (gap_mem.mp hg).2 (members i).2
  · intro i j ne hg
    exact (gap_mem.mp hg).2 (pairs i j ne)

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset
open PlaneTwelve.LightCliques

private theorem saturated_extension {S : Finset Block} (hs : Valid S) (sz : S.card = 141)
    (no : ∀ x, deg S x ≠ 12) (G : SimpleGraph ↑(light S)) [DecidableRel G.Adj]
    (adj : ∀ x y : ↑(light S), G.Adj x y ↔ y.val ∈ gap S x.val)
    (cliques :
      (∀ u : ↥(G.cliqueFinset 12), u.val.card = 12) ∧
      (∀ x, (univ.filter (fun u : ↥(G.cliqueFinset 12) => x ∈ u.val)).card = 2) ∧
      (∀ u v : ↥(G.cliqueFinset 12), u ≠ v → (u.val ∩ v.val).card ≤ 1) ∧
      (∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ u : ↥(G.cliqueFinset 12), x ∈ u.val ∧ y ∈ u.val)) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card+1 ∧ Valid T := by
  classical
  obtain ⟨kinds,heavyCard,lightCard,_⟩ := degree_counts_141 hs sz no
  change (heavy S).card = 4 at heavyCard
  change (light S).card = 96 at lightCard
  obtain ⟨e,he⟩ := card_pos.mp (show 0 < (heavy S).card by omega)
  have de := mheavy.mp he
  have disj : (gap S e ∩ heavy S).card = 0 := by
    simpa [de] using (breakdown141 hs sz no e (Or.inl de)).1
  have glight (x : P) (hx : x ∈ gap S e) : x ∈ light S := by
    rcases kinds x with h|h|h
    · have f := mem_inter.mpr ⟨hx,mheavy.mpr h⟩
      rw [card_eq_zero.mp disj] at f; exact (notMem_empty _ f).elim
    · exact mlight.mpr h
    · have g := gap_mem.mp hx
      exact (g.2 (neighbor_symm.mp (full_joins hs h g.1.symm))).elim
  let M := (gap S e).subtype (· ∈ light S)
  have mMem (x : ↑(light S)) : x ∈ M ↔ x.val ∈ gap S e := mem_subtype
  have msize : M.card = 48 := by
    rw [show M = _ from rfl,card_subtype,filter_eq_self.mpr glight,gap_size hs,de]
  have markCounts (x : ↑(light S)) :
      (M.filter (G.Adj x)).card = if x ∈ M then 14 else 8 := by
    have eq : M.filter (G.Adj x) = ((gap S e ∩ gap S x.val).subtype (· ∈ light S)) := by
      ext y; simp only [mem_filter,mMem,adj,mem_subtype,mem_inter]
    have sub (y : P) (hy : y ∈ gap S e ∩ gap S x.val) : y ∈ light S :=
      glight y (mem_inter.mp hy).1
    rw [eq,card_subtype,filter_eq_self.mpr sub]
    have dx := mlight.mp x.property
    have ne : x.val ≠ e := by intro eq; rw [eq,de] at dx; contradiction
    have c := common_gaps hs ne
    rw [de,dx] at c
    by_cases h : x ∈ M
    · rw [if_pos h]
      rw [if_pos ((mMem _).mp h)] at c
      norm_num at c; exact_mod_cast c
    · rw [if_neg h]
      rw [if_neg (fun a => h ((mMem _).mpr a))] at c
      norm_num at c; exact_mod_cast c
  let E : ↑(light S) ↪ P := Function.Embedding.subtype _
  let C : ↥(G.cliqueFinset 12) → Finset ↑(light S) := fun u => u.val
  obtain ⟨f,fi,miss,ind⟩ := sixOnLine hs sz no e he
  have count : Fintype.card ↑(light S) = 96 := by simpa using lightCard
  obtain ⟨u,full⟩ := saturated_clique C M G.Adj count cliques.1 msize cliques.2.2.2
    cliques.2.1 cliques.2.2.1 markCounts f fi
    (fun i h => miss i ((mMem _).mp h))
    (fun i j ij h => ind i j ij ((adj _ _).mp h))
  let L := (C u).map E
  have sizeL : L.card = 12 := by rw [show L = _ from rfl,card_map]; exact cliques.1 u
  have ly {x : P} (hx : x ∈ L) : x ∈ light S := (C u).property_of_mem_map_subtype hx
  have fresh : e ∉ L := by intro a; have v := mlight.mp (ly a); omega
  have covered {x : P} (hx : x ∈ L) : x ∈ gap S e := by
    obtain ⟨y,hy,eq⟩ := mem_map.mp hx
    rw [← eq]
    exact (mMem _).mp (full hy)
  have clique {x y : P} (hx : x ∈ L) (hy : y ∈ L) (ne : x ≠ y) : y ∈ gap S x := by
    obtain ⟨a,ha,ax⟩ := mem_map.mp hx
    obtain ⟨b,hb,by'⟩ := mem_map.mp hy
    rw [← ax,← by']
    apply (adj _ _).mp
    exact (cliques.2.2.2 _ _).mpr ⟨fun eq => ne (ax.symm.trans ((congrArg E eq).trans by')),u,ha,hb⟩
  apply extendingClique hs (insert e L)
  · rw [card_insert_of_notMem fresh,sizeL]
  · intro x hx y hy ne
    rcases mem_insert.mp hx with ax|lx <;> rcases mem_insert.mp hy with ay|ly'
    · exact (ne (ax.trans ay.symm)).elim
    · rw [ax]; exact covered ly'
    · rw [ay]; exact gap_symm.mp (covered lx)
    · exact clique lx ly' ne
  · have dx (x : P) (hx : x ∈ L) : (deg S x:ℤ) = 11 := by exact_mod_cast mlight.mp (ly hx)
    rw [sum_insert fresh,de,sum_congr rfl dx,sum_const,sizeL,sz]; rfl

end PlaneTwelve.Seed


namespace PlaneTwelve.Seed

/-- Every 141-line seed admits a one-line extension on the same point set. -/
theorem extend_141 (S : Finset Block) (sz : S.card = 141) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card+1 ∧ Valid T := by
  classical
  by_cases hit : ∃ p, deg S p = 12
  · obtain ⟨p, hp⟩ := hit
    exact extend_at hs p hp
  push Not at hit
  exact saturated_extension hs sz hit (lightGraph S) (fun x y => lightGraph_adj x y)
    (light_clique_geometry hs sz hit)

end PlaneTwelve.Seed

namespace PlaneTwelve.Seed
open Finset

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

/-- Every 142-line seed in the variables and incidence relation of the
catalog extends by one line. -/
theorem extend_142 (S : Finset Block) (hc : S.card = 142) (hs : Valid S) :
    ∃ T : Finset Block, S ⊆ T ∧ T.card = S.card + 1 ∧ Valid T := by
  obtain ⟨p,hp⟩ := degree_twelve hs hc
  exact extend_at hs p hp

end PlaneTwelve.Seed

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1.H2 := by
  intro S lo hi size meet
  have h : S.card = 140 ∨ S.card = 141 ∨ S.card = 142 := by omega
  rcases h with h | h | h
  · exact PlaneTwelve.Seed.extend_140 S h ⟨size, meet⟩
  · exact PlaneTwelve.Seed.extend_141 S h ⟨size, meet⟩
  · exact PlaneTwelve.Seed.extend_142 S h ⟨size, meet⟩
