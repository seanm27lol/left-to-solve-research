import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Order 12, extension from 140 to 141 blocks

Every family of 140 thirteen-point subsets on 157 points with singleton pair
intersections extends by one block. The 140-line counting argument is from
@seanm27lol and collaborators, research commit
79d441ee30269027e2b9d52023925b9d32a88432, with Lean formalization by Codex.
The incidence helpers and pencil construction are reused from the companion
142-line formalization at ad3eedbbb3b968621f9a1d4743e07566ddf851ff.

With no point of degree 12, seventeen points have degree 10, all others 11 or
13. If h counts degree-10 points on each line, summing h gives 170 and
summing its square gives 340. The range 1 ≤ h ≤ 5 bounds the latter by 320.

For 141 lines, if a degree-twelve point is absent, the possible degrees are
9, 11 and 13, with respective multiplicities 4, 96 and 57. This is a
necessary degree distribution; the 141-line extension requires additional
graph arguments.
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

#print axioms extend_140


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

#print axioms degree_counts_141

end PlaneTwelve.Seed
