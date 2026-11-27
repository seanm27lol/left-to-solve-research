import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R1
import Mathlib.Algebra.Group.Ext
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Set.Card

/-!
Credit: @seanm27lol, with Codex. The coprime-order projection argument
and the induction over prime-power components are given below. The
table-finiteness and quotient-isomorphism lemmas are adapted from PRs
754 (@kamaleshanantha) and 7292 (@gertjanvdgoot), respectively.
-/

open CategoryTheory

namespace Erdos1160Coprime

abbrev Classes := Quotient (isIsomorphicSetoid FiniteGrp.{0})
def classes (n : ℕ) : Set Classes :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}

/-- Adapted from the finite table encoding in Left to Solve
PR 754 by @kamaleshanantha. -/
private theorem classes_finite (n : ℕ) : (classes n).Finite := by
  let : Finite (Group (Fin n)) :=
    Finite.of_injective (fun h : Group (Fin n) => h.mul) (fun _ _ h => Group.ext h)
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  let code (h : Group (Fin n)) := let _ := h; q (FiniteGrp.of (Fin n))
  apply (Set.finite_range code).subset
  rintro _ ⟨G,hG,rfl⟩
  let _ := Fintype.ofFinite G
  have hh : Fintype.card G = n := (Nat.card_eq_fintype_card (α := G)).symm.trans hG
  let e : Fin n ≃ G := (Fintype.equivFinOfCardEq hh).symm
  let h := e.group
  let _ := h
  let K : FiniteGrp := FiniteGrp.of (Fin n)
  let eg : K ≃* G := e.mulEquiv
  exact ⟨h, Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := K.toGrp) (Y := G.toGrp) eg)⟩⟩

private noncomputable def rep {n : ℕ} (c : classes n) : FiniteGrp.{0} :=
  c.property.choose

private theorem card_rep {n : ℕ} (c : classes n) : Nat.card (rep c) = n :=
  c.property.choose_spec.1

private theorem class_rep {n : ℕ} (c : classes n) :
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep c) = c.val :=
  c.property.choose_spec.2

/-- Isomorphism classes and multiplicative equivalences on bundled finite
groups, as in @gertjanvdgoot's Left to Solve PR 7292, lemma mk_eq_iff. -/
private theorem class_eq_iff (G H : FiniteGrp.{0}) :
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G = Quotient.mk _ H ↔ Nonempty (G ≃* H) := by
  constructor
  · intro h
    obtain ⟨i⟩ := Quotient.exact h
    exact ⟨Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso i)⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨InducedCategory.isoMk (MulEquiv.toGrpIso (X := G.toGrp) (Y := H.toGrp) e)⟩

private theorem recover_left {G H G' H' : Type} [Group G] [Group H] [Group G'] [Group H']
    [Finite G] [Finite H'] [Finite G'] (e : G × H ≃* G' × H')
    (hcop : (Nat.card G).Coprime (Nat.card H')) (hcard : Nat.card G = Nat.card G') :
    Nonempty (G ≃* G') := by
  let embed := e.toMonoidHom.comp (MonoidHom.inl G H)
  let f := (MonoidHom.fst G' H').comp embed
  let u := (MonoidHom.snd G' H').comp embed
  have trivial (x : G) : u x = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      ((orderOf_map_dvd u x).trans (orderOf_dvd_natCard x)) (orderOf_dvd_natCard (u x)))
  have injective : Function.Injective f := by
    intro x y h
    have hxy : embed x = embed y := Prod.ext h ((trivial x).trans (trivial y).symm)
    exact congrArg Prod.fst (e.injective hxy)
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card _).mpr ⟨injective, hcard⟩)⟩

private noncomputable def productClass {a b : ℕ} (x : classes a × classes b) : classes (a*b) :=
  let G := FiniteGrp.of (rep x.1 × rep x.2)
  ⟨Quotient.mk _ G, G, (Nat.card_prod _ _).trans (by rw [card_rep, card_rep]), rfl⟩

/-- A product of two independent classes of coprime orders determines
both classes. -/
theorem coprime_supermultiplicative {a b : ℕ} (h : a.Coprime b) :
    (classes a).ncard * (classes b).ncard ≤ (classes (a*b)).ncard := by
  classical
  let : Finite (classes (a*b)) := (classes_finite _).to_subtype
  have inj : Function.Injective (@productClass a b) := by
    rintro ⟨x,y⟩ ⟨x',y'⟩ he
    let P := FiniteGrp.of (rep x × rep y)
    let Q := FiniteGrp.of (rep x' × rep y')
    have hc : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) P = Quotient.mk _ Q :=
      congrArg Subtype.val he
    obtain ⟨e⟩ := (class_eq_iff P Q).mp hc
    change (rep x × rep y) ≃* (rep x' × rep y') at e
    have hleft := recover_left e (by simpa only [card_rep] using h) (by simp only [card_rep])
    let flip := ((MulEquiv.prodComm (M := rep y) (N := rep x)).trans e).trans
      (MulEquiv.prodComm (M := rep x') (N := rep y'))
    have hright := recover_left flip (by simpa only [card_rep] using h.symm) (by simp only [card_rep])
    apply Prod.ext
    · apply Subtype.ext
      rw [← class_rep x, ← class_rep x']
      exact (class_eq_iff _ _).mpr hleft
    · apply Subtype.ext
      rw [← class_rep y, ← class_rep y']
      exact (class_eq_iff _ _).mpr hright
  have hc := Nat.card_le_card_of_injective _ inj
  rw [Nat.card_prod] at hc
  exact hc

noncomputable def sylowProfile (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, (classes (p ^ n.factorization p)).ncard

theorem profile_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : a.Coprime b) :
    sylowProfile (a*b) = sylowProfile a * sylowProfile b := by
  have side {u v : ℕ} (hv : v ≠ 0) (huv : u.Coprime v) :
      ∀ p ∈ u.primeFactors, (u*v).factorization p = u.factorization p := by
    intro p hp
    have hnd : ¬ p ∣ v := fun hd => Finset.disjoint_left.mp huv.disjoint_primeFactors hp
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, hv⟩)
    rw [Nat.factorization_mul_of_coprime huv, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, Nat.add_zero]
  unfold sylowProfile
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hc.disjoint_primeFactors]
  congr 1
  · exact Finset.prod_congr rfl (fun p hp => by rw [side hb hc p hp])
  · exact Finset.prod_congr rfl (fun p hp => by rw [Nat.mul_comm a b, side ha hc.symm p hp])

/-- All choices of one group for each prime-power part of a fixed positive
order give distinct group isomorphism classes of that order. -/
theorem sylow_profile_lower (n : ℕ) : 0 < n → sylowProfile n ≤ (classes n).ncard := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    simp [sylowProfile, Nat.primeFactors_prime_pow hk.ne' hp, hp.factorization_self]
  | zero => intro h; exact (Nat.not_lt_zero _ h).elim
  | one =>
    intro _
    simp only [sylowProfile, Nat.primeFactors_one, Finset.prod_empty]
    apply (Set.ncard_pos (classes_finite 1)).mpr
    let G := FiniteGrp.of PUnit
    exact ⟨Quotient.mk _ G, G, (show Nat.card PUnit = 1 from Nat.card_unique), rfl⟩
  | coprime a b ha hb hc ia ib =>
    intro _
    have hap : 0 < a := Nat.zero_lt_of_lt ha
    have hbp : 0 < b := Nat.zero_lt_of_lt hb
    rw [profile_mul hap.ne' hbp.ne' hc]
    exact (Nat.mul_le_mul (ia hap) (ib hbp)).trans (coprime_supermultiplicative hc)

end Erdos1160Coprime

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R1.H2 :=
  Erdos1160Coprime.sylow_profile_lower
