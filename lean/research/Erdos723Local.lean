import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.BooleanAlgebra

namespace PlaneTwelve
open Finset

/-- Three neighborhoods of size 12 in a set of size 24 cannot have all pairwise
intersections of size at most three. Used to exclude an independent triple in a
local graph at deficiency 14. -/
theorem overlap_of_three {V : Type*} [DecidableEq V] (S A B C : Finset V)
    (hS : S.card = 24) (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (a : A.card = 12) (b : B.card = 12) (c : C.card = 12) :
    4 ≤ (A ∩ B).card ∨ 4 ≤ (A ∩ C).card ∨ 4 ≤ (B ∩ C).card := by
  have s := card_le_card (union_subset (union_subset hA hB) hC)
  have h := card_union_add_card_inter A B
  have k := card_union_add_card_inter (A ∪ B) C
  rw [union_inter_distrib_right] at k
  have l := card_union_le (A ∩ C) (B ∩ C)
  omega

/-- In a triangle-free graph on 24 vertices with all degrees 11, there is an
independent set of size 12. Neighborhoods are given as finsets. -/
theorem coclique_twelve {V : Type*} [DecidableEq V] [Fintype V]
    (N : V → Finset V) (size : Fintype.card V = 24)
    (deg : ∀ x, (N x).card = 11)
    (symm : ∀ {x y}, x ∈ N y → y ∈ N x)
    (tri : ∀ {x y}, x ∈ N y → Disjoint (N x) (N y)) :
    ∃ I : Finset V, I.card = 12 ∧ ∀ x ∈ I, ∀ y ∈ I, y ∉ N x := by
  classical
  have hn : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a := Classical.choice hn
  obtain ⟨b, hba⟩ := card_pos.mp (show 0 < (N a).card by rw [deg]; decide)
  let A := N a
  let B := N b
  have dAB : Disjoint A B := (tri hba).symm
  let R : Finset V := univ \ (A ∪ B)
  have Rcard : R.card = 2 := by
    dsimp [R,A,B]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, size,
      card_union_of_disjoint dAB, deg, deg]
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < R.card by omega)
  have zA : z ∉ A := fun h => (mem_sdiff.mp hz).2 (mem_union_left _ h)
  have zB : z ∉ B := fun h => (mem_sdiff.mp hz).2 (mem_union_right _ h)
  have independent (x : V) : ∀ u ∈ N x, ∀ v ∈ N x, v ∉ N u := by
    intro u hu v hv huv
    exact disjoint_left.mp (tri hu) huv hv
  have allparts (x : V) : x ∈ A ∨ x ∈ B ∨ x ∈ R := by
    by_cases h : x ∈ A ∪ B
    · exact (mem_union.mp h).imp_right Or.inl
    · exact Or.inr (Or.inr (mem_sdiff.mpr ⟨mem_univ _,h⟩))
  have side (U W : Finset V) (p : V) (hp : U = N p)
      (cover : ∀ x, x ∈ U ∨ x ∈ W ∨ x ∈ R) (wcard : W.card = 11)
      (hit : ∃ u ∈ U, u ∈ N z) : (N z ∩ W).card ≤ 2 := by
    obtain ⟨u, hu, huz⟩ := hit
    have c : N u ⊆ W ∪ R := by
      intro v hv
      rcases cover v with hvu | hvw | hvr
      · exfalso
        rw [hp] at hu hvu
        exact independent p u hu v hvu hv
      · exact mem_union_left _ hvw
      · exact mem_union_right _ hvr
    have cover' : N u ∪ (N z ∩ W) ⊆ W ∪ R := by
      apply union_subset c
      intro y hy
      exact mem_union_left _ (mem_inter.mp hy).2
    have d : Disjoint (N u) (N z ∩ W) :=
      (tri huz).mono_right inter_subset_left
    have key := card_le_card cover'
    rw [card_union_of_disjoint d, deg] at key
    have room := card_union_le W R
    omega
  have choice : Disjoint (N z) A ∨ Disjoint (N z) B := by
    by_contra both
    push Not at both
    obtain ⟨u,hu,hua⟩ := not_disjoint_iff.mp both.1
    obtain ⟨v,hv,hvb⟩ := not_disjoint_iff.mp both.2
    have smallB := side A B a rfl allparts (deg b) ⟨u,hua,hu⟩
    have smallA := side B A b rfl (fun x => by
      rcases allparts x with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)) (deg a) ⟨v,hvb,hv⟩
    have cover : N z ⊆ (N z ∩ A) ∪ (N z ∩ B) ∪ R := by
      intro x hx
      rcases allparts x with h | h | h
      · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx,h⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hx,h⟩))
      · exact mem_union_right _ h
    have capacity := card_le_card cover
    have cap1 := card_union_le (N z ∩ A) (N z ∩ B)
    have cap2 := card_union_le ((N z ∩ A) ∪ (N z ∩ B)) R
    have nz := deg z
    omega
  have extend (x : V) (hzx : z ∉ N x) (hdis : Disjoint (N z) (N x)) :
      ∃ I : Finset V, I.card = 12 ∧ ∀ u ∈ I, ∀ v ∈ I, v ∉ N u := by
    refine ⟨insert z (N x), by rw [card_insert_of_notMem hzx, deg], ?_⟩
    intro u hu v hv huv
    by_cases uz : u = z
    · subst u
      by_cases vz : v = z
      · subst v
        exact disjoint_left.mp (tri huv) huv huv
      · exact disjoint_left.mp hdis huv ((mem_insert.mp hv).resolve_left vz)
    · have hu' := (mem_insert.mp hu).resolve_left uz
      by_cases vz : v = z
      · subst v
        exact disjoint_left.mp hdis (symm huv) hu'
      · exact independent x u hu' v ((mem_insert.mp hv).resolve_left vz) huv
  exact choice.elim (extend a zA) (extend b zB)


/-- Full local clique lemma for a deficit-two point in the 143-line case:
its 24 neighbors induce a 12-regular graph, and two nonadjacent vertices
have at most three common neighbors within it. -/
theorem local_clique_at_boundary {V : Type*} [DecidableEq V] [Fintype V]
    (E : V → Finset V) (size : Fintype.card V = 24)
    (deg : ∀ x, (E x).card = 12) (loopless : ∀ x, x ∉ E x)
    (symm : ∀ {x y}, x ∈ E y → y ∈ E x)
    (bound : ∀ {x y}, x ≠ y → y ∉ E x → ((E x) ∩ (E y)).card ≤ 3) :
    ∃ I : Finset V, I.card = 12 ∧ ∀ x ∈ I, ∀ y ∈ I, x ≠ y → y ∈ E x := by
  classical
  let N (x : V) := (univ.erase x) \ E x
  have memN {x y : V} : y ∈ N x ↔ y ≠ x ∧ y ∉ E x := by simp [N]
  have dN (x : V) : (N x).card = 11 := by
    have sub : E x ⊆ univ.erase x := by
      intro v hv
      refine mem_erase.mpr ⟨?_, mem_univ _⟩
      rintro rfl
      exact loopless _ hv
    dsimp [N]
    rw [card_sdiff_of_subset sub, card_erase_of_mem (mem_univ _), card_univ, size, deg]
  have sN {x y : V} (h : x ∈ N y) : y ∈ N x := by
    obtain ⟨hn, hnot⟩ := memN.mp h
    exact memN.mpr ⟨hn.symm, fun h => hnot (symm h)⟩
  have tri {x y : V} (h : x ∈ N y) : Disjoint (N x) (N y) := by
    refine disjoint_left.mpr ?_
    intro z hz₁ hz₂
    obtain ⟨nxy, hxy⟩ := memN.mp h
    obtain ⟨nzx, hzx⟩ := memN.mp hz₁
    obtain ⟨nzy, hzy⟩ := memN.mp hz₂
    have xy := bound nxy (fun h => hxy (symm h))
    have xz := bound nzx.symm hzx
    have yz := bound nzy.symm hzy
    have hS : (univ : Finset V).card = 24 := by simpa using size
    have key := overlap_of_three univ (E x) (E y) (E z) hS
      (subset_univ _) (subset_univ _) (subset_univ _) (deg x) (deg y) (deg z)
    omega
  obtain ⟨I,hI,hind⟩ := coclique_twelve N size dN sN tri
  refine ⟨I,hI,?_⟩
  intro x hx y hy hxy
  by_contra h
  exact hind x hx y hy (memN.mpr ⟨hxy.symm,h⟩)

end PlaneTwelve
