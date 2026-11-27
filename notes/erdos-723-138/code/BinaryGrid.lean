import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

namespace PlaneTwelve.BinaryGrid
open Finset
noncomputable section
open scoped Classical

/-- A rectangular {0,1} matrix with vanishing additive rectangle differences
depends on a single index. No finiteness or ordering of the indices is needed. -/
theorem depends_on_one_index {I J : Type*} (f : I → J → ℝ)
    (hbin : ∀ i j, f i j = 0 ∨ f i j = 1)
    (hrect : ∀ i i' j j', f i j + f i' j' = f i j' + f i' j) :
    (∀ i j j', f i j = f i j') ∨ (∀ i i' j, f i j = f i' j) := by
  classical
  by_cases hr : ∀ i j j', f i j = f i j'
  · exact Or.inl hr
  · push Not at hr
    obtain ⟨i,j,k,hne⟩ := hr
    have key (x : I) : f x j = f i j := by
      have h := hrect i x j k
      rcases hbin i j with e|e <;> rcases hbin i k with v|v <;>
        rcases hbin x j with d|d <;> rcases hbin x k with c|c <;>
        first | exact d.trans e.symm | exfalso; apply hne; linarith only [h,e,v,d,c]
    right
    intro a b t
    have ha := hrect a i t j
    have hb := hrect b i t j
    linarith only [ha,hb,key a,key b]

def markedCells (f : Fin 9 → Fin 9 → ℝ) : Finset (Fin 9 × Fin 9) :=
  univ.filter fun p => f p.1 p.2 = 1

/-- The signed inner products of a heavy point with the 81 light vectors
have the form a_i+b_j. If there are 27 marks they fill three rows or three
columns, with equality of all cells asserted, not only the count. -/
theorem three_rows_or_columns (a b : Fin 9 → ℝ)
    (hbin : ∀ i j, a i + b j = 0 ∨ a i + b j = 1)
    (hcard : (markedCells fun i j => a i + b j).card = 27) :
    (∃ R : Finset (Fin 9), R.card = 3 ∧ ∀ i j, a i + b j = 1 ↔ i ∈ R) ∨
    (∃ C : Finset (Fin 9), C.card = 3 ∧ ∀ i j, a i + b j = 1 ↔ j ∈ C) := by
  let f := fun i j => a i + b j
  have hb : ∀ i j, f i j = 0 ∨ f i j = 1 := hbin
  have hc : (markedCells f).card = 27 := hcard
  obtain hr | hl := depends_on_one_index f hb (by intros; dsimp [f]; ac_rfl)
  · left
    let R := univ.filter (fun i => f i 0 = 1)
    have he (i j) : f i j = 1 ↔ i ∈ R := by simp [R,hr i j 0]
    have eq : markedCells f = R ×ˢ (univ : Finset (Fin 9)) := by
      ext p; simp [markedCells,he]
    rw [eq,card_product] at hc
    simp only [card_univ,Fintype.card_fin] at hc
    exact ⟨R,by omega,he⟩
  · right
    let C := univ.filter (fun j => f 0 j = 1)
    have he (i j) : f i j = 1 ↔ j ∈ C := by simp [C,hl i 0 j]
    have eq : markedCells f = (univ : Finset (Fin 9)) ×ˢ C := by
      ext p; simp [markedCells,he]
    rw [eq,card_product] at hc
    simp only [card_univ,Fintype.card_fin] at hc
    exact ⟨C,by omega,he⟩

end
end PlaneTwelve.BinaryGrid
#print axioms PlaneTwelve.BinaryGrid.three_rows_or_columns
