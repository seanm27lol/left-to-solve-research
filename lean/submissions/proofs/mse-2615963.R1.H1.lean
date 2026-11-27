import OMAReductions.R_mse_2615963_R1
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic

/-!
# The prime direction of Pedja's Chebyshev congruence

Pedja posed the question. In January 2018, mathlove proved the prime
direction and G. Kós identified the monic-polynomial argument formalized here.
The finite-field power sums handle every prime, including 2.
Source: https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials
Lean formalization: @seanm27lol with Codex.
-/

open Finset Polynomial

namespace ChebyshevPrime

private theorem shape (R : Type*) [Field R] (m : ℕ) :
    (Chebyshev.C R m).natDegree ≤ m ∧
      (Chebyshev.C R ((m : ℤ) + 1)).natDegree = m + 1 ∧
        (Chebyshev.C R ((m : ℤ) + 1)).Monic := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hprev, hdegree, hmonic⟩ := ih
    have hX : (X * Chebyshev.C R ((m : ℤ) + 1)).natDegree = m + 1 + 1 := by
      rw [natDegree_X_mul hmonic.ne_zero, hdegree]
    have hlt : (Chebyshev.C R m).natDegree <
        (X * Chebyshev.C R ((m : ℤ) + 1)).natDegree := by rw [hX]; omega
    rw [Nat.cast_succ]
    change _ ∧ (Chebyshev.C R ((m : ℤ) + 2)).natDegree = _ ∧ (Chebyshev.C R ((m : ℤ) + 2)).Monic
    rw [Chebyshev.C_add_two]
    exact ⟨hdegree.le, (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hX,
      (monic_X.mul hmonic).sub_of_left (degree_lt_degree hlt)⟩

private theorem sum_top (p : ℕ) [Fact p.Prime] :
    ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hx (x : ZMod p) : x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
    by_cases h : x = 0
    · simp [h, zero_pow (by omega : p - 1 ≠ 0)]
    · simp [h, ZMod.pow_card_sub_one_eq_one h]
  simp [hx, sum_sub_distrib, ZMod.card]

private theorem sum_monic (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X])
    (hd : f.natDegree = p - 1) (hm : f.Monic) :
    ∑ x : ZMod p, f.eval x = -1 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range, hd, Finset.sum_range_succ]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have small : ∑ i ∈ range (p - 1), ∑ x : ZMod p, f.coeff i * x ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
    simpa [ZMod.card] using mem_range.mp hi
  rw [small, zero_add, ← Finset.mul_sum, ← hd, hm.coeff_natDegree, hd, one_mul, sum_top]

theorem prime_direction (p : ℕ) (hp : p.Prime) :
    Int.ModEq (p : ℤ)
      (∑ k ∈ range p, (Chebyshev.C ℤ ((p : ℤ) - 1)).eval (k : ℤ)) (-1) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let f := Chebyshev.C (ZMod p) ((p : ℤ) - 1)
  have hp2 : 2 ≤ p := hp.two_le
  have hsub : ((p - 2 : ℕ) : ℤ) + 1 = (p : ℤ) - 1 := by omega
  obtain ⟨_, hd, hm⟩ := shape (ZMod p) (p - 2)
  rw [hsub] at hd hm
  have hsum := sum_monic p f (hd.trans (by omega)) hm
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  push_cast
  have hmap (k : ℕ) :
      (((Chebyshev.C ℤ ((p : ℤ) - 1)).eval (k : ℤ) : ℤ) : ZMod p) =
        f.eval (k : ZMod p) := by
    have h := Polynomial.eval_map_apply (p := Chebyshev.C ℤ ((p : ℤ) - 1))
      (Int.castRingHom (ZMod p)) (k : ℤ)
    simpa [f] using h.symm
  simp_rw [hmap]
  calc
    ∑ k ∈ range p, f.eval (k : ZMod p) = ∑ x : ZMod p, f.eval x :=
      Finset.sum_bij' (fun k _ ↦ (k : ZMod p)) (fun x _ ↦ x.val)
        (fun _ _ ↦ mem_univ _) (fun x _ ↦ mem_range.mpr x.val_lt)
        (fun _ hk ↦ ZMod.val_cast_of_lt (mem_range.mp hk))
        (fun x _ ↦ ZMod.natCast_zmod_val x) (fun _ _ ↦ rfl)
    _ = -1 := hsum

end ChebyshevPrime

theorem OMA.solution : OMA.R_mse_2615963_R1.H1 := by
  exact ChebyshevPrime.prime_direction
