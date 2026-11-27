import OMAReductions.R_mse_2615963_R1
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Squarefree

/-!
# Two restrictions on a composite passing Pedja's test

The residue sum is computed by complete blocks modulo any divisor. This rules
out square divisors. At odd index the polynomial is odd, so negation of the
complete residue system also rules out every even input greater than two.
Source: https://math.stackexchange.com/questions/2615963/a-congruence-involving-chebyshev-polynomials
Lean formalization: @seanm27lol with Codex.
-/

open Finset Polynomial

namespace ChebyshevComposite

private theorem full_blocks (p t : ℕ) (f : ZMod p → ZMod p) :
    ∑ i ∈ range (p * t), f (i : ZMod p) =
      (t : ZMod p) * ∑ i ∈ range p, f (i : ZMod p) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    simp

private theorem sum_cast (p n : ℕ) (f : ℤ[X]) :
    ((∑ i ∈ range n, f.eval (i : ℤ) : ℤ) : ZMod p) =
      ∑ i ∈ range n, (f.map (Int.castRingHom (ZMod p))).eval (i : ZMod p) := by
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp

private theorem congruence_at_divisor {n p : ℕ} (h : p ∣ n) (f : ℤ[X])
    (hn : Int.ModEq (n : ℤ) (∑ i ∈ range n, f.eval (i : ℤ)) (-1)) :
    ∑ i ∈ range n, (f.map (Int.castRingHom (ZMod p))).eval (i : ZMod p) = -1 := by
  rw [← sum_cast]
  simpa using (ZMod.intCast_eq_intCast_iff _ _ p).mpr
    (hn.of_dvd (by exact_mod_cast h))

theorem prime_square_obstruction {p n : ℕ} (hp : p.Prime) (hp2 : p ^ 2 ∣ n)
    (f : ℤ[X]) :
    ¬ Int.ModEq (n : ℤ) (∑ i ∈ range n, f.eval (i : ℤ)) (-1) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, rfl⟩ := hp2
  intro h
  have hmul : p ^ 2 * t = p * (p * t) := by ring
  have eqn := congruence_at_divisor (p := p) (by rw [hmul]; exact dvd_mul_right _ _) f h
  rw [hmul, full_blocks p (p * t) (fun x ↦ (f.map (Int.castRingHom (ZMod p))).eval x)] at eqn
  simpa using eqn

private theorem C_eval_neg (R : Type*) [CommRing R] (x : R) (m : ℕ) :
    (Chebyshev.C R m).eval (-x) = (-1 : R)^m * (Chebyshev.C R m).eval x := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hsucc =>
    push_cast at *
    simp only [Chebyshev.C_add_two, eval_sub, eval_mul, eval_X, hn, hsucc, pow_succ]
    ring

theorem even_obstruction {n : ℕ} (hn : 1 < n) (he : Even n)
    (h : Int.ModEq (n : ℤ)
      (∑ k ∈ range n, (Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1)) : n = 2 := by
  classical
  let : NeZero n := ⟨by omega⟩
  let f := (Chebyshev.C (ZMod n) ((n : ℤ) - 1)).eval
  have hr := congruence_at_divisor (p := n) dvd_rfl _ h
  have hsum : ∑ x : ZMod n, f x = -1 := by
    calc
      ∑ x : ZMod n, f x = ∑ i ∈ range n, f (i : ZMod n) := by
        symm
        exact Finset.sum_bij' (fun k _ ↦ (k : ZMod n)) (fun x _ ↦ x.val)
          (fun _ _ ↦ mem_univ _) (fun x _ ↦ mem_range.mpr x.val_lt)
          (fun _ hk ↦ ZMod.val_cast_of_lt (mem_range.mp hk))
          (fun x _ ↦ ZMod.natCast_zmod_val x) (fun _ _ ↦ rfl)
      _ = -1 := by simpa [f] using hr
  have hodd : Odd (n - 1) := by obtain ⟨k, hk⟩ := he; exact ⟨k - 1, by omega⟩
  have hneg (x : ZMod n) : f (-x) = - f x := by
    dsimp [f]
    rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega, C_eval_neg, hodd.neg_one_pow, neg_one_mul]
  have e : (∑ x : ZMod n, f (-x)) = ∑ x : ZMod n, f x :=
    (Equiv.neg (ZMod n)).sum_comp univ f (by simp)
  simp_rw [hneg] at e
  rw [Finset.sum_neg_distrib, hsum] at e
  have h2 : (2 : ZMod n) = 0 := by linear_combination e
  have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using h2)
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem necessary {n : ℕ} (hn : 1 < n)
    (h : Int.ModEq (n : ℤ)
      (∑ k ∈ range n, (Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1)) :
    n = 2 ∨ Odd n ∧ Squarefree n := by
  rcases Nat.even_or_odd n with he | ho
  · exact Or.inl (even_obstruction hn he h)
  · right
    refine ⟨ho, Nat.squarefree_iff_prime_squarefree.mpr ?_⟩
    intro p hp hd
    exact prime_square_obstruction hp (by simpa [pow_two] using hd) _ h

end ChebyshevComposite

theorem OMA.solution : OMA.R_mse_2615963_R1.H2 := by
  intro n hn h
  exact ChebyshevComposite.necessary hn h
