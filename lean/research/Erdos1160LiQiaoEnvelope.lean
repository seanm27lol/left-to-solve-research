import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open Filter Topology

namespace LiQiaoCor1511

/-- The cubic exponent in Li--Qiao v3, equation (161). -/
noncomputable def Q (x : ℝ) : ℝ :=
  (2 / 27 : ℝ) * x ^ 3 - (4 / 9 : ℝ) * x ^ 2

/-- The exact adjacent-exponent calculation in the proof of Corollary 15.11. -/
theorem Q_sub_one_sub_Q (x : ℝ) :
    Q (x - 1) - Q x = -(2 / 9 : ℝ) * x ^ 2 + (10 / 9 : ℝ) * x - 14 / 27 := by
  unfold Q
  ring

/-- For `C ≥ 1`, the upper exponent used in Corollary 15.11 is increasing on
the nonnegative integers. This is the discrete form of the derivative argument
on p. 97 of Li--Qiao v3. -/
theorem Q_add_linear_mono_nat {C : ℝ} (hC : 1 ≤ C) :
    Monotone (fun k : ℕ => Q (k : ℝ) + C * k) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold Q
  have hs : 0 ≤ ((k : ℝ) - (3 / 2 : ℝ)) ^ 2 := sq_nonneg _
  push_cast
  nlinarith

/-- The finite envelope in the first displayed estimate of the proof of
Li--Qiao v3, Corollary 15.11. It isolates exactly what remains after inserting
their two-sided estimate (160): the entire preceding dyadic sum is bounded by
`m` copies of the final upper envelope, divided by the lower envelope at `m`.
-/
theorem dyadic_prefix_envelope (a : ℕ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    {m : ℕ} (hm : 1 ≤ m)
    (ha : ∀ k, 0 ≤ a k)
    (hupper : ∀ k, a k ≤ Real.exp (Real.log 2 * (Q k + C * k)))
    (hlower : Real.exp (Real.log 2 * Q m) ≤ a m) :
    (∑ k ∈ Finset.range m, a k) / a m ≤
      m * Real.exp (Real.log 2 *
        (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1) - Q m)) := by
  have hmono := Q_add_linear_mono_nat hC
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range m, a k :=
    Finset.sum_nonneg fun k _ => ha k
  have hlast : ∀ k ∈ Finset.range m,
      a k ≤ Real.exp (Real.log 2 *
        (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1))) := by
    intro k hk
    have hkm : k ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)
    have he := hmono hkm
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm]
      norm_num
    refine (hupper k).trans (Real.exp_le_exp.mpr ?_)
    simpa [hcast] using mul_le_mul_of_nonneg_left he (Real.log_nonneg (by norm_num))
  have hsum : (∑ k ∈ Finset.range m, a k) ≤
      m * Real.exp (Real.log 2 *
        (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1))) := by
    calc
      (∑ k ∈ Finset.range m, a k) ≤
          ∑ _k ∈ Finset.range m, Real.exp (Real.log 2 *
            (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1))) :=
        Finset.sum_le_sum hlast
      _ = m * Real.exp (Real.log 2 *
            (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1))) := by simp
  have hden : 0 < a m := (Real.exp_pos _).trans_le hlower
  calc
    (∑ k ∈ Finset.range m, a k) / a m ≤
        (m * Real.exp (Real.log 2 *
          (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1)))) /
          Real.exp (Real.log 2 * Q m) := by
      apply (div_le_div_iff₀ hden (Real.exp_pos _)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_right hlower
            (mul_nonneg (Nat.cast_nonneg' m) (Real.exp_pos _).le))
    _ = m * Real.exp (Real.log 2 *
          (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1) - Q m)) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring

end LiQiaoCor1511
