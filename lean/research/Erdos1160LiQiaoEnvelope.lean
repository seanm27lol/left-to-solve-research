import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic

open Filter Topology
open scoped Real
open Asymptotics

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

/-- The Gaussian envelope left after the adjacent-exponent calculation tends
to zero.  This is the analytic decay step in the proof of Li--Qiao v3,
Corollary 15.11, isolated from their enumeration estimate (160). -/
theorem envelope_tail_real (C : ℝ) :
    Tendsto (fun x : ℝ => x * Real.exp (Real.log 2 *
      (Q (x - 1) + C * (x - 1) - Q x))) atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquad : (-2 / 9 : ℝ) * Real.log 2 < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hlog
  have hsmall := rexp_neg_quadratic_isLittleO_rpow_atTop hquad
    (((10 / 9 : ℝ) + C) * Real.log 2) (-2)
  have hlinear : (fun x : ℝ => x) =O[atTop] (fun x : ℝ => x) :=
    isBigO_refl _ _
  have hproduct := hsmall.mul_isBigO hlinear
  have hproduct' : (fun x : ℝ =>
      x * Real.exp (((-2 / 9 : ℝ) * Real.log 2) * x ^ 2 +
        (((10 / 9 : ℝ) + C) * Real.log 2) * x)) =o[atTop]
      (fun x : ℝ => x⁻¹) := by
    apply hproduct.congr'
    · exact Filter.Eventually.of_forall (fun x => by ring)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_neg (le_of_lt hx), Real.rpow_two]
      field_simp
  have ht : Tendsto (fun x : ℝ =>
      x * Real.exp (((-2 / 9 : ℝ) * Real.log 2) * x ^ 2 +
        (((10 / 9 : ℝ) + C) * Real.log 2) * x)) atTop (𝓝 0) :=
    hproduct'.tendsto_zero_of_tendsto tendsto_inv_atTop_zero
  have hmul : Tendsto (fun x : ℝ =>
      Real.exp (Real.log 2 * (-(14 / 27 : ℝ) - C)) *
        (x * Real.exp (((-2 / 9 : ℝ) * Real.log 2) * x ^ 2 +
          (((10 / 9 : ℝ) + C) * Real.log 2) * x))) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul ht : Tendsto (fun x : ℝ =>
        Real.exp (Real.log 2 * (-(14 / 27 : ℝ) - C)) *
          (x * Real.exp (((-2 / 9 : ℝ) * Real.log 2) * x ^ 2 +
            (((10 / 9 : ℝ) + C) * Real.log 2) * x))) atTop
        (𝓝 (Real.exp (Real.log 2 * (-(14 / 27 : ℝ) - C)) * 0)))
  convert hmul using 1
  funext x
  unfold Q
  have hexp :
      Real.log 2 *
        ((2 / 27 : ℝ) * (x - 1) ^ 3 - (4 / 9 : ℝ) * (x - 1) ^ 2 +
          C * (x - 1) - ((2 / 27 : ℝ) * x ^ 3 - (4 / 9 : ℝ) * x ^ 2)) =
      Real.log 2 * (-(14 / 27 : ℝ) - C) +
        (((-2 / 9 : ℝ) * Real.log 2) * x ^ 2 +
          (((10 / 9 : ℝ) + C) * Real.log 2) * x) := by ring
  rw [hexp, Real.exp_add]
  ring

/-- The same Gaussian decay along the natural-number indices. -/
theorem envelope_tail_nat (C : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) * Real.exp (Real.log 2 *
      (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1) - Q m))) atTop (𝓝 0) := by
  exact (envelope_tail_real C).comp tendsto_natCast_atTop_atTop

/-- Under the global two-sided form of the Li--Qiao equation-(160) envelope,
the entire preceding dyadic sum is negligible compared with its final term.

This theorem formalizes the analytic limit after (160).  It does not supply
the group-enumeration estimate itself, the reduction from all groups to
2-groups, or the finite-prefix normalization needed when an envelope is
initially stated only eventually. -/
theorem dyadic_prefix_ratio_tendsto_zero (a : ℕ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (ha : ∀ k, 0 ≤ a k)
    (hupper : ∀ k, a k ≤ Real.exp (Real.log 2 * (Q k + C * k)))
    (hlower : ∀ m : ℕ, Real.exp (Real.log 2 * Q m) ≤ a m) :
    Tendsto (fun m : ℕ => (∑ k ∈ Finset.range m, a k) / a m)
      atTop (𝓝 0) := by
  refine squeeze_zero (g := fun m : ℕ => (m : ℝ) * Real.exp (Real.log 2 *
      (Q ((m : ℝ) - 1) + C * ((m : ℝ) - 1) - Q m))) ?_ ?_
        (envelope_tail_nat C)
  · intro m
    exact div_nonneg (Finset.sum_nonneg fun k _ => ha k)
      ((Real.exp_pos _).le.trans (hlower m))
  · intro m
    rcases m with _ | m
    · simp
    · exact dyadic_prefix_envelope a hC (Nat.succ_pos _)
        ha hupper (hlower (m + 1))

/-- An eventual upper exponent envelope can be made global by enlarging its
linear-error constant.  The value at index zero must be supplied separately,
because the expression `Q 0 + C * 0` is independent of `C`.

This is the finite-prefix normalization needed when the upper half of
Li--Qiao equation (160) is presented in eventual big-O form. -/
theorem eventual_upper_envelope_global (a : ℕ → ℝ) (ha0 : a 0 ≤ 1) {C : ℝ}
    (hupper : ∀ᶠ k : ℕ in atTop,
      a k ≤ Real.exp (Real.log 2 * (Q k + C * k))) :
    ∃ C' : ℝ, max 1 C ≤ C' ∧
      ∀ k, a k ≤ Real.exp (Real.log 2 * (Q k + C' * k)) := by
  rcases (eventually_atTop.1 hupper) with ⟨N, hN⟩
  let D : ℕ → ℝ := fun k =>
    Real.log (max 1 (a k)) / Real.log 2 - Q k
  let S : ℝ := ∑ k ∈ Finset.range N, max 0 (D k)
  let C' : ℝ := max 1 C + S
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hbase : max 1 C ≤ C' := by
    dsimp [C']
    linarith
  have hCnonneg : 0 ≤ C' :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans ((le_max_left 1 C).trans hbase)
  refine ⟨C', hbase, ?_⟩
  intro k
  by_cases hkN : N ≤ k
  · have hCC' : C ≤ C' := (le_max_right 1 C).trans hbase
    refine (hN k hkN).trans (Real.exp_le_exp.mpr ?_)
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_right hCC' (Nat.cast_nonneg' k)) (Q k)
  · have hklt : k < N := Nat.lt_of_not_ge hkN
    rcases k with _ | k
    · simpa [Q] using ha0
    · have hmem : k + 1 ∈ Finset.range N := Finset.mem_range.mpr hklt
      have hterm : max 0 (D (k + 1)) ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum
          (fun i hi => le_max_left 0 (D i)) hmem
      have hD : D (k + 1) ≤ S :=
        (le_max_right 0 (D (k + 1))).trans hterm
      have hSC : S ≤ C' := by
        dsimp [C']
        have : 0 ≤ max 1 C :=
          (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left 1 C)
        linarith
      have hDC : D (k + 1) ≤ C' * (k + 1 : ℕ) := by
        have hone : (1 : ℝ) ≤ (k + 1 : ℕ) := by
          exact_mod_cast Nat.succ_pos k
        have hscale : C' ≤ C' * (k + 1 : ℕ) := by
          nlinarith
        exact hD.trans (hSC.trans hscale)
      have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hratio :
          Real.log (max 1 (a (k + 1))) / Real.log 2 ≤
            Q ((k + 1 : ℕ) : ℝ) + C' * (k + 1 : ℕ) := by
        dsimp [D] at hDC
        have hh := (sub_le_iff_le_add).mp hDC
        simpa [add_comm] using hh
      calc
        a (k + 1) ≤ max 1 (a (k + 1)) := le_max_right _ _
        _ = Real.exp (Real.log (max 1 (a (k + 1)))) := by
          rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
        _ ≤ Real.exp (Real.log 2 *
            (Q ((k + 1 : ℕ) : ℝ) + C' * (k + 1 : ℕ))) := by
          apply Real.exp_le_exp.mpr
          have := (div_le_iff₀ hlogpos).mp hratio
          simpa [mul_comm] using this

/-- The Li--Qiao prefix ratio tends to zero when the upper exponent envelope
is only eventually valid.  The lower construction bound remains global, as
in the asymmetric interface extracted from equation (160). -/
theorem dyadic_prefix_ratio_of_eventual_upper
    (a : ℕ → ℝ) (ha0 : a 0 ≤ 1) {C : ℝ}
    (ha : ∀ k, 0 ≤ a k)
    (hupper : ∀ᶠ k : ℕ in atTop,
      a k ≤ Real.exp (Real.log 2 * (Q k + C * k)))
    (hlower : ∀ m : ℕ, Real.exp (Real.log 2 * Q m) ≤ a m) :
    Tendsto (fun m : ℕ => (∑ k ∈ Finset.range m, a k) / a m)
      atTop (𝓝 0) := by
  obtain ⟨C', hC', hupper'⟩ :=
    eventual_upper_envelope_global a ha0 hupper
  exact dyadic_prefix_ratio_tendsto_zero a
    ((le_max_left 1 C).trans hC') ha hupper' hlower

end LiQiaoCor1511
