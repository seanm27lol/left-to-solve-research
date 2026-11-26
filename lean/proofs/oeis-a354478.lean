import OMAStatements.S_oeis_a354478

/-!
# Reciprocal signed Stirling numbers of the first kind

For n ≥ 4, every interior entry in the unsigned row is at least n(n-1)/2.
The diagonal term is 1, so the sum of the absolute values of the remaining
reciprocals is at most 2/n. This proves Václav Kotešovec's limit.
-/

open Filter Finset
open scoped BigOperators Topology
open OMA.S_oeis_a354478

namespace ReciprocalStirling

private lemma diagonalNeighbor (m : ℕ) :
    (m + 1) * m = 2 * (m + 1).choose 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_one_right]
    nlinarith [ih]

private lemma interior (n k : ℕ) (hn : 4 ≤ n) (hk : 0 < k) (hkn : k < n) :
    n * (n - 1) ≤ 2 * n.stirlingFirst k := by
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    interval_cases k <;> decide
  | succ n hn ih =>
    by_cases edge : k = n
    · subst k
      rw [Nat.stirlingFirst_succ_self_left, Nat.succ_sub_one]
      exact (diagonalNeighbor n).le
    · have hk' : k < n := by omega
      have prev := ih k hk hk'
      rw [Nat.stirlingFirst_succ_left n k (by omega), Nat.succ_sub_one]
      have hsmall : n + 1 ≤ n * (n - 1) := by
        have h : 2 ≤ n - 1 := by omega
        nlinarith [Nat.mul_le_mul_left n h]
      calc
        (n + 1) * n ≤ (2 * n.stirlingFirst k) * n :=
          Nat.mul_le_mul_right n (hsmall.trans prev)
        _ ≤ 2 * (n * n.stirlingFirst k + n.stirlingFirst (k - 1)) := by nlinarith

private noncomputable def summand (n j : ℕ) : ℝ := 1 / (signedStirling n (j + 1) : ℝ)

private lemma absSummand (n j : ℕ) :
    |summand n j| = 1 / (n.stirlingFirst (j + 1) : ℝ) := by
  simp [summand, signedStirling, abs_mul, abs_pow]

private lemma realRow (n : ℕ) :
    ((rowSum n : ℚ) : ℝ) = ∑ j ∈ range n, summand n j := by
  unfold rowSum summand
  push_cast
  rfl

private lemma errorBound (n : ℕ) (hn : 4 ≤ n) :
    |((rowSum n : ℚ) : ℝ) - 1| ≤ 2 / (n : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [realRow, sum_range_succ]
  have last : summand (m + 1) m = 1 := by
    simp [summand, signedStirling, Nat.stirlingFirst_self]
  rw [last, add_sub_cancel_right]
  have hm : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hpos : 0 < (m + 1 : ℝ) * m := by positivity
  calc
    _ ≤ ∑ j ∈ range m, |summand (m + 1) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range m, 2 / ((m + 1 : ℝ) * m) := by
      apply sum_le_sum
      intro j hj
      rw [absSummand]
      have h := interior (m + 1) (j + 1) hn (by omega) (by
        have hj' := mem_range.mp hj
        omega)
      rw [Nat.add_sub_cancel] at h
      have b : (m + 1 : ℝ) * m ≤ 2 * ((m + 1).stirlingFirst (j + 1) : ℝ) := by
        exact_mod_cast h
      have bpos : 0 < ((m + 1).stirlingFirst (j + 1) : ℝ) := by linarith
      exact (div_le_div_iff₀ bpos hpos).mpr (by linarith)
    _ = 2 / ((m + 1 : ℕ) : ℝ) := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp

theorem limit : type_of% @OMA.S_oeis_a354478.main := by
  simp only [← Rat.cast_def]
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  filter_upwards [eventually_ge_atTop 4] with n hn
  rw [Real.dist_eq]
  exact errorBound n hn

end ReciprocalStirling

theorem OMA.solution : type_of% @OMA.S_oeis_a354478.main :=
  ReciprocalStirling.limit
