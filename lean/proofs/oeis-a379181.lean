import OMAStatements.S_oeis_a379181

/-!
# An exponential gap for the digit mean and mode

The mean of any qualifying word is an integer. Its digit sum is therefore
at most 4n or at least 5n. Two rationally tilted power sums bound both tails
over all decimal words, including words beginning in zero.
-/

open Finset Filter
open scoped BigOperators Topology
open OMA.S_oeis_a379181

namespace IntegerDigitMean
noncomputable section

private def prepend : (ℕ × List ℕ) ↪ List ℕ where
  toFun p := p.1 :: p.2
  inj' := by rintro ⟨a, x⟩ ⟨b, y⟩ h; simpa using h

private def words : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => ((range 10) ×ˢ words n).map prepend

private theorem wordMem (w : List ℕ) (hw : ∀ d ∈ w, d < 10) : w ∈ words w.length := by
  induction w with
  | nil => simp [words]
  | cons a w ih =>
    apply Finset.mem_map.mpr
    refine ⟨(a,w), mem_product.mpr ⟨mem_range.mpr (hw a (by simp)), ?_⟩, rfl⟩
    exact ih (fun d hd => hw d (by simp [hd]))

private theorem digitsBound (k : ℕ) : ∀ d ∈ digitWord k, d < 10 := by
  by_cases hk : k = 0
  · subst k
    simp [digitWord]
  · intro d hd
    exact Nat.digits_lt_base (by decide : 1 < 10) (by simpa [digitWord, hk] using hd)

private theorem decode (k : ℕ) : Nat.ofDigits 10 (digitWord k).reverse = k := by
  by_cases hk : k = 0
  · subst k
    decide
  · simp [digitWord, hk, Nat.ofDigits_digits]

private def encode : ℕ ↪ List ℕ :=
  ⟨digitWord, fun a b h => (decode a).symm.trans
    ((congrArg (fun w : List ℕ => Nat.ofDigits 10 w.reverse) h).trans (decode b))⟩

private theorem total (q : ℝ) (n : ℕ) :
    (∑ w ∈ words n, q ^ w.sum) = (∑ d ∈ range 10, q ^ d) ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words, sum_map, sum_product]
    change (∑ x ∈ range 10, ∑ y ∈ words n, q ^ (x + y.sum)) = _
    simp only [pow_add, ← mul_sum, ih, ← sum_mul, pow_succ']

private abbrev lo : ℝ := 16 / 17
private abbrev hi : ℝ := 17 / 16
private abbrev ceiling : ℝ := 197 / 20

private def weight (n : ℕ) (w : List ℕ) : ℝ :=
  lo ^ w.sum / lo ^ (4 * n) + hi ^ w.sum / hi ^ (5 * n)

private theorem covers (w : List ℕ) (n : ℕ) (hlen : w.length = n)
    (hw : qualifies w = true) : 1 ≤ weight n w := by
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp hw
  have heq : w.sum = m * n := by
    have h := (Bool.and_eq_true_iff.mp hm).2
    simpa [hlen] using h
  unfold weight
  by_cases hm4 : m ≤ 4
  · have h : lo ^ (4 * n) ≤ lo ^ w.sum :=
      pow_le_pow_of_le_one (by norm_num [lo]) (by norm_num [lo]) (heq ▸ Nat.mul_le_mul_right n hm4)
    have hd : 0 < lo ^ (4 * n) := by positivity
    have hh : 1 ≤ lo ^ w.sum / lo ^ (4 * n) := (one_le_div hd).mpr h
    have hp : 0 ≤ hi ^ w.sum / hi ^ (5 * n) := by positivity
    linarith
  · have h : hi ^ (5 * n) ≤ hi ^ w.sum :=
      pow_le_pow_right₀ (by norm_num [hi]) (heq ▸ Nat.mul_le_mul_right n (by omega))
    have hd : 0 < hi ^ (5 * n) := by positivity
    have hh : 1 ≤ hi ^ w.sum / hi ^ (5 * n) := (one_le_div hd).mpr h
    have hp : 0 ≤ lo ^ w.sum / lo ^ (4 * n) := by positivity
    linarith

private theorem envelope (n : ℕ) : (term n : ℝ) ≤ 2 * ceiling ^ n := by
  let S := (range (10 ^ n)).filter (fun k => (digitWord k).length = n ∧ qualifies (digitWord k) = true)
  let T := S.map encode
  have member {w} (hw : w ∈ T) : w.length = n ∧ qualifies w = true ∧ w ∈ words n := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hw
    have hk' := (mem_filter.mp hk).2
    change (digitWord k).length = n ∧ qualifies (digitWord k) = true ∧ digitWord k ∈ words n
    exact ⟨hk'.1, hk'.2, hk'.1 ▸ wordMem (digitWord k) (digitsBound k)⟩
  have cardEq : T.card = term n := by simp [T, S, term]
  calc
    (term n : ℝ) = ∑ _w ∈ T, (1 : ℝ) := by simp [cardEq]
    _ ≤ ∑ w ∈ T, weight n w := sum_le_sum fun w hw => covers w n (member hw).1 (member hw).2.1
    _ ≤ ∑ w ∈ words n, weight n w := by
      apply sum_le_sum_of_subset_of_nonneg (fun _ hw => (member hw).2.2)
      intro w _ _
      unfold weight
      positivity
    _ = ((∑ d ∈ range 10, lo ^ d) / lo ^ 4) ^ n +
          ((∑ d ∈ range 10, hi ^ d) / hi ^ 5) ^ n := by
      simp only [weight, sum_add_distrib, ← Finset.sum_div]
      rw [total lo n, total hi n]
      simp only [pow_mul, div_pow]
    _ ≤ ceiling ^ n + ceiling ^ n := by
      apply add_le_add
      · apply pow_le_pow_left₀ (by positivity)
        norm_num [lo, ceiling, sum_range_succ]
      · apply pow_le_pow_left₀ (by positivity)
        norm_num [hi, ceiling, sum_range_succ]
    _ = 2 * ceiling ^ n := by ring

theorem disproof : ¬ (type_of% @OMA.S_oeis_a379181.main) := by
  intro h
  let R : ℝ := 1999 / 200
  have hR : 0 < R := by norm_num [R]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp h).1 R (by norm_num [R]))
  have pos (n : ℕ) (hn : N ≤ n) : 0 < (term n : ℝ) := by
    have hh := hN n hn
    by_contra! hz
    have hz' : (term n : ℝ) = 0 := le_antisymm hz (by positivity)
    simp [hz'] at hh
    linarith
  have lower (k : ℕ) : (term N : ℝ) * R ^ k ≤ term (N + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hr := (lt_div_iff₀ (pos (N + k) (by omega))).mp (hN (N + k) (by omega))
      rw [pow_succ, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right ih hR.le).trans (by
        simpa only [Nat.add_assoc, mul_comm R] using hr.le)
  have cap (k : ℕ) : (term N : ℝ) ≤ (2 * ceiling ^ N) * (ceiling / R) ^ k := by
    have hx := (lower k).trans (envelope (N + k))
    rw [pow_add] at hx
    rw [div_pow ceiling R k, ← mul_div_assoc, le_div_iff₀ (pow_pos hR k)]
    simpa only [mul_assoc] using hx
  have z : Tendsto (fun k : ℕ => (2 * ceiling ^ N) * (ceiling / R) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2 * ceiling ^ N)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [ceiling, R] : 0 ≤ ceiling / R)
        (by norm_num [ceiling, R] : ceiling / R < 1))
  have he : (term N : ℝ) ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds z cap
  exact (not_lt_of_ge he) (pos N le_rfl)

end
end IntegerDigitMean

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a379181.main) :=
  IntegerDigitMean.disproof
