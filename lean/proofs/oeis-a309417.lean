import OMAStatements.S_oeis_a309417

/-!
# Counting repeated subtraction of the decimal digit sum

The positive departure states are all distinct, and their digit sums add to the
starting point. Bounding the fourth moment on all decimal words therefore also
bounds it on those states, without a distributional assumption on the orbit.
-/

open Finset Filter
open scoped BigOperators Topology
open OMA.S_oeis_a309417

namespace DigitSubtraction
noncomputable section

private def ds (x : ℕ) := (Nat.digits 10 x).sum

private lemma decodeZero (l : List ℕ) (h : l.sum = 0) : Nat.ofDigits 10 l = (0 : ℕ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.sum_cons, Nat.add_eq_zero_iff] at h
    rw [Nat.ofDigits_cons, h.1, ih h.2]

private lemma dsPos {x : ℕ} (hx : 0 < x) : 0 < ds x := by
  by_contra! h
  have h0 := decodeZero (Nat.digits 10 x) (Nat.eq_zero_of_le_zero h)
  rw [Nat.ofDigits_digits] at h0
  omega

private lemma orbit (fuel x : ℕ) (hx : x ≤ fuel) :
    ∃ s : Finset ℕ, (∀ y ∈ s, 0 < y ∧ y ≤ x) ∧
      s.card = countSteps fuel x ∧ ∑ y ∈ s, ds y = x := by
  induction fuel generalizing x with
  | zero =>
    have : x = 0 := by omega
    subst x
    exact ⟨∅, by simp, by rfl, by simp⟩
  | succ fuel ih =>
    cases x with
    | zero => exact ⟨∅, by simp, by rfl, by simp⟩
    | succ k =>
      let x := k + 1
      let y := x - ds x
      have hpos : 0 < ds x := dsPos (by dsimp [x]; omega)
      have hle : ds x ≤ x := Nat.digit_sum_le 10 x
      have hy : y < x := by dsimp [y]; omega
      obtain ⟨s, hmem, hcard, hsum⟩ := ih y (by dsimp [x] at hy; omega)
      have fresh : x ∉ s := fun h => (Nat.not_le_of_gt hy) (hmem x h).2
      refine ⟨insert x s, ?_, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hs
        · exact ⟨Nat.zero_lt_succ _, le_rfl⟩
        · exact ⟨(hmem i hs).1, (hmem i hs).2.trans hy.le⟩
      · rw [card_insert_of_notMem fresh, hcard]
        change countSteps fuel y + 1 = 1 + countSteps fuel y
        omega
      · rw [sum_insert fresh, hsum]
        change ds x + (x - ds x) = x
        omega

private lemma dsDigit (h j : ℕ) (hj : j < 10) : ds (j + 10 * h) = j + ds h := by
  by_cases e : j = 0 ∧ h = 0
  · simp [e.1, e.2, ds]
  · simp only [ds, Nat.digits_add 10 (by decide) j h hj (by omega), List.sum_cons]

private lemma dsPower (n : ℕ) : ds (10 ^ n) = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simpa [pow_succ', ih] using dsDigit (10 ^ n) 0 (by decide)

private lemma splitRange (m : ℕ) (f : ℕ → ℝ) :
    (∑ x ∈ range (m * 10), f x) = ∑ h ∈ range m, ∑ j ∈ range 10, f (j + 10 * h) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ (fun h => ∑ j ∈ range 10, f (j + 10 * h))]
    congr 1
    apply sum_congr rfl
    intro j _
    congr 1
    omega

private def dev (n x : ℕ) : ℝ := 2 * (ds x : ℝ) - 9 * n
private def moment (n k : ℕ) : ℝ := ∑ x ∈ range (10 ^ n), dev n x ^ k

private lemma liftMoment (n k : ℕ) :
    moment (n+1) k = ∑ h ∈ range (10 ^ n), ∑ j ∈ range 10,
      (dev n h + (2 * (j : ℝ) - 9)) ^ k := by
  unfold moment
  rw [pow_succ, splitRange]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro j hj
  rw [dev, dsDigit h j (mem_range.mp hj)]
  unfold dev
  push_cast
  ring

private lemma shiftTwo (z : ℝ) :
    (∑ j ∈ range 10, (z + (2 * (j : ℝ) - 9))^2) = 10*z^2+330 := by
  norm_num [sum_range_succ]
  ring

private lemma shiftFour (z : ℝ) :
    (∑ j ∈ range 10, (z + (2 * (j : ℝ) - 9))^4) = 10*z^4+1980*z^2+19338 := by
  norm_num [sum_range_succ]
  ring

private lemma moments (n : ℕ) :
    moment n 2 = 33 * (n : ℝ) * 10^n ∧ moment n 4 ≤ 3300 * (n : ℝ)^2 * 10^n := by
  induction n with
  | zero => norm_num [moment, dev, ds]
  | succ n ih =>
    have h2 := liftMoment n 2
    have h4 := liftMoment n 4
    simp only [shiftTwo, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat] at h2
    simp only [shiftFour, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat] at h4
    change moment (n+1) 2 = 10 * moment n 2 + (10 : ℝ)^n * 330 at h2
    change moment (n+1) 4 = 10 * moment n 4 + 1980 * moment n 2 + (10 : ℝ)^n * 19338 at h4
    constructor
    · rw [h2, ih.1, Nat.cast_succ, pow_succ (10 : ℝ) n]; ring
    · rw [h4, ih.1, Nat.cast_succ, pow_succ (10 : ℝ) n]
      nlinarith [ih.2, show (0:ℝ) ≤ 10^n by positivity,
        show 0 ≤ (n:ℝ) * (10:ℝ)^n by positivity]

private lemma squareBound (n : ℕ) : (n : ℝ)^2 ≤ 10^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ (10 : ℝ) n]
    by_cases h : n = 0
    · subst n; norm_num
    · have hp : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith [sq_nonneg ((n:ℝ)-1), ih]

private lemma allMoment (n : ℕ) (hn : 1 ≤ n) :
    (∑ x ∈ range (10 ^ n + 1), dev n x ^ 4) ≤ 10000 * (n : ℝ)^2 * 10^n := by
  rw [sum_range_succ]
  change moment n 4 + dev n (10^n)^4 ≤ _
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdev : |dev n (10^n)| ≤ 9*(n:ℝ) := by
    rw [dev, dsPower]
    norm_num
    rw [abs_le]
    constructor <;> linarith
  have hb := pow_le_pow_left₀ (abs_nonneg _) hdev 4
  rw [← abs_pow, abs_of_nonneg (by positivity)] at hb
  have hs := mul_le_mul_of_nonneg_left (squareBound n) (sq_nonneg (n : ℝ))
  nlinarith [(moments n).2, hb, hs, show 0 ≤ (n:ℝ)^2 * (10:ℝ)^n by positivity]

private def normalized (n : ℕ) : ℝ := (n : ℝ) * (term n : ℝ) / 10^n

private lemma normalizedNonneg (n : ℕ) : 0 ≤ normalized n := by unfold normalized; positivity

private lemma discrepancy (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (2 - 9 * normalized n)^4 ≤ 10000 * (normalized n)^3 := by
  obtain ⟨s, hmem, hcard, hsum⟩ := orbit (10^n) (10^n) le_rfl
  change s.card = term n at hcard
  have subset : s ⊆ range (10 ^ n + 1) := fun x hx => mem_range.mpr (by have := (hmem x hx).2; omega)
  have hsumR : (∑ x ∈ s, (ds x : ℝ)) = (10 : ℝ)^n := by exact_mod_cast hsum
  have hdev : (∑ x ∈ s, dev n x) = 2 * (10 : ℝ)^n - 9 * n * term n := by
    simp only [dev, sum_sub_distrib, ← mul_sum, hsumR, sum_const, nsmul_eq_mul, hcard]
    ring
  have hfour : (∑ x ∈ s, dev n x ^ 4) ≤ 10000 * (n:ℝ)^2 * 10^n :=
    (sum_le_sum_of_subset_of_nonneg subset (by intros; positivity)).trans (allMoment n hn)
  have jensen := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun x => |dev n x|) (fun x _ => abs_nonneg _) 3
  have tri := pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs (fun x => dev n x) s) 4
  have sj : (∑ x ∈ s, dev n x)^4 ≤ (s.card:ℝ)^3 * ∑ x ∈ s, dev n x^4 := by
    have hh := tri.trans jensen
    have abs4 (a : ℝ) : |a|^4 = a^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    simpa only [abs4] using hh
  rw [hdev, hcard] at sj
  have raw := sj.trans (mul_le_mul_of_nonneg_left hfour (by positivity))
  have nn : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  unfold normalized
  let B : ℝ := 10^n
  have bpos : 0 < B := by dsimp [B]; positivity
  change (n:ℝ) * (2 - 9 * ((n:ℝ) * term n / B))^4 ≤ 10000 * ((n:ℝ) * term n / B)^3
  apply (mul_le_mul_iff_of_pos_right (pow_pos bpos 4)).mp
  change (2*B-9*n*term n)^4 ≤ (term n:ℝ)^3 * (10000*(n:ℝ)^2*B) at raw
  field_simp [bpos.ne']
  nlinarith only [raw]

private theorem normalizedLimit : Tendsto normalized atTop (𝓝 (2/9 : ℝ)) := by
  have bound (n : ℕ) (hn : 10001 ≤ n) : normalized n ≤ 1 := by
    by_contra! hg
    have a : (normalized n)^4 ≤ (9*normalized n-2)^4 :=
      pow_le_pow_left₀ (normalizedNonneg n) (by linarith) 4
    have hn' : (10001 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 := mul_le_mul_of_nonneg_left a (show (0:ℝ) ≤ n by positivity)
    have h2 := discrepancy n (by omega)
    have h3 := mul_le_mul_of_nonneg_right hn' (show 0 ≤ (normalized n)^4 by positivity)
    have h4 := mul_lt_mul_of_pos_right hg (show 0 < (normalized n)^3 by positivity)
    nlinarith only [h1,h2,h3,h4, show 0 ≤ (normalized n)^3 by positivity]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have small := ((tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (10000:ℝ))).2
    ((9*ε)^4) (by positivity))
  filter_upwards [eventually_ge_atTop 10001, small] with n hn hs
  have hp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have c := pow_le_pow_left₀ (normalizedNonneg n) (bound n hn) 3
  have h := discrepancy n (by omega)
  have hu : (2 - 9 * normalized n)^4 ≤ 10000 / (n:ℝ) := by
    apply (le_div_iff₀ hp).mpr
    norm_num at c
    nlinarith
  rw [Real.dist_eq]
  by_contra! he
  have p := pow_le_pow_left₀ hε.le he 4
  rw [← abs_pow, abs_of_nonneg (by positivity)] at p
  nlinarith only [p, hu.trans_lt hs]

theorem ratio : type_of% @OMA.S_oeis_a309417.main := by
  have shift := normalizedLimit.comp (tendsto_add_atTop_nat 1)
  have qlim := shift.div normalizedLimit (by norm_num : (2/9:ℝ) ≠ 0)
  have frac : Tendsto (fun n : ℕ => (n:ℝ) / ((n:ℝ)+1)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply (show Tendsto (fun n : ℕ => 1 - 1 / ((n:ℝ)+1)) atTop (𝓝 1) by simpa using hh).congr
    intro n; field_simp; ring
  have lim := (qlim.mul frac).mul (tendsto_const_nhds (x := (10:ℝ)))
  apply (show Tendsto (fun n : ℕ => normalized (n+1) / normalized n * ((n:ℝ)/((n:ℝ)+1))*10)
      atTop (𝓝 10) by simpa [Function.comp_def] using lim).congr'
  filter_upwards [eventually_ge_atTop 1, (tendsto_order.mp normalizedLimit).1 0 (by norm_num)] with n hn hp
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : (term n : ℝ) ≠ 0 := by intro h; simp [normalized,h] at hp
  have hsucc : (n:ℝ)+1 ≠ 0 := by positivity
  simp only [normalized, Nat.cast_succ, pow_succ (10 : ℝ) n]
  field_simp

end
end DigitSubtraction

theorem OMA.solution : type_of% @OMA.S_oeis_a309417.main := DigitSubtraction.ratio
