import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Density thresholds for the eventual sum variant of Erdős 1160

For any natural-number count `g`, the proportion of objects of dyadic order
and growth across adjacent dyadic orders control the entire sum up to the
endpoint. The hypotheses below are explicit. The two enumeration theorems
underlying them are due to Su–Xia (arXiv:2610.11092) and Li–Qiao
(arXiv:2610.14509). The prefix estimate generalizes the factor-two argument
in Left to Solve reduction Erdos1160.erdos_1160.variants.sum.R1.
-/

open Filter Topology

namespace Erdos1160Density

def total (g : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ n ∈ Finset.Ico 1 (2 ^ m + 1), g n

def dyadic (g : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), g (2 ^ j)

private theorem prefix_bound (a : ℕ → ℕ) (k : ℕ)
    (growth : ∀ᶠ m : ℕ in atTop, (k + 1) * a m < a (m + 1)) :
    ∀ᶠ m : ℕ in atTop, k * (∑ j ∈ Finset.range m, a j) ≤ a m := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp growth
  let partialSum (m : ℕ) := ∑ j ∈ Finset.range m, a j
  have absorb (t : ℕ) :
      k * partialSum (N + t) + t ≤ a (N + t) + k * partialSum N := by
    induction t with
    | zero => simp [partialSum]
    | succ t ih =>
      have hg := hN (N + t) (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hg
      change k * partialSum ((N + t) + 1) + (t + 1) ≤ a ((N + t) + 1) + k * partialSum N
      have turn : partialSum ((N + t) + 1) = partialSum (N + t) + a (N + t) :=
        Finset.sum_range_succ _ _
      rw [turn, Nat.mul_add]
      omega
  refine eventually_atTop.mpr ⟨N + k * partialSum N, ?_⟩
  intro m hm
  have ht := absorb (m - N)
  have h : N + (m - N) = m := by omega
  rw [h] at ht
  change k * partialSum m ≤ a m
  omega

/-- An explicit density threshold and adjacent growth suffice for a strict
weighted bound, for any positive fixed weight. The endpoint count may vanish
at small indices. -/
theorem weighted_from_threshold (g : ℕ → ℕ) (k : ℕ) (hk : 0 < k)
    (growth : ∀ᶠ m : ℕ in atTop, (2 * k + 1) * g (2 ^ m) < g (2 ^ (m + 1)))
    (density : ∀ᶠ m : ℕ in atTop,
      (2 * k + 1) * total g m < (2 * k + 2) * dyadic g m) :
    ∀ᶠ m : ℕ in atTop, k * (∑ n ∈ Finset.Ico 1 (2 ^ m), g n) < g (2 ^ m) := by
  have earlier := prefix_bound (fun j => g (2 ^ j)) (2*k) growth
  filter_upwards [density, earlier] with m hd he
  let A := g (2 ^ m)
  let S := ∑ j ∈ Finset.range m, g (2 ^ j)
  let U := ∑ n ∈ Finset.Ico 1 (2 ^ m), g n
  change (2*k) * S ≤ A at he
  change k * U < A
  have hd' : (2*k+1) * (U+A) < (2*k+2) * (S+A) := by
    simpa only [total, dyadic, Finset.sum_Ico_succ_top (show 1 ≤ 2 ^ m from Nat.one_le_pow _ _ (by decide)),
      Finset.sum_range_succ, U, S, A] using hd
  by_contra! bad
  linarith only [Nat.mul_le_mul_left (k+1) he,
    Nat.mul_le_mul_left (2*k+1) bad, Nat.mul_lt_mul_of_pos_left hd' hk]

/-- Li–Qiao's density of all dyadic orders at the dyadic endpoints, together
with eventual growth by a factor strictly greater than three, implies the
strict form of the catalog's eventual sum inequality. -/
theorem strict_from_dyadic_density (g : ℕ → ℕ)
    (growth : ∀ᶠ m : ℕ in atTop, 3 * g (2 ^ m) < g (2 ^ (m + 1)))
    (density : Tendsto (fun m => (dyadic g m : ℝ) / total g m) atTop (𝓝 1)) :
    ∀ᶠ m : ℕ in atTop, (∑ n ∈ Finset.Ico 1 (2 ^ m), g n) < g (2 ^ m) := by
  have ht := density.eventually_const_lt (show (3/4 : ℝ) < 1 by norm_num)
  have hthreshold : ∀ᶠ m : ℕ in atTop, 3 * total g m < 4 * dyadic g m := by
    filter_upwards [ht] with m hm
    by_cases hz : total g m = 0
    · simp [hz] at hm
      norm_num at hm
    · have hp : 0 < (total g m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hh := (lt_div_iff₀ hp).mp hm
      have : 3 * (total g m : ℝ) < 4 * (dyadic g m : ℝ) := by linarith
      exact_mod_cast this
  simpa using weighted_from_threshold g 1 (by decide) growth hthreshold

/-- The proportion at the endpoint alone (as in Su–Xia) suffices as well. -/
theorem strict_from_endpoint_density (g : ℕ → ℕ)
    (density : Tendsto (fun m : ℕ => (g (2^m) : ℝ) / total g m) atTop (𝓝 1)) :
    ∀ᶠ m : ℕ in atTop, (∑ n ∈ Finset.Ico 1 (2 ^ m), g n) < g (2 ^ m) := by
  have ht := density.eventually_const_lt (show (1/2 : ℝ) < 1 by norm_num)
  filter_upwards [ht] with m hm
  by_cases hz : total g m = 0
  · simp [hz] at hm
    norm_num at hm
  · have hp : 0 < (total g m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hh := (lt_div_iff₀ hp).mp hm
    have : (total g m : ℝ) < 2 * (g (2^m) : ℝ) := by linarith
    have hnat : total g m < 2 * g (2^m) := by exact_mod_cast this
    rw [total, Finset.sum_Ico_succ_top (show 1 ≤ 2 ^ m from Nat.one_le_pow _ _ (by decide))] at hnat
    omega

end Erdos1160Density
