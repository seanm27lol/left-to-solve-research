import OMAStatements.S_oeis_a346644

/-!
# Every positive integer occurs as a divisor-average denominator

For n > 0 choose a prime p > 2 in the residue class -1 modulo n.
Put B = 1 + 2 + ... + 2^(n-1). For k = 2^(n-1) p^(B-1), the divisor
average is (1 + p + ... + p^(B-1))/n. The numerator is 1 modulo n
because B is odd. This proves the existence assertion in Benoit Cloitre's entry.
-/

open Finset
open OMA.S_oeis_a346644

namespace DivisorAverage

private def geom (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => b * geom b j + 1

private lemma geom_sum (b j : ℕ) : (∑ i ∈ range j, b ^ i) = geom b j := by
  induction j with
  | zero => simp [geom]
  | succ j ih =>
    rw [sum_range_succ']
    simp only [pow_succ', pow_zero, ← mul_sum, ih, geom]

private lemma geom_odd_mod {n p : ℕ} (hp : (p : ZMod n) = -1) (t : ℕ) :
    (geom p (2 * t + 1) : ZMod n) = 1 := by
  induction t with
  | zero => simp [geom]
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by omega]
    change ((p * (p * geom p (2 * t + 1) + 1) + 1 : ℕ) : ZMod n) = 1
    push_cast
    rw [hp, ih]
    ring

private lemma sumPrimePower (p a : ℕ) (hp : Nat.Prime p) :
    (∑ d ∈ (p ^ a).divisors, d) = geom p (a + 1) := by
  rw [← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow hp,
    geom_sum]

private lemma cardPrimePower (p a : ℕ) (hp : Nat.Prime p) :
    (p ^ a).divisors.card = a + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]

private lemma reducedDen (a n : ℕ) (hn : 0 < n) (h : a.Coprime n) :
    ((a : ℚ) / (n : ℚ)).den = n := by
  simpa using (Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (n : ℤ))
    (by exact_mod_cast hn) (by simpa using h))

theorem allDenominators : type_of% @OMA.S_oeis_a346644.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  letI : NeZero (m + 1) := ⟨by omega⟩
  obtain ⟨p, hgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (q := m + 1) (a := (-1 : ZMod (m + 1))) (by simp) 2
  let t := geom 2 m
  have hc : (2 ^ m).Coprime (p ^ (2 * t)) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow _ _
  refine ⟨2 ^ m * p ^ (2 * t), Nat.mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _), ?_⟩
  have hr : (geom p (2 * t + 1)).Coprime (m + 1) := by
    apply Nat.coprime_of_mul_modEq_one 1
    rw [mul_one]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa using geom_odd_mod hpmod t
  have hmean : divisorMean (2 ^ m * p ^ (2 * t)) =
      (geom p (2 * t + 1) : ℚ) / ((m + 1 : ℕ) : ℚ) := by
    unfold divisorMean
    rw [hc.sum_divisors_mul, hc.card_divisors_mul, sumPrimePower 2 m Nat.prime_two,
      sumPrimePower p _ hp, cardPrimePower 2 m Nat.prime_two, cardPrimePower p _ hp]
    change (((2 * t + 1) * geom p (2 * t + 1) : ℕ) : ℚ) /
      (((m + 1) * (2 * t + 1) : ℕ) : ℚ) = _
    push_cast
    have hB : (2 * (t : ℚ) + 1) ≠ 0 := by positivity
    have hn' : ((m : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [hmean, reducedDen _ _ (by omega) hr]

end DivisorAverage

theorem OMA.solution : type_of% @OMA.S_oeis_a346644.main :=
  DivisorAverage.allDenominators
