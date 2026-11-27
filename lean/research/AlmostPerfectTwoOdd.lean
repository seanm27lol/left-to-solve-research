import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Almost-perfect numbers with at most two distinct odd prime divisors

This file proves that an almost-perfect number other than a power of two has at least
three distinct odd prime divisors. Its main statement uses `ArithmeticFunction.sigma 1`,
the sum of positive divisors, and counts the distinct odd primes in `n.primeFactors`.

This is an independent formal proof of the two-odd-prime exclusion in Theorem 6.3 of
Ibrahim Amin Nicola Shnoudi, *On the Almost Perfect Number Conjecture: Structure and
Explicit Bounds for Odd Solutions, with a Lean 4 Formalisation* (October 2026).
<https://lifeofresearch.com/articles/144>
-/

namespace AlmostPerfectBridge
open ArithmeticFunction

def geom (p : ℕ) (n : ℕ) := ∑ j ∈ Finset.range (n+1), p^j

private theorem geom_zero (p : ℕ) : geom p 0 = 1 := by simp [geom]
private theorem geom_succ (p n : ℕ) : geom p (n+1) = geom p n + p^(n+1) := by
  unfold geom
  rw [Finset.sum_range_succ]
theorem geom_two (a : ℕ) : geom 2 a + 1 = 2 ^ (a+1) := by
  induction a with
  | zero => simp [geom]
  | succ a h =>
    rw [geom_succ, pow_succ 2 (a+1)]
    omega

private theorem geom_parity (p u : ℕ) (hp : Odd p) :
    geom p u % 2 = (u+1)%2 := by
  induction u with
  | zero => simp [geom]
  | succ u h =>
    have ho : Odd (p^(u+1)) := hp.pow
    rcases ho with ⟨n,hn⟩
    rw [geom_succ, hn]
    omega

private theorem geom_bound (p u : ℕ) : p^u ≤ geom p u := by
  cases u with
  | zero => simp [geom]
  | succ u =>
    rw [geom_succ]
    omega

private theorem geom_bound_mul (p u : ℕ) (hu : 0 < u) : (p+1)*p^u ≤ p*geom p u := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  rw [geom_succ]
  have h := Nat.mul_le_mul_left p (geom_bound p v)
  rw [pow_succ]
  nlinarith only [h]

theorem geom_algebra (p u : ℕ) :
    ((p:ℤ)-1) * (geom p u : ℤ) = (p:ℤ)^(u+1)-1 := by
  induction u with
  | zero => simp [geom]
  | succ u h =>
    rw [geom_succ, Nat.cast_add, Nat.cast_pow, mul_add, h, pow_succ _ (u+1)]
    ring

theorem sigma_bridge {a p q u v : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp2 : 2<p) (hpq : p<q) (hu : 0<u)
    (_hv : 0<v)
    (heq : sigma 1 (2^a*p^u*q^v)+1=2*(2^a*p^u*q^v)) :
    Even u ∧ Even v ∧ (2:ℤ)^(a+1)<(p:ℤ) ∧
    let H := (2:ℤ)^(a+1)
    let P := (p:ℤ)
    let Q := (q:ℤ)
    (H*(H-1)-(P-H)*(Q-H))*P^u*Q^v + ((H-1)+(P-1)*(Q-1)) =
        (H-1)*P^(u+1)+(H-1)*Q^(v+1) := by
  have h2p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  have h2q := (Nat.coprime_primes Nat.prime_two hq).2 (by omega)
  have hcop := (Nat.coprime_primes hp hq).2 hpq.ne
  rw [isMultiplicative_sigma.map_mul_of_coprime ((h2q.pow a v).mul_left (hcop.pow u v)),
      isMultiplicative_sigma.map_mul_of_coprime (h2p.pow a u),
      sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow hp,
      sigma_one_apply_prime_pow hq] at heq
  change geom 2 a * geom p u * geom q v + 1 = 2*(2^a*p^u*q^v) at heq
  have hop := hp.odd_of_ne_two (by omega)
  have hoq := hq.odd_of_ne_two (by omega)
  have hmu := geom_parity p u hop
  have hmv := geom_parity q v hoq
  have hmod : (geom 2 a * geom p u * geom q v)%2 = 1 := by omega
  rw [Nat.mul_mod, Nat.mul_mod (geom 2 a) (geom p u) 2] at hmod
  have ueven : Even u := by
    rw [Nat.even_iff]
    by_contra h
    have hz : geom p u % 2 = 0 := by omega
    simp [hz] at hmod
  have veven : Even v := by
    rw [Nat.even_iff]
    by_contra h
    have hz : geom q v % 2 = 0 := by omega
    simp [hz] at hmod
  refine ⟨ueven,veven, ?_, ?_⟩
  · have h1 := geom_bound_mul p u hu
    have h2 := geom_bound q v
    have h3 : (p+1)*p^u*q^v ≤ p*geom p u*geom q v := Nat.mul_le_mul h1 h2
    have h4 := Nat.mul_le_mul_left (geom 2 a) h3
    have h5 := congrArg (p * ·) heq
    have h6 := geom_two a
    have hp' : geom 2 a < p := by
      by_contra! hh
      have h7 := Nat.mul_le_mul_right (p^u*q^v) hh
      rw [pow_succ] at h6
      nlinarith only [h4,h5,h7,congrArg (fun z : ℕ => p*p^u*q^v*z) h6,hp2]
    have h8 : 2^(a+1)≤p := by omega
    have h9 : 2^(a+1)≠p := by
      rcases hop with ⟨i,hi⟩
      rw [pow_succ]
      omega
    exact_mod_cast lt_of_le_of_ne h8 h9
  · dsimp only
    have h6 : (geom 2 a : ℤ) + 1 = (2:ℤ)^(a+1) := by exact_mod_cast geom_two a
    have hbase : (geom 2 a : ℤ)*(geom p u : ℤ)*(geom q v : ℤ)+1 =
        (2:ℤ)*((2:ℤ)^a*(p:ℤ)^u*(q:ℤ)^v) := by exact_mod_cast heq
    rw [←show (2:ℤ)^(a+1)*(p:ℤ)^u*(q:ℤ)^v =
        2*(2^a*(p:ℤ)^u*(q:ℤ)^v) by rw [pow_succ]; ring] at hbase
    have hmult := congrArg (fun z : ℤ => ((p:ℤ)-1)*((q:ℤ)-1)*z) hbase
    have hmain : (geom 2 a : ℤ)*(((p:ℤ)^(u+1))-1)*(((q:ℤ)^(v+1))-1) +
          ((p:ℤ)-1)*((q:ℤ)-1) =
        ((p:ℤ)-1)*((q:ℤ)-1)*((2:ℤ)^(a+1)*(p:ℤ)^u*(q:ℤ)^v) := by
      rw [←geom_algebra p u, ←geom_algebra q v]
      linear_combination hmult
    rw [show (geom 2 a : ℤ) = (2:ℤ)^(a+1)-1 by omega] at hmain
    rw [pow_succ (p:ℤ) u, pow_succ (q:ℤ) v] at hmain ⊢
    linear_combination hmain
end AlmostPerfectBridge

namespace AlmostPerfectBridge
open ArithmeticFunction

/-- One odd prime in the support would have to equal a power of two. -/
theorem no_one_odd_prime {a p u : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hu : 0 < u) :
    sigma 1 (2^a*p^u)+1 ≠ 2*(2^a*p^u) := by
  intro heq
  have h2p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  rw [isMultiplicative_sigma.map_mul_of_coprime (h2p.pow a u),
      sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow hp] at heq
  change geom 2 a * geom p u + 1 = 2*(2^a*p^u) at heq
  have he : (geom 2 a : ℤ)*(geom p u : ℤ)+1 =
      2*((2:ℤ)^a*(p:ℤ)^u) := by exact_mod_cast heq
  have hge : (geom 2 a : ℤ)+1=(2:ℤ)^(a+1) := by exact_mod_cast geom_two a
  rw [show (geom 2 a : ℤ)=(2:ℤ)^(a+1)-1 by omega] at he
  have hp1 : (1:ℤ)<p := by exact_mod_cast hp.one_lt
  have hp1u : (1:ℤ)<(p:ℤ)^u := one_lt_pow₀ hp1 hu.ne'
  have hgeom := geom_algebra p u
  rw [pow_succ] at hgeom
  have hzero : ((2:ℤ)^(a+1)-p)*((p:ℤ)^u-1)=0 := by
    rw [pow_succ] at he ⊢
    linear_combination ((p:ℤ)-1)*he-(2*(2:ℤ)^a-1)*hgeom
  rcases mul_eq_zero.mp hzero with h | h
  · have h' : 2^(a+1)=p := by exact_mod_cast sub_eq_zero.mp h
    obtain ⟨i,hi⟩ := hp.odd_of_ne_two (by omega)
    rw [pow_succ] at h'
    omega
  · omega
end AlmostPerfectBridge

namespace AlmostPerfectTwoOdd

/-- The defect and the upper bound used in the exponent argument. -/
theorem defect_bounds {H p q F : ℤ} (hH : 2 ≤ H) (hp : H < p) (hq : p < q)
    (hF : 1 ≤ F) (heq : F = H * (p+q) - H - p*q) : q < p^2 := by
  have h1 : 0 ≤ (p-H-1)*(q-H) := mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ (p-H)*(p+H) := mul_nonneg (by omega) (by omega)
  nlinarith

private theorem two_or_four {A : ℕ} (hA : 2 ≤ A) (hAe : Even A) : A = 2 ∨ 4 ≤ A := by
  obtain ⟨a, ha⟩ := hAe
  omega

/-- The divisor-sum identity forces both odd-prime exponents to equal two. -/
theorem exponents_eq_two {H p q F C : ℤ} {A B : ℕ}
    (hH : 2 ≤ H) (hp : H < p) (hq : p < q) (hq2 : q < p^2) (hF : 1 ≤ F)
    (hC : C = (H-1)+(p-1)*(q-1))
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hAe : Even A) (hBe : Even B)
    (eqn : F*p^A*q^B = (H-1)*p^(A+1)+(H-1)*q^(B+1)-C) : A = 2 ∧ B = 2 := by
  have hp1 : 1 ≤ p := by omega
  have hq1 : 1 ≤ q := by omega
  have ht0 : 0 ≤ H-1 := by omega
  have hpa : 0 < p^A := pow_pos (by omega) _
  have hqb : 0 < q^B := pow_pos (by omega) _
  have hCpos : 0 < C := by
    rw [hC]
    exact add_pos_of_pos_of_nonneg (by omega) (mul_nonneg (by omega) (by omega))
  have hpp : 0 < p := by omega
  have hqq : 0 < q := by omega
  have hpow : p^2 ≤ q^B := calc
    p^2 ≤ q^2 := by gcongr
    _ ≤ q^B := pow_le_pow_right₀ hq1 hB
  have hA2 : A = 2 := by
    obtain h | hA4 := two_or_four hA hAe
    · exact h
    exfalso
    have hp4 : p^4 ≤ p^A := pow_le_pow_right₀ hp1 hA4
    have small : (H-1)*p*q ≤ p^A := calc
      (H-1)*p*q ≤ p*p*(p^2) := by gcongr; omega
      _ = p^4 := by ring
      _ ≤ p^A := hp4
    have low : p^A*q^B*p ≤ F*p^A*q^B*p := by
      calc
        p^A*q^B*p = 1*p^A*q^B*p := by ring
        _ ≤ F*p^A*q^B*p := by gcongr
    have hi1 : (H-1)*p^A*p^2 ≤ (H-1)*p^A*q^B := by gcongr
    have hi2 : ((H-1)*p*q)*q^B ≤ p^A*q^B := by gcongr
    have hh : H*(p^A*q^B) < p*(p^A*q^B) := mul_lt_mul_of_pos_right hp (mul_pos hpa hqb)
    have hE := congrArg (fun x : ℤ => x*p) eqn
    simp only [pow_succ] at hE
    have hCp : 0 < C*p := mul_pos hCpos hpp
    nlinarith only [hE, low, hi1, hi2, hh, hCp]
  refine ⟨hA2, ?_⟩
  subst A
  obtain h | hB4 := two_or_four hB hBe
  · exact h
  exfalso
  have hCbound : C < (H-1)*p^3 := by
    rw [hC]
    have hh1 := mul_le_mul_of_nonneg_left (le_of_lt hq2) (show 0 ≤ p-1 by omega)
    have hh2 : 0 ≤ (H-2)*(p^3-1) := mul_nonneg (by omega) (by nlinarith [pow_le_pow_right₀ hp1 (show 0 ≤ 3 by decide)])
    nlinarith
  have rearr : (F*p^2-(H-1)*q)*q^B=(H-1)*p^3-C := by
    change F*p^2*q^B = (H-1)*p^3+(H-1)*q^(B+1)-C at eqn
    calc
      _ = F*p^2*q^B - (H-1)*q^(B+1) := by rw [pow_succ q]; ring
      _ = _ := by rw [eqn]; ring
  have pos : 0 < F*p^2-(H-1)*q := by
    by_contra! hh
    have hle := mul_nonpos_of_nonpos_of_nonneg hh (le_of_lt hqb)
    linarith
  have lo : q^B ≤ (F*p^2-(H-1)*q)*q^B := calc
    q^B = 1*q^B := by ring
    _ ≤ _ := by gcongr; omega
  have upp : (H-1)*p^3 ≤ q^B := calc
    (H-1)*p^3 ≤ p*p^3 := by gcongr; omega
    _ = p^4 := by ring
    _ ≤ q^4 := by gcongr
    _ ≤ q^B := pow_le_pow_right₀ hq1 hB4
  linarith

/-- Arithmetic-function bridge, with the defect variables expanded. -/
theorem exponents_eq_two_of_identity {H p q : ℤ} {A B : ℕ}
    (hH : 2 ≤ H) (hp : H < p) (hq : p < q)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hAe : Even A) (hBe : Even B)
    (eqn : (H*(H-1)-(p-H)*(q-H))*p^A*q^B + ((H-1)+(p-1)*(q-1)) =
      (H-1)*p^(A+1)+(H-1)*q^(B+1)) : A = 2 ∧ B = 2 := by
  let F := H*(H-1)-(p-H)*(q-H)
  let C := (H-1)+(p-1)*(q-1)
  have hpp : 0 < p := by omega
  have hqq : 0 < q := by omega
  have hqp : 1 ≤ q := by omega
  have ht : 0 < H-1 := by omega
  have heq : F*p^A*q^B = (H-1)*p^(A+1)+(H-1)*q^(B+1)-C := by
    dsimp [F,C]
    linarith only [eqn]
  have hq2p : q^2 ≤ q^(B+1) := pow_le_pow_right₀ hqp (by omega)
  have hCbound : C < (H-1)*q^(B+1) := by
    have h1 : (p-1)*(q-1) ≤ (q-1)*(q-1) := by gcongr
    have h2 : 0 ≤ (H-2)*(q^2-1) := mul_nonneg (by omega) (by nlinarith)
    have h3 := mul_le_mul_of_nonneg_left hq2p (le_of_lt ht)
    dsimp [C]
    nlinarith only [h1,h2,h3,show 2 ≤ q by omega]
  have hF : 1 ≤ F := by
    by_contra! hf
    have hpa : 0 ≤ p^A := by positivity
    have hqb : 0 ≤ q^B := by positivity
    have hle := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (show F ≤ 0 by omega) hpa) hqb
    have hpos : 0 < (H-1)*p^(A+1) := by positivity
    linarith only [heq, hpos, hCbound, hle]
  exact exponents_eq_two hH hp hq (defect_bounds hH hp hq hF (by dsimp [F]; ring))
    hF rfl hA hB hAe hBe heq

end AlmostPerfectTwoOdd

namespace AlmostPerfect

/-- The squared two-factor divisor-sum equation has no solution in the range
forced by the almost-perfect condition. Only parity and inequalities are used. -/
theorem no_square_pair_of_lt (H p q : ℤ) (hH : 2 ≤ H) (hHp : H < p)
    (hpq : p < q)
    (eH : Even H) (op : Odd p) (oq : Odd q) :
    (H - 1) * (p ^ 2 + p + 1) * (q ^ 2 + q + 1) ≠ H * p ^ 2 * q ^ 2 - 1 := by
  intro heq
  let F := H * (p + q) - H - p * q
  let S := p + q
  let C := H - 1 + (p - 1) * (q - 1)
  have ht : 1 ≤ H - 1 := by omega
  have hp : 1 < p := by omega
  have hq : 1 < q := by omega
  have hC : 0 < C := by dsimp [C]; positivity
  -- This form isolates the error left after the two leading terms cancel.
  have hFid : F * (p ^ 2 * q ^ 2) = (H - 1) * p ^ 3 + (H - 1) * q ^ 3 - C := by
    dsimp [F,C]
    linear_combination (p - 1) * (q - 1) * heq
  have hF : 0 < F := by
    apply pos_of_mul_pos_left (b := p ^ 2 * q ^ 2) _ (by positivity)
    rw [hFid]
    have hpp : 0 ≤ p ^ 3 - 1 := by nlinarith [sq_nonneg p, mul_nonneg (sq_nonneg p) (show 0 ≤ p-1 by omega)]
    have hqq : 0 < (H-1)*q^2-(p-1) := by
      nlinarith [mul_nonneg (show 0 ≤ H-1-1 by omega) (sq_nonneg q),
        mul_nonneg (show 0 ≤ q-1 by omega) (show 0 ≤ q by omega)]
    dsimp [C]
    nlinarith only [mul_nonneg (show 0 ≤ H-1 by omega) hpp,
      mul_pos (show 0 < q by omega) hqq, hp]
  have hprod := mul_nonneg (show 0 ≤ p-H-1 by omega) (show 0 ≤ q-H by omega)
  have hqH : q < H^2 := by
    dsimp [F] at hF
    nlinarith only [hF, hprod]
  have hqp : q < p^2 := by
    nlinarith only [hqH, mul_pos (show 0 < p-H by omega) (show 0 < p+H by omega)]
  have hFH : F < H := by
    apply lt_of_mul_lt_mul_right (a := p ^ 2 * q ^ 2) _ (by positivity)
    rw [hFid]
    have hpp : 0 < q ^ 2 - (H-1)*p := by
      nlinarith [mul_pos (show 0 < q by omega) (show 0 < q-p by omega),
        mul_pos (show 0 < p by omega) (show 0 < q-(H-1) by omega)]
    nlinarith only [mul_pos (show 0 < (H-1)*q^2 by positivity) (sub_pos.mpr hqp),
      mul_pos (show 0 < p^2 by positivity) hpp, hC]
  -- The other root has the same parity as S, but lies strictly between 0 and 2.
  let B := (H+1)*F+3*H-1
  let U := B-S
  have roots : S*U = F*(F+H+1) := by
    dsimp [U,B,S,F]
    linear_combination heq
  have hS : 2 < S := by dsimp [S]; omega
  have hU : 0 < U := by
    apply pos_of_mul_pos_right (a := S) _ (by omega)
    rw [roots]
    positivity
  have negprod : (S-2)*(U-2) < 0 := by
    have hsum : S+U=B := by dsimp [U]; ring
    have bound : 0 < F*(H+1-F) + 6*(H-1) := by
      have : 0 < H+1-F := by omega
      positivity
    dsimp [B] at hsum
    nlinarith only [roots, hsum, bound]
  have hU2 : U < 2 := by
    by_contra! h
    have := mul_nonneg (show 0 ≤ S-2 by omega) (show 0 ≤ U-2 by omega)
    omega
  have one_odd : Odd (1 : ℤ) := ⟨0, by decide⟩
  have hFodd : Odd F := ((eH.mul_right _).sub eH).sub_odd (op.mul oq)
  have hB : Even B := (((eH.add_odd one_odd).mul hFodd).add_even (eH.mul_left 3)).sub_odd one_odd
  obtain ⟨u,hu⟩ := hB.sub (op.add_odd oq)
  change U = u+u at hu
  omega

end AlmostPerfect

namespace AlmostPerfectTwoOdd

/-- Enumerate the possible factorizations, counting only odd prime divisors. -/
theorem factorization_cases_of_two_odd {n : ℕ} (hn : 0 < n)
    (hcard : (n.primeFactors.erase 2).card ≤ 2) :
    (∃ a : ℕ, n = 2 ^ a) ∨
    (∃ a p u : ℕ, p.Prime ∧ Odd p ∧ 0 < u ∧ n = 2 ^ a * p ^ u) ∨
    (∃ a p q u v : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p < q ∧
        0 < u ∧ 0 < v ∧ n = 2 ^ a * p ^ u * q ^ v) := by
  classical
  let s := n.primeFactors.erase 2
  let a := n.factorization 2
  have decomp : n = 2 ^ a * ∏ p ∈ s, p ^ n.factorization p := by
    have hprod := Nat.prod_primeFactors_pow_factorization hn.ne'
    by_cases h2 : 2 ∈ n.primeFactors
    · change n = 2 ^ n.factorization 2 * ∏ p ∈ n.primeFactors.erase 2, p ^ n.factorization p
      exact hprod.trans (Finset.mul_prod_erase _ (fun p : ℕ => p ^ n.factorization p) h2).symm
    · have ha : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd
          (fun h => h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h, hn.ne'⟩))
      simpa [a, s, ha, Finset.erase_eq_of_notMem h2] using hprod
  have info {p : ℕ} (hp : p ∈ s) :
      p.Prime ∧ Odd p ∧ 0 < n.factorization p := by
    obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hin
    exact ⟨hprime, hprime.odd_of_ne_two hne,
      hprime.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hin)⟩
  have hh : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by
    change s.card ≤ 2 at hcard
    omega
  rcases hh with h | h | h
  · left
    exact ⟨a, by simpa [Finset.card_eq_zero.mp h] using decomp⟩
  · right; left
    obtain ⟨p, hs⟩ := Finset.card_eq_one.mp h
    have hp := info (p := p) (by simp [hs])
    exact ⟨a, p, n.factorization p, hp.1, hp.2.1, hp.2.2, by simpa [hs] using decomp⟩
  · right; right
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
    have hp := info (p := p) (by simp [hs])
    have hq := info (p := q) (by simp [hs])
    have heq : n = 2 ^ a * (p ^ n.factorization p * q ^ n.factorization q) := by
      simpa [hs, hpq] using decomp
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact ⟨a, p, q, _, _, hp.1, hq.1, hp.2.1, hq.2.1, hlt, hp.2.2, hq.2.2,
        by simpa [Nat.mul_assoc] using heq⟩
    · exact ⟨a, q, p, _, _, hq.1, hp.1, hq.2.1, hp.2.1, hgt, hq.2.2, hp.2.2,
        heq.trans (by ac_rfl)⟩

end AlmostPerfectTwoOdd

namespace AlmostPerfectTwoOdd

/-- Two distinct odd prime factors are impossible, with either exponent arbitrary. -/
theorem no_two_odd_primes {a p q u v : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp2 : 2 < p) (hpq : p < q)
    (hu : 0 < u) (hv : 0 < v) :
    ArithmeticFunction.sigma 1 (2 ^ a * p ^ u * q ^ v) + 1 ≠
      2 * (2 ^ a * p ^ u * q ^ v) := by
  intro heq
  let H := (2 : ℤ) ^ (a + 1)
  have hH : 2 ≤ H := by
    change (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (a + 1)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨heu, hev, hHp, hid⟩ := AlmostPerfectBridge.sigma_bridge hp hq hp2 hpq hu hv heq
  change H < (p : ℤ) at hHp
  change (H * (H-1) - ((p : ℤ)-H) * ((q : ℤ)-H)) * (p : ℤ)^u * (q : ℤ)^v +
      ((H-1) + ((p : ℤ)-1) * ((q : ℤ)-1)) =
      (H-1) * (p : ℤ)^(u+1) + (H-1) * (q : ℤ)^(v+1) at hid
  have hlt : (p : ℤ) < q := by exact_mod_cast hpq
  have hu2 : 2 ≤ u := by obtain ⟨k, hk⟩ := heu; omega
  have hv2 : 2 ≤ v := by obtain ⟨k, hk⟩ := hev; omega
  obtain ⟨rfl, rfl⟩ := exponents_eq_two_of_identity hH hHp hlt hu2 hv2 heu hev hid
  have himp :
      (((p : ℤ)-1) * ((q : ℤ)-1)) *
      ((H-1) * ((p : ℤ)^2+p+1) * ((q : ℤ)^2+q+1) - (H*(p : ℤ)^2*(q : ℤ)^2-1)) = 0 := by
    linear_combination hid
  have hz := (mul_eq_zero.mp himp).resolve_left (mul_ne_zero (by omega) (by omega))
  have eH : Even H := ⟨(2:ℤ)^a, by dsimp [H]; rw [pow_succ]; ring⟩
  have op : Odd (p : ℤ) := by exact_mod_cast hp.odd_of_ne_two (by omega)
  have oq : Odd (q : ℤ) := by exact_mod_cast hq.odd_of_ne_two (by omega)
  exact AlmostPerfect.no_square_pair_of_lt H p q hH hHp hlt eH op oq (sub_eq_zero.mp hz)

/-- An almost-perfect number with at most two distinct odd prime divisors is a power
of two. The support counts each prime once, independently of its exponent. -/
theorem eq_two_pow_of_at_most_two_odd_prime_divisors {n : ℕ}
    (hσ : ArithmeticFunction.sigma 1 n + 1 = 2 * n)
    (hcard : (n.primeFactors.erase 2).card ≤ 2) : ∃ a : ℕ, n = 2 ^ a := by
  have hn : 0 < n := by
    by_contra! hz
    have : n = 0 := by omega
    simp [this] at hσ
  rcases factorization_cases_of_two_odd hn hcard with pure | one | two
  · exact pure
  · obtain ⟨a, p, u, hp, op, hu, rfl⟩ := one
    have hp2 : 2 < p := by obtain ⟨k, hk⟩ := op; have := hp.two_le; omega
    exact (AlmostPerfectBridge.no_one_odd_prime hp hp2 hu hσ).elim
  · obtain ⟨a, p, q, u, v, hp, hq, op, _, hpq, hu, hv, rfl⟩ := two
    have hp2 : 2 < p := by obtain ⟨k, hk⟩ := op; have := hp.two_le; omega
    exact (no_two_odd_primes hp hq hp2 hpq hu hv hσ).elim

end AlmostPerfectTwoOdd

/--
info: 'AlmostPerfectTwoOdd.eq_two_pow_of_at_most_two_odd_prime_divisors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlmostPerfectTwoOdd.eq_two_pow_of_at_most_two_odd_prime_divisors
