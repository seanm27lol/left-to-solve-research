import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos366PrimeBlocks

private theorem odd_block {p r n B : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hn : 0 < n)
    (heq : p^r * B = 4 * (n*(n+1))) : 4 * p^r ≤ B+4 := by
  have h2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  have h4 : (p^r).Coprime 4 := by simpa using (h2.pow_right 2).pow_left r
  have hdiv : p^r ∣ n*(n+1) := h4.dvd_of_dvd_mul_left ⟨B,heq.symm⟩
  have hcases : p^r ∣ n ∨ p^r ∣ n+1 := by
    by_cases h : p ∣ n
    · left
      have hnext : n.Coprime (n+1) := Nat.coprime_self_add_right.mpr (by simp)
      exact ((Nat.Coprime.coprime_dvd_left h hnext).pow_left r).dvd_of_dvd_mul_right hdiv
    · right
      exact ((hp.coprime_iff_not_dvd.mpr h).pow_left r).dvd_of_dvd_mul_left hdiv
  have hpow : 0 < p^r := pow_pos hp.pos r
  rcases hcases with ⟨k,hk⟩|⟨k,hk⟩
  · have hkpos : 0 < k := by by_contra! hx; simp [show k=0 by omega] at hk; omega
    have hmul : p^r * B = p^r * (4*k*(n+1)) := by calc
      _ = 4*(n*(n+1)) := heq
      _ = _ := by conv_lhs => arg 2; arg 1; rw [hk]
                  ring
    have hb := Nat.eq_of_mul_eq_mul_left hpow hmul
    have hle := Nat.le_of_dvd hn (show p^r ∣ n from ⟨k,hk⟩)
    nlinarith [Nat.mul_le_mul_right (4*(n+1)) (show 1 ≤ k by omega)]
  · have hkpos : 0 < k := by by_contra! hx; simp [show k=0 by omega] at hk
    have hmul : p^r * B = p^r * (4*k*n) := by calc
      _ = 4*(n*(n+1)) := heq
      _ = _ := by rw [hk]; ring
    have hb := Nat.eq_of_mul_eq_mul_left hpow hmul
    have hle := Nat.le_of_dvd (Nat.succ_pos n) (show p^r ∣ n+1 from ⟨k,hk⟩)
    nlinarith [Nat.mul_le_mul_right (4*n) (show 1 ≤ k by omega)]

/-- In any normalized integral point of reduction R3.H1, every odd prime-power block
is bounded by the complementary part of the cube coordinate, including its radical. -/
theorem prime_block_bound {D z w p : ℕ} (hD : 0 < D) (hz : 0 < z) (hw : 1 < w)
    (hwo : Odd w) (heq : w^2 = D*z^3+1) (h32 : 32 ∣ D*z^3)
    (hfree : ∀ q ∈ D.primeFactors, ¬ q^3 ∣ D)
    (hloc : ∀ q ∈ D.primeFactors, q ≠ 2 → q ∣ z)
    (hp : p.Prime) (hodd : p ≠ 2) :
    let v := z / p^(z.factorization p)
    4*p^(3*z.factorization p + D.factorization p) ≤ v^3*(∏ q ∈ v.primeFactors, q)^2 + 4 := by
  let v := z / p^(z.factorization p)
  let E := D / p^(D.factorization p)
  let R := ∏ q ∈ v.primeFactors, q
  have hv : 0 < v := Nat.ordCompl_pos p hz.ne'
  have hE : E ∣ D := Nat.ordCompl_dvd D p
  have hEp : ¬ p ∣ E := Nat.not_dvd_ordCompl hp hD.ne'
  have hzfac : p^z.factorization p * v = z := Nat.ordProj_mul_ordCompl_eq_self z p
  have hDfac : p^D.factorization p * E = D := Nat.ordProj_mul_ordCompl_eq_self D p
  have h2z : 2 ∣ z := by
    by_contra h
    have hc := (Nat.prime_two.coprime_iff_not_dvd.mpr h).pow_right 3 |>.pow_left 5
    have hD32 : 2^5 ∣ D := hc.dvd_of_dvd_mul_right h32
    have hD2 : 2 ∣ D := dvd_trans (by decide : 2 ∣ 2^5) hD32
    exact hfree 2 (Nat.prime_two.mem_primeFactors hD2 hD.ne')
      (dvd_trans (by decide : 2^3 ∣ 2^5) hD32)
  have hER : E ∣ R^2 := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro q k hq hk
    by_cases hk0 : k = 0
    · simp [hk0]
    have hqE : q ∣ E := dvd_trans (dvd_pow_self q hk0) hk
    have hqD := hq.mem_primeFactors (hqE.trans hE) hD.ne'
    have hqz : q ∣ z := if h : q = 2 then h ▸ h2z else hloc q hqD h
    have hqp : q ≠ p := by rintro rfl; exact hEp hqE
    have hqv : q ∣ v := by
      rw [← hzfac] at hqz
      rcases hq.dvd_mul.mp hqz with h | h
      · exact (hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))).elim
      · exact h
    have hk2 : k ≤ 2 := by
      by_contra! h
      exact hfree q hqD ((pow_dvd_pow q (show 3 ≤ k by omega)).trans (hk.trans hE))
    have hqR : q ∣ R := Finset.dvd_prod_of_mem _ (hq.mem_primeFactors hqv hv.ne')
    exact (pow_dvd_pow q hk2).trans (pow_dvd_pow_of_dvd hqR 2)
  obtain ⟨n,hn⟩ := hwo
  have hnpos : 0 < n := by omega
  have hmul : p^(3*z.factorization p + D.factorization p) * (E*v^3) = 4*(n*(n+1)) := by
    calc
      _ = (p^D.factorization p * E) * ((p^z.factorization p * v)^3) := by
        rw [pow_add, Nat.mul_comm 3, pow_mul]; ring
      _ = D*z^3 := by rw [hDfac,hzfac]
      _ = 4*(n*(n+1)) := by rw [hn] at heq; nlinarith
  have hR : 0 < R := Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
  have hle := Nat.le_of_dvd (pow_pos hR 2) hER
  change _ ≤ v^3*R^2+4
  exact (odd_block hp hodd hnpos hmul).trans (by nlinarith [Nat.mul_le_mul_right (v^3) hle])

/-- Usable without factoring the complementary part. -/
theorem prime_block_bound_coarse {D z w p : ℕ} (hD : 0 < D) (hz : 0 < z) (hw : 1 < w)
    (hwo : Odd w) (heq : w^2 = D*z^3+1) (h32 : 32 ∣ D*z^3)
    (hfree : ∀ q ∈ D.primeFactors, ¬ q^3 ∣ D)
    (hloc : ∀ q ∈ D.primeFactors, q ≠ 2 → q ∣ z)
    (hp : p.Prime) (hodd : p ≠ 2) :
    let v := z / p^(z.factorization p)
    4*p^(3*z.factorization p + D.factorization p) ≤ v^5+4 := by
  let v := z / p^(z.factorization p)
  have hv : 0 < v := Nat.ordCompl_pos p hz.ne'
  have hle := (Nat.le_of_dvd hv (Nat.prod_primeFactors_dvd v))
  have h1 := prime_block_bound hD hz hw hwo heq h32 hfree hloc hp hodd
  change _ ≤ v^5+4
  apply h1.trans
  rw [show v^5=v^3*v^2 by ring]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (v^3) (Nat.pow_le_pow_left hle 2)) 4

/-- No odd prime power p^e in z can reach z^(5/8). The coefficient's p-part
makes the inequality strictly stronger if p divides D. -/
theorem no_dominant_odd_prime_power {D z w p : ℕ} (hD : 0 < D) (hz : 0 < z)
    (hw : 1 < w) (hwo : Odd w) (heq : w^2 = D*z^3+1) (h32 : 32 ∣ D*z^3)
    (hfree : ∀ q ∈ D.primeFactors, ¬ q^3 ∣ D)
    (hloc : ∀ q ∈ D.primeFactors, q ≠ 2 → q ∣ z)
    (hp : p.Prime) (hodd : p ≠ 2) (hpz : p ∣ z) :
    p^(8*z.factorization p + D.factorization p) < z^5 := by
  let e := z.factorization p
  let t := D.factorization p
  let v := z / p^e
  have hv : 0 < v := Nat.ordCompl_pos p hz.ne'
  have hzfac : p^e * v = z := Nat.ordProj_mul_ordCompl_eq_self z p
  have hl : 4*p^(3*e+t) ≤ v^5+4 := prime_block_bound_coarse hD hz hw hwo heq h32 hfree hloc hp hodd
  have he : 1 ≤ e := (hp.pow_dvd_iff_le_factorization hz.ne').mp (by simpa using hpz)
  have hbig : 2 ≤ p^(3*e+t) := hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.pos (show 1 ≤ 3*e+t by omega))
  have hlt : p^(3*e+t) < v^5 := by omega
  calc
    _ = p^(5*e) * p^(3*e+t) := by rw [←pow_add]; congr 1; omega
    _ < p^(5*e) * v^5 := Nat.mul_lt_mul_of_pos_left hlt (pow_pos hp.pos _)
    _ = z^5 := by rw [← hzfac, mul_pow, ←pow_mul, Nat.mul_comm e 5]

end Erdos366PrimeBlocks
#print axioms Erdos366PrimeBlocks.prime_block_bound
#print axioms Erdos366PrimeBlocks.prime_block_bound_coarse
#print axioms Erdos366PrimeBlocks.no_dominant_odd_prime_power
