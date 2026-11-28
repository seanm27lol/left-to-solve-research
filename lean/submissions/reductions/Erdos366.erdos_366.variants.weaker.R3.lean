import FormalConjectures.ErdosProblems.«366»
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

/-! Mordell curves for the cubefull-pair question.
The coordinates X = D*z and Y = D*w satisfy Y² = X³ + D².
An odd prime in the coefficient must divide z. At the prime 2 the division by four
in (w² - 1)/4 is accounted for by requiring 32 to divide D*z³.
Source: @seanm27lol and collaborators, left-to-solve-research PR #7,
notes/erdos-366-cubefull.md. -/

namespace OMA.R_Erdos366_erdos_366_variants_weaker_R3

/-- Find a positive integral point on a normalized Mordell curve whose coefficient
and coordinates meet the stated local divisibility conditions. -/
def H1 : Prop :=
  ∃ D z w : ℕ, 0 < D ∧ 0 < z ∧ 1 < w ∧ Odd w ∧
    w ^ 2 = D * z ^ 3 + 1 ∧ 32 ∣ D * z ^ 3 ∧
    (∀ p ∈ D.primeFactors, ¬ p^3 ∣ D) ∧
    ∀ p ∈ D.primeFactors, p ≠ 2 → p ∣ z

/-- Recover cubefullness after dividing the Mordell parameter by four. -/
def H2 : Prop :=
  ∀ D z m : ℕ, 0 < D → 0 < m → 4 * m = D * z ^ 3 →
    32 ∣ D * z ^ 3 → (∀ p ∈ D.primeFactors, p ≠ 2 → p ∣ z) → Nat.Full 3 m

section Details

private theorem full_of_coprime_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hf : Nat.Full 3 (a*b)) : Nat.Full 3 a := by
  intro p hp
  obtain ⟨hprime, hd, _⟩ := Nat.mem_primeFactors.mp hp
  have hc : p.Coprime b := Nat.Coprime.coprime_dvd_left hd hab
  have hprod := hf p (hprime.mem_primeFactors (dvd_mul_of_dvd_left hd b) (mul_pos ha hb).ne')
  exact (hc.pow_left 3).dvd_of_dvd_mul_right hprod

/-- Moving a prime cube from the coefficient into z preserves the point and local tests. -/
private theorem normalize_coefficient (D z : ℕ) (hD : 0 < D) (hz : 0 < z)
    (hlocal : ∀ p ∈ D.primeFactors, p ≠ 2 → p ∣ z) :
    ∃ d t : ℕ, 0 < d ∧ 0 < t ∧ d*t^3 = D*z^3 ∧
      (∀ p ∈ d.primeFactors, ¬ p^3 ∣ d) ∧
      (∀ p ∈ d.primeFactors, p ≠ 2 → p ∣ t) := by
  induction D using Nat.strong_induction_on generalizing z with
  | h D ih =>
    by_cases hfree : ∀ p ∈ D.primeFactors, ¬ p^3 ∣ D
    · exact ⟨D, z, hD, hz, rfl, hfree, hlocal⟩
    · push Not at hfree
      obtain ⟨p, hp, k, hk⟩ := hfree
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hkpos : 0 < k := by
        by_contra! h
        simp [show k = 0 by omega] at hk
        omega
      have hcube : 1 < p^3 := one_lt_pow₀ hprime.one_lt (by decide)
      have hsmall : k < D := hk ▸ lt_mul_of_one_lt_left hkpos hcube
      have hkdiv : k ∣ D := ⟨p^3, by rw [hk]; ac_rfl⟩
      have hnext : ∀ l ∈ k.primeFactors, l ≠ 2 → l ∣ p*z := by
        intro l hl hne
        have hlD := Nat.primeFactors_mono hkdiv hD.ne' hl
        exact dvd_mul_of_dvd_right (hlocal l hlD hne) p
      obtain ⟨d, t, hd, ht, he, hf, hl⟩ :=
        ih k hsmall (p*z) hkpos (mul_pos hprime.pos hz) hnext
      refine ⟨d, t, hd, ht, ?_, hf, hl⟩
      rw [he, hk]
      ring

/-- Each possible pair yields an integral point with the required local data. -/
theorem point_of_pair {n : ℕ} (hn : 0 < n)
    (hf : Nat.Full 3 n) (hg : Nat.Full 3 (n+1)) : H1 := by
  let m := n*(n+1)
  have hm : 0 < m := mul_pos hn (Nat.succ_pos _)
  have hfull : Nat.Full 3 m := by
    intro p hp
    obtain ⟨hprime, hd, _⟩ := Nat.mem_primeFactors.mp hp
    rcases hprime.dvd_mul.mp hd with h | h
    · exact dvd_mul_of_dvd_left (hf p (hprime.mem_primeFactors h hn.ne')) _
    · exact dvd_mul_of_dvd_right (hg p (hprime.mem_primeFactors h (Nat.succ_ne_zero _))) _
  let z := ∏ p ∈ m.primeFactors, p
  have hz : 0 < z := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hz3 : z^3 ∣ m := by
    calc z^3 = ∏ p ∈ m.primeFactors, p^3 := (Finset.prod_pow ..).symm
      _ ∣ ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
        apply Finset.prod_dvd_prod_of_dvd
        intro p hp
        exact pow_dvd_pow _ (((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hm.ne').mp (hfull p hp))
      _ = m := (Nat.prod_primeFactors_pow_factorization hm.ne').symm
  obtain ⟨q, hq⟩ := hz3
  have hqpos : 0 < q := by by_contra! h; simp [show q=0 by omega] at hq; omega
  have h8 : 8 ∣ m := by
    have h2 : 2 ∣ m := by
      by_cases he : 2 ∣ n
      · exact dvd_mul_of_dvd_left he _
      · exact dvd_mul_of_dvd_right (show 2 ∣ n+1 by omega) _
    exact hfull 2 (Nat.prime_two.mem_primeFactors h2 hm.ne')
  have hx : (4*q)*z^3 = 4*m := by rw [hq]; ring
  have hodd : ∀ p ∈ (4*q).primeFactors, p ≠ 2 → p ∣ z := by
    intro p hp hne
    obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp hp
    have hq' : p ∣ q := by
      rcases hprime.dvd_mul.mp hd with h4 | hq'
      · have h2 : p ∣ 2 := hprime.dvd_of_dvd_pow (show p ∣ 2^2 from h4)
        exact (hne ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp h2)).elim
      · exact hq'
    have hpm : p ∣ m := hq ▸ dvd_mul_of_dvd_right hq' _
    exact Finset.dvd_prod_of_mem _ (hprime.mem_primeFactors hpm hm.ne')
  obtain ⟨D, t, hD, ht, hparam, hfree, hlocal⟩ :=
    normalize_coefficient (4*q) z (by positivity) hz hodd
  refine ⟨D, t, 2*n+1, hD, ht, by omega, ⟨n,rfl⟩, ?_, ?_, hfree, hlocal⟩
  · rw [hparam, hx]
    dsimp [m]
    ring
  · rw [hparam, hx]
    omega

theorem main : H1 → H2 → type_of% @Erdos366.erdos_366.variants.weaker := by
  rintro ⟨D,z,w,hD,_,hw,⟨n,hw'⟩,he,h32,_,hodd⟩ hlocal
  have hn : 0 < n := by omega
  have hfactor : 4 * (n * (n+1)) = D * z^3 := by rw [hw'] at he; nlinarith
  have hp := hlocal D z (n*(n+1)) hD (mul_pos hn (Nat.succ_pos _)) hfactor h32 hodd
  have hc : n.Coprime (n+1) := Nat.coprime_self_add_right.mpr (by simp)
  refine ⟨n,hn,full_of_coprime_product hn (Nat.succ_pos _) hc hp,?_⟩
  apply full_of_coprime_product (Nat.succ_pos _) hn hc.symm
  simpa only [mul_comm] using hp

end Details

end OMA.R_Erdos366_erdos_366_variants_weaker_R3
