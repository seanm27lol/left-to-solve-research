import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The prescribed-Sylow theorem of L. Pyber, Enumerating finite groups of given
order, Annals of Mathematics 137 (1993), gives the first bound after summing
over profiles. The second bound is elementary and goes in the complementary
direction: taking direct products realizes different profiles as different
groups. For orders below 2^m, the polynomial overhead in Pyber's theorem
costs at most 2^(75*(m+1)^2); raising to the 27th power gives 2025.
Credit: @seanm27lol, with Codex. Left to Solve PR 9018 uses the same
maximum-exponent estimate in its solvable-group reduction.
-/

open Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R1

theorem profile_mul (g : ℕ → ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : a.Coprime b) :
    (∏ p ∈ (a*b).primeFactors, g (p ^ (a*b).factorization p)) =
      (∏ p ∈ a.primeFactors, g (p ^ a.factorization p)) *
      (∏ p ∈ b.primeFactors, g (p ^ b.factorization p)) := by
  have side {u v : ℕ} (hv : v ≠ 0) (huv : u.Coprime v) :
      ∀ p ∈ u.primeFactors, (u*v).factorization p = u.factorization p := by
    intro p hp
    have hnd : ¬ p ∣ v := fun hd => Finset.disjoint_left.mp huv.disjoint_primeFactors hp
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, hv⟩)
    rw [Nat.factorization_mul_of_coprime huv, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, Nat.add_zero]
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hc.disjoint_primeFactors]
  congr 1
  · exact Finset.prod_congr rfl (fun p hp => by rw [side hb hc p hp])
  · exact Finset.prod_congr rfl (fun p hp => by rw [Nat.mul_comm a b, side ha hc.symm p hp])

/-- Pyber's prescribed-Sylow bound, summed over the possible Sylow types. -/
def H1 : Prop := ∀ n : ℕ, 0 < n →
  g n ≤ n ^ (75 * n.primeFactors.sup n.factorization + 16) *
    ∏ p ∈ n.primeFactors, g (p ^ n.factorization p)

/-- One choice of group for every prime-power factor of an order gives
a distinct isomorphism class at the complete order. -/
def H2 : Prop := ∀ n : ℕ, 0 < n →
  (∏ p ∈ n.primeFactors, g (p ^ n.factorization p)) ≤ g n

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1.H3 := by
  intro pyber product_lower
  refine ⟨2025, ?_⟩
  intro a q m ho hlt
  let n := 2^a*q
  have hq : 0 < q := by obtain ⟨w, hw⟩ := ho; omega
  have htwo : 0 < (2:ℕ)^a := Nat.pow_pos (by decide)
  have hn : 0 < n := Nat.mul_pos htwo hq
  let mu := n.primeFactors.sup n.factorization
  have hmu : mu ≤ m := by
    apply Finset.sup_le
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hb : 2 ^ n.factorization p < 2 ^ m := lt_of_le_of_lt
      ((Nat.pow_le_pow_left hprime.two_le _).trans
        (Nat.le_of_dvd hn (Nat.ordProj_dvd n p))) hlt
    exact ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hb).le
  have hbudget : n ^ (75*mu+16) ≤ 2 ^ (75*(m+1)^2) := by
    calc
      n ^ (75*mu+16) ≤ (2^m) ^ (75*mu+16) := Nat.pow_le_pow_left hlt.le _
      _ = 2^(m*(75*mu+16)) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        nlinarith only [Nat.mul_le_mul_left m hmu, Nat.zero_le m])
  have hmix : (∏ p ∈ n.primeFactors, g (p ^ n.factorization p)) ≤ g (2^a) * g q := by
    rw [show n = 2^a*q from rfl,
      profile_mul g htwo.ne' hq.ne' (ho.coprime_two_left.pow_left a)]
    exact Nat.mul_le_mul (product_lower _ htwo) (product_lower _ hq)
  have hgn := (pyber n hn).trans (Nat.mul_le_mul hbudget hmix)
  calc
    _ ≤ (2 ^ (75*(m+1)^2) * (g (2^a)*g q))^27 := Nat.pow_le_pow_left hgn _
    _ = _ := by
      rw [mul_pow, mul_pow, ← pow_mul]
      rw [show 75*(m+1)^2*27 = 2025*(m+1)^2 by ring]
      exact Nat.mul_comm _ _

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R1
