import FormalConjecturesForMathlib.Data.Nat.Full
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Push

/-! A finite certificate for the consecutive cubefull variant of Erdős 366.
Every positive cubefull integer at most 1000001 divides a fixed smooth integer.
The certificate tests its possible consecutive divisors against fifteen primes.
The earlier Lean exclusions at 100000 appear in Left to Solve PRs #3203
(@DomTheDeveloper) and #4100 (@dk8827). The independent enumeration to
10^26 in @seanm27lol’s research PR #7 is computational. This proof gives
a separate Lean kernel certificate at the intermediate bound 1000000. -/

namespace Erdos366Bounded

/-- The product, over primes up to 100, of their largest powers at most 1000001. -/
private def universal : ℕ :=
  16199787461677043563066712357652632724725285153859641941320869471814304540397656320919987363429417692400203610241159692743854284800000000

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem prime_powers : ∀ p : Fin 101, Nat.Prime p.val → ∀ k : Fin 21,
    p.val ^ k.val ≤ 1000001 → p.val ^ k.val ∣ universal := by decide +kernel

private theorem dvd_universal {n : ℕ} (hn : 0 < n) (hb : n ≤ 1000001)
    (hf : Nat.Full 3 n) : n ∣ universal := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  by_cases hz : k = 0
  · simp [hz]
  have hpd : p ∣ n := (dvd_pow_self p hz).trans hpk
  have h3 : p ^ 3 ≤ n := Nat.le_of_dvd hn (hf p (hp.mem_primeFactors hpd hn.ne'))
  have hp100 : p < 101 := by
    by_contra! h
    have h' : 101 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h _
    omega
  have hpower : p ^ k ≤ n := Nat.le_of_dvd hn hpk
  have hk20 : k < 21 := by
    by_contra! h
    have h' : 2 ^ 21 ≤ p ^ k :=
      (Nat.pow_le_pow_left hp.two_le 21).trans (Nat.pow_le_pow_right hp.pos h)
    omega
  exact prime_powers ⟨p,hp100⟩ hp ⟨k,hk20⟩ (hpower.trans hb)

/-- Each prime supplies a local test: if it divides an endpoint, its cube must divide it. -/
private def witnesses : List ℕ := [3,5,7,11,13,17,29,19,23,61,31,37,43,53,71]

private theorem all_prime : ∀ p ∈ witnesses, Nat.Prime p := by decide +kernel

private def obstruction (p n : ℕ) : Bool := n % p == 0 && n % (p ^ 3) != 0

private theorem no_obstruction {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hf : Nat.Full 3 n) : obstruction p n = false := by
  by_cases hd : p ∣ n
  · have hc := hf p (hp.mem_primeFactors hd hn.ne')
    simp [obstruction, Nat.dvd_iff_mod_eq_zero.mp hc]
  · simp [obstruction, (Nat.dvd_iff_mod_eq_zero.not.mp hd)]

private def excluded (n : ℕ) : Bool :=
  universal % n != 0 || universal % (n+1) != 0 ||
    witnesses.any (fun p => obstruction p n || obstruction p (n+1))

private theorem candidate_survives {n : ℕ} (hn : 0 < n) (hb : n ≤ 1000000)
    (hf : Nat.Full 3 n) (hg : Nat.Full 3 (n + 1)) : excluded n = false := by
  have h₁ := Nat.dvd_iff_mod_eq_zero.mp (dvd_universal hn (by omega) hf)
  have h₂ := Nat.dvd_iff_mod_eq_zero.mp (dvd_universal (by omega) (by omega) hg)
  simp only [excluded, h₁, h₂, Bool.false_or, bne_self_eq_false]
  apply List.any_eq_false.mpr
  intro p hp
  simp [no_obstruction (all_prime p hp) hn hf,
    no_obstruction (all_prime p hp) (Nat.succ_pos n) hg]

/-- The even endpoint is divisible by eight. A first endpoint can only be 0 or 7 modulo 8. -/
private def block (b : ℕ) : Bool :=
  (List.range 256).all fun j =>
    let m := 8 * (256*b+j)
    excluded m && excluded (m+7)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certificate : (List.range 489).all block = true := by decide +kernel

/-- No positive integer through one million begins a consecutive pair of cubefull integers. -/
theorem no_consecutive_through_million {n : ℕ} (hn : 0 < n) (hb : n ≤ 1000000)
    (hf : Nat.Full 3 n) (hg : Nat.Full 3 (n+1)) : False := by
  have hres : n % 8 = 0 ∨ n % 8 = 7 := by
    by_cases he : 2 ∣ n
    · have h := hf 2 (Nat.prime_two.mem_primeFactors he hn.ne')
      omega
    · have he' : 2 ∣ n+1 := by omega
      have h := hg 2 (Nat.prime_two.mem_primeFactors he' (Nat.succ_ne_zero _))
      omega
  let i := n / 8
  have hi : i / 256 < 489 := by dsimp [i]; omega
  have hc := List.all_eq_true.mp certificate (i / 256) (List.mem_range.mpr hi)
  have hj := List.all_eq_true.mp hc (i % 256) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simp only [Bool.and_eq_true] at hj
  have hre : 256 * (i/256) + i%256 = i := by omega
  rw [hre] at hj
  have hbad := candidate_survives hn hb hf hg
  rcases hres with h | h
  · have hn' : 8 * i = n := by dsimp [i]; omega
    simpa [hn', hbad] using hj.1
  · have hn' : 8 * i + 7 = n := by dsimp [i]; omega
    simpa [hn', hbad] using hj.2

/-- This is the negation of the bounded existence step in the original R1 reduction. -/
theorem refute_bounded_existence_step :
    ¬ ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1) := by
  rintro ⟨n, hn, hb, hf, hg⟩
  exact no_consecutive_through_million hn (by omega) hf hg

end Erdos366Bounded
