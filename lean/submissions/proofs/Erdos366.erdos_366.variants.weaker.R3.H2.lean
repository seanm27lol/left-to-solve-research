import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R3

/-! Local divisibility certificate for the Mordell reduction of Erdős 366. -/

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R3.H2 := by
  intro D z m hD hm he h32 hlocal p hp
  obtain ⟨hprime, hpm, _⟩ := Nat.mem_primeFactors.mp hp
  by_cases h2 : p = 2
  · subst p
    rw [← he] at h32
    omega
  have hprod : p ∣ D * z^3 := he ▸ dvd_mul_of_dvd_right hpm 4
  have hpz : p ∣ z := by
    rcases hprime.dvd_mul.mp hprod with hd | hz
    · exact hlocal p (hprime.mem_primeFactors hd hD.ne') h2
    · exact hprime.dvd_of_dvd_pow hz
  have hc : p.Coprime 2 := hprime.coprime_iff_not_dvd.mpr (fun h =>
    h2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp h))
  have hc4 : (p^3).Coprime 4 := Nat.Coprime.pow 3 2 hc
  apply hc4.dvd_of_dvd_mul_left
  rw [he]
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpz 3) _
