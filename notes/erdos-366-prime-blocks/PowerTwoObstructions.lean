import FormalConjecturesForMathlib.Data.Nat.Full
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Power-of-two endpoints in the consecutive cubefull pair problem. -/

namespace Erdos366PowerTwo

private theorem one_le_two_pow (k : ℕ) : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)

private theorem mersenne_order {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdiv : p ∣ 2^q-1) : q ∣ p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hc : (2 : ZMod p)^q = 1 := by
    have hm := ((Nat.modEq_iff_dvd' (one_le_two_pow q)).mpr hdiv).symm
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have hne : (2 : ZMod p) ≠ 1 := by
    intro h
    have hm : (2:ℕ) ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 2 1 p).mp (by simpa using h)
    exact hp.not_dvd_one ((Nat.modEq_iff_dvd' (by decide : 1 ≤ 2)).mp hm.symm)
  have hnz : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne_zero] at hc
    exact zero_ne_one hc
  rw [← orderOf_eq_prime hc hne]
  exact ZMod.orderOf_dvd_card_sub_one hnz

private theorem mersenne_dvd_mersenne {p a b : ℕ} (hab : a ∣ b) (hp : p ∣ 2^a-1) :
    p ∣ 2^b-1 := by
  obtain ⟨k,rfl⟩ := hab
  have he := (Nat.modEq_iff_dvd' (one_le_two_pow a)).mpr hp
  apply (Nat.modEq_iff_dvd' (one_le_two_pow _)).mp
  simpa only [pow_mul, one_pow] using he.pow k

/-- Each prime factor of the Mersenne number at the largest prime exponent already
has valuation at least three in that smaller Mersenne number. -/
theorem mersenne_largest_prime {a q : ℕ} (ha : 1 < a) (hq : q.Prime) (hqa : q ∣ a)
    (hmax : ∀ r ∈ a.primeFactors, r ≤ q) (hfull : Nat.Full 3 (2^a-1)) :
    Nat.Full 3 (2^q-1) := by
  intro p hmem
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hmem
  have hqp := mersenne_order hp hq hd
  have hqle : q ≤ p-1 := Nat.le_of_dvd (by have := hp.two_le; omega) hqp
  have hpa : ¬ p ∣ a := fun h => by
    have h' := hmax p (hp.mem_primeFactors h (by omega))
    have := hp.two_le
    omega
  have h2 : p ≠ 2 := by have := hq.two_le; omega
  have hr : ¬ p ∣ 2^q := by
    intro h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hd' := mersenne_dvd_mersenne hqa hd
  have hpos : 0 < 2^a-1 := by have := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : a ≠ 0); omega
  have h3 := hfull p (hp.mem_primeFactors hd' hpos.ne')
  obtain ⟨k,hk⟩ := hqa
  have hpk : ¬ p ∣ k := fun h => hpa (hk ▸ dvd_mul_of_dvd_right h q)
  have hlt := Nat.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two h2) (x:=2^q) (y:=1) hd hr k
  simp only [one_pow, emultiplicity_eq_zero.mpr hpk, add_zero, ← pow_mul, ← hk] at hlt
  rw [pow_dvd_iff_le_emultiplicity] at h3 ⊢
  rwa [← hlt]

/-- Any prime divisor of that reduced Mersenne number is a base-two Wieferich
prime modulo its cube. -/
theorem mersenne_wieferich_witness {a : ℕ} (ha : 1 < a) (hf : Nat.Full 3 (2^a-1)) :
    ∃ p : ℕ, p.Prime ∧ p^3 ∣ 2^(p-1)-1 ∧ p ∣ 2^a-1 := by
  let q := a.primeFactors.max' (Nat.nonempty_primeFactors.mpr ha)
  have hqmem : q ∈ a.primeFactors := Finset.max'_mem _ _
  obtain ⟨hq, hqa, _⟩ := Nat.mem_primeFactors.mp hqmem
  have hqfull := mersenne_largest_prime ha hq hqa (fun r hr => Finset.le_max' _ _ hr) hf
  have hnon : 1 < 2^q-1 := by
    have h2 : 2^2 ≤ 2^q := Nat.pow_le_pow_right (by decide) hq.two_le
    omega
  obtain ⟨p, hp⟩ := (Nat.nonempty_primeFactors.mpr hnon)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdiv := (Nat.mem_primeFactors.mp hp).2.1
  exact ⟨p, hprime, mersenne_dvd_mersenne (mersenne_order hprime hq hdiv) (hqfull p hp),
    mersenne_dvd_mersenne hqa hdiv⟩


private theorem plus_quotient_valuation {p b q c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ho : Odd q) (h : b^q+1=(b+1)*c) (hd : p ∣ b+1) :
    emultiplicity p c = emultiplicity p q := by
  have hnb : ¬p ∣ b := by
    intro h'
    exact hp.not_dvd_one (by simpa using Nat.dvd_sub hd h')
  have he := Nat.emultiplicity_pow_add_pow hp (hp.odd_of_ne_two hp2) (x:=b) (y:=1) hd hnb ho
  simp only [one_pow,h, emultiplicity_mul hp.prime] at he
  have hfin : FiniteMultiplicity p (b+1) := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one,by omega⟩
  exact ENat.add_right_injective_of_ne_top (by rw [hfin.emultiplicity_eq_multiplicity]; simp) he

private theorem odd_power_quotient_factor {b q : ℕ} (hb : 2 ≤ b) (hbEven : Even b) (hq : q.Prime)
    (hq2 : q ≠ 2) (hlarge : 3 ≤ b ∨ 4 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ q < p ∧ p ∣ b^q+1 := by
  have hqodd := hq.odd_of_ne_two hq2
  have hq3 := hq.odd_iff.mp hqodd
  obtain ⟨c,hc⟩ : b+1 ∣ b^q+1 := by simpa using hqodd.nat_add_dvd_pow_add_pow b 1
  have hbc : b+1 < c := by
    have hi : (b+1)^2 < b^q+1 := by
      by_cases h : 3 ≤ b
      · have hpow := Nat.pow_le_pow_right (by omega : 0 < b) hq3
        obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
        nlinarith
      · have hb2 : b = 2 := by omega
        have h4 : 4 ≤ q := by omega
        have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) h4
        subst b
        omega
    by_contra! h
    have h' := Nat.mul_le_mul_left (b+1) h
    nlinarith
  have hdiv : ∃ p : ℕ, p.Prime ∧ p ∣ c ∧ p ≠ q := by
    by_cases hqc : q ∣ c
    · let : Fact q.Prime := ⟨hq⟩
      have hqn : q ∣ b^q+1 := hc ▸ dvd_mul_of_dvd_right hqc _
      have hqbase : q ∣ b+1 := by
        apply (ZMod.natCast_eq_zero_iff _ _).mp
        have h' := (ZMod.natCast_eq_zero_iff _ _).mpr hqn
        push_cast at h' ⊢
        rwa [ZMod.pow_card] at h'
      have hone := plus_quotient_valuation hq hq2 hqodd hc hqbase
      have hf : FiniteMultiplicity q q := Nat.finiteMultiplicity_iff.mpr ⟨hq.ne_one,hq.pos⟩
      rw [hf.emultiplicity_self] at hone
      have hns : ¬ q^2 ∣ c := by
        rw [pow_dvd_iff_le_emultiplicity,hone]
        decide
      have hlt := (Nat.le_of_dvd (by omega) hqbase).trans_lt hbc
      obtain ⟨k,hk⟩ := hqc
      have hk2 : 1 < k := by by_contra! h; have hh := Nat.mul_le_mul_left q h; omega
      obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
      refine ⟨p,hp,hk ▸ dvd_mul_of_dvd_right hd _,?_⟩
      rintro rfl
      apply hns
      rw [pow_two,hk]
      exact Nat.mul_dvd_mul_left _ hd
    · obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
      exact ⟨p,hp,hd,fun he => hqc (he ▸ hd)⟩
  obtain ⟨p,hp,hpc,hpq⟩ := hdiv
  have hpn : p ∣ b^q+1 := hc ▸ dvd_mul_of_dvd_right hpc _
  have hp2 : p ≠ 2 := by
    rintro rfl
    have ho : Odd (b^q+1) := (hbEven.pow_of_ne_zero hq.ne_zero).add_odd (by decide)
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpn)
  have hnot : ¬ p ∣ b+1 := by
    intro hpb
    have hv := plus_quotient_valuation hp hp2 hqodd hc hpb
    have hnq : ¬p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    rw [emultiplicity_eq_zero.mpr hnq] at hv
    exact (emultiplicity_eq_zero.mp hv) hpc
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
  push_cast at hz
  have hn : ¬ ((b : ZMod p)+1) = 0 := by
    intro hh
    exact hnot ((ZMod.natCast_eq_zero_iff (b+1) p).mp (by simpa using hh))
  have hpow : (-(b:ZMod p))^q = 1 := by rw [hqodd.neg_pow]; linear_combination -hz
  have hne : -(b:ZMod p) ≠ 1 := by intro hh; apply hn; linear_combination -hh
  have hnz : -(b:ZMod p) ≠ 0 := by
    intro h
    rw [h,zero_pow hq.ne_zero] at hpow
    exact zero_ne_one hpow
  have hd : q ∣ p-1 := (orderOf_eq_prime hpow hne) ▸ ZMod.orderOf_dvd_card_sub_one hnz
  have := hp.two_le
  exact ⟨p,hp,by have := Nat.le_of_dvd (by omega) hd; omega,hpn⟩


private theorem plus_wieferich {a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : ¬ p ∣ a) (hc : p^3 ∣ 2^a+1) : p^3 ∣ 2^(p-1)-1 := by
  let x := (2 : ZMod (p^3))
  have hp2cop : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  have h0 : x^a+1 = 0 := by
    simpa [x] using (ZMod.natCast_eq_zero_iff (2^a+1) (p^3)).mpr hc
  have hxa : x^a = -1 := eq_neg_of_add_eq_zero_left h0
  have hx2a : x^(a*2) = 1 := by rw [pow_mul,hxa]; norm_num
  have hxe : x^((p^3).totient) = 1 := by
    have hnat := Nat.ModEq.pow_totient (hp2cop.symm.pow_right 3)
    simpa [x] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hnat
  have hdiv : orderOf x ∣ p^2*(p-1) := by
    simpa [Nat.totient_prime_pow hp (by decide : 0 < 3)] using orderOf_dvd_of_pow_eq_one hxe
  have hcop : (orderOf x).Coprime p := by
    apply Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx2a)
    exact Nat.Coprime.mul_left (hp.coprime_iff_not_dvd.mpr hpa).symm hp2cop.symm
  have hpow := orderOf_dvd_iff_pow_eq_one.mp ((hcop.pow_right 2).dvd_of_dvd_mul_left hdiv)
  have he : 2^(p-1) ≡ 1 [MOD p^3] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [x] using hpow
  exact (Nat.modEq_iff_dvd' (one_le_two_pow _)).mp he.symm

/-- A cubefull upper neighbor of a positive power of two with exponent at least
three also forces a prime of Wieferich order at least two. -/
theorem plus_wieferich_witness {a : ℕ} (ha : 3 ≤ a) (hf : Nat.Full 3 (2^a+1)) :
    ∃ p : ℕ, p.Prime ∧ p^3 ∣ 2^(p-1)-1 ∧ p ∣ 2^a+1 := by
  have ha3 : a ≠ 3 := by
    rintro rfl
    have hf' := hf 3 (Nat.prime_three.mem_primeFactors (by decide) (by decide))
    norm_num at hf'
  let q := a.primeFactors.max' (Nat.nonempty_primeFactors.mpr (by omega))
  have hqm : q ∈ a.primeFactors := Finset.max'_mem _ _
  obtain ⟨hq,hqa,_⟩ := Nat.mem_primeFactors.mp hqm
  have hmax : ∀ r ∈ a.primeFactors, r ≤ q := fun _ h => Finset.le_max' _ _ h
  have hb : ∃ p : ℕ, p.Prime ∧ q < p ∧ p ∣ 2^a+1 := by
    by_cases he : q = 2
    · obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by have := one_le_two_pow a; omega : 2^a+1 ≠ 1)
      have ho : Odd (2^a+1) := (show Even (2:ℕ) by decide).pow_of_ne_zero (by omega : a ≠ 0) |>.add_odd (by decide)
      have hp2 : p ≠ 2 := fun e => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (e ▸ hd))
      exact ⟨p,hp,by have := hp.two_le; omega,hd⟩
    · obtain ⟨k,hk⟩ := hqa
      have hk1 : 1 ≤ k := by by_contra! hh; simp [show k=0 by omega] at hk; omega
      have hb2 : 2 ≤ 2^k := by simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk1
      have hbe : Even (2^k : ℕ) := (show Even (2:ℕ) by decide).pow_of_ne_zero (by omega)
      have hlarge : 3 ≤ 2^k ∨ 4 ≤ q := by
        by_cases hq3 : q=3
        · left
          have hk2 : 2 ≤ k := by rw [hq3] at hk; omega
          have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk2
          omega
        · right
          have := hq.two_le
          omega
      obtain ⟨p,hp,hbig,hd⟩ := odd_power_quotient_factor hb2 hbe hq he hlarge
      refine ⟨p,hp,hbig,?_⟩
      simpa only [hk, Nat.mul_comm q k, pow_mul] using hd
  obtain ⟨p,hp,hbig,hd⟩ := hb
  have hp2 : p ≠ 2 := by have := hq.two_le; omega
  have hpa : ¬ p ∣ a := fun h => (not_le.mpr hbig) (hmax p (hp.mem_primeFactors h (by omega)))
  exact ⟨p,hp,plus_wieferich hp hp2 hpa (hf p (hp.mem_primeFactors hd (Nat.succ_ne_zero _))),hd⟩


/-- For an odd multiplier k, a prime of the form 2^t+1 consumes two powers
in k itself. This includes every prime Fermat number, at all heights. -/
theorem fermat_prime_square_dvd {t k : ℕ} (ht : 0 < t) (hk : Odd k)
    (hp : (2^t+1).Prime) (hf : Nat.Full 3 (2^(t*k)+1)) : (2^t+1)^2 ∣ k := by
  let p := 2^t+1
  have h2 : 2 ≤ 2^t := by simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ht
  have hodd : Odd p := hp.odd_iff.mpr (by omega)
  have hnd : ¬p ∣ 2^t := by
    intro h
    have := Nat.le_of_dvd (pow_pos (by decide : 0 < (2:ℕ)) t) h
    dsimp [p] at this
    omega
  have he := Nat.emultiplicity_pow_add_pow hp hodd (x:=2^t) (y:=1) (by rfl) hnd hk
  simp only [one_pow, ← pow_mul] at he
  have hd : p ∣ 2^(t*k)+1 := by simpa [p, pow_mul] using hk.nat_add_dvd_pow_add_pow (2^t) 1
  have h3 := hf p (hp.mem_primeFactors hd (Nat.succ_ne_zero _))
  have hself : FiniteMultiplicity p p := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one,hp.pos⟩
  have hkp : 0 < k := by obtain ⟨j,hj⟩ := hk; omega
  have hfin : FiniteMultiplicity p k := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one,hkp⟩
  change p^2 ∣ k
  rw [pow_dvd_iff_le_emultiplicity] at h3 ⊢
  change emultiplicity p (2^(t*k)+1) = emultiplicity p p + emultiplicity p k at he
  rw [he,hself.emultiplicity_self,hfin.emultiplicity_eq_multiplicity] at h3
  rw [hfin.emultiplicity_eq_multiplicity]
  norm_cast at h3 ⊢
  omega

private def smallPrimeMersenne : List ℕ := [2,3,5,7,13,17,19,31,61,89,107,127]

private theorem small_mersenne_primality :
    ∀ q ∈ smallPrimeMersenne, (2^q-1).Prime := by
  intro q h
  simp only [smallPrimeMersenne, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> subst q
  · decide
  all_goals apply lucas_lehmer_sufficiency _ (by decide); norm_num

/-- (exponent, coprime divisor, trial bound). No primality assumption on the divisor. -/
private def factors : List (ℕ × ℕ × ℕ) :=
  [(11,23,2), (23,47,3), (29,233,6), (37,223,6), (41,13367,23),
   (43,431,7), (47,2351,13), (53,6361,18), (59,179951,56), (67,193707721,578),
   (71,228479,61), (73,439,7), (79,2687,13), (83,167,5), (97,11447,22),
   (101,7432339208719,19515), (103,2550183799,1366), (109,745988807,906), (113,3391,15)]

private def valid (row : ℕ × ℕ × ℕ) : Bool :=
  let (q,d,b) := row
  let n := 2^q-1
  decide (1 < d ∧ d ∣ n ∧ d.Coprime (n/d) ∧ d < (b+2)^3) &&
    (List.range b).all (fun k => d % (k+2) != 0)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem checked_factors : factors.all valid = true := by decide +kernel

private theorem covered : ∀ q : Fin 128, Nat.Prime q.val →
    q.val ∈ smallPrimeMersenne ∨ q.val ∈ factors.map Prod.fst := by decide +kernel

private theorem factor_rules_out {q d b : ℕ} (ha : valid (q,d,b) = true) :
    ¬ Nat.Full 3 (2^q-1) := by
  let n := 2^q-1
  change (decide (1 < d ∧ d ∣ n ∧ d.Coprime (n/d) ∧ d < (b+2)^3) && _) = true at ha
  obtain ⟨hc, hs⟩ := Bool.and_eq_true_iff.mp ha
  obtain ⟨hd, hdv, hcop, hsize⟩ := of_decide_eq_true hc
  let p := d.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ d := Nat.minFac_dvd _
  have h2 : 2 ≤ p := hp.two_le
  have hlow : b+2 ≤ p := by
    by_contra! h
    have htest := List.all_eq_true.mp hs (p-2) (List.mem_range.mpr (by omega))
    have hz := Nat.dvd_iff_mod_eq_zero.mp hpd
    simp [show p-2+2=p by omega, hz] at htest
  have h0 : n ≠ 0 := by
    intro hn
    rw [hn, Nat.zero_div] at hcop
    have : d = 1 := by simpa using hcop
    omega
  intro hf
  have h3 := hf p (hp.mem_primeFactors (hpd.trans hdv) h0)
  have h3' : p^3 ∣ d := by
    apply ((Nat.Coprime.coprime_dvd_left hpd hcop).pow_left 3).dvd_of_dvd_mul_right
    simpa only [Nat.mul_div_cancel' hdv] using h3
  have hu := Nat.le_of_dvd (by omega) h3'
  have hl := Nat.pow_le_pow_left hlow 3
  omega

/-- All 127-smooth exponents are excluded for the lower neighbor, with no bound on the exponent. -/
theorem exclude_smooth_mersenne {a : ℕ} (ha : 1 < a)
    (hs : ∀ p ∈ a.primeFactors, p ≤ 127) : ¬ Nat.Full 3 (2^a-1) := by
  intro hf
  let q := a.primeFactors.max' (Nat.nonempty_primeFactors.mpr ha)
  have hqm : q ∈ a.primeFactors := Finset.max'_mem _ _
  have hq := Nat.prime_of_mem_primeFactors hqm
  have hbelow : q < 128 := by have := hs q hqm; omega
  have hr := mersenne_largest_prime ha hq (Nat.mem_primeFactors.mp hqm).2.1
    (fun p hp => Finset.le_max' _ _ hp) hf
  rcases covered ⟨q,hbelow⟩ hq with h | h
  · have hprime := small_mersenne_primality q h
    have h3 := hr _ hprime.mem_primeFactors_self
    have hu := Nat.le_of_dvd hprime.pos h3
    have hh := hprime.two_le
    have ht : (2^q-1) < (2^q-1)^3 := lt_self_pow₀ (by omega) (by decide)
    omega
  · obtain ⟨⟨r,d,b⟩,hmem,heq⟩ := List.mem_map.mp h
    change r = q at heq
    subst r
    exact factor_rules_out (List.all_eq_true.mp checked_factors _ hmem) hr

end Erdos366PowerTwo
#print axioms Erdos366PowerTwo.mersenne_largest_prime
#print axioms Erdos366PowerTwo.mersenne_wieferich_witness
#print axioms Erdos366PowerTwo.plus_wieferich_witness
#print axioms Erdos366PowerTwo.fermat_prime_square_dvd
#print axioms Erdos366PowerTwo.exclude_smooth_mersenne
