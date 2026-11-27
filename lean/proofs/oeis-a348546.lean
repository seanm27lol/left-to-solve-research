import OMAStatements.S_oeis_a348546

/-!
The pole of the von Mangoldt series gives divergent reciprocal primes in a
reduced residue class. A finite totient sieve then counts integers missing
those primes in any interval.
-/
namespace PairedFactors
noncomputable section
open Finset Filter
open scoped BigOperators Topology Classical
open ArithmeticFunction vonMangoldt

private def recip (a : ZMod 10) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n:ZMod 10)=a then 1/(n:ℝ) else 0

private lemma reciprocalDiverges (a : ZMod 10) (ha : IsUnit a) :
    ¬ Summable (recip a) := by
  intro hsum
  let δ (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  have hd : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp (k) : 0 < δ k := by dsimp [δ]; positivity
  have hle (k) : δ k ≤ 1 := by dsimp [δ]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  let F (k n : ℕ) : ℝ := δ k * (residueClass a n / (n:ℝ)^(1+δ k))
  let B (n : ℕ) : ℝ := recip a n + (if n.Prime then 0 else residueClass a n)/n
  have hB : Summable B := hsum.add (summable_residueClass_non_primes_div a)
  have point (n : ℕ) : Tendsto (fun k => F k n) atTop (𝓝 0) := by
    by_cases hn : n=0
    · simp [hn,F]
    have hpos : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hc : ContinuousAt (fun x : ℝ => x * (residueClass a n / (n:ℝ)^(1+x))) 0 := by
      fun_prop (disch := positivity)
    simpa [F,Function.comp_def] using hc.tendsto.comp hd
  have bound (k n : ℕ) : ‖F k n‖ ≤ B n := by
    have hdpos := hp k
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ F k n by
      dsimp [F]; positivity [residueClass_nonneg a n])]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F,B,recip]
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpos : 0 < (n:ℝ) := by linarith
    have hpow := Real.rpow_pos_of_pos hpos (δ k)
    have hpow1 : 1 ≤ (n:ℝ)^(δ k) := Real.one_le_rpow hn1 hdpos.le
    simp only [B,F,Real.rpow_add hpos,Real.rpow_one]
    by_cases hpr : n.Prime
    · by_cases hc : (n:ZMod 10)=a
      · simp [recip,hpr,hc,residueClass,Set.indicator,vonMangoldt_apply_prime hpr]
        have hlog := Real.add_one_le_exp ((n:ℝ).log*δ k)
        rw [← Real.rpow_def_of_pos hpos] at hlog
        rw [← one_div (n:ℝ),← mul_div_assoc]
        apply (div_le_div_iff₀ (mul_pos hpos hpow) hpos).mpr
        nlinarith [mul_le_mul_of_nonneg_right hlog hpos.le]
      · simp [recip,hpr,hc,residueClass,Set.indicator]
    · simp only [recip,hpr,false_and,if_false,zero_add]
      have hr := residueClass_nonneg a n
      have hδ := hle k
      calc
        _ ≤ 1 * (residueClass a n / ((n:ℝ)* (n:ℝ)^(δ k))) :=
          mul_le_mul_of_nonneg_right hδ (by positivity)
        _ ≤ _ := by rw [one_mul]; exact div_le_div_of_nonneg_left hr hpos (by nlinarith)
  have lim : Tendsto (fun k => ∑' n, F k n) atTop (𝓝 0) := by
    simpa using (tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ => (0:ℝ))
      hB point (Eventually.of_forall bound))
  obtain ⟨C,hC⟩ := LSeries_residueClass_lower_bound ha
  have hlow (k : ℕ) : ((10:ℕ).totient:ℝ)⁻¹ ≤ (∑' n, F k n) + δ k * C := by
    have hlo := hC (x:=1+δ k) (show 1+δ k ∈ Set.Ioc 1 2 from ⟨by linarith [hp k],by linarith [hle k]⟩)
    rw [show 1+δ k-1 = δ k by ring] at hlo
    have h := (div_le_iff₀ (hp k)).mp (sub_le_iff_le_add.mp hlo)
    simp only [F,tsum_mul_left]
    linarith
  have hz : ((10:ℕ).totient:ℝ)⁻¹ ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds
    (show Tendsto (fun k => (∑' n, F k n) + δ k * C) atTop (𝓝 0) by
      simpa using lim.add (hd.mul_const C)) hlow
  norm_num [show (10:ℕ).totient=4 by decide] at hz

private def sieveMod (s : Finset ℕ) := ∏ p ∈ s, p
private def sieveWeight (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1/(p:ℝ)
private lemma productBound (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    (sieveMod s).totient * (1+sieveWeight s) ≤ (sieveMod s : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp [sieveMod,sieveWeight]
  | insert p s hps ih =>
    have hp := hs p (mem_insert_self ..)
    have hs' : ∀ q ∈ s, Nat.Prime q := fun q hq => hs q (mem_insert_of_mem hq)
    have hc : p.Coprime (sieveMod s) := Nat.coprime_prod_right_iff.mpr fun q hq =>
      (Nat.coprime_primes hp (hs' q hq)).mpr (fun he => hps (he ▸ hq))
    have h1 := ih hs'
    have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp.pos
    have hp0 : (0:ℝ) < p := by linarith
    have hW : 0 ≤ sieveWeight s := by unfold sieveWeight; positivity
    simp only [sieveMod,sieveWeight,prod_insert hps,sum_insert hps]
    change ((p*sieveMod s).totient:ℝ) * (1+(1/(p:ℝ)+sieveWeight s)) ≤ _
    rw [Nat.totient_mul hc,Nat.totient_prime hp]
    push_cast [Nat.one_le_iff_ne_zero.mpr hp.ne_zero]
    have hφ : 0 ≤ ((sieveMod s).totient:ℝ) := by positivity
    calc
      _ ≤ (p:ℝ) * ((sieveMod s).totient * (1+sieveWeight s)) := by
        apply (mul_le_mul_iff_of_pos_right hp0).mp
        field_simp
        nlinarith [mul_nonneg hφ hW, mul_nonneg (mul_nonneg hφ hW) hp0.le]
      _ ≤ _ := by simpa [sieveMod] using mul_le_mul_of_nonneg_left h1 hp0.le

private lemma smallSieve (a : ZMod 10) (ha : IsUnit a) (ε : ℝ) (he : 0<ε) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (p:ZMod 10)=a) ∧ 0<sieveMod s ∧
      ((sieveMod s).totient:ℝ)/sieveMod s < ε := by
  have hD := (not_summable_iff_tendsto_nat_atTop_of_nonneg (f := recip a)
    (fun n => by unfold recip; positivity)).mp (reciprocalDiverges a ha)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hD.eventually_gt_atTop (1/ε))
  let s := (range N).filter fun (p:ℕ) => p.Prime ∧ (p:ZMod 10)=a
  have hs (p) (hp : p∈s) := (mem_filter.mp hp).2
  have hmod : 0 < sieveMod s := prod_pos fun p hp => (hs p hp).1.pos
  have hW : 1/ε < sieveWeight s := by simpa [s,sieveWeight,recip,sum_filter] using hN N le_rfl
  have b := productBound s (fun p hp => (hs p hp).1)
  have hd : 0 < (sieveMod s:ℝ) := by exact_mod_cast hmod
  have hφ : 0 < ((sieveMod s).totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hmod
  refine ⟨s,hs,hmod,(div_lt_iff₀ hd).mpr ?_⟩
  have hW' := (div_lt_iff₀ he).mp hW
  nlinarith [mul_le_mul_of_nonneg_right b he.le,mul_lt_mul_of_pos_left hW' hφ]

private def count (P : ℕ → Prop) (x : ℕ) : ℝ :=
  ∑ i ∈ range x, if P i then (1:ℝ) else 0
private def dens (P : ℕ → Prop) (x : ℕ) : ℝ := count P x / x
private def Miss (a : ZMod 10) (x : ℕ) : Prop :=
  ¬ ∃ p : ℕ, p.Prime ∧ (p:ZMod 10) = a ∧ p ∣ x
private lemma countCard (P : ℕ → Prop) (x : ℕ) :
    count P x = ((range x).filter P).card := by simp [count]
private lemma monoCount (P Q : ℕ → Prop) (x : ℕ) (h : ∀ n, P n → Q n) :
    count P x ≤ count Q x := by
  apply sum_le_sum
  intro i _
  by_cases hp : P i <;> by_cases hq : Q i <;> simp_all

private lemma missingLimit (a : ZMod 10) (ha : IsUnit a) :
    Tendsto (dens (Miss a)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨s,hs,hd,hfr⟩ := smallSieve a ha (ε/2) (by positivity)
  let d := sieveMod s
  have hden : 0 < (d:ℝ) := by exact_mod_cast hd
  have hb (x : ℕ) : count (Miss a) x ≤ d.totient * ((x:ℝ)/d+1) := by
    have cover : count (Miss a) x ≤ count (d.Coprime ·) x := by
      apply monoCount
      intro i hi
      apply Nat.coprime_prod_left_iff.mpr
      intro p hp
      exact (hs p hp).1.coprime_iff_not_dvd.mpr (fun h => hi ⟨p,(hs p hp).1,(hs p hp).2,h⟩)
    have nh := Nat.Ico_filter_coprime_le 0 x hd.ne'
    have hnat : ((range x).filter (d.Coprime ·)).card ≤ d.totient*(x/d+1) := by
      simpa [Nat.Ico_zero_eq_range] using nh
    have hx : ((x/d : ℕ):ℝ) ≤ x/(d:ℝ) := (le_div_iff₀ hden).mpr (by exact_mod_cast Nat.div_mul_le_self x d)
    have hreal : (((range x).filter (d.Coprime ·)).card:ℝ) ≤ (d.totient:ℝ)*((x/d:ℕ)+1) := by exact_mod_cast hnat
    rw [countCard (d.Coprime ·) x] at cover
    have hadd : ((x/d : ℕ):ℝ) + 1 ≤ (x:ℝ)/(d:ℝ) + 1 := by linarith
    have hbnd := mul_le_mul_of_nonneg_left hadd (show 0 ≤ (d.totient:ℝ) by positivity)
    apply cover.trans
    convert! hreal.trans hbnd using 1
    congr 2
    ext i
    simp only [mem_filter]
  have small := (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (d.totient:ℝ))).2 (ε/2) (by positivity)
  filter_upwards [eventually_ge_atTop 1,small] with x hx hsx
  have hxR : 0<(x:ℝ) := by exact_mod_cast hx
  have hcn : 0 ≤ count (Miss a) x := by unfold count; positivity
  rw [Real.dist_eq,sub_zero,dens,abs_of_nonneg (div_nonneg hcn hxR.le)]
  calc
    _ ≤ d.totient * ((x:ℝ)/d+1) / x := div_le_div_of_nonneg_right (hb x) hxR.le
    _ = (d.totient:ℝ)/d + (d.totient:ℝ)/x := by field_simp
    _ < _ := by change (d.totient:ℝ)/d < ε/2 at hfr; linarith

private lemma residueCount (d r k : ℕ) (hr : r<d) :
    count (fun i => i%d=r) (k*d) = k := by
  have one : (∑ i ∈ range d, if i%d=r then (1:ℝ) else 0) = 1 := by
    calc
      _ = ∑ i ∈ range d, if i=r then (1:ℝ) else 0 := by
        apply sum_congr rfl
        intro i hi
        rw [Nat.mod_eq_of_lt (mem_range.mp hi)]
      _ = 1 := by simp [hr]
  induction k with
  | zero => simp [count]
  | succ k ih =>
    simp only [count,Nat.succ_mul,sum_range_add,Nat.mul_add_mod_self_right,Nat.cast_succ] at ih ⊢
    rw [ih]; congr 1

private lemma densityOfCriterion (P : ℕ → Prop) (d r : ℕ) (hr : r<d) (hdiv : d∣100)
    (necessary : ∀ i, P i → i%d=r)
    (sufficient : ∀ i, i%d=r → ¬Miss 3 i → ¬Miss 7 i → P i) :
    Tendsto (fun n : ℕ => dens P (10^n)) atTop (𝓝 (1/(d:ℝ))) := by
  have unit3 : IsUnit (3 : ZMod 10) := (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 10)).isUnit
  have unit7 : IsUnit (7 : ZMod 10) := (ZMod.unitOfCoprime 7 (by decide : Nat.Coprime 7 10)).isUnit
  have grow : Tendsto (fun n : ℕ => (10:ℕ)^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have m3 := (missingLimit 3 unit3).comp grow
  have m7 := (missingLimit 7 unit7).comp grow
  have amb (n : ℕ) (hn : 2 ≤ n) : dens (fun i => i%d=r) (10^n) = 1/d := by
    have hdn : d ∣ (10:ℕ)^n := hdiv.trans (show 10^2 ∣ (10:ℕ)^n from pow_dvd_pow _ hn)
    obtain ⟨k,hk⟩ := hdn
    have hpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ (pow_pos (by decide : 0<(10:ℕ)) n))
    have hD : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0<d)
    have hK : 0 < (k:ℝ) := by exact_mod_cast hpos
    unfold dens
    rw [hk,mul_comm d k,residueCount _ _ _ hr,Nat.cast_mul]; field_simp
  have cover (x : ℕ) : count (fun i => i%d=r) x ≤ count P x + count (Miss 3) x + count (Miss 7) x := by
    simp only [count,← sum_add_distrib]
    apply sum_le_sum
    intro i _
    by_cases hi : i%d=r <;> by_cases h3 : Miss 3 i <;> by_cases h7 : Miss 7 i <;>
      by_cases hp : P i <;> simp_all
  have hconst := tendsto_const_nhds (f := atTop (α := ℕ)) (x := 1/(d:ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using (hconst.sub m3).sub m7) hconst
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hcov := div_le_div_of_nonneg_right (cover (10^n)) (by positivity : 0 ≤ ((10^n:ℕ):ℝ))
    rw [add_div,add_div] at hcov
    change dens _ _ ≤ dens _ _ + dens _ _ + dens _ _ at hcov
    rw [amb n hn] at hcov
    simp only [one_div] at hcov
    change _ - dens _ _ - dens _ _ ≤ dens _ _
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    rw [← amb n hn]
    exact div_le_div_of_nonneg_right (monoCount _ _ _ necessary) (by positivity)

private def block (P : ℕ → Prop) (n : ℕ) : ℕ :=
  ((Ico (10^(n-1)) (10^n)).filter P).card

private lemma ratioOfDensity (P : ℕ → Prop) (c : ℝ) (hc : 0<c)
    (h : Tendsto (fun n : ℕ => dens P (10^n)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (block P n:ℝ)/block P (n-1)) atTop (𝓝 10) := by
  let u (n : ℕ) : ℝ := block P (n+1)/(10:ℝ)^n
  have scaled (n : ℕ) : u n = 10 * dens P (10^(n+1)) - dens P (10^n) := by
    have hle : (10:ℕ)^n ≤ 10^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hblock : (block P (n+1):ℝ) = count P (10^(n+1)) - count P (10^n) := by
      simp only [block,Nat.add_one_sub_one,count]
      rw [← Finset.sum_Ico_eq_sub _ hle]
      simp
    dsimp [u]
    rw [hblock]
    simp only [dens,Nat.cast_pow,Nat.cast_ofNat,pow_succ,Nat.cast_mul]
    field_simp
  have hu : Tendsto u atTop (𝓝 (9*c)) := by
    have hl := (tendsto_const_nhds (x := (10:ℝ))).mul (h.comp (tendsto_add_atTop_nat 1)) |>.sub h
    rw [show 9*c=10*c-c by ring]; simpa only [Function.comp_def,←scaled] using hl
  have hq := ((hu.comp (tendsto_add_atTop_nat 1)).div hu (by positivity : 9*c≠0)).mul
    (tendsto_const_nhds (x := (10:ℝ)))
  apply (tendsto_add_atTop_iff_nat 2).mp
  apply (show Tendsto (fun n => u (n+1)/u n*10) atTop (𝓝 10) by simpa [Function.comp_def,hc.ne'] using hq).congr
  intro n; simp only [u,pow_succ (10:ℝ) n,Nat.reduceSubDiff]
  field_simp

open OMA.S_oeis_a348546

private lemma pair (i d : ℕ) : hasPairEndingIn i d = true ↔ i ≠ 0 ∧
    ∃ u v : ℕ, i = u*v ∧ u%10=d ∧ v%10=d := by
  simp only [hasPairEndingIn,decide_eq_true_eq]
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨hdiv,h1,h2⟩ := mem_filter.mp hu
    obtain ⟨hd,hn⟩ := Nat.mem_divisors.mp hdiv
    exact ⟨hn,u,i/u,(Nat.mul_div_cancel' hd).symm,h1,h2⟩
  · rintro ⟨hn,u,v,rfl,h1,h2⟩
    have hu : 0<u := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hn
    exact ⟨u,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,hn⟩,h1,
      by simpa [Nat.mul_div_cancel_left _ hu] using h2⟩⟩

private def P (i : ℕ) := hasPairEndingIn i 3 = true ∧ hasPairEndingIn i 7 = true

private lemma necessary (i : ℕ) (h : P i) : i%10=9 := by
  obtain ⟨_,u,v,rfl,hu,hv⟩ := (pair ..).mp h.1
  rw [Nat.mul_mod,hu,hv]

private lemma sufficient (i : ℕ) (hi : i%10=9) (h3 : ¬Miss 3 i) (h7 : ¬Miss 7 i) : P i := by
  have hn : i ≠ 0 := by omega
  obtain ⟨p,hp,h3c,k,hk⟩ := Classical.not_not.mp h3
  obtain ⟨q,hq,h7c,l,hl⟩ := Classical.not_not.mp h7
  have hr : p%10=3 := by simpa [ZMod.val_natCast,show (3:ZMod 10).val=3 by decide,show (7:ZMod 10).val=7 by decide] using congrArg ZMod.val h3c
  have hs : q%10=7 := by simpa [ZMod.val_natCast,show (3:ZMod 10).val=3 by decide,show (7:ZMod 10).val=7 by decide] using congrArg ZMod.val h7c
  have hK := hi; rw [hk,Nat.mul_mod,hr] at hK
  have hL := hi; rw [hl,Nat.mul_mod,hs] at hL
  exact ⟨(pair ..).mpr ⟨hn,p,k,hk,hr,by omega⟩,(pair ..).mpr ⟨hn,q,l,hl,hs,by omega⟩⟩

theorem result : type_of% @OMA.S_oeis_a348546.main := by
  have same (n : ℕ) : term n = block P n := by
    unfold term block P
    congr 1
    ext x
    simp only [mem_filter]
  simp_rw [same]
  exact ratioOfDensity P (1/10) (by norm_num)
    (densityOfCriterion P 10 9 (by decide) (by decide) necessary sufficient)

end
end PairedFactors

theorem OMA.solution : type_of% @OMA.S_oeis_a348546.main := PairedFactors.result
