import OMAStatements.S_oeis_a383307

namespace DigitRange
noncomputable section
open Finset Filter
open scoped BigOperators Topology
open OMA.S_oeis_a383307

private abbrev Digit := Fin 10
private abbrev Word (n : ℕ) := Fin n → Digit
private def freq {n : ℕ} (w : Word n) (a : Digit) : ℕ := ∑ i, if w i = a then 1 else 0
private def step (a b d : Digit) : ℤ :=
  (if d = a then 1 else 0) - (if d = b then 1 else 0)
private def score {n : ℕ} (a b : Digit) (w : Word n) : ℤ := ∑ i, step a b (w i)
private theorem score_eq {n : ℕ} (a b : Digit) (w : Word n) :
    score a b w = (freq w a : ℤ) - freq w b := by
  simp only [score,step,freq,sum_sub_distrib, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

open scoped Classical
private def prob {n : ℕ} (P : Word n → Prop) : ℝ :=
  (∑ w : Word n, if P w then 1 else 0) / (10:ℝ)^n

private lemma monoProb {n : ℕ} (P Q : Word n → Prop)
    (h : ∀ w, P w → Q w) : prob P ≤ prob Q := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro w _
  split_ifs <;> simp_all

section Fourier
variable {m : ℕ} [NeZero m]
private abbrev ch := ZMod.stdAddChar (N := m)
private def eig (t : ZMod m) : ℂ := (8 + ch t + ch (-t)) / 10

private lemma contraction (t : ZMod m) (ht : t ≠ 0) : ‖eig t‖ < 1 := by
  let z := ch t
  have hn : ‖z‖ = 1 := Circle.norm_coe _
  have hne : z ≠ 1 := by
    intro h
    exact ht (ZMod.injective_stdAddChar (h.trans (ch.map_zero_eq_one.symm)))
  have hlt : z.re < 1 := by
    have hsq := Complex.norm_sub_one_sq_eq_of_norm_eq_one hn
    have hpos := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    linarith
  have hlo := (abs_le.mp (Complex.abs_re_le_norm z)).1
  rw [hn] at hlo
  have hc : ch (-t) = starRingEnd ℂ z := by
    change ((ZMod.toCircle (-t) : Circle):ℂ) = _
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
    rfl
  have he : eig t = ((8+2*z.re)/10 : ℝ) := by
    unfold eig
    rw [hc]
    change (8 + z + starRingEnd ℂ z)/10 = _
    rw [add_assoc,Complex.add_conj]
    push_cast
    rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

private lemma orthog (t : ZMod m) :
    (∑ i : ZMod m, ch (t*i)) = if t=0 then (m:ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m h)

private lemma digitChar (a b : Digit) (hab : a ≠ b) (t : ZMod m) :
    (∑ d : Digit, ch ((step a b d : ZMod m) * t)) = 10 * eig t := by
  have h (d : Digit) : ch ((step a b d : ZMod m)*t) =
      1 + (if d=a then ch t - 1 else 0) + (if d=b then ch (-t) - 1 else 0) := by
    by_cases ha : d=a <;> by_cases hb : d=b <;> simp_all [step,add_comm]
  simp only [h,sum_add_distrib]
  simp [eig]
  ring

private lemma charSum {ι : Type*} (s : Finset ι) (f : ι → ℤ) (t : ZMod m) :
    ch (((∑ i ∈ s, f i : ℤ) : ZMod m)*t) = ∏ i ∈ s, ch ((f i : ZMod m)*t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi,prod_insert hi,Int.cast_add,add_mul,AddChar.map_add_eq_mul,ih]

private lemma charWord (n : ℕ) (a b : Digit) (hab : a ≠ b) (t : ZMod m) :
    (∑ w : Word n, ch ((score a b w : ZMod m)*t)) = (10*eig t)^n := by
  simp only [score,charSum]
  rw [← Fintype.sum_pow (fun d : Digit => ch ((step a b d : ZMod m)*t)),digitChar a b hab]

private theorem modLimit (a b : Digit) (hab : a ≠ b) (r : ZMod m) :
    Tendsto (fun n => prob (fun w : Word n => (score a b w : ZMod m) = r))
      atTop (𝓝 (1/(m:ℝ))) := by
  have hm : (m:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h (n : ℕ) : ((prob (fun w : Word n => (score a b w : ZMod m) = r)):ℂ) =
      (∑ t : ZMod m, ch (-(r*t)) * eig t ^ n) / m := by
    unfold prob
    push_cast
    have ind (x : ZMod m) : (if x=r then (1:ℂ) else 0) =
        (∑ t : ZMod m, ch ((x-r)*t))/m := by
      rw [orthog]; by_cases hx : x=r <;> simp [hx,sub_eq_zero,hm]
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, ind,← Finset.sum_div]
    rw [sum_comm]
    have spl (x t : ZMod m) : ch ((x-r)*t) = ch (x*t) * ch (-(r*t)) := by
      rw [sub_mul,sub_eq_add_neg,AddChar.map_add_eq_mul]
    simp only [spl,← sum_mul,charWord n a b hab,mul_pow]
    field_simp
    simp only [mul_assoc, mul_comm, Finset.mul_sum]
  have ht (t : ZMod m) : Tendsto (fun n : ℕ => ch (-(r*t)) * eig t ^ n)
      atTop (𝓝 (if t=0 then (1:ℂ) else 0)) := by
    by_cases hz : t=0
    · subst t; norm_num [eig]
    · simpa [hz] using (tendsto_const_nhds (x := ch (-(r*t)))).mul
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (contraction t hz))
  apply Filter.tendsto_ofReal_iff.mp
  simp_rw [h]
  simpa using (tendsto_finsetSum univ (fun t _ => ht t)).div_const (m:ℂ)

end Fourier

private theorem atomLimit (a b : Digit) (hab : a ≠ b) (z : ℤ) :
    Tendsto (fun n => prob (fun w : Word n => score a b w = z)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ε)
  have hp : 0 < (m:ℝ) := lt_trans (by positivity) hm
  have : NeZero m := ⟨by exact_mod_cast hp.ne'⟩
  have hsmall : 1/(m:ℝ) < ε := by rwa [div_lt_iff₀ hp, mul_comm, ← div_lt_iff₀ hε]
  have ev := (tendsto_order.mp (modLimit a b hab (z:ZMod m))).2 ε hsmall
  filter_upwards [ev] with n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg]
  · exact (monoProb _ _ (fun w hw => congrArg (fun u : ℤ => (u:ZMod m)) hw)).trans_lt hn
  · unfold prob; positivity

open scoped Classical
private abbrev Event := (n : ℕ) → Word n → Prop
private def Rare (P : Event) : Prop := Tendsto (fun n => prob (P n)) atTop (𝓝 0)
private lemma probNonneg {n : ℕ} (P : Word n → Prop) : 0 ≤ prob P := by unfold prob; positivity
private lemma subRare {P Q : Event} (hQ : Rare Q) (h : ∀ n w, P n w → Q n w) : Rare P :=
  squeeze_zero (fun _ => probNonneg _) (fun n => monoProb _ _ (h n)) hQ

private lemma unionRare {ι : Type*} [Fintype ι] (P : ι → Event) (hP : ∀ i, Rare (P i)) :
    Rare (fun n w => ∃ i, P i n w) := by
  have h : Tendsto (fun n => ∑ i, prob (P i n)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun i _ => hP i)
  apply squeeze_zero (fun _ => probNonneg _) _ h
  intro n
  simp only [prob,← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [sum_comm]
  apply sum_le_sum
  intro w _
  by_cases he : ∃ i, P i n w
  · obtain ⟨i,hi⟩ := he
    have hh := single_le_sum (f := fun j => if P j n w then (1:ℝ) else 0)
      (fun _ _ => by positivity) (mem_univ i)
    simpa [hi,show ∃ j, P j n w from ⟨i,hi⟩] using hh
  · simp only [he,if_false]; positivity

private lemma orRare {P Q : Event} (hp : Rare P) (hq : Rare Q) :
    Rare (fun n w => P n w ∨ Q n w) := by
  let A : Bool → Event := fun b => if b then P else Q
  apply subRare (unionRare A (by rintro (⟨⟩|⟨⟩) <;> simp_all [A]))
  rintro n w (h|h)
  · exact ⟨true,h⟩
  · exact ⟨false,h⟩

private lemma missing (d : Digit) : Rare (fun _ w => ∀ i, w i ≠ d) := by
  have h (n : ℕ) : prob (fun w : Word n => ∀ i, w i ≠ d) = ((9:ℝ)/10)^n := by
    have hsum : (∑ i : Digit, if i≠d then (1:ℝ) else 0) = 9 := by
      simp [sum_ite, filter_ne', card_erase_of_mem]
    rw [div_pow,← hsum,Fintype.sum_pow,prob]
    congr 1
    apply sum_congr rfl
    intro w _
    rw [Fintype.prod_boole]
    split_ifs <;> rfl
  unfold Rare; simp_rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private def Good {n : ℕ} (w : Word n) : Prop :=
  (∀ d, ∃ i, w i = d) ∧ ∀ a b, a ≠ b → score a b w < -1 ∨ 1 < score a b w

private lemma exceptions : Rare (fun _ w => ¬ Good w) := by
  have pairs (d : Digit × Digit) : Rare (fun _ w => d.1 ≠ d.2 ∧
      (score d.1 d.2 w = -1 ∨ score d.1 d.2 w = 0 ∨ score d.1 d.2 w = 1)) := by
    by_cases h : d.1 = d.2
    · have hh (n : ℕ) : prob (fun w : Word n => d.1 ≠ d.2 ∧
          (score d.1 d.2 w = -1 ∨ score d.1 d.2 w = 0 ∨ score d.1 d.2 w = 1)) = 0 := by simp [h,prob]
      unfold Rare; simp_rw [hh]; exact tendsto_const_nhds
    · apply subRare (Q := fun _ w => score d.1 d.2 w = -1 ∨ score d.1 d.2 w = 0 ∨ score d.1 d.2 w = 1) _ (fun _ _ h => h.2)
      exact orRare (P := fun _ w => score d.1 d.2 w = -1) (Q := fun _ w => score d.1 d.2 w = 0 ∨ score d.1 d.2 w = 1) (atomLimit d.1 d.2 h (-1))
        (orRare (P := fun _ w => score d.1 d.2 w = 0) (Q := fun _ w => score d.1 d.2 w = 1) (atomLimit d.1 d.2 h 0) (atomLimit d.1 d.2 h 1))
  apply subRare (orRare (unionRare _ missing) (unionRare _ pairs))
  intro n w h
  by_cases allDigits : ∀ d, ∃ i, w i = d
  · right
    have ng : ¬ ∀ a b, a ≠ b → score a b w < -1 ∨ 1 < score a b w :=
      fun hs => h ⟨allDigits,hs⟩
    push Not at ng
    obtain ⟨a,b,hab,h1,h2⟩ := ng
    exact ⟨(a,b),hab,by dsimp; omega⟩
  · left; simpa using allDigits

private def Wins {n : ℕ} (w : Word n) (d : Digit) := ∀ e, e ≠ d → freq w e < freq w d

private lemma winnerExists {n : ℕ} {w : Word n} (hg : Good w) : ∃ d, Wins w d := by
  obtain ⟨d,_,hd⟩ := exists_max_image univ (freq w) univ_nonempty
  refine ⟨d,fun e he => ?_⟩
  have hm := hd e (mem_univ e)
  have hx := hg.2 e d he
  rw [score_eq] at hx
  omega

private lemma probNot {n : ℕ} (P : Word n → Prop) :
    prob (fun w => ¬ P w) = 1 - prob P := by
  unfold prob
  calc
    _ = (∑ w : Word n, (1 - (if P w then (1:ℝ) else 0))) / 10^n := by
      congr 1
      apply sum_congr rfl
      intro w _
      by_cases h : P w <;> simp [h]
    _ = _ := by
      simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_fin,mul_one,Nat.cast_pow,Nat.cast_ofNat]
      field_simp

private lemma winProb (n : ℕ) (d e : Digit) :
    prob (fun w : Word n => Wins w d) = prob (fun w : Word n => Wins w e) := by
  let σ := Equiv.swap d e
  let E := (Equiv.refl (Fin n)).arrowCongr σ
  have hf (w : Word n) (a : Digit) : freq (E w) (σ a) = freq w a := by
    simp [freq,E]
  have hw (w : Word n) : Wins (E w) (σ d) ↔ Wins w d := by
    constructor
    · intro h z hz
      simpa only [hf] using h (σ z) (σ.injective.ne hz)
    · intro h z hz
      obtain ⟨u,rfl⟩ := σ.surjective z
      simpa only [hf] using h u (fun he => hz (congrArg σ he))
  have he : σ d = e := Equiv.swap_apply_left d e
  rw [he] at hw
  unfold prob
  congr 1
  calc
    _ = ∑ w : Word n, if Wins (E w) e then (1:ℝ) else 0 := by simp_rw [hw]
    _ = _ := E.sum_comp (fun w => if Wins w e then (1:ℝ) else 0)

private lemma winLimit : Tendsto (fun n => prob (fun w : Word n => Wins w 9)) atTop (𝓝 (1/10:ℝ)) := by
  have hrare : Rare (fun _ w => ¬ ∃ d, Wins w d) :=
    subRare exceptions (fun _ _ h hg => h (winnerExists hg))
  have h (n : ℕ) : (10:ℝ) * prob (fun w : Word n => Wins w 9) =
      prob (fun w : Word n => ∃ d, Wins w d) := by
    calc
      _ = ∑ d : Digit, prob (fun w : Word n => Wins w d) := by
        simp_rw [winProb n _ 9]; simp
      _ = _ := by
        unfold prob
        rw [← sum_div,sum_comm]
        congr 1
        apply sum_congr rfl
        intro w _
        by_cases hex : ∃ d, Wins w d
        · obtain ⟨d,hd⟩ := hex
          rw [if_pos (show ∃ j, Wins w j from ⟨d,hd⟩)]
          rw [sum_eq_single d, if_pos hd]
          · intro e _ he
            exact if_neg (fun h => (not_lt_of_ge (hd e he).le) (h d he.symm))
          · simp
        · simp_all
  have h' (n : ℕ) : prob (fun w : Word n => Wins w 9) =
      (1 - prob (fun w : Word n => ¬ ∃ d, Wins w d))/10 := by
    rw [probNot]; linarith [h n]
  simp_rw [h']
  simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hrare).div_const 10

private def tail {n : ℕ} (w : Word n) := List.ofFn fun i => (w i).val
private def digits {n : ℕ} (h : Fin 9) (w : Word n) := (h.val+1) :: tail w

private lemma countTail {n : ℕ} (w : Word n) (d : Digit) : (tail w).count d.val = freq w d := by
  induction n with
  | zero => simp [tail,freq,List.ofFn_zero]
  | succ n ih =>
    rw [tail,List.ofFn_succ,List.count_cons, freq,Fin.sum_univ_succ]
    have hh := ih (fun i => w i.succ)
    change (tail (fun i : Fin n => w i.succ)).count d.val + _ = _ + _
    rw [hh]
    unfold freq
    by_cases h : w 0 = d
    · simp [h,Nat.add_comm]
    · have he : (w 0).val ≠ d.val := fun hh => h (Fin.ext hh)
      simp [h,he,beq_iff_eq]

private lemma goodQualifies {n : ℕ} (h : Fin 9) (w : Word n) (hg : Good w) :
    (qualifies (digits h w) = true) ↔ Wins w 9 := by
  have hd (d : Digit) : d.val ∈ digits h w := by
    obtain ⟨i,hi⟩ := hg.1 d
    simp [digits,tail,List.mem_ofFn,← hi]
  have bound (x : ℕ) (hx : x ∈ digits h w) : x ≤ 9 := by
    simp only [digits,List.mem_cons,tail,List.mem_ofFn] at hx
    rcases hx with rfl | ⟨i,rfl⟩ <;> omega
  have hm : (digits h w).max? = some 9 :=
    List.max?_eq_some_iff.mpr ⟨hd 9, bound⟩
  have hl : (digits h w).min? = some 0 :=
    List.min?_eq_some_iff.mpr ⟨hd 0,fun _ _ => Nat.zero_le _⟩
  have hc (d : Digit) : (digits h w).count d.val =
      freq w d + (if h.val+1=d.val then 1 else 0) := by
    simp [digits,List.count_cons,countTail,beq_iff_eq]
  have compare (d : Digit) (hne : d ≠ 9) :
      (digits h w).count d.val < (digits h w).count 9 ↔ freq w d < freq w 9 := by
    have hgap := hg.2 d 9 hne
    rw [score_eq] at hgap
    change (digits h w).count d.val < (digits h w).count (9:Digit).val ↔ _
    rw [hc,hc]
    split_ifs <;> omega
  simp only [qualifies,hm,hl,Option.getD_some,Nat.sub_zero,uniqueMode,List.all_eq_true,
    List.mem_range,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro h d hne
    exact (compare d hne).mp ((h d.val d.isLt).resolve_left (fun he => hne (Fin.ext he)))
  · intro hw k hk
    let d : Digit := ⟨k,hk⟩
    by_cases he : d=9
    · exact Or.inl (congrArg Fin.val he)
    · exact Or.inr ((compare d he).mpr (hw d he))

private def code {n : ℕ} (x : Fin 9 × Word n) := Nat.ofDigits 10 (digits x.1 x.2).reverse
private lemma lengthDigits {n : ℕ} (h : Fin 9) (w : Word n) :
    (digits h w).length = n+1 := by simp [digits,tail]
private lemma digitsBound {n : ℕ} (h : Fin 9) (w : Word n) {i : ℕ} (hi : i ∈ digits h w) :
    i < 10 := by
  simp only [digits,List.mem_cons,tail,List.mem_ofFn] at hi
  rcases hi with rfl | ⟨j,rfl⟩ <;> omega
private lemma decode {n : ℕ} (x : Fin 9 × Word n) : digitWord (code x) = digits x.1 x.2 := by
  have hd := Nat.digits_ofDigits 10 (by decide) (digits x.1 x.2).reverse
    (fun _ hi => digitsBound _ _ (List.mem_reverse.mp hi))
    (fun h => by simp [List.getLast_eq_head_reverse,digits])
  change Nat.digits 10 (code x) = _ at hd
  have hn : code x ≠ 0 := by
    intro hh; simp [hh,digits] at hd
  simp [digitWord,hn,hd]
private lemma codeBound {n : ℕ} (x : Fin 9 × Word n) : code x < 10^(n+1) := by
  simpa [code,lengthDigits] using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10)
    (fun _ (hi : _ ∈ (digits x.1 x.2).reverse) => digitsBound _ _ (List.mem_reverse.mp hi))

private lemma represent (k n : ℕ) (hn : 0 < n) (hk : (digitWord k).length = n+1) :
    ∃ x : Fin 9 × Word n, digits x.1 x.2 = digitWord k := by
  have hkn : k ≠ 0 := by rintro rfl; simp [digitWord] at hk; omega
  have hb {d : ℕ} (hd : d ∈ digitWord k) : d < 10 :=
    Nat.digits_lt_base (by decide : 1<10) (by simpa [digitWord,hkn] using hd)
  have hhead (hne : digitWord k ≠ []) : (digitWord k).head hne ≠ 0 := by
    simpa [digitWord,hkn,List.head_reverse] using Nat.getLast_digit_ne_zero 10 hkn
  obtain ⟨a,l,hl⟩ := List.exists_cons_of_ne_nil (show digitWord k ≠ [] by intro h; simp [h] at hk)
  have hal : a < 10 := hb (hl ▸ List.mem_cons_self)
  have hap : a ≠ 0 := by simpa [hl] using hhead (hl ▸ List.cons_ne_nil _ _)
  have hlen : l.length = n := by simpa [hl] using hk
  subst n
  let w : Word l.length := fun i => ⟨l[i], hb (hl ▸ (List.mem_cons_of_mem _ (List.getElem_mem i.isLt)))⟩
  refine ⟨(⟨a-1,by omega⟩,w),?_⟩
  simp [digits,tail,w,hl,show a-1+1=a by omega]

private lemma catalogCount (n : ℕ) (hn : 0 < n) :
    (term (n+1) : ℝ) / 10^n =
    ∑ h : Fin 9, prob (fun w : Word n => qualifies (digits h w) = true) := by
  let S := (univ : Finset (Fin 9 × Word n)).filter fun x => qualifies (digits x.1 x.2) = true
  have hcard : S.card = term (n+1) := by
    apply card_bij (fun x _ => code x)
    · intro x hx
      exact mem_filter.mpr ⟨mem_range.mpr (codeBound x), by rw [decode]; exact ⟨lengthDigits _ _,(mem_filter.mp hx).2⟩⟩
    · rintro ⟨a,w⟩ _ ⟨b,v⟩ _ h
      have he := congrArg digitWord h
      rw [decode,decode] at he
      have hlist := List.cons.inj he
      apply Prod.ext
      · apply Fin.ext; simpa using hlist.1
      · have hh := List.ofFn_injective hlist.2
        funext i; exact Fin.ext (congrFun hh i)
    · intro k hk
      obtain ⟨hkn,hq⟩ := (mem_filter.mp hk).2
      obtain ⟨x,hx⟩ := represent k n hn hkn
      refine ⟨x, mem_filter.mpr ⟨mem_univ _,hx ▸ hq⟩,?_⟩
      have hz : k ≠ 0 := by rintro rfl; simp [digitWord] at hkn; omega
      simp [code,hx,digitWord,hz,Nat.ofDigits_digits]
  rw [← hcard]
  simp only [prob,← sum_div]
  congr 1
  rw [← Fintype.sum_prod_type']
  simp only [S,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro x _
  split_ifs <;> rfl

private lemma probCompare {n : ℕ} (P Q : Word n → Prop)
    (h : ∀ w, Good w → (P w ↔ Q w)) :
    prob P ≤ prob Q + prob (fun w : Word n => ¬ Good w) := by
  simp only [prob,← add_div,← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro w _
  by_cases hg : Good w
  · simp [hg,h w hg]
  · by_cases hp : P w <;> by_cases hq : Q w <;> norm_num [hg,hp,hq]

private lemma leadingLimit (h : Fin 9) : Tendsto
    (fun n => prob (fun w : Word n => qualifies (digits h w) = true)) atTop (𝓝 (1/10:ℝ)) := by
  have hu := winLimit.add exceptions
  have hl := winLimit.sub exceptions
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hl) (by simpa using hu)
  · intro n; apply sub_le_iff_le_add.mpr
    exact probCompare _ _ (fun w hw => (goodQualifies h w hw).symm)
  · intro n; exact probCompare _ _ (fun w hw => goodQualifies h w hw)

private def scaled (n : ℕ) : ℝ := term (n+1) / (10:ℝ)^n
private lemma scaledLimit : Tendsto scaled atTop (𝓝 (9/10:ℝ)) := by
  have h := tendsto_finsetSum univ (fun (i : Fin 9) _ => leadingLimit i)
  apply (show Tendsto _ atTop (𝓝 (9/10:ℝ)) by simpa [div_eq_mul_inv] using h).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (catalogCount n hn).symm

theorem ratio : type_of% @OMA.S_oeis_a383307.main := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := ((scaledLimit.comp (tendsto_add_atTop_nat 1)).div scaledLimit
    (by norm_num : (9/10:ℝ) ≠ 0)).mul (tendsto_const_nhds (x := (10:ℝ)))
  apply (show Tendsto (fun n => scaled (n+1) / scaled n * 10) atTop (𝓝 10) by
    simpa [Function.comp_def] using h).congr
  intro n
  simp only [scaled,pow_succ (10:ℝ) n]
  field_simp

end
end DigitRange

theorem OMA.solution : type_of% @OMA.S_oeis_a383307.main := DigitRange.ratio
