import OMAStatements.S_oeis_a122251

namespace HankelNumerator

open Finset Matrix
open OMA.S_oeis_a122251

private def mat (a p n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / ((a : ℚ) + p * (i.val + (j.val : ℚ)))

private def split (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩ | j) <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

private def denominators (a p n : ℕ) := ∏ i ∈ range n, (a + p * (i+1))

private theorem pivot (a p n : ℕ) (ha : 0 < a) :
    (mat a p (n+1)).det =
    (1/(a:ℚ)) * (((p:ℚ)^n * n.factorial) / denominators a p n)^2 *
      (mat (a+2*p) p n).det := by
  classical
  let H := mat a p (n+1)
  let w : Fin (n+1) → ℚ := Fin.cases (a:ℚ) fun _ => 1
  let T := Matrix.of fun i j => w i * H i j
  let B : Matrix Unit (Fin n) ℚ := fun _ j => (a:ℚ) * H 0 j.succ
  let C : Matrix (Fin n) Unit ℚ := fun i _ => H i.succ 0
  let D : Matrix (Fin n) (Fin n) ℚ := fun i j => H i.succ j.succ
  let v : Fin n → ℚ := fun i => p * ((i.val:ℚ)+1) / (a + p * ((i.val:ℚ)+1))
  let R := mat (a+2*p) p n
  have ha' : (a:ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hT : T.submatrix (split n) (split n) = Matrix.fromBlocks 1 B C D := by
    ext i j
    rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
      simp [T, w, B, C, D, split, Matrix.submatrix, Matrix.fromBlocks, H, mat, ha']
  have hS : D - C * B = Matrix.of (fun i j => v i *
      (Matrix.of (fun i j => v j * R i j)) i j) := by
    ext i j
    rw [Matrix.sub_apply, Matrix.mul_apply]
    simp [D, C, B, R, v, H, mat, Fin.val_succ]
    have haPos : (0:ℚ) < a := by exact_mod_cast ha
    field_simp
    ring
  have hdet := congrArg Matrix.det hT
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_one₁₁, hS,
    Matrix.det_mul_column v _, Matrix.det_mul_row v R] at hdet
  have hW : (∏ i, w i) = (a:ℚ) := by rw [Fin.prod_univ_succ]; simp [w]
  have hv : (∏ i, v i) = ((p:ℚ)^n * n.factorial) / denominators a p n := by
    simp only [v, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Fin.prod_univ_eq_prod_range (fun i => (i:ℚ)+1),
      Fin.prod_univ_eq_prod_range (fun i => (a:ℚ)+p*((i:ℚ)+1))]
    norm_cast
    rw [Finset.prod_range_add_one_eq_factorial]
    rfl
  change (Matrix.of fun i j => w i * H i j).det = _ at hdet
  rw [Matrix.det_mul_column, hW, hv] at hdet
  change H.det = _ * _ * R.det
  calc
    H.det = (1/(a:ℚ)) * (a*H.det) := by field_simp
    _ = _ := by rw [hdet]; ring

/-- The prime-to-p part of n! cancels against every length-n progression of step p. -/
private theorem cancels (a p n : ℕ) (hp : p.Prime) :
    (ordCompl[p] n.factorial) ∣ denominators a p n := by
  let m := ordCompl[p] n.factorial
  have : NeZero m := ⟨(Nat.ordCompl_pos p n.factorial_ne_zero).ne'⟩
  let x : ℕ := (((p:ZMod m)⁻¹ * (a+p) : ZMod m)).val
  have hpx : (p:ZMod m) * x = a+p := by
    simp only [x,ZMod.natCast_zmod_val, ← mul_assoc,
      ZMod.coe_mul_inv_eq_one p (Nat.coprime_ordCompl hp n.factorial_ne_zero), one_mul]
  have hfac := (Nat.ordCompl_dvd n.factorial p).trans (Nat.factorial_dvd_ascFactorial x n)
  rw [Nat.ascFactorial_eq_prod_range] at hfac
  have hz := (ZMod.natCast_eq_zero_iff _ m).mpr hfac
  push_cast at hz
  apply (ZMod.natCast_eq_zero_iff _ m).mp
  unfold denominators
  push_cast
  calc
    _ = ∏ i ∈ range n, ((p:ZMod m) * (x+i)) := by
      apply prod_congr rfl
      intro i _
      rw [mul_add (p:ZMod m) (x:ZMod m), hpx]
      ring
    _ = 0 := by rw [prod_mul_distrib, hz, mul_zero]

private def powerIndex (p n : ℕ) :=
  ∑ k ∈ range n, (k+1 + (k+1).factorial.factorization p)

private theorem index_eq (p n : ℕ) (hp : p.Prime) :
    powerIndex p n = exponent p n := by
  apply sum_congr rfl
  intro k hk
  have hkn : k+1 ≤ n := mem_range.mp hk
  have hb : Nat.log p (k+1) < n+1 := (Nat.log_le_self _ _).trans_lt (by omega)
  rw [Nat.factorization_factorial hp hb, sum_range_eq_add_Ico _ (by omega : 0 < n+1)]
  simp

private theorem reduced (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (ha : 0 < a) (hc : p.Coprime a) :
    ∃ b : ℕ, 0 < b ∧ p.Coprime b ∧
      (mat a p (n+1)).det = ((p:ℚ)^2)^(powerIndex p n) / b := by
  induction n generalizing a with
  | zero =>
    refine ⟨a,ha,hc,?_⟩
    simp [mat,powerIndex]
  | succ n ih =>
    have hshift : p.Coprime (a+2*p) := by
      simpa [Nat.mul_comm 2 p] using (Nat.coprime_add_mul_left_left a p 2).mpr hc.symm |>.symm
    obtain ⟨d,hd,hcd,heq⟩ := ih (a+2*p) (by omega) hshift
    let k := n+1
    let m := ordCompl[p] k.factorial
    obtain ⟨c, hprod⟩ := cancels a p k hp
    change denominators a p k = m*c at hprod
    have hrpos : 0 < denominators a p k :=
      Finset.prod_pos fun i _ => by omega
    have hcp : 0 < c := by
      rw [hprod] at hrpos
      exact Nat.pos_of_mul_pos_left hrpos
    have hcop : p.Coprime (denominators a p k) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro i _
      exact ((Nat.coprime_add_mul_left_left a p (i+1)).mpr hc.symm).symm
    have hcc : p.Coprime c := Nat.Coprime.of_dvd_right (hprod ▸ dvd_mul_left c m) hcop
    refine ⟨a*c^2*d, by positivity, (hc.mul_right (hcc.pow_right 2)).mul_right hcd, ?_⟩
    rw [pivot _ _ _ ha,heq]
    have hm : (0:ℚ) < m := by exact_mod_cast Nat.ordCompl_pos p k.factorial_ne_zero
    have hf : k.factorial = p^(k.factorial.factorization p)*m :=
      (Nat.mul_div_cancel' (Nat.ordProj_dvd k.factorial p)).symm
    have hfq : (k.factorial:ℚ) = (p:ℚ)^(k.factorial.factorization p)*m := by exact_mod_cast hf
    have hq : (denominators a p k:ℚ) = m*(c:ℚ) := by exact_mod_cast hprod
    have hidx : powerIndex p (n+1) = powerIndex p n + (k+k.factorial.factorization p) :=
      Finset.sum_range_succ _ _
    change 1/(a:ℚ) * (((p:ℚ)^k * k.factorial)/denominators a p k)^2 *
      (((p:ℚ)^2)^powerIndex p n / d) = _
    rw [hfq,hq,hidx,pow_add,pow_add]
    push_cast
    have h1 : (a:ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have h2 : (c:ℚ) ≠ 0 := by exact_mod_cast hcp.ne'
    have h3 : (d:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    simp only [← pow_mul, Nat.mul_comm 2]
    ring

theorem result : type_of% @OMA.S_oeis_a122251.main := by
  intro p hp n
  obtain ⟨b,hb,hc,h⟩ := reduced p hp n 1 (by decide) (Nat.coprime_one_right _)
  rw [index_eq p n hp] at h
  change (mat 1 p (n+1)).det.num = _
  rw [h]
  have hn := Rat.num_div_eq_of_coprime (a := ((p:ℤ)^2)^exponent p n)
    (b := (b:ℤ)) (by exact_mod_cast hb) (by simpa using (hc.pow_left 2).pow_left (exponent p n))
  simpa using hn

end HankelNumerator

theorem OMA.solution : type_of% @OMA.S_oeis_a122251.main := HankelNumerator.result
