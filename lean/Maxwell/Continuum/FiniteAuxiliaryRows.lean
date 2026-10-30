import Maxwell.Continuum.FiniteAuxiliaryLattice
import Maxwell.Continuum.FiniteAuxiliaryBlocks

/-! Whole-operator off-site and non-neighbor estimates for the actual
finite continuum assembly. The constant contour error is summed only
over the finite occupied set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Bloch EffectiveMass Auxiliary MasterConstants

variable {ι : Type*} [Fintype ι]

def shellBlocks {L : ℕ} {z σ : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (d : ℕ)
    (position : ι → Bloch.Alias) (n : ℕ) (i j : ι) : FieldL2 →L[ℂ] FieldL2 :=
  if n ≤ latticeOneNorm (position i-position j) then
    physicalWellBlock D hσ0 hσ d (position i-position j) else 0

theorem shellBlocks_sum_bound {L : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (p : ι → Bloch.Alias) (n : ℕ) {B : ℝ}
    (hb : ∑ i ∈ Finset.univ.filter (fun i => n ≤ latticeOneNorm (p i)),
      (((3 : ℝ)^d)⁻¹)^latticeOneNorm (p i) ≤ B) :
    (∑ i, ‖if n ≤ latticeOneNorm (p i) then physicalWellBlock D hσ0 hσ d (p i) else 0‖) ≤
      Cs*(L : ℝ)^5*(B+(Fintype.card ι : ℝ)*Real.exp (-cs*(L : ℝ))) := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => n ≤ latticeOneNorm (p i))
  have he : (∑ i, ‖if n ≤ latticeOneNorm (p i) then physicalWellBlock D hσ0 hσ d (p i) else 0‖) =
      ∑ i ∈ s, ‖physicalWellBlock D hσ0 hσ d (p i)‖ := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [norm_zero]
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, Cs*(L : ℝ)^5*
        ((((3 : ℝ)^d)⁻¹)^latticeOneNorm (p i)+Real.exp (-cs*(L : ℝ))) :=
      Finset.sum_le_sum (fun i _ => physicalWellBlock_geometric hL D hσ0 hσ d (p i))
    _ = Cs*(L : ℝ)^5*((∑ i ∈ s, (((3 : ℝ)^d)⁻¹)^latticeOneNorm (p i))+
        (s.card : ℝ)*Real.exp (-cs*(L : ℝ))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg Cs_pos.le (pow_nonneg (Nat.cast_nonneg L) 5))
      apply add_le_add hb
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast s.card_le_univ

theorem offsite_weight {d : ℕ} (hd : 1 ≤ d) (p : ι → Bloch.Alias)
    (hinj : Function.Injective p) :
    ∑ i ∈ Finset.univ.filter (fun i => 1 ≤ latticeOneNorm (p i)),
      (((3 : ℝ)^d)⁻¹)^latticeOneNorm (p i) ≤ 64*((3 : ℝ)^d)⁻¹ := by
  apply occupied_nonzero_weight p hinj _ (by positivity)
  · have hp : (3 : ℝ) ≤ 3^d := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hd
    rw [one_div]
    exact (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [hp])
  · intro i hi hz
    have hn := (Finset.mem_filter.mp hi).2
    simp only [hz, latticeOneNorm, Pi.zero_apply, Int.natAbs_zero, Finset.sum_const_zero] at hn
    omega

theorem far_weight {d : ℕ} (hd : 1 ≤ d) (p : ι → Bloch.Alias)
    (hinj : Function.Injective p) :
    ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ latticeOneNorm (p i)),
      (((3 : ℝ)^d)⁻¹)^latticeOneNorm (p i) ≤ 256*(((3 : ℝ)^d)⁻¹)^2 := by
  apply occupied_far_weight p hinj _ (by positivity)
  · have hp : (3 : ℝ) ≤ 3^d := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hd
    rw [one_div]
    exact (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [hp])
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

theorem offsite_operator_norm {L d : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (hd : 1 ≤ d) (position : ι → Bloch.Alias) (hinj : Function.Injective position) :
    ‖blockOperator (shellBlocks D hσ0 hσ d position 1)‖ ≤
      Cs*(L : ℝ)^5*(64*((3 : ℝ)^d)⁻¹+(Fintype.card ι : ℝ)*Real.exp (-cs*(L : ℝ))) := by
  apply blockOperator_norm_le _ (mul_nonneg (mul_nonneg Cs_pos.le (by positivity)) (by positivity))
  · intro i
    exact shellBlocks_sum_bound hL D hσ0 hσ d (fun j => position i-position j) 1
      (offsite_weight hd _ (fun a b hab => hinj (sub_right_inj.mp hab)))
  · intro j
    exact shellBlocks_sum_bound hL D hσ0 hσ d (fun i => position i-position j) 1
      (offsite_weight hd _ (fun a b hab => hinj (sub_left_inj.mp hab)))

theorem nonneighbor_operator_norm {L d : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (hd : 1 ≤ d) (position : ι → Bloch.Alias) (hinj : Function.Injective position) :
    ‖blockOperator (shellBlocks D hσ0 hσ d position 2)‖ ≤
      Cs*(L : ℝ)^5*(256*(((3 : ℝ)^d)⁻¹)^2+(Fintype.card ι : ℝ)*Real.exp (-cs*(L : ℝ))) := by
  apply blockOperator_norm_le _ (mul_nonneg (mul_nonneg Cs_pos.le (by positivity)) (by positivity))
  · intro i
    exact shellBlocks_sum_bound hL D hσ0 hσ d (fun j => position i-position j) 2
      (far_weight hd _ (fun a b hab => hinj (sub_right_inj.mp hab)))
  · intro j
    exact shellBlocks_sum_bound hL D hσ0 hσ d (fun i => position i-position j) 2
      (far_weight hd _ (fun a b hab => hinj (sub_left_inj.mp hab)))

#print axioms offsite_operator_norm
#print axioms nonneighbor_operator_norm

end Maxwell.Continuum.FiniteAuxiliary
