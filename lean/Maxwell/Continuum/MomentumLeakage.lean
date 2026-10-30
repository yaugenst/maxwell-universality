import Maxwell.Continuum.MomentumLeakageSource
import Maxwell.Continuum.MomentumLeakageScale

/-! The literal continuum nested momentum-cutoff leakage theorem.
Its source is the actual constructed mode; its potential is the actual
finite collection of translated wells; its inverse is the full cutoff
Maxwell inverse. No support or polarization premise is imposed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open Bloch EffectiveMass PeriodicBand MasterConstants

attribute [local irreducible] highMomentumProjection Auxiliary.resolvent actualSource cutoffOperator

theorem actualSource_high_half {L z : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z) :
    ‖highMomentumProjection (smallRadius/2) (actualSource D (inverse_length_le_1024 hL))‖ ≤
      (2 : ℝ)^234 * Real.exp (-cs*L^(1/3 : ℝ)) := by
  have hL1 := length_ge_one hL
  have hb := actualSource_nested_bound D (inverse_length_le_1024 hL)
    (leakageStep L) (leakageStep_pos hL1).le (leakageDepth L)
  rw [leakageStep_endpoint hL1] at hb
  have he : smallRadius/4+smallRadius/4 = smallRadius/2 := by ring
  rw [he] at hb
  calc
    _ ≤ Real.exp (-cs*L^(1/3 : ℝ)) + (2 : ℝ)^233*Real.exp (-cs*L^(1/3 : ℝ)) :=
      hb.trans (add_le_add (leakage_quarter_decay hL1)
        (mul_le_mul_of_nonneg_left (leakage_sqrt_decay hL1) (by positivity)))
    _ ≤ _ := by nlinarith [Real.exp_pos (-cs*L^(1/3 : ℝ))]

variable {ι : Type*} [Fintype ι]

theorem translatedSource_sum_high {L z : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (r : ι → Space) (c : ι → ℂ) {s : ℝ} (hs : smallRadius/2 ≤ s) :
    ‖highMomentumProjection s (∑ i, c i • fieldTranslation (-r i)
      (actualSource D (inverse_length_le_1024 hL)))‖ ≤
      ((2 : ℝ)^234 * Real.exp (-cs*L^(1/3 : ℝ))) * ∑ i, ‖c i‖ := by
  classical
  rw [map_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [map_smul, norm_smul, highMomentumProjection_translation_norm]
  have hb := (highMomentumProjection_norm_mono hs (actualSource D (inverse_length_le_1024 hL))).trans
    (actualSource_high_half hL D)
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The continuum manuscript's leakage theorem for the fully defined
physical fields and operators. Arbitrary real well centers are allowed;
in particular it applies to every placement-lattice configuration. -/
theorem nestedMomentumLeakage {L z σ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*(L⁻¹)^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (f : FieldL2) (c : ι → ℂ)
    (heq : f = (∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL))) +
      finiteWellOperator L⁻¹ r v (resolvent D hσ0 hσ f)) :
    ‖f-cutoffOperator f‖ ≤ Cs*(1+(Fintype.card ι : ℝ))*Real.exp (-cs*L^(1/3 : ℝ)) *
      (‖f‖+∑ i, ‖c i‖) := by
  classical
  let E := Real.exp (-cs*L^(1/3 : ℝ))
  let S : ℝ := ∑ i, ‖c i‖
  let J : ℝ := Fintype.card ι
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hL1 := length_ge_one hL
  have hb := finiteWell_nested_bound D hσ0 hσ (inverse_length_le_1024 hL) r v hv0 hv
    (by simpa only [inv_inv] using hdisj) f
    (∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL))) heq
    (smallRadius/2) (2*leakageStep L) (((2 : ℝ)^234*E)*S)
    (by linarith [smallRadius_pos])
    (mul_nonneg (by norm_num) (leakageStep_pos hL1).le) (by positivity)
    (fun s hs => translatedSource_sum_high hL D r c hs) (leakageDepth L)
  have he : smallRadius/2+(leakageDepth L : ℝ)*(2*leakageStep L) = smallRadius := by
    have hk := leakageStep_endpoint hL1
    nlinarith
  rw [he] at hb
  have hhigh : ‖highMomentumProjection smallRadius f‖ ≤
      E*‖f‖ + 2*((2 : ℝ)^234*E*S + ((2 : ℝ)^232*J*E)*‖f‖) := by
    apply hb.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (leakage_quarter_decay hL1) (norm_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (leakage_twice_sqrt_decay hL1) (by positivity)) (norm_nonneg _)
  have h1 : 1+(2 : ℝ)^233*J ≤ (2 : ℝ)^236*(1+J) := by nlinarith
  have h2 : (2 : ℝ)^235 ≤ (2 : ℝ)^236*(1+J) := by nlinarith
  have hCs : (2 : ℝ)^236 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  calc
    _ ≤ ‖highMomentumProjection smallRadius f‖ := cutoff_error_norm_le_high f
    _ ≤ E*‖f‖+2*((2 : ℝ)^234*E*S+((2 : ℝ)^232*J*E)*‖f‖) := hhigh
    _ = ((1+(2 : ℝ)^233*J)*‖f‖+(2 : ℝ)^235*S)*E := by ring
    _ ≤ (((2 : ℝ)^236*(1+J))*‖f‖+((2 : ℝ)^236*(1+J))*S)*E :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_right h2 hS)) hE
    _ = (2 : ℝ)^236*(1+J)*E*(‖f‖+S) := by ring
    _ ≤ Cs*(1+J)*E*(‖f‖+S) := by gcongr

#print axioms actualSource_high_half
#print axioms nestedMomentumLeakage

end Maxwell.Continuum.Auxiliary
