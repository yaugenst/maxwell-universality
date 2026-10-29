import Maxwell.Continuum.EffectiveMassDiagonalKernel
import Maxwell.Continuum.EffectiveMassKernelMeasurable
import Maxwell.Continuum.AliasOperatorPairing

/-! The actual effective-mass comparison for the physical packet Gram
operator. Both kernels are derived from the operators; the off-alias
estimate consequently has no assumed kernel-identification premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

theorem boundedKernel_pairing_integrable (h : ℝ) (K : Space → Space → ℂ)
    (hK : StronglyMeasurable (fun pr : Space × Space => K pr.1 pr.2))
    (C : ℝ) (hbound : ∀ p r, ‖K p r‖ ≤ C) (f g : ScalarL2) :
    Integrable (fun pr : Space × Space => star (g pr.1) * (K pr.1 pr.2 * f pr.2))
      ((volume.restrict (aliasChart h)).prod (volume.restrict (aliasChart h))) := by
  have hf := (integrableOn_Lp_of_measure_ne_top f (by norm_num) (aliasChart_finite h)).norm
  have hg := (integrableOn_Lp_of_measure_ne_top g (by norm_num) (aliasChart_finite h)).norm
  apply ((hg.mul_prod hf).mul_const C).mono'
    ((((Lp.stronglyMeasurable g).comp_measurable measurable_fst).star).mul
      (hK.mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd))).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun pr => by
    change ‖star (g pr.1) * (K pr.1 pr.2 * f pr.2)‖ ≤ (‖g pr.1‖ * ‖f pr.2‖) * C
    rw [norm_mul, norm_mul, norm_star]
    calc
      _ = (‖g pr.1‖ * ‖f pr.2‖) * ‖K pr.1 pr.2‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem bandGram_minus_diagonal_pairing {h z : ℝ} (D : Calibration h z) (f g : ScalarL2) :
    inner ℂ g ((bandGramOperator D - diagonalBandOperator D) f) =
      ∫ p in aliasChart h, star (g p) *
        (∫ r in aliasChart h, weightedOffAliasKernel h z p r * f r) := by
  rw [sub_apply, inner_sub_right, bandGramOperator_pairing_full,
    diagonalBandOperator_pairing]
  simp_rw [← integral_const_mul]
  rw [← integral_integral_sub
    (boundedKernel_pairing_integrable h _ (weightedFullAliasKernel_stronglyMeasurable D)
      98304 (weightedFullAliasKernel_bound D) f g)
    (boundedKernel_pairing_integrable h _ (diagonalAliasKernel_stronglyMeasurable D)
      384 (diagonalAliasKernel_bound D) f g)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (aliasChart_measurable h)] with p hp
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (aliasChart_measurable h)] with r hr
  rw [weightedFullAliasKernel_split D.h_pos p r hp hr]
  ring

theorem bandGram_offAlias_error {h z : ℝ} (D : Calibration h z) :
    ‖bandGramOperator D - diagonalBandOperator D‖ ≤ (2 : ℝ)^512 * h :=
  weightedOffAlias_operator_norm_of_pairing D _ (bandGram_minus_diagonal_pairing D)

set_option maxRecDepth 2048 in
theorem bandGram_effectiveMass_error {h z : ℝ} (D : Calibration h z) :
    ‖bandGramOperator D - diagonalReferenceOperator‖ ≤ (2 : ℝ)^513 * h := by
  calc
    _ ≤ ‖bandGramOperator D - diagonalBandOperator D‖ +
      ‖diagonalBandOperator D - diagonalReferenceOperator‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 : ℝ)^512 * h + (2 : ℝ)^133 * h :=
      add_le_add (bandGram_offAlias_error D) (diagonalComparison_error D)
    _ ≤ (2 : ℝ)^513 * h := by
      have hp : (2 : ℝ)^133 ≤ (2 : ℝ)^512 := pow_le_pow_right₀ (by norm_num) (by omega)
      have hm := mul_le_mul_of_nonneg_right hp D.h_pos.le
      calc
        _ ≤ (2 : ℝ)^512 * h + (2 : ℝ)^512 * h := add_le_add le_rfl hm
        _ = (2 : ℝ)^512 * 2 * h := by rw [← mul_two, mul_right_comm ((2 : ℝ)^512) h 2]
        _ = (2 : ℝ)^513 * h := by rw [pow_succ (2 : ℝ) 512]

theorem bandGram_effectiveMass_error_paper {h z : ℝ} (D : Calibration h z) :
    ‖bandGramOperator D - diagonalReferenceOperator‖ ≤ (2 : ℝ)^520 * h :=
  (bandGram_effectiveMass_error D).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) D.h_pos.le)

#print axioms bandGram_minus_diagonal_pairing
#print axioms bandGram_effectiveMass_error

end Maxwell.Continuum.EffectiveMass
