import Maxwell.Continuum.EffectiveMassDiagonalWave
import Maxwell.Continuum.EffectiveMassAliasSplit

/-! The exact diagonal-alias weak kernel of the actual angular-Fourier
conjugate of the well. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Auxiliary
open scoped InnerProduct

attribute [local irreducible] vectorMultiplier bandVectorOperator diagonalWave

set_option maxRecDepth 2048 in
theorem diagonalBandOperator_pairing_wave {h z : ℝ} (D : Calibration h z) (f g : ScalarL2) :
    inner ℂ g (diagonalBandOperator D f) = (fourierNormalization : ℂ)^2 *
      ∫ p, star (chartAmplitude h g p) * (∫ r, chartAmplitude h f r *
        (∫ x, (Well.w x : ℂ) * inner ℂ (diagonalWave h z x p) (diagonalWave h z x r))) := by
  change inner ℂ g (((bandVectorOperator D)†)
    (angularWellConvolution FiberSpace (bandVectorOperator D f))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, angularWellConvolution_apply]
  rw [← (angularFourier FiberSpace).symm.inner_map_map (bandVectorOperator D g)
    (angularFourier FiberSpace (physicalWellMultiplier FiberSpace
      ((angularFourier FiberSpace).symm (bandVectorOperator D f)))),
    LinearIsometryEquiv.symm_apply_apply, L2.inner_def]
  have he : (fun x => inner ℂ
      ((angularFourier FiberSpace).symm (bandVectorOperator D g) x)
      (physicalWellMultiplier FiberSpace ((angularFourier FiberSpace).symm (bandVectorOperator D f)) x))
      =ᵐ[volume] fun x => (fourierNormalization : ℂ)^2 * ((Well.w x : ℂ) * inner ℂ
        (∫ p, chartAmplitude h g p • diagonalWave h z x p)
        (∫ r, chartAmplitude h f r • diagonalWave h z x r)) := by
    filter_upwards [inverse_bandVectorOperator D g, inverse_bandVectorOperator D f,
      physicalWellMultiplier_ae FiberSpace ((angularFourier FiberSpace).symm (bandVectorOperator D f))]
      with x hg hf hw
    rw [hw, hg, hf, inner_smul_right, inner_smul_left, inner_smul_right]
    have hstar (a : ℝ) : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
    simp only [hstar, fourierNormalization]
    ring
  rw [integral_congr_ae he, integral_const_mul]
  congr 1
  exact bounded_hilbert_wave_gram (H := FiberSpace)
    (fun xp : Space × Space => diagonalWave h z xp.1 xp.2)
    (diagonalWave_stronglyMeasurable D) 4 (by norm_num) (fun x p => diagonalWave_norm D x p)
    (fun x => (Well.w x : ℂ)) Well.w_integrable.ofReal
    (Complex.continuous_ofReal.comp Well.w_contDiff.continuous).stronglyMeasurable
    (chartAmplitude h g) (chartAmplitude h f) (chartAmplitude_integrable h g)
    (chartAmplitude_integrable h f) (chartAmplitude_stronglyMeasurable h g)
    (chartAmplitude_stronglyMeasurable h f)

theorem diagonalWave_gram (h z : ℝ) (p r : Space) :
    (∫ x, (Well.w x : ℂ) * inner ℂ (diagonalWave h z x p) (diagonalWave h z x r)) =
      inner ℂ (vectorMultiplier h z p) (vectorMultiplier h z r) *
        Well.rawPhysicalFourier Well.w (p-r) := by
  have hw (x : Space) : inner ℂ (diagonalWave h z x p) (diagonalWave h z x r) =
      inner ℂ (vectorMultiplier h z p) (vectorMultiplier h z r) * angularPhase (-(p-r)) x := by
    rw [diagonalWave, diagonalWave, inner_smul_left, inner_smul_right]
    change star (angularPhase p x) *
      (angularPhase r x * inner ℂ (vectorMultiplier h z p) (vectorMultiplier h z r)) = _
    rw [angularPhase_star, ← mul_assoc, ← angularPhase_add,
      show -p + r = -(p-r) by abel]
    exact mul_comm _ _
  simp_rw [hw]
  rw [rawPhysicalFourier_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem normalized_diagonalWave_gram (h z : ℝ) (p r : Space) :
    (fourierNormalization : ℂ)^2 *
      (∫ x, (Well.w x : ℂ) * inner ℂ (diagonalWave h z x p) (diagonalWave h z x r)) =
      diagonalAliasKernel h z p r := by
  rw [diagonalWave_gram]
  simp only [diagonalAliasKernel, vectorMultiplier, inner_smul_left, inner_smul_right,
    Well.physicalFourier, Complex.real_smul]
  have hstar (a : ℝ) : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  simp only [hstar, fourierNormalization]
  ring

theorem diagonalBandOperator_pairing {h z : ℝ} (D : Calibration h z) (f g : ScalarL2) :
    inner ℂ g (diagonalBandOperator D f) =
      ∫ p in aliasChart h, star (g p) *
        (∫ r in aliasChart h, diagonalAliasKernel h z p r * f r) := by
  rw [diagonalBandOperator_pairing_wave, ← integral_const_mul,
    ← integral_indicator (aliasChart_measurable h)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    by_cases hp : p ∈ aliasChart h
    · rw [Set.indicator_of_mem hp, chartAmplitude, Set.indicator_of_mem hp,
        ← integral_indicator (aliasChart_measurable h), ← integral_const_mul,
        ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r => by
        dsimp only
        by_cases hr : r ∈ aliasChart h
        · rw [chartAmplitude, Set.indicator_of_mem hr, Set.indicator_of_mem hr]
          have he := normalized_diagonalWave_gram h z p r
          calc
            _ = star (g p) * f r * ((fourierNormalization : ℂ)^2 *
              ∫ x, (Well.w x : ℂ) * inner ℂ (diagonalWave h z x p) (diagonalWave h z x r)) := by ring
            _ = _ := by rw [he]; ring
        · rw [chartAmplitude, Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
          ring
    · rw [chartAmplitude, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      simp only [star_zero, zero_mul, mul_zero]

#print axioms diagonalBandOperator_pairing

end Maxwell.Continuum.EffectiveMass
