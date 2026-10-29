import Maxwell.Continuum.EffectiveMassBandOperator
import Maxwell.Continuum.EffectiveMassScalingOnto
import Maxwell.Continuum.EffectiveMassQuasiExtension
import Maxwell.Continuum.VectorMultiplierAdjoint
import Maxwell.Continuum.AuxiliaryResolvent

/-! Exact selected-band packet factorization and its full-space Gram
operator. Both dilation and restriction coisometries have literal L² proofs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary Bloch BandWavePacket FreeFiber
open scoped ENNReal InnerProduct

def scaledRestriction {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] Lp ℂ 2 quasiMeasure :=
  angularToQuasiCLM.comp (scaledAngularIsometry hh).toContinuousLinearMap

theorem scaledRestriction_ae {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    scaledRestriction hh f =ᵐ[quasiMeasure]
      fun q => (amplitudeFactor h : ℂ) * f (h⁻¹ • q.val) := by
  filter_upwards [angularToQuasi_ae (scaledAngular hh f), quasi_coe_ae (scaledAngular_ae hh f)]
    with q hr hs
  exact hr.trans hs

theorem comp_gram_of_coisometry {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (T : X →L[ℂ] Y) (hT : T.comp (T†) = ContinuousLinearMap.id ℂ Y)
    (V : Y →L[ℂ] Z) : (V.comp T).comp ((V.comp T)†) = V.comp (V†) := by
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro f
  change V (T ((T†) ((V†) f))) = V ((V†) f)
  exact congrArg V (congrArg (fun A : Y →L[ℂ] Y => A ((V†) f)) hT)

theorem scaledRestriction_comp_adjoint {h : ℝ} (hh : 0 < h) :
    (scaledRestriction hh).comp ((scaledRestriction hh)†) =
      ContinuousLinearMap.id ℂ (Lp ℂ 2 quasiMeasure) := by
  rw [scaledRestriction, comp_gram_of_coisometry _ (scaledAngular_comp_adjoint hh),
    angularToQuasi_comp_adjoint]

def weightedSection {h z : ℝ} (D : Calibration h z) :
    VectorMultiplier.Data (H := FiberSpace) quasiMeasure 2 where
  coefficient q := (cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) • sectionValue q
  measurable := by
    have ha := ((cutoffBandMultiplier_measurable D).smul_measure
      (ENNReal.ofReal (scaledDensity h))).comp_measurePreserving (inverseDilation_measurePreserving D.h_pos)
    have hq := ha.restrict.comp_measurePreserving quasi_coe_measurePreserving
    exact hq.smul sectionValue_measurable
  nonneg := by norm_num
  bound q := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoffBandMultiplier_nonneg h z _)]
    exact (mul_le_mul (cutoffBandMultiplier_le_two D _) (actualSection.norm_le q)
      (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)

def packetBand {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] FieldL2 :=
  (Uh D.h_pos).comp (cutoffAmplitudeOperator D)

theorem unitary_packetBand {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    unitary (packetBand D f) = Complex.I • (weightedSection D).operator (scaledRestriction D.h_pos f) := by
  change unitary (Uh D.h_pos (cutoffAmplitudeOperator D f)) = _
  rw [Uh_unitary]
  congr 1
  apply Lp.ext
  filter_upwards [fiberEmbedding_ae (scaledAmplitude D.h_pos (cutoffAmplitudeOperator D f)),
    scaledAmplitude_ae D.h_pos (cutoffAmplitudeOperator D f),
    quasi_coe_ae (inverseDilation_ae D.h_pos (cutoffAmplitudeOperator_ae D f)),
    (weightedSection D).operator_ae (scaledRestriction D.h_pos f),
    scaledRestriction_ae D.h_pos f] with q he hs ha hp hr
  rw [he, hs, hp, hr]
  change region.indicator
      (fun q => (amplitudeFactor h : ℂ) * cutoffAmplitudeOperator D f (h⁻¹ • q.val)) q • sectionValue q =
    ((amplitudeFactor h : ℂ) * f (h⁻¹ • q.val)) •
      ((cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) • sectionValue q)
  by_cases hq : q ∈ region
  · rw [Set.indicator_of_mem hq, ha, smul_smul]
    congr 1
    ring
  · rw [Set.indicator_of_notMem hq, sectionValue_zero hq]
    simp only [smul_zero]

theorem packetBand_factorization {h z : ℝ} (D : Calibration h z) :
    packetBand D = Complex.I •
      (unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((weightedSection D).operator.comp (scaledRestriction D.h_pos))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  rw [unitary_packetBand]
  change _ = unitary (Complex.I • unitary.symm ((weightedSection D).operator (scaledRestriction D.h_pos f)))
  rw [map_smul, unitary.apply_symm_apply]


theorem phase_gram {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : X →L[ℂ] Y) :
    (Complex.I • A).comp ((Complex.I • A)†) = A.comp (A†) := by
  rw [map_smulₛₗ]
  apply ContinuousLinearMap.ext
  intro f
  change Complex.I • A ((starRingEnd ℂ Complex.I) • (A†) f) = A ((A†) f)
  rw [map_smul, smul_smul]
  have hc : Complex.I * starRingEnd ℂ Complex.I = 1 := by norm_num
  rw [hc, one_smul]

attribute [local irreducible] weightedSection packetBand Bloch.unitary

set_option maxHeartbeats 800000 in
theorem packetBand_gram {h z : ℝ} (D : Calibration h z) :
    (packetBand D).comp ((packetBand D)†) =
      physicalize ((weightedSection D).operator.comp ((weightedSection D).operator†)) := by
  rw [packetBand_factorization, phase_gram, ContinuousLinearMap.adjoint_comp,
    unitary.symm.adjoint_eq_symm]
  have hg := comp_gram_of_coisometry (scaledRestriction D.h_pos)
    (scaledRestriction_comp_adjoint D.h_pos) (weightedSection D).operator
  apply ContinuousLinearMap.ext
  intro f
  change unitary.symm ((weightedSection D).operator (scaledRestriction D.h_pos
    ((((weightedSection D).operator.comp (scaledRestriction D.h_pos))†) (unitary f)))) =
      unitary.symm ((weightedSection D).operator (((weightedSection D).operator†) (unitary f)))
  exact congrArg unitary.symm (congrArg (fun A : FiberL2 →L[ℂ] FiberL2 => A (unitary f)) hg)

theorem packetBand_gram_ae {h z : ℝ} (D : Calibration h z) (f : FieldL2) :
    unitary (packetBand D (((packetBand D)†) f)) =ᵐ[quasiMeasure]
      fun q => (inner ℂ ((weightedSection D).coefficient q) (unitary f q)) •
        (weightedSection D).coefficient q := by
  change unitary (((packetBand D).comp ((packetBand D)†)) f) =ᵐ[quasiMeasure] _
  rw [packetBand_gram, unitary_physicalize]
  exact (weightedSection D).gram_ae (unitary f)

end Maxwell.Continuum.EffectiveMass
