import Maxwell.Continuum.DerivativeCellGevrey
import Maxwell.Continuum.FullCellKernel

/-! Exact cell compression of the derivative resolvent. The Fourier
symbol has one cutoff, and the identity uses the complete Bloch transform. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier FreeFiber Auxiliary Bloch OperatorFourier MeasureTheory Set Metric
open scoped InnerProduct

local instance derivativeCellKernelRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] fullFiberResolvent derivativeCellSymbol Bloch.unitary
  Auxiliary.derivativeResolvent embedLatticeCell fiberResolvent localInverseFiber
  PeriodicMaterial.derivativeFiber

theorem cutoffDerivativeCellSymbol_apply (z σ : ℝ) (j : Fin 3) (q : QuasiCell) (f : CellFieldL2) :
    cutoffDerivativeCellSymbol z σ j q.val f = antiGauge (quasiMomentum q)
      (conjugate (derivativeResolventFiber z σ j q) (antiUngauge (quasiMomentum q) f)) := by
  rw [derivativeResolventFiber_one_cutoff]
  by_cases hq : q ∈ cutoffRegion
  · rw [localInverseFiber_eq hq]
    unfold cutoffDerivativeCellSymbol cutoffSymbol realSymbol derivativeCellSymbol
    change (cutoff q.val : ℂ) • antiGauge (quasiMomentum q)
      (conjugate (derivativeFiberSymbol z σ j (quasiMomentum q)) (antiUngauge (quasiMomentum q) f)) = _
    have he : derivativeFiberSymbol z σ j (quasiMomentum q) =
        fiberResolvent z σ (fun k => q.val k) * PeriodicMaterial.derivativeFiber j *
          fiberResolvent z σ (fun k => q.val k) := by
      unfold derivativeFiberSymbol
      change (fullFiberResolvent z σ (realMomentum (fun k => q.val k))).comp
        ((PeriodicMaterial.derivativeFiber j).comp
          (fullFiberResolvent z σ (realMomentum (fun k => q.val k)))) = _
      rw [fullFiberResolvent_real]
      apply ContinuousLinearMap.ext
      intro u
      rfl
    rw [he, map_smul, smul_apply, map_smul]
  · rw [cutoff_eq_zero_outside hq, Complex.ofReal_zero]
    have hz : (0 : ℂ) •
        (localInverseFiber z σ q * PeriodicMaterial.derivativeFiber j * localInverseFiber z σ q) =
        (0 : FiberAnalytic.FiberMap) := by
      apply ContinuousLinearMap.ext
      intro u
      change (0 : ℂ) •
        ((localInverseFiber z σ q * PeriodicMaterial.derivativeFiber j * localInverseFiber z σ q) u) =
        (0 : FreeFiber.FiberSpace)
      exact zero_smul ℂ _
    rw [hz, map_zero, zero_apply, map_zero]
    unfold cutoffDerivativeCellSymbol cutoffSymbol
    rw [cutoff_eq_zero_outside hq, Complex.ofReal_zero]
    exact congrArg (fun T : CellMap => T f) (zero_smul ℂ (realSymbol (derivativeCellSymbol z σ j) q.val))

theorem cutoffDerivativeCellSymbol_pairing (z σ : ℝ) (j : Fin 3) (q : QuasiCell) (g f : CellFieldL2) :
    inner ℂ (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) g))
      (derivativeResolventFiber z σ j q (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) f))) =
      inner ℂ g (cutoffDerivativeCellSymbol z σ j q.val f) := by
  rw [cutoffDerivativeCellSymbol_apply]
  exact gauged_inner (fun k => q.val k) (derivativeResolventFiber z σ j q) g f

theorem derivativeResolvent_cell_pairing {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (j : Fin 3) (a b : Bloch.Alias) (g f : CellFieldL2) :
    inner ℂ (embedLatticeCell a g) (derivativeResolvent D hσ0 hσ j (embedLatticeCell b f)) =
      (64 : ℂ) * ∫ q : QuasiCell, (star (latticePhase a q) * latticePhase b q) *
        inner ℂ g (cutoffDerivativeCellSymbol z σ j q.val f) ∂quasiMeasure := by
  rw [← unitary_inner, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [unitary_embedLatticeCell a g, unitary_embedLatticeCell b f,
    derivativeResolvent_ae D hσ0 hσ j (embedLatticeCell b f)] with q hg hf hR
  rw [hg, hR, hf, map_smul, inner_smul_left, inner_smul_right, cutoffDerivativeCellSymbol_pairing]
  simp only [map_mul, map_ofNat, starRingEnd_apply]
  ring

theorem cutoffDerivativeCellSymbol_integrable {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (j : Fin 3) :
    Integrable (cutoffDerivativeCellSymbol z σ j) :=
  (cutoffDerivativeCellSymbol_contDiff D hh hσ0 hσ j).continuous.integrable_of_hasCompactSupport
    (cutoffSymbol_compact (derivativeCellSymbol z σ j))

theorem cutoffDerivativeCellSymbol_zero_outside (z σ : ℝ) (j : Fin 3) {q : Space} (hq : q ∉ quasiCell) :
    cutoffDerivativeCellSymbol z σ j q = 0 := by
  unfold cutoffDerivativeCellSymbol cutoffSymbol
  rw [cutoff_zero_outside_quasi hq, Complex.ofReal_zero]
  exact zero_smul ℂ (realSymbol (derivativeCellSymbol z σ j) q)

theorem derivativeResolvent_fourier_pairing {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a b : Bloch.Alias) (g f : CellFieldL2) :
    inner ℂ (embedLatticeCell a g) (derivativeResolvent D hσ0 hσ j (embedLatticeCell b f)) =
      ((64 * blochDensity : ℝ) : ℂ) * carrier (latticeShift a - latticeShift b) *
        inner ℂ g (angularFourier (cutoffDerivativeCellSymbol z σ j) (latticeShift b - latticeShift a) f) := by
  rw [derivativeResolvent_cell_pairing D hσ0 hσ]
  simp_rw [latticePhase_ratio]
  have he : (∫ q : QuasiCell, (carrier (latticeShift a - latticeShift b) *
      Complex.exp ((-inner ℝ q.val (latticeShift b - latticeShift a) : ℝ) * Complex.I)) *
        inner ℂ g (cutoffDerivativeCellSymbol z σ j q.val f) ∂quasiMeasure) =
      carrier (latticeShift a - latticeShift b) *
        ∫ q : QuasiCell, angularPhase q.val (latticeShift b - latticeShift a) *
          inner ℂ g (cutoffDerivativeCellSymbol z σ j q.val f) ∂quasiMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by unfold angularPhase; ring
  have hz (q : Space) (hq : q ∉ quasiCell) :
      angularPhase q (latticeShift b - latticeShift a) *
        inner ℂ g (cutoffDerivativeCellSymbol z σ j q f) = 0 := by
    rw [cutoffDerivativeCellSymbol_zero_outside z σ j hq, zero_apply, inner_zero_right, mul_zero]
  have hqi := quasi_integral_supported
    (fun q : Space => angularPhase q (latticeShift b - latticeShift a) *
      inner ℂ g (cutoffDerivativeCellSymbol z σ j q f)) hz
  rw [he, hqi, ← angularFourier_pairing (cutoffDerivativeCellSymbol z σ j)
    (cutoffDerivativeCellSymbol_integrable D hh hσ0 hσ j)]
  change (64 : ℂ) * (carrier (latticeShift a - latticeShift b) *
    ((blochDensity : ℂ) * inner ℂ g
      (angularFourier (cutoffDerivativeCellSymbol z σ j) (latticeShift b - latticeShift a) f))) = _
  push_cast
  ring

def derivativeResolventCellBlock {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (j : Fin 3) (a b : Bloch.Alias) : CellMap :=
  ((embedLatticeCell a)†).comp ((derivativeResolvent D hσ0 hσ j).comp (embedLatticeCell b))

theorem derivativeResolventCellBlock_eq {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a b : Bloch.Alias) :
    derivativeResolventCellBlock D hσ0 hσ j a b =
      (((64 * blochDensity : ℝ) : ℂ) * carrier (latticeShift a - latticeShift b)) •
        angularFourier (cutoffDerivativeCellSymbol z σ j) (latticeShift b - latticeShift a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (((embedLatticeCell a)†) (derivativeResolvent D hσ0 hσ j (embedLatticeCell b f))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, derivativeResolvent_fourier_pairing D hh hσ0 hσ,
    smul_apply, inner_smul_right]

def derivativeResolventSpatialBlock {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (j : Fin 3) (a b : Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  (cellProjection a).comp ((derivativeResolvent D hσ0 hσ j).comp (cellProjection b))

theorem derivativeResolventSpatialBlock_norm_le_kernel {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a b : Bloch.Alias) :
    ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤
      64 * ‖angularFourier (cutoffDerivativeCellSymbol z σ j) (latticeShift b - latticeShift a)‖ := by
  have hb := spatialBlock_norm_le (derivativeResolvent D hσ0 hσ j) a b
  change ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤
    ‖derivativeResolventCellBlock D hσ0 hσ j a b‖ at hb
  apply hb.trans
  rw [derivativeResolventCellBlock_eq D hh, norm_smul, norm_mul, carrier_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [blochDensity_le_one]

#print axioms derivativeResolventCellBlock_eq
#print axioms derivativeResolventSpatialBlock_norm_le_kernel

end Maxwell.Continuum.CellGauge
