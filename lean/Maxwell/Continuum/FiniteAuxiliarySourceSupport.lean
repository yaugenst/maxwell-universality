import Maxwell.Continuum.FiniteAuxiliaryIdealSource
import Maxwell.Continuum.FiniteAuxiliaryH1Bootstrap

/-! The solved auxiliary source and its actual weak derivatives are
supported in precisely the finite union of physical well balls. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MeasureTheory FourierSobolev

variable {ι : Type*} [Fintype ι]

theorem finiteWellOperator_supported {h : ℝ} (hh : 0 < h) (r : ι → Space) (v : ι → ℝ)
    (f : FieldL2) (k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, h⁻¹ ≤ ‖x-r i‖) → finiteWellOperator h r v f k x = 0 := by
  filter_upwards [finiteWellOperator_ae h r v f k] with x hx hdist
  have hz : finiteWellCoefficient h r v x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : Well.w (h • (x-r i)) = 0 := by
      by_contra hnot
      have hi := translatedWell_nonzero_mem_ball hh (r i) x hnot
      exact (not_lt_of_ge (hdist i)) (by simpa only [Metric.mem_ball, dist_eq_norm] using hi)
    rw [hw, mul_zero]
  rw [hx, hz, Complex.ofReal_zero, zero_mul]

theorem auxiliarySource_supported {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    {f : FieldL2} (hf : ∀ k, ∀ᵐ x ∂volume, (∀ i, h⁻¹ ≤ ‖x-r i‖) → f k x = 0) (k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, h⁻¹ ≤ ‖x-r i‖) → auxiliarySource D hσ0 hσ r A f k x = 0 := by
  rw [auxiliarySource_equation D hσ0 hσ r v hv A hA f]
  filter_upwards [hf k,
    finiteWellOperator_supported D.h_pos r v (auxiliaryField D hσ0 hσ r A f) k,
    Lp.coeFn_add (f k) (finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f) k)]
    with x hx hy hs hdist
  change (f k+finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f) k) x = 0
  rw [hs, Pi.add_apply, hx hdist, hy hdist, add_zero]

theorem auxiliarySource_derivative_supported {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    {f : FieldL2} (hf : ∀ k, ∀ᵐ x ∂volume, (∀ i, h⁻¹ ≤ ‖x-r i‖) → f k x = 0)
    (Df : H1Data (auxiliarySource D hσ0 hσ r A f)) (j k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, h⁻¹ ≤ ‖x-r i‖) → Df.derivative j k x = 0 :=
  Df.derivative_supported_balls r h⁻¹ (auxiliarySource_supported D hσ0 hσ r v hv A hA hf) j k

#print axioms auxiliarySource_derivative_supported

end Maxwell.Continuum.FiniteAuxiliary
