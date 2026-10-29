import Maxwell.Certificate.GenericPoint.JetBounds
import Maxwell.Certificate.OtherPointBudgets
import Maxwell.Spectral.YeeLocal

namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.YeeTaylor
noncomputable section
variable (D : GenericPoint.Data)

/-- The common checked budget also covers the two more accurate point
witnesses; no per-point analytic construction is duplicated. -/
theorem other_corrector_budget
    (hρ : D.residualRadius ≤ OtherPointBudgets.residualRadius)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (hg : OtherPointBudgets.spectralGap ≤ D.gap) :
    ((1/10^11:ℝ)+D.residualRadius*(2909/1000)+(11/5)*(16*D.gramRadius))/D.energyGap ≤
      OtherPointBudgets.correctorError := by
  apply (div_le_iff₀ D.energyGap_pos).mpr
  have he : OtherPointBudgets.energyGap ≤ D.energyGap := by
    dsimp [energyGap,OtherPointBudgets.energyGap]
    linarith
  have hn : (1/10^11:ℝ)+D.residualRadius*(2909/1000)+(11/5)*(16*D.gramRadius) ≤
      (1/10^11:ℝ)+OtherPointBudgets.residualRadius*(2909/1000)+(11/5)*OtherPointBudgets.frameError := by
    rw [← OtherPointBudgets.frame_error_eq]
    gcongr
  have hb := (div_le_iff₀ OtherPointBudgets.energyGap_pos).mp OtherPointBudgets.corrector_error_budget
  exact hn.trans (hb.trans (mul_le_mul_of_nonneg_left he (by norm_num [OtherPointBudgets.correctorError])))

theorem corrector_saved_close (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j)=σ • D.vector j)
    (hρ : D.residualRadius ≤ OtherPointBudgets.residualRadius)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (hg : OtherPointBudgets.spectralGap ≤ D.gap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (hY : HasParity D.inversion (-σ) savedY)
    (hnorm : ‖savedY‖ ≤ (2909/1000:ℝ)*radius q)
    (hres : ‖D.savedCorrectorResidual q savedY‖ ≤ (1/10^11:ℝ)*radius q) :
    ‖D.corrector hgap q-savedY‖ ≤ OtherPointBudgets.correctorError*radius q :=
  D.corrector_error_of_saved_bounds hgap σ hσ hv q savedY hY _ _ _ hnorm hres
    (D.other_corrector_budget hρ hε hg)

theorem corrector_norm_le (hgap : D.ComplementGap) (q : PeriodicYee.Momentum)
    (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (hnorm : ‖savedY‖ ≤ (2909/1000:ℝ)*radius q)
    (herror : ‖D.corrector hgap q-savedY‖ ≤ OtherPointBudgets.correctorError*radius q) :
    ‖D.corrector hgap q‖ ≤ 3*radius q :=
  (D.corrector_norm_of_saved_error hgap q savedY _ _ hnorm herror).trans
    (mul_le_mul_of_nonneg_right OtherPointBudgets.corrector_norm_budget (radius_nonneg q))

theorem effectiveCoefficient_saved_error_other (hgap : D.ComplementGap)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (hY : ‖D.corrector hgap q‖ ≤ 3*radius q)
    (herror : ‖D.corrector hgap q-savedY‖ ≤ OtherPointBudgets.correctorError*radius q) :
    ‖D.effectiveCoefficient hgap q-D.savedEffectiveCoefficient q savedY‖ ≤ (1/10^6:ℝ)*radius q^2 := by
  apply (D.effectiveCoefficient_saved_error hgap q savedY _ hY herror).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ OtherPointBudgets.frameError*(186/25)+(22/5)*OtherPointBudgets.correctorError := by
      rw [← OtherPointBudgets.frame_error_eq]
      gcongr
    _ ≤ _ := by
      convert OtherPointBudgets.effective_coefficient_error_budget using 1
      ring

def savedQuadraticResidual (q : PeriodicYee.Momentum)
    (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space) : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space :=
  (D.taylorCoefficient q 2).comp D.referenceMap-(D.taylorCoefficient q 1).comp savedY

theorem quadraticResidual_saved_error_other (hgap : D.ComplementGap)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (herror : ‖D.corrector hgap q-savedY‖ ≤ OtherPointBudgets.correctorError*radius q) :
    ‖residualTaylorTerm (D.taylorCoefficient q) (D.exactIsometry hgap).toContinuousLinearMap
        (D.corrector hgap q) 1-D.savedQuadraticResidual q savedY‖ ≤ (1/10^6:ℝ)*radius q^2 := by
  have h := JetTransfer.residual_error (D.taylorCoefficient q 1) (D.taylorCoefficient q 2)
    (D.exactIsometry hgap).toContinuousLinearMap D.referenceMap (D.corrector hgap q) savedY
  have hf := D.exactIsometry_close hgap
  have h1 := D.taylorCoefficient_first_norm q
  have h2 := D.taylorCoefficient_second_norm q
  have he : ‖(D.exactIsometry hgap).toContinuousLinearMap-D.referenceMap‖ ≤
      OtherPointBudgets.frameError := by
    apply hf.trans
    rw [← OtherPointBudgets.frame_error_eq]
    gcongr
  have hr := radius_nonneg q
  change ‖residualTaylorTerm (D.taylorCoefficient q) (D.exactIsometry hgap).toContinuousLinearMap
        (D.corrector hgap q) 1-D.savedQuadraticResidual q savedY‖ ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ ((7/25)*radius q^2)*OtherPointBudgets.frameError+
        ((11/5)*radius q)*(OtherPointBudgets.correctorError*radius q) := by
      gcongr
    _ = ((7/25)*OtherPointBudgets.frameError+(11/5)*OtherPointBudgets.correctorError)*radius q^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right OtherPointBudgets.quadratic_residual_error_budget (sq_nonneg _)

end
end Maxwell.Certificate.GenericPoint.Data
