import Maxwell.Certificate.GenericPoint.Corrector

namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.YeeTaylor
noncomputable section
variable (D : GenericPoint.Data)

def effectiveCoefficient (hgap : D.ComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (D.exactIsometry hgap).toContinuousLinearMap.adjoint.comp
      ((D.taylorCoefficient q 2).comp (D.exactIsometry hgap).toContinuousLinearMap)-
    (D.exactIsometry hgap).toContinuousLinearMap.adjoint.comp
      ((D.taylorCoefficient q 1).comp (D.corrector hgap q))

def savedEffectiveCoefficient (q : PeriodicYee.Momentum)
    (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  D.referenceMap.adjoint.comp ((D.taylorCoefficient q 2).comp D.referenceMap)-
    D.referenceMap.adjoint.comp ((D.taylorCoefficient q 1).comp savedY)

theorem referenceMap_norm_le (hgap : D.ComplementGap) : ‖D.referenceMap‖ ≤ 2 := by
  have he := D.exactIsometry_close hgap
  have hn := (D.exactIsometry hgap).norm_toContinuousLinearMap_le
  have ht := norm_le_norm_add_norm_sub (D.exactIsometry hgap).toContinuousLinearMap D.referenceMap
  have hg := D.gram_small
  linarith

theorem taylorCoefficient_second_norm (q : PeriodicYee.Momentum) :
    ‖D.taylorCoefficient q 2‖ ≤ (7/25:ℝ)*radius q^2 := by
  have h := shiftedOperatorCoefficient_norm_le Concrete.material
    (PrimitiveYee.timeReversalMomentum D.k) q D.energy 2 (by omega)
  have hc : taylorCoefficientMajorant 2 ≤ (7/25:ℝ) := by norm_num [taylorCoefficientMajorant]
  exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

/-- The exact quadratic transfer loss, retaining the frame and corrector
error parameters needed by the different canonical L-point witnesses. -/
theorem effectiveCoefficient_saved_error (hgap : D.ComplementGap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space)
    (η : ℝ)
    (hY : ‖D.corrector hgap q‖ ≤ 3*radius q)
    (hdiff : ‖D.corrector hgap q-savedY‖ ≤ η*radius q) :
    ‖D.effectiveCoefficient hgap q-D.savedEffectiveCoefficient q savedY‖ ≤
      ((16*D.gramRadius)*(186/25)+(22/5)*η)*radius q^2 := by
  have h := JetTransfer.effective_quadratic_error (D.taylorCoefficient q 1)
    (D.taylorCoefficient q 2) (D.exactIsometry hgap).toContinuousLinearMap D.referenceMap
    (D.corrector hgap q) savedY
  have hΦ := (D.exactIsometry hgap).norm_toContinuousLinearMap_le
  have hU := D.referenceMap_norm_le hgap
  have hframe := D.exactIsometry_close hgap
  have hfirst := D.taylorCoefficient_first_norm q
  have hsecond := D.taylorCoefficient_second_norm q
  have hr := radius_nonneg q
  have hε := D.gram_nonneg
  change ‖D.effectiveCoefficient hgap q-D.savedEffectiveCoefficient q savedY‖ ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ (16*D.gramRadius)*((7/25)*radius q^2)*(1+2)+
        ((16*D.gramRadius)*((11/5)*radius q)*(3*radius q)+
          2*((11/5)*radius q)*(η*radius q)) := by
      gcongr
    _ = _ := by ring

end
end Maxwell.Certificate.GenericPoint.Data
