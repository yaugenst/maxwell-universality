import Maxwell.Continuum.CalibrationSupercellTransport

/-! Exact adjoint and sandwich consequences of physical intertwining. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge
open scoped InnerProduct

variable (M : ℕ) [NeZero M]

theorem selfAdjoint_of_intertwines (A : FieldL2 →L[ℂ] FieldL2) (Q : FiberSpace →L[ℂ] FiberSpace)
    (hA : IsSelfAdjoint A) (h : ∀ u, A (embedding M u)=embedding M (Q u)) : IsSelfAdjoint Q := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change inner ℂ (Q u) v=inner ℂ u (Q v)
  rw [← (embedding M).inner_map_map,← (embedding M).inner_map_map u (Q v),← h,← h]
  exact hA.isSymmetric (embedding M u) (embedding M v)

theorem adjoint_intertwines (A : FieldL2 →L[ℂ] FieldL2) (Q : FiberSpace →L[ℂ] FiberSpace)
    (hA : IsSelfAdjoint A) (h : ∀ u, A (embedding M u)=embedding M (Q u)) (f : FieldL2) :
    (embedding M).toContinuousLinearMap.adjoint (A f)=
      Q ((embedding M).toContinuousLinearMap.adjoint f) := by
  have hQ := selfAdjoint_of_intertwines M A Q hA h
  have he : A.comp (embedding M).toContinuousLinearMap=
      (embedding M).toContinuousLinearMap.comp Q := by
    apply ContinuousLinearMap.ext
    exact h
  have ha := congrArg ContinuousLinearMap.adjoint he
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,hA.adjoint_eq,hQ.adjoint_eq] at ha
  exact congrArg (fun T : FieldL2 →L[ℂ] FiberSpace => T f) ha

theorem physicalLift_sandwich (A : FieldL2 →L[ℂ] FieldL2) (Q R : FiberSpace →L[ℂ] FiberSpace)
    (hA : IsSelfAdjoint A) (h : ∀ u, A (embedding M u)=embedding M (Q u)) :
    physicalLift M (Q*R*Q)=A*physicalLift M R*A := by
  apply ContinuousLinearMap.ext
  intro f
  change embedding M (Q (R (Q ((embedding M).toContinuousLinearMap.adjoint f))))=
    A (embedding M (R ((embedding M).toContinuousLinearMap.adjoint (A f))))
  rw [adjoint_intertwines M A Q hA h,h]

#print axioms physicalLift_sandwich

end Maxwell.Continuum.Calibration.Supercell
