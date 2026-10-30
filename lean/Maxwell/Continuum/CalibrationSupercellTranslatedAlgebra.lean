import Maxwell.Continuum.CalibrationSupercellLiftAlgebra

/-! Exact passage from a translation identity on embedded well fields
to the global physical two-well operator. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge

variable (M : ℕ) [NeZero M]

theorem localized_translation_lift
    (A P : FieldL2 →L[ℂ] FieldL2) (Q F : FiberSpace →L[ℂ] FiberSpace)
    (hA : IsSelfAdjoint A) (hQ : ∀ u, A (embedding M u)=embedding M (Q u))
    (hRange : ∀ f, embedding M ((embedding M).toContinuousLinearMap.adjoint (A f))=A f)
    (hF : ∀ u, embedding M (F (Q u))=P (A (embedding M u))) (f : FieldL2) :
    F (Q ((embedding M).toContinuousLinearMap.adjoint f))=
      (embedding M).toContinuousLinearMap.adjoint (P (A f)) := by
  have he : embedding M (F (Q ((embedding M).toContinuousLinearMap.adjoint f)))=P (A f) := by
    rw [hF,hQ,← adjoint_intertwines M A Q hA hQ,hRange]
  have hh := congrArg (embedding M).toContinuousLinearMap.adjoint he
  rw [embedding_adjoint_embedding] at hh
  exact hh

theorem physicalLift_translated_sandwich
    (A P : FieldL2 →L[ℂ] FieldL2) (Q R F : FiberSpace →L[ℂ] FiberSpace)
    (hA : IsSelfAdjoint A) (hQ : ∀ u, A (embedding M u)=embedding M (Q u))
    (hRange : ∀ f, embedding M ((embedding M).toContinuousLinearMap.adjoint (A f))=A f)
    (hF : ∀ u, embedding M (F (Q u))=P (A (embedding M u))) :
    physicalLift M (Q*R*F*Q)=A*physicalLift M R*P*A := by
  apply ContinuousLinearMap.ext
  intro f
  change embedding M (Q (R (F (Q ((embedding M).toContinuousLinearMap.adjoint f)))))=
    A (embedding M (R ((embedding M).toContinuousLinearMap.adjoint (P (A f)))))
  rw [localized_translation_lift M A P Q F hA hQ hRange hF,hQ]

#print axioms physicalLift_translated_sandwich

end Maxwell.Continuum.Calibration.Supercell
