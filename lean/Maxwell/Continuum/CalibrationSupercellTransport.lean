import Maxwell.Continuum.CalibrationSupercellKernel
import Maxwell.Continuum.CalibrationFinitePhysical

/-! Conjugation through the literal physical supercell isometry. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier
open scoped InnerProduct

variable (M : ℕ) [NeZero M]

theorem embedding_adjoint (f : FieldL2) :
    (embedding M).toContinuousLinearMap.adjoint f=(unitary M).symm (blockAnalysis M f) := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (blockEmbedding M (unitary M u)) f=_
  rw [blockEmbedding_pairing]
  rw [← (unitary M).inner_map_map u ((unitary M).symm (blockAnalysis M f)),
    LinearIsometryEquiv.apply_symm_apply]

theorem embedding_operator_adjoint (T : Grid M → FiberSpace →L[ℂ] FiberSpace)
    (f : FieldL2) :
    embedding M (operator M T ((embedding M).toContinuousLinearMap.adjoint f))=
      physicalOperator M T f := by
  rw [embedding_adjoint,physicalOperator_apply]
  change blockEmbedding M (unitary M ((unitary M).symm
    (blockOperator M T (unitary M ((unitary M).symm (blockAnalysis M f))))))=_
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]

theorem embedding_adjoint_embedding (u : FiberSpace) :
    (embedding M).toContinuousLinearMap.adjoint (embedding M u)=u := by
  exact congrArg (fun T : FiberSpace →L[ℂ] FiberSpace => T u) (embedding M).adjoint_comp_self

theorem physicalOperator_embedding (T : Grid M → FiberSpace →L[ℂ] FiberSpace)
    (u : FiberSpace) : physicalOperator M T (embedding M u)=embedding M (operator M T u) := by
  rw [← embedding_operator_adjoint,embedding_adjoint_embedding]

theorem physicalLift_operator (T : Grid M → FiberSpace →L[ℂ] FiberSpace) :
    physicalLift M (operator M T)=physicalOperator M T := by
  apply ContinuousLinearMap.ext
  exact embedding_operator_adjoint M T

#print axioms embedding_operator_adjoint
#print axioms physicalOperator_embedding
#print axioms physicalLift_operator

end Maxwell.Continuum.Calibration.Supercell
