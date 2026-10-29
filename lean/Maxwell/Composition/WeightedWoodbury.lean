import Maxwell.Composition.SourceIdentity
import Maxwell.Composition.Woodbury

/-! Conversion from the weighted defect inverse to the full physical
Maxwell inverse. Only the local weighted core and background are assumed
invertible; the full physical equivalence is constructed. -/

noncomputable section

namespace Maxwell.Composition

variable {E D : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

def unweightedCoreEquiv (W M : D ≃L[ℝ] D) : D ≃L[ℝ] D :=
  W.symm.trans (M.trans W.symm)

@[simp] theorem unweightedCoreEquiv_apply (W M : D ≃L[ℝ] D) (d : D) :
    unweightedCoreEquiv W M d = W.symm (M (W.symm d)) := rfl

@[simp] theorem unweightedCoreEquiv_symm_apply (W M : D ≃L[ℝ] D) (d : D) :
    (unweightedCoreEquiv W M).symm d = W (M.symm (W d)) := rfl

theorem unweightedCoreEquiv_eq_core (K : E ≃L[ℝ] E) (V W M : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (hM : (M : D →L[ℝ] D) = weightedBirmanSchwinger K V W Q Qt) :
    (unweightedCoreEquiv W M : D →L[ℝ] D) = woodburyCore K V.symm Qt Q := by
  ext d
  have hm := congrArg (fun T : D →L[ℝ] D => T (W.symm d)) hM
  simp only [weightedBirmanSchwinger, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearEquiv.coe_apply,
    ContinuousLinearEquiv.apply_symm_apply] at hm
  change W.symm (M (W.symm d)) = V.symm d - Q (K.symm (Qt d))
  rw [hm, ContinuousLinearEquiv.symm_apply_apply]

theorem unweightedCoreEquiv_inverse_norm_le (W M : D ≃L[ℝ] D)
    (QM : ℝ) (hW : ‖(W : D →L[ℝ] D)‖ ≤ 1)
    (hM : ‖(M.symm : D →L[ℝ] D)‖ ≤ QM) :
    ‖((unweightedCoreEquiv W M).symm : D →L[ℝ] D)‖ ≤ QM := by
  have hQM : 0 ≤ QM := (norm_nonneg _).trans hM
  have hid : ((unweightedCoreEquiv W M).symm : D →L[ℝ] D) =
      (W : D →L[ℝ] D).comp ((M.symm : D →L[ℝ] D).comp (W : D →L[ℝ] D)) := by
    ext d
    rfl
  rw [hid]
  calc
    _ ≤ ‖(W : D →L[ℝ] D)‖ *
        ‖(M.symm : D →L[ℝ] D).comp (W : D →L[ℝ] D)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (QM * 1) := mul_le_mul hW
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hM hW (norm_nonneg _) hQM)) (norm_nonneg _) zero_le_one
    _ = QM := by ring

def physicalEquivOfWeighted (K : E ≃L[ℝ] E) (V W M : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (hM : (M : D →L[ℝ] D) = weightedBirmanSchwinger K V W Q Qt) : E ≃L[ℝ] E :=
  woodburyEquiv K V.symm (unweightedCoreEquiv W M) Qt Q
    (unweightedCoreEquiv_eq_core K V W M Q Qt hM)

@[simp] theorem physicalEquivOfWeighted_operator (K : E ≃L[ℝ] E)
    (V W M : D ≃L[ℝ] D) (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (hM : (M : D →L[ℝ] D) = weightedBirmanSchwinger K V W Q Qt) :
    (physicalEquivOfWeighted K V W M Q Qt hM : E →L[ℝ] E) =
      finitePhysicalOperator K V Q Qt := by
  ext y
  rfl

/-- Full physical inverse control from the weighted bright/complementary
core. The weight contraction is used twice, so no inverse weight constant
or number of defects appears in this Woodbury estimate. -/
theorem physicalEquivOfWeighted_inverse_norm_le (K : E ≃L[ℝ] E)
    (V W M : D ≃L[ℝ] D) (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (hM : (M : D →L[ℝ] D) = weightedBirmanSchwinger K V W Q Qt)
    (L QM : ℝ) (hK : ‖(K.symm : E →L[ℝ] E)‖ ≤ L)
    (hW : ‖(W : D →L[ℝ] D)‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hQt : ‖Qt‖ ≤ 1)
    (hcore : ‖(M.symm : D →L[ℝ] D)‖ ≤ QM) :
    ‖((physicalEquivOfWeighted K V W M Q Qt hM).symm : E →L[ℝ] E)‖ ≤
      L + L ^ 2 * QM := by
  exact physical_full_inverse_norm_le K V.symm (unweightedCoreEquiv W M) Qt Q
    (unweightedCoreEquiv_eq_core K V W M Q Qt hM) L QM hK hQt hQ
    (unweightedCoreEquiv_inverse_norm_le W M QM hW hcore)

end Maxwell.Composition
