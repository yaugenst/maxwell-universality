import Maxwell.Continuum.CalibrationSupercellUnitary

/-! Complete Bloch-grid operator multiplication on the global supercell
Fourier space, with a uniform bound rather than a loss in the grid size. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

def blockOperator (T : Grid M → FiberSpace →L[ℂ] FiberSpace) : BlockSpace M →L[ℂ] BlockSpace M :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Grid M => FiberSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => (T j).comp (PiLp.proj 2 _ j)))

omit [NeZero M] in
theorem blockOperator_apply (T : Grid M → FiberSpace →L[ℂ] FiberSpace) (u : BlockSpace M) (j : Grid M) :
    blockOperator M T u j=T j (u j) := rfl

theorem blockOperator_bound (T : Grid M → FiberSpace →L[ℂ] FiberSpace) {B : ℝ} (hB : 0≤B)
    (hT : ∀ j, ‖T j‖≤B) (u : BlockSpace M) : ‖blockOperator M T u‖≤B*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [mul_pow,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ‖T j (u j)‖^2≤B^2*‖u j‖^2
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((T j).le_opNorm (u j) |>.trans (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg _))) 2

theorem blockOperator_norm (T : Grid M → FiberSpace →L[ℂ] FiberSpace) {B : ℝ} (hB : 0≤B)
    (hT : ∀ j, ‖T j‖≤B) : ‖blockOperator M T‖≤B :=
  ContinuousLinearMap.opNorm_le_bound _ hB (blockOperator_bound M T hB hT)

def operator (T : Grid M → FiberSpace →L[ℂ] FiberSpace) : FiberSpace →L[ℂ] FiberSpace :=
  (unitary M).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((blockOperator M T).comp (unitary M).toLinearIsometry.toContinuousLinearMap)

theorem operator_apply (T : Grid M → FiberSpace →L[ℂ] FiberSpace) (u : FiberSpace)
    (j : Grid M) (ν : Alias) : operator M T u (join M (j,ν))=T j (fiber M u j) ν := by
  change (unitary M).symm (blockOperator M T (unitary M u)) (join M (j,ν))=_
  rw [unitary_symm_apply,blockOperator_apply]
  rfl

theorem operator_norm (T : Grid M → FiberSpace →L[ℂ] FiberSpace) {B : ℝ} (hB : 0≤B)
    (hT : ∀ j, ‖T j‖≤B) : ‖operator M T‖≤B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  change ‖(unitary M).symm (blockOperator M T (unitary M u))‖≤_
  rw [LinearIsometryEquiv.norm_map]
  exact (blockOperator_bound M T hB hT _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

theorem operator_sub (T S : Grid M → FiberSpace →L[ℂ] FiberSpace) :
    operator M (fun j => T j-S j)=operator M T-operator M S := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext n
  obtain ⟨⟨j,ν⟩,rfl⟩ := (indexEquiv M).surjective n
  change operator M (fun j => T j-S j) u (join M (j,ν))=
    (operator M T u-operator M S u) (join M (j,ν))
  rw [lp.coeFn_sub]
  simp only [Pi.sub_apply,operator_apply,sub_apply,lp.coeFn_sub]

theorem operator_error (T S : Grid M → FiberSpace →L[ℂ] FiberSpace) {B : ℝ} (hB : 0≤B)
    (hT : ∀ j, ‖T j-S j‖≤B) : ‖operator M T-operator M S‖≤B := by
  rw [← operator_sub]
  exact operator_norm M _ hB hT

#print axioms operator_error

end Maxwell.Continuum.Calibration.Supercell
