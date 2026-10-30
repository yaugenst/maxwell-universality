import Maxwell.Continuum.FiniteAuxiliaryCollection
import Maxwell.SchurBound

/-! Finite block operators with infinite-dimensional Hilbert blocks.
The scalar Schur estimate controls the full operator with no local
dimension or site-count loss. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

variable {ι : Type*} [Fintype ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def blockOperator (A : ι → ι → H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j, (A i j).comp (PiLp.proj 2 (fun _ : ι => H) j))

theorem blockOperator_apply (A : ι → ι → H →L[ℂ] H)
    (f : PiLp 2 (fun _ : ι => H)) (i : ι) :
    blockOperator A f i = ∑ j, A i j (f j) := by
  change (∑ j, (A i j).comp (PiLp.proj 2 (fun _ : ι => H) j)) f = _
  simp only [sum_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]

theorem blockOperator_norm_le (A : ι → ι → H →L[ℂ] H)
    {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ R) :
    ‖blockOperator A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg f))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  have hp (i : ι) : ‖blockOperator A f i‖ ≤ ∑ j, ‖A i j‖*‖f j‖ := by
    rw [blockOperator_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (A i j).le_opNorm (f j))
  calc
    _ ≤ ∑ i, (∑ j, ‖A i j‖*‖f j‖)^2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hp i) 2
    _ ≤ _ := Maxwell.matrix_schur_square_bound (fun i j => ‖A i j‖) R hR
      (by simpa only [abs_norm] using hrow) (by simpa only [abs_norm] using hcol) (fun j => ‖f j‖)

def diagonalBlocks (A : ι → H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (A i).comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [Fintype ι] in
@[simp] theorem diagonalBlocks_apply (A : ι → H →L[ℂ] H)
    (f : PiLp 2 (fun _ : ι => H)) (i : ι) : diagonalBlocks A f i = A i (f i) := rfl

theorem diagonalBlocks_norm_le (A : ι → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ i, ‖A i‖ ≤ R) : ‖diagonalBlocks A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg f))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((A i).le_of_opNorm_le (hA i) (f i)) 2

#print axioms blockOperator_norm_le

end Maxwell.Continuum.FiniteAuxiliary
