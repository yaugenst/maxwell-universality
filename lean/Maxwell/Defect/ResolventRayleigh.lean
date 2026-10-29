import Maxwell.Spectral.ClusterInverse
import Maxwell.Spectral.SeparatedInverse
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! The lower Rayleigh bound of the actual finite selfadjoint resolvent,
derived from its spectral coordinates rather than assumed as an estimate. -/
namespace Maxwell.Defect

open InnerProductSpace Module.End
open scoped Ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

noncomputable def finiteResolvent (H : E →L[ℂ] E) (z : ℝ) : E →L[ℂ] E :=
  Ring.inverse (H - (z : ℂ) • 1)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem shifted_isUnit_of_not_mem_spectrum (H : E →L[ℂ] E) (z : ℝ)
    (hz : (z : ℂ) ∉ spectrum ℂ H) : IsUnit (H - (z : ℂ) • 1) := by
  have hh := (spectrum.notMem_iff.mp hz).neg
  simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using hh

theorem selfadjoint_eigenvalue_mem_spectrum (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) (i : Fin (Module.finrank ℂ E)) :
    (hH.eigenvalues rfl i : ℂ) ∈ spectrum ℂ H := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (hH.hasEigenvalue_eigenvalues rfl i).mem_spectrum

/-- The actual inverse acts diagonally in the operator's eigenbasis. -/
theorem finiteResolvent_repr (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    (z : ℝ) (hz : (z : ℂ) ∉ spectrum ℂ H) (v : E) (i : Fin (Module.finrank ℂ E)) :
    (hH.eigenvectorBasis rfl).repr (finiteResolvent H z v) i =
      (((hH.eigenvalues rfl i - z)⁻¹ : ℝ) : ℂ) * (hH.eigenvectorBasis rfl).repr v i := by
  let b := hH.eigenvectorBasis rfl
  have hi := shifted_isUnit_of_not_mem_spectrum H z hz
  have heq : (H - (z : ℂ) • 1) (finiteResolvent H z v) = v := by
    have hh := congrArg (fun A : E →L[ℂ] E => A v) (Ring.mul_inverse_cancel _ hi)
    exact hh
  have hcoord := congrArg (fun x : E => b.repr x i) heq
  change b.repr (H (finiteResolvent H z v) - (z : ℂ) • finiteResolvent H z v) i = b.repr v i at hcoord
  simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hcoord
  rw [show b.repr (H (finiteResolvent H z v)) i =
      (hH.eigenvalues rfl i : ℂ) * b.repr (finiteResolvent H z v) i from
    hH.eigenvectorBasis_apply_self_apply rfl _ i, ← sub_mul] at hcoord
  have hn : (hH.eigenvalues rfl i : ℂ) - (z : ℂ) ≠ 0 := by
    intro hh
    exact hz (sub_eq_zero.mp hh ▸ selfadjoint_eigenvalue_mem_spectrum H hH i)
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  apply mul_left_cancel₀ hn
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  exact hcoord

theorem finiteResolvent_quadratic (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    (z : ℝ) (hz : (z : ℂ) ∉ spectrum ℂ H) (v : E) :
    (inner ℂ v (finiteResolvent H z v)).re =
      ∑ i, (hH.eigenvalues rfl i - z)⁻¹ * ‖(hH.eigenvectorBasis rfl).repr v i‖ ^ 2 :=
  Spectral.diagonal_quadratic_form (hH.eigenvectorBasis rfl)
    (fun i => (hH.eigenvalues rfl i - z)⁻¹) (finiteResolvent_repr H hH z hz) v

/-- The spectrum below the evaluation point lies at distance at least
`g`; contributions above it are nonnegative. -/
theorem finiteResolvent_lower (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    (z g : ℝ) (hg : 0 < g) (hz : (z : ℂ) ∉ spectrum ℂ H)
    (hgap : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ H → t ≤ z - g ∨ z ≤ t) (v : E) :
    -(‖v‖ ^ 2 / g) ≤ (inner ℂ v (finiteResolvent H z v)).re := by
  have hcoeff (i : Fin (Module.finrank ℂ E)) :
      -g⁻¹ ≤ (hH.eigenvalues rfl i - z)⁻¹ := by
    rcases hgap _ (selfadjoint_eigenvalue_mem_spectrum H hH i) with hlo | hhi
    · have hinv : (z - hH.eigenvalues rfl i)⁻¹ ≤ g⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hg (by linarith : g ≤ z - hH.eigenvalues rfl i)
      have hneg : hH.eigenvalues rfl i - z = -(z - hH.eigenvalues rfl i) := by ring
      simpa only [hneg, inv_neg] using neg_le_neg hinv
    · exact (neg_nonpos.mpr (inv_nonneg.mpr hg.le)).trans (inv_nonneg.mpr (sub_nonneg.mpr hhi))
  rw [finiteResolvent_quadratic H hH z hz]
  have hn : ∑ i, ‖(hH.eigenvectorBasis rfl).repr v i‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using (hH.eigenvectorBasis rfl).sum_sq_norm_inner_right v
  calc
    -(‖v‖ ^ 2 / g) = ∑ i, -g⁻¹ * ‖(hH.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
      rw [← Finset.mul_sum, hn]
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcoeff i) (sq_nonneg _)

omit [FiniteDimensional ℂ E] in
theorem finiteResolvent_isSymmetric (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) (z : ℝ) :
    (finiteResolvent H z).toLinearMap.IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  have hA : IsSelfAdjoint (H - (z : ℂ) • 1) := by
    apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hH).sub
    simp only [IsSelfAdjoint, star_smul, star_one, RCLike.star_def, Complex.conj_ofReal]
  exact hA.ringInverse

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem finiteResolvent_eigenvector (H : E →L[ℂ] E) (z lam : ℝ)
    (hz : (z : ℂ) ∉ spectrum ℂ H) (hlam : z < lam) (φ : E)
    (hφ : H φ = (lam : ℂ) • φ) :
    finiteResolvent H z φ = (((lam - z)⁻¹ : ℝ) : ℂ) • φ := by
  have hi := shifted_isUnit_of_not_mem_spectrum H z hz
  have heq : finiteResolvent H z ((H - (z : ℂ) • 1) φ) = φ := by
    exact congrArg (fun A : E →L[ℂ] E => A φ) (Ring.inverse_mul_cancel _ hi)
  have hshift : (H - (z : ℂ) • 1) φ = ((lam - z : ℝ) : ℂ) • φ := by
    change H φ - (z : ℂ) • φ = _
    rw [hφ, Complex.ofReal_sub, sub_smul]
  rw [hshift, map_smul] at heq
  have hn : ((lam - z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hlam).ne'
  calc
    finiteResolvent H z φ = (((lam - z)⁻¹ : ℝ) : ℂ) •
        (((lam - z : ℝ) : ℂ) • finiteResolvent H z φ) := by
      rw [smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hn, one_smul]
    _ = _ := congrArg (fun x : E => (((lam - z)⁻¹ : ℝ) : ℂ) • x) heq

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- Orthogonal splitting of the quadratic form at one normalized eigenvector. -/
theorem eigenvector_quadratic_split (R : E →L[ℂ] E)
    (hR : R.toLinearMap.IsSymmetric) (φ : E) (hunit : ‖φ‖ = 1)
    (a : ℝ) (heig : R φ = (a : ℂ) • φ) (v : E) :
    let y := v - (inner ℂ φ v) • φ
    (inner ℂ v (R v)).re = a * ‖inner ℂ φ v‖ ^ 2 + (inner ℂ y (R y)).re ∧
      ‖y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let α := inner ℂ φ v
  let y := v - α • φ
  have hφφ : inner ℂ φ φ = 1 := by simp [inner_self_eq_norm_sq_to_K, hunit]
  have horth : inner ℂ φ y = 0 := by
    dsimp only [y]
    rw [inner_sub_right, inner_smul_right, hφφ, mul_one]
    exact sub_self _
  have hyφ : inner ℂ y φ = 0 := by rw [← inner_conj_symm, horth, map_zero]
  have hφRy : inner ℂ φ (R y) = 0 := by
    have hh := hR φ y
    change inner ℂ (R φ) y = inner ℂ φ (R y) at hh
    rw [← hh]
    rw [heig, inner_smul_left, horth, mul_zero]
  have hsum : α • φ + y = v := by dsimp [y]; abel
  have hcross : inner ℂ (α • φ) y = 0 := by rw [inner_smul_left, horth, mul_zero]
  constructor
  · change (inner ℂ v (R v)).re = a * ‖α‖ ^ 2 + (inner ℂ y (R y)).re
    conv_lhs => rw [← hsum]
    simp only [map_add, map_smul, heig, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hφφ, hyφ, hφRy, mul_zero, add_zero,
      zero_add, mul_one]
    have hh : α * ((a : ℂ) * starRingEnd ℂ α) = (a : ℂ) * (‖α‖ ^ 2 : ℝ) := by
      calc
        _ = (a : ℂ) * (α * starRingEnd ℂ α) := by ring
        _ = _ := by rw [Complex.mul_conj', Complex.ofReal_pow]
    rw [hh]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  · change ‖y‖ ^ 2 ≤ ‖v‖ ^ 2
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (α • φ) y hcross
    rw [hsum] at hpyth
    nlinarith [sq_nonneg ‖α • φ‖]

/-- A selected upper eigenvector contributes its full positive pole; all
remaining spectral contributions cost at most the lower gap bound. -/
theorem finiteResolvent_selected_lower (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) (z g lam : ℝ) (hg : 0 < g)
    (hz : (z : ℂ) ∉ spectrum ℂ H)
    (hgap : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ H → t ≤ z - g ∨ z ≤ t)
    (hlam : z < lam) (φ : E) (hunit : ‖φ‖ = 1)
    (heig : H φ = (lam : ℂ) • φ) (v : E) :
    ‖inner ℂ φ v‖ ^ 2 / (lam - z) - ‖v‖ ^ 2 / g ≤
      (inner ℂ v (finiteResolvent H z v)).re := by
  let y := v - (inner ℂ φ v) • φ
  obtain ⟨hsplit, hnorm⟩ := eigenvector_quadratic_split (finiteResolvent H z)
    (finiteResolvent_isSymmetric H hH z) φ hunit (lam - z)⁻¹
    (finiteResolvent_eigenvector H z lam hz hlam φ heig) v
  have hlo := finiteResolvent_lower H hH z g hg hz hgap y
  have hdiv := div_le_div_of_nonneg_right hnorm hg.le
  change (inner ℂ v (finiteResolvent H z v)).re =
    (lam - z)⁻¹ * ‖inner ℂ φ v‖ ^ 2 + (inner ℂ y (finiteResolvent H z y)).re at hsplit
  rw [hsplit, div_eq_mul_inv]
  nlinarith

/-- The same bound in the continuous-linear-map inverse notation used for
the Bloch resolvent. -/
theorem inverse_selected_lower (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (z g lam : ℝ) (hg : 0 < g) (hz : (z : ℂ) ∉ spectrum ℂ H)
    (hgap : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ H → t ≤ z - g ∨ z ≤ t)
    (hlam : z < lam) (φ : E) (hunit : ‖φ‖ = 1)
    (heig : H φ = (lam : ℂ) • φ) (v : E) :
    ‖inner ℂ φ v‖ ^ 2 / (lam - z) - ‖v‖ ^ 2 / g ≤
      (inner ℂ v ((H - (z : ℂ) • 1).inverse v)).re := by
  simpa only [finiteResolvent, ContinuousLinearMap.ringInverse_eq_inverse] using
    finiteResolvent_selected_lower H hH.isSymmetric z g lam hg hz hgap hlam φ hunit heig v

end Maxwell.Defect
