import Maxwell.Continuum.TopEigenDataSpectrum
import Maxwell.Continuum.GramSpectralGap

/-! Exact transport, scaling and simplicity of isolated top eigenpairs.
All spectral conclusions concern the bounded operator spectrum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation.Data

open scoped InnerProduct

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem gramData (B : X →L[ℂ] Y) {u : Y} {mu d : ℝ}
    (D : Data (B.comp (B†)) u mu d) :
    Data ((B†).comp B) (GramSpectral.vector B mu u) mu d where
  unit_norm := GramSpectral.vector_norm B u D.unit_norm
    (lt_of_lt_of_le D.gap_pos D.gap_le_mu) D.eigenvector
  symmetric := (ContinuousLinearMap.isPositive_adjoint_comp_self B).isSelfAdjoint.isSymmetric
  eigenvector := GramSpectral.vector_eigen B u
    (lt_of_lt_of_le D.gap_pos D.gap_le_mu) D.eigenvector
  gap_pos := D.gap_pos
  gap_le_mu := D.gap_le_mu
  complement := GramSpectral.gram_complement B u
    (lt_of_lt_of_le D.gap_pos D.gap_le_mu) (sub_nonneg.mpr D.gap_le_mu) D.complement

variable {A : X →L[ℂ] X} {u : X} {mu d : ℝ} (D : Data A u mu d)

include D

theorem positive_scale {c : ℝ} (hc : 0 < c) :
    Data ((c : ℂ) • A) u (c * mu) (c * d) where
  unit_norm := D.unit_norm
  symmetric := ((show IsSelfAdjoint (c : ℂ) by simp [IsSelfAdjoint]).smul
    D.symmetric.isSelfAdjoint).isSymmetric
  eigenvector := by simp only [smul_apply, D.eigenvector, Complex.ofReal_mul, smul_smul]
  gap_pos := mul_pos hc D.gap_pos
  gap_le_mu := mul_le_mul_of_nonneg_left D.gap_le_mu hc.le
  complement := by
    intro f hf
    rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have h := mul_le_mul_of_nonneg_left (D.complement f hf) hc.le
    nlinarith

omit [CompleteSpace X] in
theorem residual_gap (f : X) (hf : inner ℂ u f = 0) :
    d * ‖f‖ ≤ ‖A f - (mu : ℂ) • f‖ := by
  have ht := norm_le_norm_sub_add ((mu : ℂ) • f) (A f)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_of_lt_of_le D.gap_pos D.gap_le_mu), norm_sub_rev] at ht
  linarith [D.complement f hf]

omit [CompleteSpace X] in
theorem eigenvector_simple (f : X) (hf : A f = (mu : ℂ) • f) :
    f = inner ℂ u f • u := by
  let v := f - inner ℂ u f • u
  have hv : inner ℂ u v = 0 := by
    simp only [v, inner_sub_right, inner_smul_right, D.inner_self_one, mul_one, sub_self]
  have he : A v - (mu : ℂ) • v = 0 := by
    simp only [v, map_sub, map_smul, hf, D.eigenvector]
    module
  have hb := D.residual_gap v hv
  rw [he, norm_zero] at hb
  have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v, D.gap_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem mem_spectrum : (mu : ℂ) ∈ spectrum ℂ A := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hu
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have he : u = 0 := hi (by
    simp only [sub_apply, smul_apply, one_apply_eq_self, D.eigenvector,
      sub_self, map_zero])
  have hn := D.unit_norm
  rw [he, norm_zero] at hn
  norm_num at hn

end Maxwell.Continuum.TopEigenPerturbation.Data
