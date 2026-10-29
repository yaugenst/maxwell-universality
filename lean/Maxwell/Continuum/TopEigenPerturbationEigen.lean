import Maxwell.Continuum.TopEigenPerturbationBasic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! An actual perturbed eigenpair and quantitative eigenvector and
eigenvalue bounds, constructed without perturbed compactness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation

open Set Metric NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem normalize_sub_unit (v u : H) (hv : v ≠ 0) (hu : ‖u‖ = 1) :
    ‖normalize v - u‖ ≤ 2 * ‖v - u‖ := by
  have hn := norm_normalize hv
  have he : normalize v - v = (1 - ‖v‖) • normalize v := by
    rw [sub_smul, one_smul, norm_smul_normalize]
  have hdiff : ‖normalize v - v‖ ≤ ‖v - u‖ := by
    rw [he, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_sub_comm]
    simpa only [hu] using abs_norm_sub_norm_le v u
  have ht := dist_triangle (normalize v) v u
  simp only [dist_eq_norm] at ht
  linarith

namespace Data

variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

omit [CompleteSpace H] in
theorem scaled_operator_apply (E : H →L[ℂ] H) (e : ℂ) (x : H) :
    (scale d : ℂ) • RankOneBand.operator (base A mu d) (perturbation E d) e x =
      (A + E) x - ((mu : ℂ) + (scale d : ℂ) * e) • x := by
  have hc : (scale d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr D.scale_pos.ne'
  simp only [RankOneBand.operator, base, perturbation, sub_apply, add_apply, smul_apply,
    one_apply_eq_self, smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul,
    add_smul]
  simp only [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  module

theorem rawVector_eigen (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    (A + E) (D.rawVector E hE) = D.eigenvalue E hE • D.rawVector E hE := by
  have h := D.rankData.bandVector_kernel (D.perturbationData E hE) () (Set.mem_univ ())
  have hs := congrArg (fun x : H => (scale d : ℂ) • x) h
  change (scale d : ℂ) • RankOneBand.operator (base A mu d) (perturbation E d)
    (D.root E hE) (D.rawVector E hE) = _ at hs
  rw [D.scaled_operator_apply, smul_zero] at hs
  exact sub_eq_zero.mp hs

def vector (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) : H := normalize (D.rawVector E hE)

theorem vector_norm (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) : ‖D.vector E hE‖ = 1 :=
  norm_normalize (D.rawVector_ne_zero E hE)

theorem vector_eigen (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    (A + E) (D.vector E hE) = D.eigenvalue E hE • D.vector E hE := by
  unfold vector NormedSpace.normalize
  rw [ContinuousLinearMap.map_smul_of_tower, D.rawVector_eigen]
  exact smul_comm _ _ _

theorem vector_error (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖D.vector E hE - u‖ ≤ 4 * ‖E‖ / d := by
  apply (normalize_sub_unit (D.rawVector E hE) u (D.rawVector_ne_zero E hE) D.unit_norm).trans
  have h := mul_le_mul_of_nonneg_left (D.rawVector_error E hE) (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  ring

theorem zero_root : D.rankData.bandRoot D.zeroData () = 0 := by
  have hu : u ≠ 0 := by intro h; simpa [h] using D.unit_norm
  have hk : RankOneBand.operator (base A mu d) (family 0 d () 0) 0 u = 0 := by
    simp only [RankOneBand.operator, family, perturbation, smul_zero, add_zero, zero_smul,
      sub_zero]
    simpa only [Complex.ofReal_zero, zero_smul] using D.rankData.eigenvector
  have h := (D.rankData.kernel_nonzero_iff_bandRoot D.zeroData () (Set.mem_univ ()) 0
    (by simp [Metric.mem_closedBall])).mp ⟨u, hu, hk⟩
  exact h.symm

theorem root_error (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖D.root E hE‖ ≤ 4 * ‖E‖ / scale d := by
  have h := D.rankData.bandRoot_sub_bound (D.perturbationData E hE) D.zeroData ()
    (Set.mem_univ ()) (ε := ‖perturbation E d‖) (norm_nonneg _) (by
      intro e _
      simp only [family, perturbation, smul_zero, sub_zero, le_refl])
  rw [D.zero_root, sub_zero, D.perturbation_norm] at h
  change ‖D.root E hE‖ ≤ _ at h
  convert h using 1
  ring

theorem eigenvalue_error (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖D.eigenvalue E hE - (mu : ℂ)‖ ≤ 4 * ‖E‖ := by
  rw [eigenvalue, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg D.scale_pos.le]
  have h := mul_le_mul_of_nonneg_left (D.root_error E hE) D.scale_pos.le
  apply h.trans_eq
  field_simp [D.scale_pos.ne']

theorem eigenvalue_center_bound (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖D.eigenvalue E hE - (mu : ℂ)‖ ≤ d / 10 := by
  rw [eigenvalue, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg D.scale_pos.le]
  have h := mul_le_mul_of_nonneg_left (D.root_norm E hE) D.scale_pos.le
  unfold scale at h ⊢
  linarith

theorem eigenvalue_real (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric) :
    ((D.eigenvalue E hE).re : ℂ) = D.eigenvalue E hE := by
  have hs : (A + E).IsSymmetric := D.symmetric.add hEs
  have hev : Module.End.HasEigenvalue (A + E : H →L[ℂ] H).toLinearMap (D.eigenvalue E hE) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (D.rawVector_eigen E hE), D.rawVector_ne_zero E hE⟩
  have hc := hs.conj_eigenvalue_eq_self hev
  have hi : (D.eigenvalue E hE).im = 0 := by
    have h := congrArg Complex.im hc
    simp only [Complex.conj_im] at h
    linarith
  apply Complex.ext <;> simp [hi]

end Data
end Maxwell.Continuum.TopEigenPerturbation
