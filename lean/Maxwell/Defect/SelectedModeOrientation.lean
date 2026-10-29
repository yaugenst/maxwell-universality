import Maxwell.Defect.CertifiedFilterData
import Mathlib.Analysis.Normed.Module.Normalize

/-! The positive orientation supplied by a finite certificate identifies
the normalized spectral projection with that certificate's actual unit
eigenvector. No additional eigenvector selection is required. -/

namespace Maxwell.Defect

open InnerProductSpace Module.End

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem selectedProjection_eq_inner_smul
    (S : E →L[ℝ] E) (μ : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (heig : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1) :
    selectedProjection S μ v = (inner ℝ v u) • u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hspan : eigenspace S.toLinearMap μ = ℝ ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple (mem_eigenspace_iff.mpr heig) hu0
  have hp : selectedProjection S μ v ∈ ℝ ∙ u := by
    rw [← hspan]
    exact (eigenspace S.toLinearMap μ).starProjection_apply_mem v
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hp
  have ho := (eigenspace S.toLinearMap μ).starProjection_inner_eq_zero
    v u (mem_eigenspace_iff.mpr heig)
  change inner ℝ (v - selectedProjection S μ v) u = 0 at ho
  rw [inner_sub_left, ← ha, inner_smul_left, conj_trivial,
    real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at ho
  have hae : a = inner ℝ v u := by linarith
  simpa only [hae] using ha.symm

theorem normalize_selectedProjection_of_pos
    (S : E →L[ℝ] E) (μ : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (heig : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hpositive : 0 < inner ℝ v u) :
    NormedSpace.normalize (selectedProjection S μ v) = u := by
  rw [selectedProjection_eq_inner_smul S μ u v hu heig hsimple,
    NormedSpace.normalize_smul_of_pos hpositive,
    NormedSpace.normalize_eq_self_of_norm_eq_one hu]

end General

/-- The overlap already returned by `SimpleCertificate.filter_data` fixes
the normalization sign of its same selected spectral component. -/
theorem normalize_selectedProjection_of_rational_overlap {n : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℚ)
    (hu : ‖u‖ = 1) (heig : S u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace S.toLinearMap μ) = 1)
    (hv : v ≠ 0)
    (hoverlap : (1 / 2 : ℝ) ≤ inner ℝ (rationalUnitVector v) u) :
    NormedSpace.normalize (selectedProjection S μ (rationalVector v)) = u := by
  apply normalize_selectedProjection_of_pos S μ u (rationalVector v) hu heig hsimple
  have hn : 0 < ‖rationalVector v‖ := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  have hscale : ‖rationalVector v‖ • rationalUnitVector v = rationalVector v := by
    simp [rationalUnitVector, smul_smul, hn.ne']
  rw [← hscale, inner_smul_left, conj_trivial]
  exact mul_pos hn (lt_of_lt_of_le (by norm_num) hoverlap)

end Maxwell.Defect
