import Maxwell.Continuum.TopEigenPerturbationEigen

/-! Actual spectrum exclusion around the perturbed top eigenvalue,
using a two-sided bounded inverse rather than a compactness assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation.Data

open Set Metric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

theorem spectrum_exclusion (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64)
    (z : ℂ) (hz : ‖z - (mu : ℂ)‖ ≤ d / 5) (hne : z ≠ D.eigenvalue E hE) :
    z ∉ spectrum ℂ (A + E) := by
  let e : ℂ := (z - (mu : ℂ)) / (scale d : ℂ)
  have hc : (scale d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr D.scale_pos.ne'
  have hze : (mu : ℂ) + (scale d : ℂ) * e = z := by
    dsimp [e]
    field_simp
    ring
  have he : e ∈ closedBall (0 : ℂ) (1 / 100) := by
    rw [mem_closedBall, dist_zero_right]
    dsimp only [e]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg D.scale_pos.le]
    apply (div_le_iff₀ D.scale_pos).mpr
    unfold scale
    linarith
  have hen : e ≠ D.root E hE := by
    intro h
    apply hne
    rw [← hze, h]
    rfl
  have hg := D.rankData.scalarResidual_ne_zero (D.perturbationData E hE) ()
    (Set.mem_univ ()) e he hen
  have hu := D.rankData.operator_isUnit (perturbation E d) e
    (D.perturbation_small E hE) (by simpa only [mem_closedBall, dist_eq_norm, Complex.ofReal_zero] using he) hg
  have hs : IsUnit ((-(scale d : ℂ)) •
      RankOneBand.operator (base A mu d) (perturbation E d) e) := by
    have hscalar := (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc)).map
      (algebraMap ℂ (H →L[ℂ] H))
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using hscalar.mul hu
  have hid : z • (1 : H →L[ℂ] H) - (A + E) = (-(scale d : ℂ)) •
      RankOneBand.operator (base A mu d) (perturbation E d) e := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sub_apply, smul_apply, one_apply_eq_self, neg_smul, neg_apply]
    rw [D.scaled_operator_apply, hze]
    abel
  apply spectrum.notMem_iff.mpr
  rw [Algebra.algebraMap_eq_smul_one, hid]
  exact hs

theorem eigenvalue_mem_spectrum (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    D.eigenvalue E hE ∈ spectrum ℂ (A + E) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hu
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  apply D.rawVector_ne_zero E hE
  apply hi
  simp only [sub_apply, smul_apply, one_apply_eq_self, D.rawVector_eigen,
    sub_self, map_zero]

theorem spectrum_gap (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64)
    (z : ℂ) (hz : z ∈ spectrum ℂ (A + E)) (hne : z ≠ D.eigenvalue E hE) :
    d / 10 ≤ dist z (D.eigenvalue E hE) := by
  have hout : d / 5 < ‖z - (mu : ℂ)‖ := by
    by_contra h
    exact D.spectrum_exclusion E hE z (le_of_not_gt h) hne hz
  have ht := dist_triangle z (D.eigenvalue E hE) (mu : ℂ)
  rw [dist_eq_norm z (mu : ℂ), dist_eq_norm (D.eigenvalue E hE) (mu : ℂ)] at ht
  linarith [D.eigenvalue_center_bound E hE]

theorem eigenvector_reconstruction (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64)
    (f : H) (hf : (A + E) f = D.eigenvalue E hE • f) :
    f = RankOneBand.coefficient u f • D.rawVector E hE := by
  have h : RankOneBand.operator (base A mu d) (perturbation E d) (D.root E hE) f = 0 := by
    have hs := D.scaled_operator_apply E (D.root E hE) f
    change (scale d : ℂ) • _ = (A + E) f - D.eigenvalue E hE • f at hs
    rw [hf, sub_self] at hs
    exact (smul_eq_zero.mp hs).resolve_left (Complex.ofReal_ne_zero.mpr D.scale_pos.ne')
  exact D.rankData.kernel_reconstruction (perturbation E d) (D.root E hE)
    (D.perturbation_small E hE) (by
      simpa only [mem_closedBall, dist_eq_norm, Complex.ofReal_zero] using D.root_mem E hE) f h

theorem eigenvector_iff (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (f : H) :
    (A + E) f = D.eigenvalue E hE • f ↔ ∃ c : ℂ, f = c • D.rawVector E hE := by
  constructor
  · intro h
    exact ⟨RankOneBand.coefficient u f, D.eigenvector_reconstruction E hE f h⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, D.rawVector_eigen, smul_comm]

end Maxwell.Continuum.TopEigenPerturbation.Data
