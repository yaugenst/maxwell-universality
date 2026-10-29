import Maxwell.Continuum.WellGap

/-! The actual scalar well has a simple isolated top spectral point,
with an explicit gap from the remainder of its complex spectrum. -/

noncomputable section

namespace Maxwell.Continuum.Well

open Module.End

theorem mu_mem_spectrum : (mu : ℂ) ∈ spectrum ℂ physicalBirmanSchwinger := by
  let : Nontrivial ScalarL2 := nontrivial_of_ne rootVector 0 rootVector_ne_zero
  apply (physicalBirmanSchwinger_compact.hasEigenvalue_iff_mem_spectrum
    (Complex.ofReal_ne_zero.mpr mu_pos.ne')).mp
  apply hasEigenvalue_of_hasEigenvector (x := topVector)
  refine ⟨?_, ?_⟩
  · exact mem_eigenspace_iff.mpr topVector_eigen
  · intro h
    have hn := topVector_norm
    rw [h, norm_zero] at hn
    norm_num at hn

theorem other_eigenvector_orthogonal (z : ℂ) (hz : z ≠ (mu : ℂ))
    (v : ScalarL2) (hv : physicalBirmanSchwinger v = z • v) :
    inner ℂ topVector v = 0 := by
  have h := physicalBirmanSchwinger_positive.inner_left_eq_inner_right topVector v
  rw [topVector_eigen, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have he : ((mu : ℂ) - z) * inner ℂ topVector v = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hz.symm)

theorem well_spectrum_remainder_norm (z : ℂ) (hz : z ∈ spectrum ℂ physicalBirmanSchwinger)
    (hne : z ≠ (mu : ℂ)) : ‖z‖ ≤ mu - gap := by
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero]
    exact sub_nonneg.mpr gap_le_mu
  · have he := (physicalBirmanSchwinger_compact.hasEigenvalue_iff_mem_spectrum hz0).mpr hz
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hve : physicalBirmanSchwinger v = z • v := hv.apply_eq_smul
    have ho := other_eigenvector_orthogonal z hne v hve
    have h := well_complement_norm v ho
    rw [hve, norm_smul] at h
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv.2)).mp (by simpa [mul_comm] using h)

theorem well_spectrum_gap (z : ℂ) (hz : z ∈ spectrum ℂ physicalBirmanSchwinger)
    (hne : z ≠ (mu : ℂ)) : gap ≤ dist z (mu : ℂ) := by
  have h := well_spectrum_remainder_norm z hz hne
  have ht := norm_le_norm_sub_add (mu : ℂ) z
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg mu_pos.le,
    norm_sub_rev, ← dist_eq_norm] at ht
  linarith

theorem well_spectrum_gap_numeric (z : ℂ) (hz : z ∈ spectrum ℂ physicalBirmanSchwinger)
    (hne : z ≠ (mu : ℂ)) : (1 / (2 : ℝ) ^ 190) ≤ dist z (mu : ℂ) :=
  gap_numeric.trans (well_spectrum_gap z hz hne)

end Maxwell.Continuum.Well
