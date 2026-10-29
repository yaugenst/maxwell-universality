import Maxwell.Continuum.WellSpectrum
import Maxwell.Continuum.TopEigenPerturbationComplement

/-! The proved literal scalar-well gap supplies the hypotheses of the
noncompact perturbation construction. -/

noncomputable section

namespace Maxwell.Continuum.Well

theorem mu_lower_numeric : (1 / (2 : ℝ) ^ 127) ≤ mu := by
  have h := mu_lower
  norm_num [FreeFiber.backgroundAmplitude] at h ⊢
  exact h

theorem mu_upper_numeric : mu ≤ 1 / (2 : ℝ) ^ 92 := by
  have h := mu_upper
  norm_num [FreeFiber.backgroundAmplitude] at h ⊢
  exact h

theorem gap_exact : gap = 1 / (2 : ℝ) ^ 188 := by
  norm_num [gap, FreeFiber.backgroundAmplitude]

theorem perturbation_data :
    TopEigenPerturbation.Data physicalBirmanSchwinger topVector mu gap where
  unit_norm := topVector_norm
  symmetric := physicalBirmanSchwinger_positive.isSymmetric
  eigenvector := topVector_eigen
  gap_pos := gap_pos
  gap_le_mu := gap_le_mu
  complement := well_complement_norm

end Maxwell.Continuum.Well
