import Maxwell.Continuum.TopEigenPerturbationSpectrum

/-! Reality of the constructed eigenvector follows from actual
conjugation symmetry and its fixed reference coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation.Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

theorem rawVector_coefficient (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    inner ℂ u (D.rawVector E hE) = 1 :=
  D.rankData.coefficient_eigenvectorLift _ _

theorem rawVector_conjugation (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (J : H →L[ℝ] H) (hJsmul : ∀ c : ℂ, ∀ x : H, J (c • x) = star c • J x)
    (hJinner : ∀ x : H, inner ℂ u (J x) = star (inner ℂ u x))
    (hcomm : ∀ x : H, (A + E) (J x) = J ((A + E) x)) :
    J (D.rawVector E hE) = D.rawVector E hE := by
  have hreal : star (D.eigenvalue E hE) = D.eigenvalue E hE := by
    rw [← D.eigenvalue_real E hE hEs]
    simp
  have he : (A + E) (J (D.rawVector E hE)) =
      D.eigenvalue E hE • J (D.rawVector E hE) := by
    rw [hcomm, D.rawVector_eigen, hJsmul, hreal]
  have h := D.eigenvector_reconstruction E hE (J (D.rawVector E hE)) he
  change J (D.rawVector E hE) = inner ℂ u (J (D.rawVector E hE)) • D.rawVector E hE at h
  rw [hJinner, D.rawVector_coefficient, star_one, one_smul] at h
  exact h

theorem vector_conjugation (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (J : H →L[ℝ] H) (hJsmul : ∀ c : ℂ, ∀ x : H, J (c • x) = star c • J x)
    (hJinner : ∀ x : H, inner ℂ u (J x) = star (inner ℂ u x))
    (hcomm : ∀ x : H, (A + E) (J x) = J ((A + E) x)) :
    J (D.vector E hE) = D.vector E hE := by
  unfold vector NormedSpace.normalize
  rw [map_smul, D.rawVector_conjugation E hE hEs J hJsmul hJinner hcomm]

theorem vector_coefficient_ne_zero (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    inner ℂ u (D.vector E hE) ≠ 0 := by
  unfold vector NormedSpace.normalize
  rw [← algebraMap_smul ℂ (‖D.rawVector E hE‖⁻¹) (D.rawVector E hE),
    inner_smul_right, D.rawVector_coefficient, mul_one]
  change ((‖D.rawVector E hE‖⁻¹ : ℝ) : ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr (D.rawVector_ne_zero E hE)))

end Maxwell.Continuum.TopEigenPerturbation.Data
