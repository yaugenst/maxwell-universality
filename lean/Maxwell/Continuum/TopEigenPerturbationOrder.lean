import Maxwell.Continuum.TopEigenPerturbationSpectrum

/-! The constructed perturbed eigenvalue is the largest real spectral
point. The exclusion above the energy bound uses coercivity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inner_mass_sub (A : H →L[ℂ] H) (m : ℝ) (x : H) :
    (inner ℂ x ((m : ℂ) • x - A x)).re = m * ‖x‖ ^ 2 - (inner ℂ x (A x)).re := by
  simp only [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [h]

namespace Data

variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

omit [CompleteSpace H] in
theorem energy_upper (x : H) : (inner ℂ x (A x)).re ≤ mu * ‖x‖ ^ 2 := by
  let z := x - inner ℂ u x • u
  have hii : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, D.unit_norm]; simp
  have hz : inner ℂ u z = 0 := by
    simp only [z, inner_sub_right, inner_smul_right, hii, mul_one, sub_self]
  have ha : (mu : ℂ) • z - A z = (mu : ℂ) • x - A x := by
    simp only [z, smul_sub, map_sub, map_smul, D.eigenvector]
    module
  have ho : inner ℂ u ((mu : ℂ) • x - A x) = 0 := by
    have hs : inner ℂ (A u) x = inner ℂ u (A x) := D.symmetric u x
    rw [D.eigenvector, inner_smul_left, Complex.conj_ofReal] at hs
    rw [inner_sub_right, inner_smul_right, hs, sub_self]
  have he : inner ℂ z ((mu : ℂ) • z - A z) = inner ℂ x ((mu : ℂ) • x - A x) := by
    rw [ha]
    simp only [z, inner_sub_left, inner_smul_left, ho, mul_zero, sub_zero]
  have hnonneg : 0 ≤ (inner ℂ z ((mu : ℂ) • z - A z)).re := by
    rw [inner_mass_sub]
    have h := D.complement_energy z hz
    nlinarith [D.gap_pos, sq_nonneg ‖z‖]
  rw [he, inner_mass_sub] at hnonneg
  linarith

omit [CompleteSpace H] in
theorem perturbed_energy_upper (E : H →L[ℂ] H) (x : H) :
    (inner ℂ x ((A + E) x)).re ≤ (mu + ‖E‖) * ‖x‖ ^ 2 := by
  have hE : (inner ℂ x (E x)).re ≤ ‖E‖ * ‖x‖ ^ 2 := by
    change RCLike.re (inner ℂ x (E x)) ≤ _
    exact (re_inner_le_norm (𝕜 := ℂ) x (E x)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (E.le_opNorm x) (norm_nonneg x)])
  simp only [add_apply, inner_add_right, Complex.add_re]
  nlinarith [D.energy_upper x]

theorem above_energy_not_mem_spectrum (E : H →L[ℂ] H) (t : ℝ) (ht : mu + ‖E‖ < t) :
    (t : ℂ) ∉ spectrum ℂ (A + E) := by
  apply spectrum.notMem_iff.mpr
  rw [Algebra.algebraMap_eq_smul_one]
  apply CoerciveInverse.isUnit _ (show 0 < t - mu - ‖E‖ by linarith)
  intro x
  change (t - mu - ‖E‖) * ‖x‖ ^ 2 ≤
    (inner ℂ x ((t : ℂ) • x - (A + E) x)).re
  rw [inner_mass_sub]
  nlinarith [D.perturbed_energy_upper E x]

theorem real_spectrum_upper (E : H →L[ℂ] H) (t : ℝ)
    (ht : (t : ℂ) ∈ spectrum ℂ (A + E)) : t ≤ mu + ‖E‖ := by
  by_contra h
  exact D.above_energy_not_mem_spectrum E t (lt_of_not_ge h) ht

theorem eigenvalue_largest (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (t : ℝ) (ht : (t : ℂ) ∈ spectrum ℂ (A + E)) : t ≤ (D.eigenvalue E hE).re := by
  by_contra h
  have hlt : (D.eigenvalue E hE).re < t := lt_of_not_ge h
  have hcenter := D.eigenvalue_center_bound E hE
  rw [← D.eigenvalue_real E hE hEs, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hcenter
  have htup := D.real_spectrum_upper E t ht
  have hnear : ‖(t : ℂ) - (mu : ℂ)‖ ≤ d / 5 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [abs_le.mp hcenter |>.1, abs_le.mp hcenter |>.2, D.gap_pos]
  have hne : (t : ℂ) ≠ D.eigenvalue E hE := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.ofReal_re] at hr
    linarith
  exact D.spectrum_exclusion E hE (t : ℂ) hnear hne ht

theorem eigenvalue_pos (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric) :
    0 < (D.eigenvalue E hE).re := by
  have h := D.eigenvalue_center_bound E hE
  rw [← D.eigenvalue_real E hE hEs, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  linarith [(abs_le.mp h).1, D.gap_pos, D.gap_le_mu]

end Data
end Maxwell.Continuum.TopEigenPerturbation
