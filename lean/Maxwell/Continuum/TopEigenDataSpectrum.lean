import Maxwell.Continuum.TopEigenPerturbationComplement
import Maxwell.Continuum.CompactDeflation

/-! An actual spectral gap from a normalized eigenvector and a complementary
norm bound. The construction uses a bounded inverse and needs no compactness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.TopEigenPerturbation.Data

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

omit [CompleteSpace H] in
theorem inner_self_one : inner ℂ u u = 1 := by
  rw [inner_self_eq_norm_sq_to_K, D.unit_norm]
  simp

omit [CompleteSpace H] in
theorem coefficient_apply (x : H) : inner ℂ u (A x) = (mu : ℂ) * inner ℂ u x := by
  have he : inner ℂ (A u) x = inner ℂ u (A x) := D.symmetric u x
  rw [D.eigenvector, inner_smul_left, Complex.conj_ofReal] at he
  exact he.symm

omit [CompleteSpace H] in
theorem deflated_norm : ‖A - (mu : ℂ) • rankOne ℂ u u‖ ≤ mu - d := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sub_nonneg.mpr D.gap_le_mu)
  intro x
  let Q := ((ℂ ∙ u)ᗮ).starProjection
  have hQ : Q x = x - inner ℂ u x • u := by
    dsimp [Q]
    rw [Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_unit_singleton ℂ D.unit_norm]
  have hAx : (A - (mu : ℂ) • rankOne ℂ u u) x = A (Q x) := by
    rw [hQ]
    simp only [sub_apply, smul_apply, rankOne_apply, map_sub, map_smul, D.eigenvector]
    module
  rw [hAx]
  exact (D.complement (Q x)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (((ℂ ∙ u)ᗮ).starProjection_apply_mem x))).trans
    (mul_le_mul_of_nonneg_left (((ℂ ∙ u)ᗮ).norm_starProjection_apply_le x)
      (sub_nonneg.mpr D.gap_le_mu))

omit [CompleteSpace H] in
theorem projection_shift_unit (z : ℂ) (hz : z ≠ 0) (hm : z ≠ (mu : ℂ)) :
    IsUnit (1 - ((mu : ℂ) / z) • rankOne ℂ u u) := by
  let P := rankOne ℂ u u
  let a : ℂ := (mu : ℂ) / z
  let b : ℂ := (mu : ℂ) / (z - (mu : ℂ))
  have hab : b - a - a * b = 0 := by
    dsimp [a, b]
    field_simp
    ring
  have hP : P * P = P := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [P, mul_apply_eq_comp, rankOne_apply, inner_smul_right,
      D.inner_self_one, mul_one]
  have hl : (1 - a • P) * (1 + b • P) = 1 := by
    rw [sub_mul, mul_add, mul_add]
    simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hP, smul_smul]
    calc
      _ = 1 + (b - a - a * b) • P := by module
      _ = 1 := by rw [hab, zero_smul, add_zero]
  have hr : (1 + b • P) * (1 - a • P) = 1 := by
    rw [mul_sub, add_mul, add_mul]
    simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hP, smul_smul]
    calc
      _ = 1 + (b - a - a * b) • P := by module
      _ = 1 := by rw [hab, zero_smul, add_zero]
  exact ⟨⟨1 - a • P, 1 + b • P, hl, hr⟩, rfl⟩

theorem spectrum_remainder_norm (z : ℂ) (hz : z ∈ spectrum ℂ A)
    (hm : z ≠ (mu : ℂ)) : ‖z‖ ≤ mu - d := by
  let : Nontrivial H := nontrivial_of_ne u 0 (by
    intro he
    have hn := D.unit_norm
    rw [he, norm_zero] at hn
    norm_num at hn)
  by_contra h
  have hnorm : mu - d < ‖z‖ := lt_of_not_ge h
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, norm_zero] at hnorm
    linarith [D.gap_le_mu]
  let A₀ := A - (mu : ℂ) • rankOne ℂ u u
  have hu₀ : IsUnit (z • (1 : H →L[ℂ] H) - A₀) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    apply spectrum.notMem_iff.mp
    intro hs
    exact (not_lt_of_ge ((spectrum.norm_le_norm_of_mem hs).trans D.deflated_norm)) hnorm
  have hid : z • (1 : H →L[ℂ] H) - A =
      (z • (1 : H →L[ℂ] H) - A₀) *
        (1 - ((mu : ℂ) / z) • rankOne ℂ u u) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [A₀, mul_apply_eq_comp, sub_apply, smul_apply,
      one_apply_eq_self, rankOne_apply, map_sub, map_smul, D.eigenvector,
      D.inner_self_one]
    match_scalars <;> field_simp
    all_goals ring
  apply (spectrum.mem_iff.mp hz)
  rw [Algebra.algebraMap_eq_smul_one, hid]
  exact hu₀.mul (D.projection_shift_unit z hz0 hm)

theorem actual_spectrum_gap (z : ℂ) (hz : z ∈ spectrum ℂ A)
    (hm : z ≠ (mu : ℂ)) : d ≤ dist z (mu : ℂ) := by
  have hb := D.spectrum_remainder_norm z hz hm
  have ht := norm_le_norm_sub_add (mu : ℂ) z
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_of_lt_of_le D.gap_pos D.gap_le_mu), norm_sub_rev] at ht
  rw [dist_eq_norm]
  linarith

end Maxwell.Continuum.TopEigenPerturbation.Data
