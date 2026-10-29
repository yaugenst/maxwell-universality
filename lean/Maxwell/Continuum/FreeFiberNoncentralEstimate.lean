import Maxwell.Continuum.FreeFiberBlockNorm

/-!
# Uniform inverse estimate for large real base momenta

This estimate handles arbitrary complex perturbations of a real momentum.
Its hypotheses will be verified for every noncentral integer alias in the
paper's complex box. No limiting argument or transverse truncation is used.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

theorem small_momentum_perturbation (p q : Momentum)
    (hp : 24 ≤ ‖momentumVector p‖ ^ 2) (hq : ‖momentumVector q‖ ≤ 1 / 10) :
    ‖momentumVector (p + q)‖ ^ 2 ≤ (11 / 10) * ‖momentumVector p‖ ^ 2 ∧
    ‖momentumSquare (p + q) - momentumSquare p‖ ≤ ‖momentumVector p‖ ^ 2 / 10 := by
  have hr : (4 : ℝ) ≤ ‖momentumVector p‖ :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp (by linarith)
  have hquadratic : ‖momentumVector p‖ / 5 + 1 / 100 ≤ ‖momentumVector p‖ ^ 2 / 10 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (norm_nonneg (momentumVector p))]
  have hcross : 2 * ‖momentumVector p‖ * ‖momentumVector q‖ ≤ ‖momentumVector p‖ / 5 := by
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * ‖momentumVector p‖)]
  have hq2 : ‖momentumVector q‖ ^ 2 ≤ (1 / 100 : ℝ) := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)).mpr hq
    norm_num at h
    exact h
  have herror : 2 * ‖momentumVector p‖ * ‖momentumVector q‖ +
      ‖momentumVector q‖ ^ 2 ≤ ‖momentumVector p‖ ^ 2 / 10 := by linarith
  constructor
  · have htriangle : ‖momentumVector (p + q)‖ ≤ ‖momentumVector p‖ + ‖momentumVector q‖ :=
      norm_add_le _ _
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ ‖momentumVector p‖ + ‖momentumVector q‖)).mpr htriangle
    nlinarith
  · exact (momentumSquare_add_error p q).trans herror

/-- A norm bound for the full three-polarization inverse. The conservative
constant `3/4` is uniform even as the real base momentum tends to infinity. -/
theorem inverseBlock_coarse_noncentral (p : Fin 3 → ℝ) (q : Momentum)
    (E₀ : ℝ) (δ : ℂ) (hp : 24 ≤ ‖momentumVector (realMomentum p)‖ ^ 2)
    (hq : ‖momentumVector q‖ ≤ 1 / 10) (hElo : 27 / 4 ≤ E₀) (hEhi : E₀ ≤ 12)
    (hδ : ‖δ‖ ≤ 1 / 100) :
    (E₀ : ℂ) + δ ≠ 0 ∧
      momentumSquare (realMomentum p + q) - ((E₀ : ℂ) + δ) ≠ 0 ∧
      ‖inverseBlock (realMomentum p + q) ((E₀ : ℂ) + δ)‖ ≤ 3 / 4 := by
  let a : ℝ := ‖momentumVector (realMomentum p)‖ ^ 2
  have ha : 24 ≤ a := hp
  have ha0 : 0 < a := by linarith
  have hE₀ : 0 ≤ E₀ := by linarith
  obtain ⟨hnorm, herr⟩ := small_momentum_perturbation (realMomentum p) q hp hq
  rw [momentumSquare_real] at herr
  have hEtriangle : E₀ ≤ ‖(E₀ : ℂ) + δ‖ + ‖δ‖ := by
    calc
      E₀ = ‖(E₀ : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE₀]
      _ = ‖((E₀ : ℂ) + δ) - δ‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖(E₀ : ℂ) + δ‖ + ‖δ‖ := norm_sub_le _ _
  have hEnorm : 6 ≤ ‖(E₀ : ℂ) + δ‖ := by linarith
  have hEpos : 0 < ‖(E₀ : ℂ) + δ‖ := by linarith
  have hbase : 0 ≤ a - E₀ := by linarith
  have hDtriangle : a - E₀ ≤
      ‖momentumSquare (realMomentum p + q) - ((E₀ : ℂ) + δ)‖ +
      ‖momentumSquare (realMomentum p + q) - (a : ℂ)‖ + ‖δ‖ := by
    calc
      a - E₀ = ‖((a - E₀ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbase]
      _ = ‖(momentumSquare (realMomentum p + q) - ((E₀ : ℂ) + δ)) -
          (momentumSquare (realMomentum p + q) - (a : ℂ)) + δ‖ := by
        congr 1
        push_cast
        ring
      _ ≤ ‖(momentumSquare (realMomentum p + q) - ((E₀ : ℂ) + δ)) -
          (momentumSquare (realMomentum p + q) - (a : ℂ))‖ + ‖δ‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) (le_refl ‖δ‖)
  have hDnorm : a / 3 ≤ ‖momentumSquare (realMomentum p + q) - ((E₀ : ℂ) + δ)‖ := by
    change ‖momentumSquare (realMomentum p + q) - (a : ℂ)‖ ≤ a / 10 at herr
    linarith
  have hDpos : 0 < ‖momentumSquare (realMomentum p + q) - ((E₀ : ℂ) + δ)‖ := by
    linarith
  refine ⟨norm_pos_iff.mp hEpos, norm_pos_iff.mp hDpos, ?_⟩
  have hEinv : ‖(E₀ : ℂ) + δ‖⁻¹ ≤ (1 / 6 : ℝ) := by
    simpa only [one_div] using
      (inv_le_inv₀ hEpos (by norm_num : (0 : ℝ) < 6)).mpr hEnorm
  have hnum : 1 + ‖(E₀ : ℂ) + δ‖⁻¹ * ‖momentumVector (realMomentum p + q)‖ ^ 2 ≤ a / 4 := by
    have hmul := mul_le_mul hEinv hnorm (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 6)
    change ‖(E₀ : ℂ) + δ‖⁻¹ * ‖momentumVector (realMomentum p + q)‖ ^ 2 ≤
      1 / 6 * (11 / 10 * a) at hmul
    nlinarith
  apply (inverseBlock_norm_le _ _).trans
  rw [inv_mul_eq_div, div_le_iff₀ hDpos]
  nlinarith

end Maxwell.Continuum.FreeFiber
