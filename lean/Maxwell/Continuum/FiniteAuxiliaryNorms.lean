import Maxwell.Continuum.FiniteAuxiliaryCoordinates
import Maxwell.Continuum.CoerciveInverse

/-! Norm and coercivity facts used by the literal finite well assembly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

section Norms

variable {H G K J : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup J] [NormedSpace ℂ J]

theorem contractive_compression_norm (P : K →L[ℂ] J) (A : G →L[ℂ] K) (Z : H →L[ℂ] G)
    (hP : ‖P‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) : ‖P.comp (A.comp Z)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖P‖*(‖A‖*‖Z‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg P))
    _ ≤ 1*(‖A‖*1) := mul_le_mul hP
      (mul_le_mul_of_nonneg_left hZ (norm_nonneg A)) (by positivity) zero_le_one
    _ = _ := by ring

end Norms

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem coercive_of_norm_sub_le (A B : H →L[ℂ] H) {c δ : ℝ}
    (hB : CoerciveInverse.Coercive B c) (hAB : ‖A-B‖ ≤ δ) :
    CoerciveInverse.Coercive A (c-δ) := by
  intro x
  have hlow := hB x
  have he : ‖(B-A) x‖ ≤ δ*‖x‖ := by
    have hn : ‖B-A‖ ≤ δ := by simpa only [norm_sub_rev] using hAB
    exact (B-A).le_of_opNorm_le hn x
  have hi := (re_inner_le_norm (𝕜 := ℂ) x ((B-A) x)).trans
    (mul_le_mul_of_nonneg_left he (norm_nonneg x))
  change (inner ℂ x ((B-A) x)).re ≤ ‖x‖*(δ*‖x‖) at hi
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hi
  nlinarith only [hlow, hi]

end Hilbert

variable {ι : Type*} [Fintype ι]

theorem diagonal_norm_le (v : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    ‖diagonal v‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg f))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonal_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)) 2

#print axioms coercive_of_norm_sub_le

end Maxwell.Continuum.FiniteAuxiliary
