import Maxwell.Continuum.ClusterComplementProjection

/-!
# Quantitative momentum variation of the actual Maxwell blocks

The estimates use bilinear complex momentum squares and rank-one matrices.
They retain the full three-polarization block.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

theorem matrixCLM_add (M N : BlockMatrix) :
    matrixCLM (M + N) = matrixCLM M + matrixCLM N := by
  simp only [matrixCLM, map_add]

theorem matrixCLM_sub (M N : BlockMatrix) :
    matrixCLM (M - N) = matrixCLM M - matrixCLM N := by
  simp only [matrixCLM, map_sub]

theorem matrixCLM_smul (c : ℂ) (M : BlockMatrix) :
    matrixCLM (c • M) = c • matrixCLM M := by
  simp only [matrixCLM, map_smul]

theorem matrixCLM_one_eq : matrixCLM 1 = (1 : Polarization →L[ℂ] Polarization) := by
  apply ContinuousLinearMap.ext
  exact matrixCLM_one

theorem vecMulVec_rankOne (p q : Momentum) :
    matrixCLM (Matrix.vecMulVec p q) =
      InnerProductSpace.rankOne ℂ (momentumVector p) (conjugateVector q) := by
  apply ContinuousLinearMap.coe_injective
  change (Matrix.vecMulVec p q).toEuclideanLin =
    (InnerProductSpace.rankOne ℂ (momentumVector p) (conjugateVector q)).toLinearMap
  apply Matrix.toEuclideanLin.symm.injective
  rw [LinearEquiv.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne]
  ext i j
  simp [Matrix.vecMulVec_apply, momentumVector, conjugateVector]

theorem vecMulVec_norm (p q : Momentum) :
    ‖matrixCLM (Matrix.vecMulVec p q)‖ = ‖momentumVector p‖ * ‖momentumVector q‖ := by
  rw [vecMulVec_rankOne, InnerProductSpace.norm_rankOne, conjugateVector_norm]

theorem momentumOuter_add (p q : Momentum) :
    momentumOuter (p + q) = momentumOuter p + Matrix.vecMulVec p q +
      Matrix.vecMulVec q p + momentumOuter q := by
  ext i j
  simp only [momentumOuter, Matrix.vecMulVec_apply, Matrix.add_apply, Pi.add_apply]
  ring

theorem momentumOuter_smul (c : ℂ) (p : Momentum) :
    momentumOuter (c • p) = c ^ 2 • momentumOuter p := by
  ext i j
  simp only [momentumOuter, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  ring

theorem block_variation (p q : Momentum) (E : ℂ) :
    block (p + q) E - block p E =
      (2 * bilinearDot p q + momentumSquare q) • (1 : Polarization →L[ℂ] Polarization) -
        (matrixCLM (Matrix.vecMulVec p q) + matrixCLM (Matrix.vecMulVec q p) +
          matrixCLM (momentumOuter q)) := by
  have hm : blockMatrix (p + q) E - blockMatrix p E =
      (2 * bilinearDot p q + momentumSquare q) • (1 : BlockMatrix) -
        (Matrix.vecMulVec p q + Matrix.vecMulVec q p + momentumOuter q) := by
    rw [blockMatrix, blockMatrix, momentumSquare_add, momentumOuter_add]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  change matrixCLM (blockMatrix (p + q) E) - matrixCLM (blockMatrix p E) = _
  rw [← matrixCLM_sub, hm, matrixCLM_sub, matrixCLM_smul, matrixCLM_one_eq,
    matrixCLM_add, matrixCLM_add]

theorem block_variation_norm_le (p q : Momentum) (E : ℂ) :
    ‖block (p + q) E - block p E‖ ≤
      4 * ‖momentumVector p‖ * ‖momentumVector q‖ + 2 * ‖momentumVector q‖ ^ 2 := by
  have hs : ‖2 * bilinearDot p q + momentumSquare q‖ ≤
      2 * (‖momentumVector p‖ * ‖momentumVector q‖) + ‖momentumVector q‖ ^ 2 := by
    calc
      _ ≤ ‖2 * bilinearDot p q‖ + ‖momentumSquare q‖ := norm_add_le _ _
      _ = 2 * ‖bilinearDot p q‖ + ‖momentumSquare q‖ := by rw [norm_mul]; norm_num
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (bilinearDot_norm_le p q) (by norm_num))
        (momentumSquare_norm_le q)
  rw [block_variation]
  have htri := norm_sub_le
    ((2 * bilinearDot p q + momentumSquare q) • (1 : Polarization →L[ℂ] Polarization))
    (matrixCLM (Matrix.vecMulVec p q) + matrixCLM (Matrix.vecMulVec q p) +
      matrixCLM (momentumOuter q))
  rw [norm_smul, norm_one, mul_one] at htri
  have hsum := (norm_add_le
    (matrixCLM (Matrix.vecMulVec p q) + matrixCLM (Matrix.vecMulVec q p))
    (matrixCLM (momentumOuter q))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [vecMulVec_norm, vecMulVec_norm, momentumOuter_norm] at hsum
  nlinarith

theorem momentum_box_norm_le (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖momentumVector t‖ ≤ 1 / 1024 := by
  have hsq (j : Fin 3) : ‖t j‖ ^ 2 ≤ (1 / 16777216 : ℝ) := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ ((2 : ℝ) ^ 12)⁻¹)).mpr (ht j)
    norm_num at h
    exact h
  have hn := EuclideanSpace.norm_sq_eq (momentumVector t)
  change ‖momentumVector t‖ ^ 2 = ∑ j : Fin 3, ‖t j‖ ^ 2 at hn
  norm_num [Fin.sum_univ_succ] at hn
  nlinarith [hsq 0, hsq 1, hsq 2, norm_nonneg (momentumVector t)]

theorem scaledMomentum_norm_le_scaled (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖momentumVector (scaledMomentum t)‖ ≤ backgroundAmplitude / 1024 := by
  have hvec : momentumVector (scaledMomentum t) = (backgroundAmplitude : ℂ) • momentumVector t := rfl
  rw [hvec, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  exact (mul_le_mul_of_nonneg_left (momentum_box_norm_le t ht) backgroundAmplitude_pos.le).trans_eq
    (by ring)

theorem central_baseMomentum_norm_le (ν : Alias) (hν : IsCentralAlias ν) :
    ‖momentumVector (realMomentum (baseMomentum ν))‖ ≤ 4 := by
  have heq : realMomentum (baseMomentum ν) = ((Real.pi : ℂ) / 2) • realMomentum (cornerSigns ν) := by
    funext j
    simp only [realMomentum, baseMomentum, cornerSigns, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hvec : momentumVector (((Real.pi : ℂ) / 2) • realMomentum (cornerSigns ν)) =
      ((Real.pi : ℂ) / 2) • momentumVector (realMomentum (cornerSigns ν)) := rfl
  rw [heq, hvec, norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num only [Complex.norm_ofNat]
  have hs := cornerSigns_norm_sq ν hν
  have hn := norm_nonneg (momentumVector (realMomentum (cornerSigns ν)))
  have hsle : ‖momentumVector (realMomentum (cornerSigns ν))‖ ≤ 2 := by nlinarith
  have hm := mul_le_mul (show Real.pi / 2 ≤ 2 by linarith [Real.pi_lt_four]) hsle hn
    (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at hm
  exact hm

theorem central_block_variation_norm_le (t : Momentum) (E : ℂ) (ν : Alias)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (hν : IsCentralAlias ν) :
    ‖block (aliasMomentum (scaledMomentum t) ν) E -
      block (realMomentum (baseMomentum ν)) E‖ ≤ backgroundAmplitude / 32 := by
  rw [aliasMomentum_decomposition]
  have hvar := block_variation_norm_le (realMomentum (baseMomentum ν)) (scaledMomentum t) E
  have hp := central_baseMomentum_norm_le ν hν
  have hq := scaledMomentum_norm_le_scaled t ht
  have hq0 := norm_nonneg (momentumVector (scaledMomentum t))
  have hq1 : ‖momentumVector (scaledMomentum t)‖ ≤ 1 := by linarith [backgroundAmplitude_le]
  have hpq := mul_le_mul_of_nonneg_right hp hq0
  have hq2 : ‖momentumVector (scaledMomentum t)‖ ^ 2 ≤
      ‖momentumVector (scaledMomentum t)‖ := by nlinarith
  nlinarith

end Maxwell.Continuum.ClusterComplement
