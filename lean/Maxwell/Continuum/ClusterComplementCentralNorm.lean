import Maxwell.Continuum.ClusterComplementCentral

/-! # Bounds and exact inverses for the fixed central longitudinal blocks -/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

def cornerSigns (ν : Alias) : Fin 3 → ℝ := fun j => 2 * (ν j : ℝ) + 1

theorem cornerSigns_sq (ν : Alias) (hν : IsCentralAlias ν) (j : Fin 3) :
    cornerSigns ν j ^ 2 = 1 := by
  rcases hν j with h | h <;> norm_num [cornerSigns, h]

theorem cornerSigns_norm_sq (ν : Alias) (hν : IsCentralAlias ν) :
    ‖momentumVector (realMomentum (cornerSigns ν))‖ ^ 2 = 3 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [momentumVector, realMomentum, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [cornerSigns_sq ν hν, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem central_momentum_decomposition (ν : Alias) (q : Momentum) :
    aliasMomentum q ν = ((Real.pi : ℂ) / 2) • realMomentum (cornerSigns ν) + q := by
  funext j
  simp only [aliasMomentum, cornerSigns, realMomentum, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_intCast, Complex.ofReal_one]
  ring

theorem totalEnergy_norm_bounds (e : ℂ) (he : ‖e‖ ≤ 8) :
    6 ≤ ‖totalEnergy e‖ ∧ ‖totalEnergy e‖ ≤ 13 := by
  have hδ := energy_perturbation_norm_le e he
  have hlo : (27 / 4 : ℝ) ≤ 3 * Real.pi ^ 2 / 4 := by nlinarith [Real.pi_gt_three]
  have hhi : 3 * Real.pi ^ 2 / 4 ≤ 12 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hpos : 0 ≤ 3 * Real.pi ^ 2 / 4 := by positivity
  have hn : ‖((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ)‖ = 3 * Real.pi ^ 2 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hupper := norm_add_le ((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) ((backgroundAmplitude : ℂ) * e)
  rw [hn] at hupper
  have hlower := norm_sub_le (totalEnergy e) ((backgroundAmplitude : ℂ) * e)
  have hsub : totalEnergy e - (backgroundAmplitude : ℂ) * e = ((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) := by
    simp only [totalEnergy, add_sub_cancel_right]
  rw [hsub, hn] at hlower
  change ‖totalEnergy e‖ ≤ _ at hupper
  constructor <;> linarith

theorem longitudinal_denominator_norm (s : Fin 3 → ℝ) (q : Momentum) (E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3)
    (hq : ‖momentumVector q‖ ≤ 1 / 10) (hE : 6 ≤ ‖E‖) :
    5 ≤ ‖longitudinalDenominator s q E‖ := by
  have hdot := bilinearDot_norm_le (realMomentum s) q
  have hdot2 := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hdot
  rw [mul_pow, hs] at hdot2
  have hq2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)).mpr hq
  have hcorr : ‖momentumSquare q - (bilinearDot (realMomentum s) q) ^ 2 / 3‖ ≤ 1 / 50 := by
    have htri := norm_sub_le (momentumSquare q) ((bilinearDot (realMomentum s) q) ^ 2 / 3)
    rw [norm_div, norm_pow] at htri
    norm_num at htri
    have hsq := momentumSquare_norm_le q
    nlinarith
  have htri := norm_sub_le (momentumSquare q - (bilinearDot (realMomentum s) q) ^ 2 / 3)
    (longitudinalDenominator s q E)
  have hid : momentumSquare q - (bilinearDot (realMomentum s) q) ^ 2 / 3 -
      longitudinalDenominator s q E = E := by simp only [longitudinalDenominator, sub_sub_cancel]
  rw [hid] at htri
  linarith

def centralRegularizedBlock (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ) :
    Polarization →L[ℂ] Polarization :=
  longitudinal s * block (c • realMomentum s + q) E * longitudinal s + (1 - longitudinal s)

def centralRegularizedInverse (s : Fin 3 → ℝ) (q : Momentum) (E : ℂ) :
    Polarization →L[ℂ] Polarization :=
  (longitudinalDenominator s q E)⁻¹ • longitudinal s + (1 - longitudinal s)

theorem central_regularized_inverse_left (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3)
    (hd : longitudinalDenominator s q E ≠ 0) :
    centralRegularizedBlock s q c E * centralRegularizedInverse s q E = 1 := by
  have hLL := (longitudinal_isStarProjection s hs).isIdempotentElem.eq
  have hLLv (v : Polarization) : longitudinal s (longitudinal s v) = longitudinal s v :=
    congrArg (fun T : Polarization →L[ℂ] Polarization => T v) hLL
  rw [centralRegularizedBlock, centralRegularizedInverse, longitudinal_block_compression _ _ _ _ hs]
  apply ContinuousLinearMap.ext
  intro v
  change longitudinalDenominator s q E • longitudinal s
      ((longitudinalDenominator s q E)⁻¹ • longitudinal s v + (v - longitudinal s v)) +
    (((longitudinalDenominator s q E)⁻¹ • longitudinal s v + (v - longitudinal s v)) -
      longitudinal s ((longitudinalDenominator s q E)⁻¹ • longitudinal s v + (v - longitudinal s v))) = v
  simp only [map_add, map_sub, map_smul, hLLv, sub_self, add_zero,
    smul_smul, mul_inv_cancel₀ hd, one_smul]
  abel

theorem central_regularized_inverse_right (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3)
    (hd : longitudinalDenominator s q E ≠ 0) :
    centralRegularizedInverse s q E * centralRegularizedBlock s q c E = 1 := by
  have hLL := (longitudinal_isStarProjection s hs).isIdempotentElem.eq
  have hLLv (v : Polarization) : longitudinal s (longitudinal s v) = longitudinal s v :=
    congrArg (fun T : Polarization →L[ℂ] Polarization => T v) hLL
  rw [centralRegularizedBlock, centralRegularizedInverse, longitudinal_block_compression _ _ _ _ hs]
  apply ContinuousLinearMap.ext
  intro v
  change (longitudinalDenominator s q E)⁻¹ • longitudinal s
      (longitudinalDenominator s q E • longitudinal s v + (v - longitudinal s v)) +
    ((longitudinalDenominator s q E • longitudinal s v + (v - longitudinal s v)) -
      longitudinal s (longitudinalDenominator s q E • longitudinal s v + (v - longitudinal s v))) = v
  simp only [map_add, map_sub, map_smul, hLLv, sub_self, add_zero,
    smul_smul, inv_mul_cancel₀ hd, one_smul]
  abel

theorem central_regularized_inverse_left_apply (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3)
    (hd : longitudinalDenominator s q E ≠ 0) (v : Polarization) :
    centralRegularizedBlock s q c E (centralRegularizedInverse s q E v) = v := by
  exact congrArg (fun T : Polarization →L[ℂ] Polarization => T v)
    (central_regularized_inverse_left s q c E hs hd)

theorem central_regularized_inverse_right_apply (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3)
    (hd : longitudinalDenominator s q E ≠ 0) (v : Polarization) :
    centralRegularizedInverse s q E (centralRegularizedBlock s q c E v) = v := by
  exact congrArg (fun T : Polarization →L[ℂ] Polarization => T v)
    (central_regularized_inverse_right s q c E hs hd)

theorem centralRegularizedInverse_norm_le (s : Fin 3 → ℝ) (q : Momentum) (E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3)
    (hq : ‖momentumVector q‖ ≤ 1 / 10) (hE : 6 ≤ ‖E‖) :
    ‖centralRegularizedInverse s q E‖ ≤ 6 / 5 := by
  have hd := longitudinal_denominator_norm s q E hs hq hE
  have hdpos : 0 < ‖longitudinalDenominator s q E‖ := by linarith
  have hinv : ‖longitudinalDenominator s q E‖⁻¹ ≤ (1 / 5 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hdpos (by norm_num : (0 : ℝ) < 5)).mpr hd
  calc
    ‖centralRegularizedInverse s q E‖ ≤
        ‖(longitudinalDenominator s q E)⁻¹ • longitudinal s‖ + ‖1 - longitudinal s‖ := norm_add_le _ _
    _ = ‖longitudinalDenominator s q E‖⁻¹ * ‖longitudinal s‖ + ‖1 - longitudinal s‖ := by
      rw [norm_smul, norm_inv]
    _ ≤ 1 / 5 * 1 + 1 := add_le_add
      (mul_le_mul hinv (longitudinal_norm_le s hs) (norm_nonneg _) (by norm_num))
      (transverse_norm_le s hs)
    _ = 6 / 5 := by norm_num

end Maxwell.Continuum.ClusterComplement
