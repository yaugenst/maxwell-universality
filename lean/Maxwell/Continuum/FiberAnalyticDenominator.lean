import Maxwell.Continuum.FiberAnalyticCoefficients

/-!
# Uniformly invertible normalized scalar denominator

At noncentral aliases the denominator is `(p(q)²-E)/|p(0)|²`.
It is one on the central aliases. The operator is a polynomial in bounded
coefficient operators, and its scalar blocks have modulus at least `1/3`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement
open scoped Classical

def normalizedDenominator (z : Parameter) : FiberMap :=
  1 + (2 : ℂ) • (∑ j : Fin 3, scaledMomentum z.1 j • coordinateMap j) +
    (momentumSquare (scaledMomentum z.1) - totalEnergy z.2) • weightMap

def denominatorValue (z : Parameter) (ν : Alias) : ℂ :=
  if IsCentralAlias ν then 1 else
    (momentumSquare (aliasMomentum (scaledMomentum z.1) ν) - totalEnergy z.2) / (baseSize ν : ℂ)

theorem coordinate_sum_apply (q : Momentum) (u : FiberSpace) (ν : Alias) :
    (∑ j : Fin 3, q j • coordinateMap j) u ν =
      (normalizedWeight ν * bilinearDot (realMomentum (baseMomentum ν)) q) • u ν := by
  simp only [sum_apply, smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, coordinateMap_apply, normalizedCoordinate, smul_smul]
  rw [← Finset.sum_smul, bilinearDot, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [realMomentum]
  ring

theorem normalizedDenominator_apply (z : Parameter) (u : FiberSpace) (ν : Alias) :
    normalizedDenominator z u ν = denominatorValue z ν • u ν := by
  have hraw : normalizedDenominator z u ν =
      (1 + 2 * (normalizedWeight ν * bilinearDot (realMomentum (baseMomentum ν)) (scaledMomentum z.1)) +
        (momentumSquare (scaledMomentum z.1) - totalEnergy z.2) * normalizedWeight ν) • u ν := by
    change (u ν + (2 : ℂ) • ((∑ j : Fin 3, scaledMomentum z.1 j • coordinateMap j) u ν)) +
      (momentumSquare (scaledMomentum z.1) - totalEnergy z.2) • weightMap u ν = _
    rw [coordinate_sum_apply, weightMap_apply, smul_smul, smul_smul]
    simp only [add_smul, one_smul]
  rw [hraw]
  congr 1
  by_cases hν : IsCentralAlias ν
  · simp [denominatorValue, normalizedWeight, hν]
  · rw [denominatorValue, ite_eq_right hν, normalizedWeight, ite_eq_right hν,
      aliasMomentum_decomposition, momentumSquare_add, momentumSquare_real]
    change 1 + 2 * ((baseSize ν : ℂ)⁻¹ *
      bilinearDot (realMomentum (baseMomentum ν)) (scaledMomentum z.1)) +
      (momentumSquare (scaledMomentum z.1) - totalEnergy z.2) * (baseSize ν : ℂ)⁻¹ =
      ((baseSize ν : ℂ) + 2 * bilinearDot (realMomentum (baseMomentum ν)) (scaledMomentum z.1) +
        momentumSquare (scaledMomentum z.1) - totalEnergy z.2) / (baseSize ν : ℂ)
    have ha : (baseSize ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (baseSize_pos ν hν))
    field_simp
    ring

theorem analyticAt_normalizedDenominator (z : Parameter) :
    AnalyticAt ℂ normalizedDenominator z := by
  have hsum : AnalyticAt ℂ (fun w : Parameter => ∑ j : Fin 3,
      scaledMomentum w.1 j • coordinateMap j) z :=
    Finset.analyticAt_fun_sum _ (fun j _ => (analyticAt_scaledCoordinate z j).smul analyticAt_const)
  have hfirst : AnalyticAt ℂ (fun w : Parameter => (1 : FiberMap) +
      (2 : ℂ) • (∑ j : Fin 3, scaledMomentum w.1 j • coordinateMap j)) z :=
    (analyticAt_const (v := (1 : FiberMap))).add ((analyticAt_const (v := (2 : ℂ))).smul hsum)
  exact hfirst.add (((analyticAt_momentumSquare (fun w => scaledMomentum w.1) z
    (analyticAt_scaledCoordinate z)).sub (analyticAt_totalEnergy z)).smul analyticAt_const)

theorem noncentral_denominator_norm_lower (z : Parameter) (hz : InBox z)
    (ν : Alias) (hν : ¬IsCentralAlias ν) :
    baseSize ν / 3 ≤
      ‖momentumSquare (aliasMomentum (scaledMomentum z.1) ν) - totalEnergy z.2‖ := by
  have herr := (small_momentum_perturbation (realMomentum (baseMomentum ν)) (scaledMomentum z.1)
    (baseSize_ge ν hν) (scaledMomentum_norm_le z.1 hz.1)).2
  rw [momentumSquare_real] at herr
  have hE := (totalEnergy_norm_bounds z.2 hz.2).2
  have htri : baseSize ν ≤
      ‖momentumSquare (aliasMomentum (scaledMomentum z.1) ν) - totalEnergy z.2‖ +
      ‖momentumSquare (realMomentum (baseMomentum ν) + scaledMomentum z.1) - (baseSize ν : ℂ)‖ +
      ‖totalEnergy z.2‖ := by
    calc
      baseSize ν = ‖(baseSize ν : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (baseSize_pos ν hν)]
      _ = ‖(momentumSquare (aliasMomentum (scaledMomentum z.1) ν) - totalEnergy z.2) -
          (momentumSquare (realMomentum (baseMomentum ν) + scaledMomentum z.1) - (baseSize ν : ℂ)) +
          totalEnergy z.2‖ := by rw [aliasMomentum_decomposition]; congr 1; ring
      _ ≤ ‖(momentumSquare (aliasMomentum (scaledMomentum z.1) ν) - totalEnergy z.2) -
          (momentumSquare (realMomentum (baseMomentum ν) + scaledMomentum z.1) - (baseSize ν : ℂ))‖ +
          ‖totalEnergy z.2‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
  change ‖momentumSquare (realMomentum (baseMomentum ν) + scaledMomentum z.1) - (baseSize ν : ℂ)‖ ≤
    baseSize ν / 10 at herr
  linarith [baseSize_ge ν hν]

theorem denominatorValue_norm_lower (z : Parameter) (hz : InBox z) (ν : Alias) :
    1 / 3 ≤ ‖denominatorValue z ν‖ := by
  by_cases hν : IsCentralAlias ν
  · simp [denominatorValue, hν]
    norm_num
  · rw [denominatorValue, ite_eq_right hν, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (baseSize_pos ν hν)]
    apply (le_div_iff₀ (baseSize_pos ν hν)).mpr
    nlinarith [noncentral_denominator_norm_lower z hz ν hν]

theorem denominatorValue_ne_zero (z : Parameter) (hz : InBox z) (ν : Alias) :
    denominatorValue z ν ≠ 0 := norm_pos_iff.mp (by linarith [denominatorValue_norm_lower z hz ν])

theorem denominatorValue_inv_norm_le (z : Parameter) (hz : InBox z) (ν : Alias) :
    ‖(denominatorValue z ν)⁻¹‖ ≤ 3 := by
  rw [norm_inv]
  have hpos := norm_pos_iff.mpr (denominatorValue_ne_zero z hz ν)
  have h := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 3)).mpr
    (denominatorValue_norm_lower z hz ν)
  norm_num at h
  exact h

def denominatorInverse (z : Parameter) (hz : InBox z) : FiberMap :=
  scalarMap (fun ν => (denominatorValue z ν)⁻¹) (by norm_num) (denominatorValue_inv_norm_le z hz)

def denominatorUnit (z : Parameter) (hz : InBox z) : FiberMapˣ where
  val := normalizedDenominator z
  inv := denominatorInverse z hz
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    change normalizedDenominator z (denominatorInverse z hz u) ν = u ν
    rw [normalizedDenominator_apply]
    change denominatorValue z ν • ((denominatorValue z ν)⁻¹ • u ν) = u ν
    rw [smul_smul, mul_inv_cancel₀ (denominatorValue_ne_zero z hz ν), one_smul]
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    change (denominatorValue z ν)⁻¹ • (normalizedDenominator z u ν) = u ν
    rw [normalizedDenominator_apply, smul_smul, inv_mul_cancel₀ (denominatorValue_ne_zero z hz ν), one_smul]

theorem denominator_ringInverse_apply (z : Parameter) (hz : InBox z) (u : FiberSpace) (ν : Alias) :
    Ring.inverse (normalizedDenominator z) u ν = (denominatorValue z ν)⁻¹ • u ν := by
  change Ring.inverse (denominatorUnit z hz : FiberMap) u ν = _
  rw [Ring.inverse_unit]
  rfl

theorem analyticAt_denominatorInverse (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ (fun w => Ring.inverse (normalizedDenominator w)) z := by
  exact AnalyticAt.comp (f := normalizedDenominator)
    (analyticAt_inverse (𝕜 := ℂ) (denominatorUnit z hz)) (analyticAt_normalizedDenominator z)

end Maxwell.Continuum.FiberAnalytic
