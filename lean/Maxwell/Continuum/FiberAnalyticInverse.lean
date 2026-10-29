import Maxwell.Continuum.FiberAnalyticNumerator

/-!
# Operator-norm holomorphy of the actual complementary inverse

The normalized noncentral numerator and denominator yield the exact free
inverse. A bounded Neumann factor gives the actual material complement.
All parameter-dependent functions below take values in bounded operators;
no common domain for the unbounded free operators is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement
open scoped Classical

def noncentralInverseExtension (z : Parameter) : FiberMap :=
  normalizedNumerator z * Ring.inverse (normalizedDenominator z)

theorem noncentralInverseExtension_apply (z : Parameter) (hz : InBox z)
    (u : FiberSpace) (ν : Alias) :
    noncentralInverseExtension z u ν =
      if IsCentralAlias ν then 0 else
        inverseBlock (aliasMomentum (scaledMomentum z.1) ν) (totalEnergy z.2) (u ν) := by
  change normalizedNumerator z (Ring.inverse (normalizedDenominator z) u) ν = _
  rw [normalizedNumerator_apply, denominator_ringInverse_apply z hz]
  by_cases hν : IsCentralAlias ν
  · rw [ite_eq_left hν, normalizedWeight, ite_eq_left hν, zero_smul]
  · rw [ite_eq_right hν]
    have ha : (baseSize ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (baseSize_pos ν hν))
    have hD := (noncentral_inverse_estimate z.1 z.2 ν hz.1 hz.2 hν).2.1
    have hprod : normalizedWeight ν * (denominatorValue z ν)⁻¹ =
        (momentumSquare (aliasMomentum (scaledMomentum z.1) ν) - totalEnergy z.2)⁻¹ := by
      rw [normalizedWeight, ite_eq_right hν, denominatorValue, ite_eq_right hν]
      field_simp
    rw [map_smul, smul_comm ((totalEnergy z.2)⁻¹) ((denominatorValue z ν)⁻¹),
      ← smul_sub, smul_smul, hprod, inverseBlock_eq_CLM]
    rfl

theorem analyticAt_noncentralInverseExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ noncentralInverseExtension z :=
  (analyticAt_normalizedNumerator z hz).mul (analyticAt_denominatorInverse z hz)

def regularizedFreeExtension (z : Parameter) : FiberMap :=
  centralFreeInverse z + noncentralInverseExtension z

theorem regularizedFreeExtension_eq (z : Parameter) (hz : InBox z) :
    regularizedFreeExtension z = (regularizedFreeInverse z.1 z.2 hz.1 hz.2).map := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  funext ν
  change centralFreeInverse z u ν + noncentralInverseExtension z u ν =
    regularizedInverseBlock z.1 z.2 ν (u ν)
  rw [noncentralInverseExtension_apply z hz]
  change centralFamilyCLM _ u ν + _ = _
  rw [centralFamilyCLM_apply]
  by_cases hν : IsCentralAlias ν <;>
    simp [centralBlockFamily, regularizedInverseBlock, hν]

theorem analyticAt_regularizedFreeExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ regularizedFreeExtension z :=
  (analyticAt_centralFreeInverse z hz).add (analyticAt_noncentralInverseExtension z hz)

def materialNeumannUnit (z : Parameter) (hz : InBox z) : FiberMapˣ := by
  have hsmall : ‖-(compressedMaterial * regularizedFreeExtension z)‖ < 1 := by
    rw [norm_neg, regularizedFreeExtension_eq z hz]
    exact (compressedMaterial_inverse_product_norm z.1 z.2 hz.1 hz.2).trans_lt (by norm_num)
  exact
    { val := 1 + compressedMaterial * regularizedFreeExtension z
      inv := Neumann.series (-(compressedMaterial * regularizedFreeExtension z))
      val_inv := by
        apply ContinuousLinearMap.ext
        intro u
        have h := Neumann.series_left (-(compressedMaterial * regularizedFreeExtension z)) hsmall u
        change _ - -(compressedMaterial (regularizedFreeExtension z (_))) = u at h
        change Neumann.series _ u + compressedMaterial (regularizedFreeExtension z (Neumann.series _ u)) = u
        simpa only [sub_neg_eq_add] using h
      inv_val := by
        apply ContinuousLinearMap.ext
        intro u
        have h := Neumann.series_right (-(compressedMaterial * regularizedFreeExtension z)) hsmall u
        change Neumann.series _ (u - -(compressedMaterial (regularizedFreeExtension z u))) = u at h
        change Neumann.series _ (u + compressedMaterial (regularizedFreeExtension z u)) = u
        simpa only [sub_neg_eq_add] using h }

def regularizedMaterialExtension (z : Parameter) : FiberMap :=
  regularizedFreeExtension z * Ring.inverse (1 + compressedMaterial * regularizedFreeExtension z)

theorem regularizedMaterialExtension_eq (z : Parameter) (hz : InBox z) :
    regularizedMaterialExtension z = (regularizedMaterialInverse z.1 z.2 hz.1 hz.2).map := by
  change regularizedFreeExtension z * Ring.inverse (materialNeumannUnit z hz : FiberMap) = _
  rw [Ring.inverse_unit]
  change regularizedFreeExtension z * Neumann.series (-(compressedMaterial * regularizedFreeExtension z)) = _
  rw [regularizedFreeExtension_eq z hz]
  rfl

theorem analyticAt_regularizedMaterialExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ regularizedMaterialExtension z := by
  have hN : AnalyticAt ℂ (fun w : Parameter => 1 + compressedMaterial * regularizedFreeExtension w) z :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_regularizedFreeExtension z hz))
  exact (analyticAt_regularizedFreeExtension z hz).mul
    (AnalyticAt.comp (f := fun w : Parameter => 1 + compressedMaterial * regularizedFreeExtension w)
      (analyticAt_inverse (𝕜 := ℂ) (materialNeumannUnit z hz)) hN)

def complementInverseExtension (z : Parameter) : FiberMap :=
  regularizedMaterialExtension z * complementProjection

theorem complementInverseExtension_eq (z : Parameter) (hz : InBox z) :
    complementInverseExtension z = complementInverse z.1 z.2 hz.1 hz.2 := by
  rw [complementInverseExtension, regularizedMaterialExtension_eq z hz]
  rfl

theorem analyticAt_complementInverseExtension (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ complementInverseExtension z :=
  (analyticAt_regularizedMaterialExtension z hz).mul analyticAt_const

/-- Holomorphy in the actual full Hilbert-space operator norm. -/
theorem analyticOnNhd_complementInverseExtension :
    AnalyticOnNhd ℂ complementInverseExtension OpenBox :=
  fun z hz => analyticAt_complementInverseExtension z (openBox_inBox hz)

end Maxwell.Continuum.FiberAnalytic
