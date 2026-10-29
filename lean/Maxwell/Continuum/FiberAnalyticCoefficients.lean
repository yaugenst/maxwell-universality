import Maxwell.Continuum.FiberAnalyticFinite

/-!
# Bounded normalized coefficients over the infinite alias lattice

Normalization uses the actual squared real base momentum. Its reciprocal,
its linear coordinate ratios, and its rank-one matrix ratio define bounded
operators uniformly over every noncentral alias.
-/

noncomputable section

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement
open scoped Classical

def baseSize (ν : Alias) : ℝ := ‖momentumVector (realMomentum (baseMomentum ν))‖ ^ 2

theorem baseSize_ge (ν : Alias) (hν : ¬IsCentralAlias ν) : 24 ≤ baseSize ν :=
  noncentral_base_norm_sq ν hν

theorem baseSize_pos (ν : Alias) (hν : ¬IsCentralAlias ν) : 0 < baseSize ν := by
  linarith [baseSize_ge ν hν]

def normalizedWeight (ν : Alias) : ℂ :=
  if IsCentralAlias ν then 0 else (baseSize ν : ℂ)⁻¹

theorem normalizedWeight_norm_le (ν : Alias) : ‖normalizedWeight ν‖ ≤ 1 := by
  by_cases hν : IsCentralAlias ν
  · simp [normalizedWeight, hν]
  · rw [normalizedWeight, ite_eq_right hν, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (baseSize_pos ν hν)]
    exact (inv_le_one₀ (baseSize_pos ν hν)).mpr (by linarith [baseSize_ge ν hν])

def normalizedCoordinate (j : Fin 3) (ν : Alias) : ℂ :=
  normalizedWeight ν * (baseMomentum ν j : ℂ)

theorem normalizedCoordinate_norm_le (j : Fin 3) (ν : Alias) :
    ‖normalizedCoordinate j ν‖ ≤ 1 := by
  by_cases hν : IsCentralAlias ν
  · simp [normalizedCoordinate, normalizedWeight, hν]
  · have hp := PiLp.norm_apply_le (momentumVector (realMomentum (baseMomentum ν))) j
    change ‖(baseMomentum ν j : ℂ)‖ ≤ ‖momentumVector (realMomentum (baseMomentum ν))‖ at hp
    have hsize : ‖momentumVector (realMomentum (baseMomentum ν))‖ ≤ baseSize ν := by
      have hs := baseSize_ge ν hν
      unfold baseSize at hs ⊢
      nlinarith [norm_nonneg (momentumVector (realMomentum (baseMomentum ν)))]
    rw [normalizedCoordinate, norm_mul, normalizedWeight, ite_eq_right hν, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (baseSize_pos ν hν)]
    exact (mul_le_mul_of_nonneg_left (hp.trans hsize)
      (inv_nonneg.mpr (baseSize_pos ν hν).le)).trans_eq
      (inv_mul_cancel₀ (ne_of_gt (baseSize_pos ν hν)))

def scalarMap (c : Alias → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ ν, ‖c ν‖ ≤ C) : FiberMap :=
  boundedBlocks (fun ν => c ν • (1 : PolarizationMap)) hC
    (fun ν => by simpa only [norm_smul, norm_one, mul_one] using hc ν)

theorem scalarMap_apply (c : Alias → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ ν, ‖c ν‖ ≤ C)
    (u : FiberSpace) (ν : Alias) : scalarMap c hC hc u ν = c ν • u ν := rfl

theorem scalarMap_norm_le (c : Alias → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ ν, ‖c ν‖ ≤ C) :
    ‖scalarMap c hC hc‖ ≤ C := boundedBlocks_norm_le _ _ _

def weightMap : FiberMap := scalarMap normalizedWeight (by norm_num) normalizedWeight_norm_le

def coordinateMap (j : Fin 3) : FiberMap :=
  scalarMap (normalizedCoordinate j) (by norm_num) (normalizedCoordinate_norm_le j)

theorem weightMap_apply (u : FiberSpace) (ν : Alias) : weightMap u ν = normalizedWeight ν • u ν := rfl

theorem coordinateMap_apply (j : Fin 3) (u : FiberSpace) (ν : Alias) :
    coordinateMap j u ν = normalizedCoordinate j ν • u ν := rfl

def normalizedOuterBaseBlock (ν : Alias) : PolarizationMap :=
  normalizedWeight ν • matrixCLM (momentumOuter (realMomentum (baseMomentum ν)))

theorem normalizedOuterBaseBlock_norm_le (ν : Alias) : ‖normalizedOuterBaseBlock ν‖ ≤ 1 := by
  by_cases hν : IsCentralAlias ν
  · rw [normalizedOuterBaseBlock, norm_smul]
    simp [normalizedWeight, hν]
  · rw [normalizedOuterBaseBlock, norm_smul, normalizedWeight, ite_eq_right hν,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (baseSize_pos ν hν), momentumOuter_norm]
    change (baseSize ν)⁻¹ * baseSize ν ≤ 1
    rw [inv_mul_cancel₀ (ne_of_gt (baseSize_pos ν hν))]

def outerBaseMap : FiberMap :=
  boundedBlocks normalizedOuterBaseBlock (by norm_num) normalizedOuterBaseBlock_norm_le

def matrixUnit (j k : Fin 3) : BlockMatrix := fun i l => if i = j ∧ l = k then 1 else 0

def uniformMatrixMap (M : BlockMatrix) : FiberMap :=
  boundedBlocks (fun _ => matrixCLM M) (norm_nonneg _) (fun _ => le_rfl)

theorem uniformMatrixMap_apply (M : BlockMatrix) (u : FiberSpace) (ν : Alias) :
    uniformMatrixMap M u ν = matrixCLM M (u ν) := rfl

theorem matrixUnit_decomposition (M : BlockMatrix) :
    (∑ j : Fin 3, ∑ k : Fin 3, M j k • matrixUnit j k) = M := by
  ext i l
  simp [matrixUnit, Matrix.sum_apply, Matrix.smul_apply, ite_and]

end Maxwell.Continuum.FiberAnalytic
