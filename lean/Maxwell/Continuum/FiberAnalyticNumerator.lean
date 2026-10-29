import Maxwell.Continuum.FiberAnalyticDenominator

/-!
# Operator-norm analytic normalized Maxwell numerator

The infinite quadratic numerator is expressed as a finite polynomial in
bounded coefficient operators. Its pointwise action is the literal
`(I - p pᵀ/E)/|p(0)|²` on every noncentral alias.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement
open scoped Classical

theorem matrixCLM_sum {ι : Type*} (s : Finset ι) (M : ι → BlockMatrix) :
    matrixCLM (∑ i ∈ s, M i) = ∑ i ∈ s, matrixCLM (M i) :=
  map_sum matrixCLMLinear M s

theorem weightedOuter_expansion (p q : Momentum) (w : ℂ) :
    w • matrixCLM (momentumOuter p) +
      (∑ j : Fin 3, ∑ k : Fin 3,
        (q k * (w * p j) + q j * (w * p k) + (q j * q k) * w) • matrixCLM (matrixUnit j k)) =
      w • matrixCLM (momentumOuter (p + q)) := by
  have hm : w • momentumOuter p +
      (∑ j : Fin 3, ∑ k : Fin 3,
        (q k * (w * p j) + q j * (w * p k) + (q j * q k) * w) • matrixUnit j k) =
      w • momentumOuter (p + q) := by
    ext i l
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      momentumOuter, Matrix.vecMulVec_apply, Pi.add_apply, matrixUnit, ite_and]
    ring
  have h := congrArg matrixCLM hm
  simpa only [matrixCLM_add, matrixCLM_smul, matrixCLM_sum] using h

def normalizedOuter (z : Parameter) : FiberMap :=
  outerBaseMap + ∑ j : Fin 3, ∑ k : Fin 3,
    (scaledMomentum z.1 k • coordinateMap j + scaledMomentum z.1 j • coordinateMap k +
      (scaledMomentum z.1 j * scaledMomentum z.1 k) • weightMap) * uniformMatrixMap (matrixUnit j k)

theorem normalizedOuter_apply (z : Parameter) (u : FiberSpace) (ν : Alias) :
    normalizedOuter z u ν = normalizedWeight ν •
      matrixCLM (momentumOuter (aliasMomentum (scaledMomentum z.1) ν)) (u ν) := by
  have h := congrArg (fun T : PolarizationMap => T (u ν))
    (weightedOuter_expansion (realMomentum (baseMomentum ν)) (scaledMomentum z.1) (normalizedWeight ν))
  rw [aliasMomentum_decomposition]
  change normalizedOuter z u ν = _
  rw [normalizedOuter]
  simp only [add_apply, sum_apply, lp.coeFn_add, lp.coeFn_sum, Pi.add_apply, Finset.sum_apply]
  change normalizedWeight ν • matrixCLM (momentumOuter (realMomentum (baseMomentum ν))) (u ν) +
    (∑ j : Fin 3, ∑ k : Fin 3,
      ((scaledMomentum z.1 k • coordinateMap j + scaledMomentum z.1 j • coordinateMap k +
        (scaledMomentum z.1 j * scaledMomentum z.1 k) • weightMap)
        (uniformMatrixMap (matrixUnit j k) u)) ν) = _
  simp only [add_apply, smul_apply, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    coordinateMap_apply, weightMap_apply, uniformMatrixMap_apply, normalizedCoordinate, smul_smul]
  simpa only [add_apply, sum_apply, smul_apply, add_smul, realMomentum] using h

theorem analyticAt_normalizedOuter (z : Parameter) : AnalyticAt ℂ normalizedOuter z := by
  have hsum : AnalyticAt ℂ (fun w : Parameter => ∑ j : Fin 3, ∑ k : Fin 3,
      (scaledMomentum w.1 k • coordinateMap j + scaledMomentum w.1 j • coordinateMap k +
        (scaledMomentum w.1 j * scaledMomentum w.1 k) • weightMap) * uniformMatrixMap (matrixUnit j k)) z := by
    apply Finset.analyticAt_fun_sum
    intro j _
    apply Finset.analyticAt_fun_sum
    intro k _
    have hcoef : AnalyticAt ℂ (fun w : Parameter =>
        scaledMomentum w.1 k • coordinateMap j + scaledMomentum w.1 j • coordinateMap k +
          (scaledMomentum w.1 j * scaledMomentum w.1 k) • weightMap) z :=
      (((analyticAt_scaledCoordinate z k).smul (analyticAt_const (v := coordinateMap j))).add
        ((analyticAt_scaledCoordinate z j).smul (analyticAt_const (v := coordinateMap k)))).add
          (((analyticAt_scaledCoordinate z j).mul (analyticAt_scaledCoordinate z k)).smul
            (analyticAt_const (v := weightMap)))
    exact hcoef.mul (analyticAt_const (v := uniformMatrixMap (matrixUnit j k)))
  exact (analyticAt_const (v := outerBaseMap)).add hsum

def normalizedNumerator (z : Parameter) : FiberMap :=
  weightMap - (totalEnergy z.2)⁻¹ • normalizedOuter z

theorem normalizedNumerator_apply (z : Parameter) (u : FiberSpace) (ν : Alias) :
    normalizedNumerator z u ν = normalizedWeight ν •
      (u ν - (totalEnergy z.2)⁻¹ •
        matrixCLM (momentumOuter (aliasMomentum (scaledMomentum z.1) ν)) (u ν)) := by
  change weightMap u ν - (totalEnergy z.2)⁻¹ • normalizedOuter z u ν = _
  rw [weightMap_apply, normalizedOuter_apply, smul_sub, smul_smul, smul_smul]
  rw [mul_comm (normalizedWeight ν) ((totalEnergy z.2)⁻¹)]

theorem analyticAt_normalizedNumerator (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ normalizedNumerator z := by
  have hE : totalEnergy z.2 ≠ 0 := norm_pos_iff.mp (by
    have h := (totalEnergy_norm_bounds z.2 hz.2).1
    linarith)
  exact analyticAt_const.sub (((analyticAt_totalEnergy z).inv hE).smul (analyticAt_normalizedOuter z))

end Maxwell.Continuum.FiberAnalytic
