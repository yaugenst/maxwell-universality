import Maxwell.Continuum.ClusterComplementKernel
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Matrix.Normed

/-!
# Operator-norm analytic finite alias families

Finite central blocks are assembled through a continuous linear map into
the bounded operators on the full alias Hilbert space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement
open scoped Classical Matrix.Norms.Elementwise

abbrev Parameter := Momentum × ℂ
abbrev FiberMap := FiberSpace →L[ℂ] FiberSpace
abbrev PolarizationMap := Polarization →L[ℂ] Polarization
abbrev CentralFamily := CentralAlias → PolarizationMap

def InBox (z : Parameter) : Prop :=
  (∀ j, ‖z.1 j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) ∧ ‖z.2‖ ≤ 8

def OpenBox : Set Parameter :=
  {z | (∀ j, ‖z.1 j‖ < ((2 : ℝ) ^ 12)⁻¹) ∧ ‖z.2‖ < 8}

theorem openBox_inBox {z : Parameter} (hz : z ∈ OpenBox) : InBox z :=
  ⟨fun j => (hz.1 j).le, hz.2.le⟩

def centralBlockFamily (F : CentralFamily) (ν : Alias) : PolarizationMap :=
  if hν : IsCentralAlias ν then F ⟨ν, hν⟩ else 0

theorem centralBlockFamily_norm_le (F : CentralFamily) (ν : Alias) :
    ‖centralBlockFamily F ν‖ ≤ ‖F‖ := by
  by_cases hν : IsCentralAlias ν
  · simpa only [centralBlockFamily, dite_eq_left hν] using norm_le_pi_norm F ⟨ν, hν⟩
  · simp only [centralBlockFamily, dite_eq_right hν, norm_zero, norm_nonneg]

def centralFamilyMap (F : CentralFamily) : FiberMap :=
  boundedBlocks (centralBlockFamily F) (norm_nonneg F) (centralBlockFamily_norm_le F)

theorem centralFamilyMap_norm_le (F : CentralFamily) : ‖centralFamilyMap F‖ ≤ ‖F‖ :=
  boundedBlocks_norm_le _ _ _

def centralFamilyLinear : CentralFamily →ₗ[ℂ] FiberMap where
  toFun := centralFamilyMap
  map_add' F G := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    by_cases hν : IsCentralAlias ν
    · simp [centralFamilyMap, centralBlockFamily, hν]
    · simp [centralFamilyMap, centralBlockFamily, hν]
  map_smul' c F := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    by_cases hν : IsCentralAlias ν
    · simp [centralFamilyMap, centralBlockFamily, hν]
    · simp [centralFamilyMap, centralBlockFamily, hν]

def centralFamilyCLM : CentralFamily →L[ℂ] FiberMap :=
  centralFamilyLinear.mkContinuous 1 (by
    intro F
    change ‖centralFamilyMap F‖ ≤ 1 * ‖F‖
    simpa only [one_mul] using centralFamilyMap_norm_le F)

theorem centralFamilyCLM_apply (F : CentralFamily) (u : FiberSpace) (ν : Alias) :
    centralFamilyCLM F u ν = centralBlockFamily F ν (u ν) := rfl

def matrixCLMLinear : BlockMatrix →ₗ[ℂ] PolarizationMap where
  toFun := matrixCLM
  map_add' := matrixCLM_add
  map_smul' := matrixCLM_smul

def matrixCLMContinuous : BlockMatrix →L[ℂ] PolarizationMap :=
  matrixCLMLinear.toContinuousLinearMap

theorem analyticAt_coordinate (z : Parameter) (j : Fin 3) :
    AnalyticAt ℂ (fun w : Parameter => w.1 j) z :=
  ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z.1).comp analyticAt_fst

theorem analyticAt_scaledCoordinate (z : Parameter) (j : Fin 3) :
    AnalyticAt ℂ (fun w : Parameter => scaledMomentum w.1 j) z :=
  analyticAt_const.mul (analyticAt_coordinate z j)

theorem analyticAt_totalEnergy (z : Parameter) :
    AnalyticAt ℂ (fun w : Parameter => totalEnergy w.2) z :=
  analyticAt_const.add (analyticAt_const.mul analyticAt_snd)

theorem analyticAt_momentumSquare (p : Parameter → Momentum) (z : Parameter)
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) :
    AnalyticAt ℂ (fun w => momentumSquare (p w)) z :=
  Finset.analyticAt_fun_sum _ (fun j _ => (hp j).pow 2)

theorem analyticAt_bilinearDot (s : Momentum) (p : Parameter → Momentum) (z : Parameter)
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) :
    AnalyticAt ℂ (fun w => bilinearDot s (p w)) z :=
  Finset.analyticAt_fun_sum _ (fun j _ => analyticAt_const.mul (hp j))

theorem analyticAt_block (p : Parameter → Momentum) (E : Parameter → ℂ) (z : Parameter)
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) (hE : AnalyticAt ℂ E z) :
    AnalyticAt ℂ (fun w => block (p w) (E w)) z := by
  have hm : AnalyticAt ℂ (fun w => blockMatrix (p w) (E w)) z := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    change AnalyticAt ℂ (fun w =>
      (momentumSquare (p w) - E w) * (1 : BlockMatrix) i j - p w i * p w j) z
    exact (((analyticAt_momentumSquare p z hp).sub hE).mul analyticAt_const).sub ((hp i).mul (hp j))
  change AnalyticAt ℂ (matrixCLMContinuous ∘ (fun w => blockMatrix (p w) (E w))) z
  exact AnalyticAt.comp (f := fun w : Parameter => blockMatrix (p w) (E w))
    (matrixCLMContinuous.analyticAt (blockMatrix (p z) (E z))) hm

theorem analyticAt_longitudinalDenominator (s : Fin 3 → ℝ) (z : Parameter) :
    AnalyticAt ℂ (fun w : Parameter => longitudinalDenominator s (scaledMomentum w.1) (totalEnergy w.2)) z := by
  exact ((analyticAt_momentumSquare (fun w => scaledMomentum w.1) z (analyticAt_scaledCoordinate z)).sub
    (((analyticAt_bilinearDot (realMomentum s) (fun w => scaledMomentum w.1) z
      (analyticAt_scaledCoordinate z)).pow 2).mul analyticAt_const)).sub (analyticAt_totalEnergy z)

def centralFreeInverse (z : Parameter) : FiberMap :=
  centralFamilyCLM (fun ν =>
    centralRegularizedInverse (cornerSigns ν.val) (scaledMomentum z.1) (totalEnergy z.2))

theorem analyticAt_centralFreeInverse (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ centralFreeInverse z := by
  apply (centralFamilyCLM.analyticAt _).comp
  apply AnalyticAt.pi
  intro ν
  have hd : longitudinalDenominator (cornerSigns ν.val) (scaledMomentum z.1) (totalEnergy z.2) ≠ 0 := by
    apply norm_pos_iff.mp
    have h := longitudinal_denominator_norm (cornerSigns ν.val) (scaledMomentum z.1) (totalEnergy z.2)
      (cornerSigns_norm_sq ν.val ν.property) (scaledMomentum_norm_le z.1 hz.1)
      (totalEnergy_norm_bounds z.2 hz.2).1
    linarith
  exact (((analyticAt_longitudinalDenominator (cornerSigns ν.val) z).inv hd).smul
    analyticAt_const).add analyticAt_const

end Maxwell.Continuum.FiberAnalytic
