import Maxwell.Continuum.CalibrationFiniteSeed
import Maxwell.Continuum.CalibrationGlobalLinear

/-! The finite seed has eight supported aliases.  The root convolution can
therefore use eight cache terms per output, without materializing a zero-filled
input cube.  This identity concerns the exact rational field. -/
namespace Maxwell.Continuum.Calibration.Supercell
open FreeFiber PeriodicSampling
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

variable (M : ℕ) [NeZero M]

def seedAlias (s : Corner.Parity) : Alias := join M (0,rationalCubeAlias s)

theorem seedAlias_injective : Function.Injective (seedAlias M) := by
  intro s t h
  have hp := (indexEquiv M).injective h
  exact rationalCubeAlias_injective (congrArg Prod.snd hp)

def seedCoefficient (N : ℕ) (s : Corner.Parity) (j : Fin 3) : RationalComplex :=
  (0,seedSign s j*seedComponent N j)

theorem finiteSeed_field (N : ℕ) :
    (finiteSeed M N).field=rationalPhase (rationalInjection M 0 (rationalSeed N)) :=
  FourierData.ofSupported_field
    (rationalPhase_supported (rationalInjection_supported M (rationalSeed_supported N) 0))

theorem finiteSeed_at (N : ℕ) (s : Corner.Parity) (j : Fin 3) :
    (finiteSeed M N).field (seedAlias M s) j=seedCoefficient N s j := by
  rw [finiteSeed_field]
  unfold rationalPhase seedAlias
  rw [rationalInjection_join]
  have hcentral := (rationalCentralCheck_true (rationalCubeAlias s)).mpr
    (CornerBridge.alias_central s)
  simp [rationalSeed,rationalExpandCoordinates,hcentral,rationalAliasParity_cube,
    rationalSeedCoordinates,rationalComplexMul,seedCoefficient]

theorem finiteSeed_off (N : ℕ) (ν : Alias)
    (hν : ¬∃s,ν=seedAlias M s) (j : Fin 3) : (finiteSeed M N).field ν j=0 := by
  obtain ⟨⟨k,ξ⟩,rfl⟩ := (indexEquiv M).surjective ν
  rw [finiteSeed_field]
  unfold rationalPhase
  change rationalComplexMul (0,1) (rationalInjection M 0 (rationalSeed N) (join M (k,ξ)) j)=0
  rw [rationalInjection_join]
  by_cases hk : k=0
  · subst k
    have hc : rationalCentralCheck ξ=false := by
      apply Bool.eq_false_iff.mpr
      intro hc
      obtain ⟨s,hs⟩ := CornerBridge.parityAliasEquiv.surjective
        ⟨ξ,(rationalCentralCheck_true ξ).mp hc⟩
      have he : rationalCubeAlias s=ξ := congrArg Subtype.val hs
      exact hν ⟨s,by rw [←he];rfl⟩
    simp [rationalSeed,rationalExpandCoordinates,hc,rationalComplexMul_zero]
  · simp [hk,rationalComplexMul_zero]

theorem finiteSeed_sparse (N : ℕ) (ν : Alias) (j : Fin 3) :
    (finiteSeed M N).field ν j=
      ∑s : Corner.Parity,if ν=seedAlias M s then seedCoefficient N s j else 0 := by
  by_cases hν : ∃s,ν=seedAlias M s
  · obtain ⟨s,rfl⟩ := hν
    rw [finiteSeed_at]
    simp [(seedAlias_injective M).eq_iff]
  · rw [finiteSeed_off M N ν hν]
    symm
    apply Finset.sum_eq_zero
    intro s _
    exact ite_eq_right (fun h => hν ⟨s,h⟩)

theorem rationalComplexMul_sum {ι : Type*} (s : Finset ι)
    (a : RationalComplex) (b : ι→RationalComplex) :
    rationalComplexMul a (∑i∈s,b i)=∑i∈s,rationalComplexMul a (b i) := by
  ext <;> simp [rationalComplexMul,Prod.fst_sum,Prod.snd_sum,Finset.mul_sum,Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

theorem convolution_sparse (D N : ℕ) (c : Alias→RationalComplex)
    (ν : Alias) (j : Fin 3) :
    rationalConvolution D c (finiteSeed M N).field ν j=
      ∑s : Corner.Parity,if ν-seedAlias M s∈Product.frequencyCube D then
        rationalComplexMul (c (ν-seedAlias M s)) (seedCoefficient N s j) else 0 := by
  unfold rationalConvolution
  simp_rw [finiteSeed_sparse M,rationalComplexMul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have he (n : Alias) : ν-n=seedAlias M s ↔ n=ν-seedAlias M s := by
    constructor <;> intro h <;>
      (ext k;have hk := congrFun h k;simp only [Pi.sub_apply] at hk ⊢;omega)
  simp_rw [apply_ite (rationalComplexMul _) _,rationalComplexMul_zero,he]
  simp

theorem rootApply_sparse (scale : ℚ) (N ell precision : ℕ) (ν : Alias) (j : Fin 3) :
    (FourierData.rootApply scale N ell (finiteSeed M precision)).field ν j=
      ∑s : Corner.Parity,if ν-seedAlias M s∈Product.frequencyCube (rootDegree scale N ell) then
        rationalComplexMul
          (rectangleRational (computedRootCoefficient scale N ell (ν-seedAlias M s)))
          (seedCoefficient precision s j) else 0 := by
  rw [GlobalPower.rootApply_field]
  exact convolution_sparse M (rootDegree scale N ell) precision _ ν j

#print axioms finiteSeed_sparse
#print axioms rootApply_sparse
end Maxwell.Continuum.Calibration.Supercell
