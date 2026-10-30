import Maxwell.Continuum.CalibrationSupercellFourier
import Maxwell.Continuum.CalibrationTorusConvolution

/-! Multiplication by an actual continuous supercell coefficient agrees
with its full alias-space Fourier multiplier under the physical embedding. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set

variable (M : ℕ) [NeZero M]

def physicalMultiplierCLM : C(Torus,ℂ) →L[ℂ] (FieldL2 →L[ℂ] FieldL2) :=
  DiagonalMap.diagonalCLM.comp
    (CompactCoefficient.coefficientMap (μ := (volume : Measure Space))
      (torusPoint M) (torusPoint_measurable M))

def physicalMultiplier (f : C(Torus,ℂ)) : FieldL2 →L[ℂ] FieldL2 := physicalMultiplierCLM M f

omit [NeZero M] in
theorem physicalMultiplier_ae (f : C(Torus,ℂ)) (u : FieldL2) (i : Fin 3) :
    physicalMultiplier M f u i =ᵐ[volume] fun x => f (torusPoint M x)*u i x :=
  CompactCoefficient.multiplier_ae (torusPoint M) (torusPoint_measurable M) f (u i)

theorem shift_single (n k : Alias) (v : Polarization) :
    shift (-n) (lp.single 2 k v)=lp.single 2 (n+k) v := by
  classical
  apply lp.ext
  funext m
  rw [shift_apply]
  simp only [lp.coeFn_single,Pi.single_apply]
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination h

theorem embedding_character_single (hEven : Even M) (n k : Alias) (v : Polarization) :
    embedding M (shift (-n) (lp.single 2 k v))=
      physicalMultiplier M (mFourier n) (embedding M (lp.single 2 k v)) := by
  classical
  rw [shift_single]
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [embedding_single_ae M hEven (n+k) v i,
    embedding_single_ae M hEven k v i,
    physicalMultiplier_ae M (mFourier n) (embedding M (lp.single 2 k v)) i]
      with x hnk hk hm
  rw [hnk,hm,hk]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : x∈spatialBox (representative M a)
  · rw [indicator_of_mem hx,indicator_of_mem hx,mFourier_add]
    ring
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero]

theorem embedding_character (hEven : Even M) (n : Alias) (u : FiberSpace) :
    embedding M (shift (-n) u)=physicalMultiplier M (mFourier n) (embedding M u) := by
  have he : (embedding M).toContinuousLinearMap.comp (shift (-n))=
      (physicalMultiplier M (mFourier n)).comp (embedding M).toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (p := 2) (E := fun _ : Alias => Polarization)
      ENNReal.ofNat_ne_top
    intro k
    apply ContinuousLinearMap.ext
    intro v
    exact embedding_character_single M hEven n k v
  exact congrArg (fun A : FiberSpace →L[ℂ] FieldL2 => A u) he

theorem embedding_multiplier (hEven : Even M) (f : C(Torus,ℂ))
    (hf : Summable (mFourierCoeff f)) (u : FiberSpace) :
    embedding M (aliasMultiplier f u)=physicalMultiplier M f (embedding M u) := by
  have hs := hasSum_mFourier_series_of_summable hf
  have hl := ((embedding M).toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℂ FiberSpace u).comp aliasMultiplierCLM)).hasSum hs
  have hr := ((ContinuousLinearMap.apply ℂ FieldL2 (embedding M u)).comp
    (physicalMultiplierCLM M)).hasSum hs
  apply hl.unique
  convert hr using 1
  · funext n
    simp only [ContinuousLinearMap.comp_apply,map_smul]
    change mFourierCoeff f n • embedding M (aliasMultiplier (mFourier n) u)=
      mFourierCoeff f n • physicalMultiplier M (mFourier n) (embedding M u)
    congr 1
    change embedding M (CellFourier.unitary.symm
      (torusMultiplier (mFourier n) (CellFourier.unitary u)))=_
    rw [torusMultiplier_character]
    exact embedding_character M hEven n u
  · rfl

#print axioms embedding_multiplier

end Maxwell.Continuum.Calibration.Supercell
