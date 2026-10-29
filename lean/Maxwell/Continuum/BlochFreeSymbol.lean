import Maxwell.Continuum.BlochDistributionRow

/-! The exact continuum curl-curl symbol, retaining every longitudinal polarization. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def frequencyCoordinate (i : Fin 3) (ξ : Space) : ℂ := ξ i

@[fun_prop] theorem frequencyCoordinate_temperate (i : Fin 3) :
    (frequencyCoordinate i).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : Space →L[ℝ] ℝ).hasTemperateGrowth

theorem coordinateMultiplier_eq (i : Fin 3) :
    coordinateMultiplier i = TemperedDistribution.smulLeftCLM ℂ (frequencyCoordinate i) := by
  have h : (fun ξ : Space => (inner ℝ ξ (coordinateDirection i) : ℂ)) = frequencyCoordinate i := by
    funext ξ
    simp [coordinateDirection, EuclideanSpace.inner_single_right, frequencyCoordinate]
  exact congrArg (TemperedDistribution.smulLeftCLM ℂ) h

def fourierDerivativeConstant : ℂ := 2 * Real.pi * Complex.I

def curlCurlCoefficients (E : ℂ) (i : Fin 3) : Fin 5 → Space → ℂ :=
  ![fourierDerivativeConstant ^ 2 • (frequencyCoordinate i * frequencyCoordinate (i + 1)),
    -(fourierDerivativeConstant ^ 2) • (frequencyCoordinate (i + 1) * frequencyCoordinate (i + 1)),
    -(fourierDerivativeConstant ^ 2) • (frequencyCoordinate (i + 2) * frequencyCoordinate (i + 2)),
    fourierDerivativeConstant ^ 2 • (frequencyCoordinate i * frequencyCoordinate (i + 2)),
    fun _ => -E]

def curlCurlInputs (u : FieldL2) (i : Fin 3) : Fin 5 → ScalarL2 :=
  ![u (i + 1), u i, u i, u (i + 2), u i]

theorem curlCurlCoefficients_temperate (E : ℂ) (i : Fin 3) (j : Fin 5) :
    (curlCurlCoefficients E i j).HasTemperateGrowth := by
  fin_cases j <;> dsimp [curlCurlCoefficients] <;> fun_prop

theorem frequencyCross_twice_row (E : ℂ) (u : FieldL2) (i : Fin 3) :
    fourierDerivativeConstant ^ 2 • frequencyCross (frequencyCross (fieldDistribution u)) i -
      E • fieldDistribution u i =
        distributionRow (curlCurlCoefficients E i) (curlCurlInputs u i) := by
  have h11 : i + 1 + 1 = i + 2 := by omega
  have h12 : i + 1 + 2 = i := by omega
  have h21 : i + 2 + 1 = i := by omega
  have h22 : i + 2 + 2 = i + 1 := by omega
  have hm (j k : Fin 3) (c : ℂ) :
      TemperedDistribution.smulLeftCLM ℂ (c • (frequencyCoordinate j * frequencyCoordinate k)) =
        c • TemperedDistribution.smulLeftCLM ℂ (frequencyCoordinate j * frequencyCoordinate k) :=
    TemperedDistribution.smulLeftCLM_smul
      ((frequencyCoordinate_temperate j).mul (frequencyCoordinate_temperate k)) c
  simp only [frequencyCross_apply, map_sub, h11, h12, h21, h22,
    fieldDistribution_apply, coordinateMultiplier_eq,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (frequencyCoordinate_temperate _) (frequencyCoordinate_temperate _)]
  simp only [distributionRow, curlCurlCoefficients, curlCurlInputs, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [hm, smul_apply, TemperedDistribution.smulLeftCLM_const]
  simp only [smul_sub]
  module

def physicalMomentum (ξ : Space) : FreeFiber.Momentum := fun i => 2 * Real.pi * (ξ i : ℂ)

def pointPolarization (u : FieldL2) (ξ : Space) : FreeFiber.Polarization :=
  WithLp.toLp 2 (fun i => u i ξ)

/-- The five literal derivative terms are the full p²I−ppᵀ−EI matrix, including its kernel. -/
theorem curlCurl_rowValue_eq_block (E : ℂ) (u : FieldL2) (ξ : Space) (i : Fin 3) :
    rowValue (curlCurlCoefficients E i) (curlCurlInputs u i) ξ =
      FreeFiber.block (physicalMomentum ξ) E (pointPolarization u ξ) i := by
  have hc : fourierDerivativeConstant ^ 2 = -(2 * (Real.pi : ℂ)) ^ 2 := by
    simp only [fourierDerivativeConstant, mul_pow, Complex.I_sq]
    ring
  change rowValue (curlCurlCoefficients E i) (curlCurlInputs u i) ξ =
    ∑ j : Fin 3, FreeFiber.blockMatrix (physicalMomentum ξ) E i j * u j ξ
  fin_cases i <;>
    simp [rowValue, curlCurlCoefficients, curlCurlInputs, frequencyCoordinate, hc,
      FreeFiber.blockMatrix, FreeFiber.momentumSquare, FreeFiber.momentumOuter,
      Matrix.vecMulVec, physicalMomentum, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem frequencyCross_twice_eq_iff (E : ℂ) (u v : FieldL2) :
    fourierDerivativeConstant ^ 2 • frequencyCross (frequencyCross (fieldDistribution u)) -
      E • fieldDistribution u = fieldDistribution v ↔
      ∀ i : Fin 3, (fun ξ => FreeFiber.block (physicalMomentum ξ) E (pointPolarization u ξ) i)
        =ᵐ[volume] v i := by
  constructor
  · intro h i
    have hi := congrFun h i
    change fourierDerivativeConstant ^ 2 • frequencyCross (frequencyCross (fieldDistribution u)) i -
      E • fieldDistribution u i = Lp.toTemperedDistribution (v i) at hi
    rw [frequencyCross_twice_row] at hi
    have hr := (distributionRow_eq_iff _ (curlCurlCoefficients_temperate E i) _ (v i)).mp hi
    filter_upwards [hr] with ξ hξ
    simpa only [curlCurl_rowValue_eq_block] using hξ
  · intro h
    funext i
    change fourierDerivativeConstant ^ 2 • frequencyCross (frequencyCross (fieldDistribution u)) i -
      E • fieldDistribution u i = Lp.toTemperedDistribution (v i)
    rw [frequencyCross_twice_row, distributionRow_eq_iff _ (curlCurlCoefficients_temperate E i)]
    filter_upwards [h i] with ξ hξ
    simpa only [curlCurl_rowValue_eq_block] using hξ

end Maxwell.Continuum.Bloch
