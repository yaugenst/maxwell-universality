import Maxwell.Continuum.WellResolvent
import Maxwell.Continuum.BlochDistributionRow

/-! The scalar Fourier inverse solves the literal distributional anisotropic
elliptic equation, with its full maximal L² domain. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory FourierTransform
open scoped SchwartzMap

set_option backward.isDefEq.respectTransparency false

def directionCoordinate (v : Space) (ξ : Space) : ℂ := inner ℝ ξ v

@[fun_prop] theorem directionCoordinate_temperate (v : Space) :
    (directionCoordinate v).HasTemperateGrowth := by
  unfold directionCoordinate
  fun_prop

def ellipticDerivative (H : Space →L[ℝ] Space) : ScalarDistribution →L[ℂ] ScalarDistribution :=
  1 - ∑ i : Fin 3, (LineDeriv.lineDerivOpCLM ℂ ScalarDistribution (coordinateDirection i)).comp
    (LineDeriv.lineDerivOpCLM ℂ ScalarDistribution (H (coordinateDirection i)))

def ellipticRow (H : Space →L[ℝ] Space) : Fin 4 → Space → ℂ :=
  ![fun _ => 1,
    -((2 * Real.pi * Complex.I) ^ 2) •
      (directionCoordinate (H (coordinateDirection 0)) * directionCoordinate (coordinateDirection 0)),
    -((2 * Real.pi * Complex.I) ^ 2) •
      (directionCoordinate (H (coordinateDirection 1)) * directionCoordinate (coordinateDirection 1)),
    -((2 * Real.pi * Complex.I) ^ 2) •
      (directionCoordinate (H (coordinateDirection 2)) * directionCoordinate (coordinateDirection 2))]

theorem ellipticRow_temperate (H : Space →L[ℝ] Space) (i : Fin 4) :
    (ellipticRow H i).HasTemperateGrowth := by
  fin_cases i <;> dsimp [ellipticRow] <;> fun_prop

theorem coordinate_expansion (ξ : Space) :
    (∑ i : Fin 3, ξ i • coordinateDirection i) = ξ := by
  apply PiLp.ext
  intro j
  simp [coordinateDirection, Pi.single_apply]

theorem elliptic_quadratic_expansion (H : Space →L[ℝ] Space) (ξ : Space) :
    inner ℝ ξ (H ξ) = ∑ i : Fin 3, inner ℝ ξ (H (coordinateDirection i)) * ξ i := by
  nth_rw 2 [← coordinate_expansion ξ]
  rw [map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, inner_smul_right]
  exact mul_comm _ _

theorem ellipticRow_value (H : Space →L[ℝ] Space) (u : ScalarL2) (ξ : Space) :
    Bloch.rowValue (ellipticRow H) (fun _ => u) ξ =
      ((1 + ellipticSymbol H ξ : ℝ) : ℂ) * u ξ := by
  have hc : (2 * Real.pi * Complex.I) ^ 2 = -(2 * (Real.pi : ℂ)) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  simp only [Bloch.rowValue, ellipticRow, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, directionCoordinate, coordinateDirection, EuclideanSpace.inner_single_right,
    ellipticSymbol, elliptic_quadratic_expansion, starRingEnd_apply, star_trivial, hc]
  push_cast
  ring

theorem ellipticDerivative_fourier_row (H : Space →L[ℝ] Space) (u : ScalarL2) :
    𝓕 (ellipticDerivative H (Lp.toTemperedDistribution u)) =
      Bloch.distributionRow (ellipticRow H) (fun _ => scalarFourier u) := by
  have hd (T : ScalarDistribution) (v : Space) :
      𝓕 (LineDeriv.lineDerivOp v T) = (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ (directionCoordinate v) (𝓕 T) :=
    TemperedDistribution.fourier_lineDerivOp_eq T v
  have hm (v w : Space) (T : ScalarDistribution) :
      TemperedDistribution.smulLeftCLM ℂ
        (-((2 * Real.pi * Complex.I) ^ 2) • (directionCoordinate v * directionCoordinate w)) T =
      -((2 * Real.pi * Complex.I) ^ 2) •
        TemperedDistribution.smulLeftCLM ℂ (directionCoordinate v * directionCoordinate w) T := by
    rw [TemperedDistribution.smulLeftCLM_smul
      ((directionCoordinate_temperate v).mul (directionCoordinate_temperate w))]
    rfl
  change (fourierCLM ℂ ScalarDistribution)
    (ellipticDerivative H (Lp.toTemperedDistribution u)) = _
  simp only [ellipticDerivative, sub_apply, one_apply_eq_self, sum_apply,
    ContinuousLinearMap.comp_apply, LineDeriv.lineDerivOpCLM_apply, map_sub, map_sum,
    fourierCLM_apply, hd, map_smul, smul_smul, ← pow_two,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (directionCoordinate_temperate _) (directionCoordinate_temperate _),
    Lp.fourier_toTemperedDistribution_eq]
  simp only [Bloch.distributionRow, ellipticRow, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, hm,
    TemperedDistribution.smulLeftCLM_const, one_smul]
  have hneg (a : ℂ) (T : ScalarDistribution) : (-a) • T = -(a • T) := neg_smul a T
  simp only [hneg, sub_eq_add_neg, neg_add]
  rfl

def WeakEllipticEquation (H : Space →L[ℝ] Space) (u f : ScalarL2) : Prop :=
  ellipticDerivative H (Lp.toTemperedDistribution u) = Lp.toTemperedDistribution f

theorem weakEllipticEquation_fourier_iff (H : Space →L[ℝ] Space) (u f : ScalarL2) :
    WeakEllipticEquation H u f ↔ EllipticFourierEquation H u f := by
  have hinj : Function.Injective (fun T : ScalarDistribution => 𝓕 T) := by
    intro T S h
    have hh := congrArg (fun U : ScalarDistribution => 𝓕⁻ U) h
    simpa only [fourierInv_fourier_eq] using hh
  unfold WeakEllipticEquation
  rw [← hinj.eq_iff, ellipticDerivative_fourier_row, Lp.fourier_toTemperedDistribution_eq]
  change Bloch.distributionRow (ellipticRow H) (fun _ => scalarFourier u) =
    Lp.toTemperedDistribution (scalarFourier f) ↔ _
  rw [Bloch.distributionRow_eq_iff _ (ellipticRow_temperate H)]
  have he : Bloch.rowValue (ellipticRow H) (fun _ => scalarFourier u) =
      fun ξ => ((1 + ellipticSymbol H ξ : ℝ) : ℂ) * scalarFourier u ξ :=
    funext (ellipticRow_value H (scalarFourier u))
  rw [he]
  rfl

theorem weakEllipticEquation_iff (H : Space →L[ℝ] Space)
    (hH : ∀ ξ, 0 ≤ inner ℝ ξ (H ξ)) (u f : ScalarL2) :
    WeakEllipticEquation H u f ↔ u = resolvent H hH f := by
  rw [weakEllipticEquation_fourier_iff, ellipticFourierEquation_iff H hH]

theorem resolvent_weak_solution (H : Space →L[ℝ] Space)
    (hH : ∀ ξ, 0 ≤ inner ℝ ξ (H ξ)) (f : ScalarL2) :
    WeakEllipticEquation H (resolvent H hH f) f :=
  (weakEllipticEquation_iff H hH _ _).mpr rfl

end Maxwell.Continuum.Well
