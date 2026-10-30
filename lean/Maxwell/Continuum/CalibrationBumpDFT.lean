import Maxwell.Continuum.CalibrationBumpEvaluation
import Maxwell.Continuum.CalibrationBumpTorus
import Maxwell.Continuum.ChebyshevWaveDFT

/-! Executable rational tensor-grid sampling of the literal compact
well root. Every arithmetic output is rational; the exact sample and
character errors yield a certified coefficient error. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate PeriodicSampling UnitAddTorus

variable (grid : ℕ) [NeZero grid]

def rootSample (s : ℚ) (P : ℕ) (j : Fin 3 → ZMod grid) : ComplexRectangle :=
  ⟨rootApprox (fun i => s*centeredGrid grid (j i)) P, ⟨0,0,le_rfl⟩⟩

theorem rootSample_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (P : ℕ) (j : Fin 3 → ZMod grid) :
    ‖rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle))-
      rectangleCenter (rootSample grid s P j)‖ ≤ (1/2 : ℝ)^P := by
  change ‖(Well.qw ((s : ℝ) • WithLp.toLp 2 (centeredRepresentative
    (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle)))) : ℂ)-
      rectangleCenter (rootSample grid s P j)‖ ≤ _
  rw [centeredRepresentative_grid]
  have he : (s : ℝ) • (WithLp.toLp 2 (fun i => (centeredGrid grid (j i) : ℝ)) : Space) =
      WithLp.toLp 2 (fun i => ((s*centeredGrid grid (j i) : ℚ) : ℝ)) := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply, smul_eq_mul, Rat.cast_mul]
  rw [he]
  simp only [rectangleCenter, rootSample, Rat.cast_zero, zero_mul, add_zero,
    ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact rootApprox_error _ _

def rootProductSample (s : ℚ) (P : ℕ) (n : Fin 3 → ℤ) (j : Fin 3 → ZMod grid) : ComplexRectangle :=
  (productCharacterApprox grid P (-(Product.frequency grid n)) j).mul (rootSample grid s P j)

def rationalRootCoefficient (s : ℚ) (P : ℕ) (n : Fin 3 → ℤ) : ComplexRectangle :=
  ComplexRectangle.point
    (((grid : ℚ)^3)⁻¹*∑ j : Fin 3 → ZMod grid, (rootProductSample grid s P n j).re.center)
    (((grid : ℚ)^3)⁻¹*∑ j : Fin 3 → ZMod grid, (rootProductSample grid s P n j).im.center)

theorem rationalRootCoefficient_center (s : ℚ) (P : ℕ) (n : Fin 3 → ℤ) :
    rectangleCenter (rationalRootCoefficient grid s P n) =
      ((grid : ℂ)^3)⁻¹*∑ j : Fin 3 → ZMod grid,
        rectangleCenter (productCharacterApprox grid P (-(Product.frequency grid n)) j)*
        rectangleCenter (rootSample grid s P j) := by
  simp_rw [← Profile.rectangleCenter_mul]
  change rectangleCenter (rationalRootCoefficient grid s P n) =
    ((grid : ℂ)^3)⁻¹*∑ j : Fin 3 → ZMod grid, rectangleCenter (rootProductSample grid s P n j)
  simp only [rationalRootCoefficient, rectangleCenter, ComplexRectangle.point]
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem rationalRootCoefficient_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (P : ℕ) (n : Fin 3 → ℤ) :
    ‖Product.coefficient grid
      (fun j => rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle)))
        (Product.frequency grid n)-rectangleCenter (rationalRootCoefficient grid s P n)‖ ≤
      8*(1/2 : ℝ)^P := by
  have he (j : Fin 3 → ZMod grid) :
      ‖Product.character grid (-(Product.frequency grid n)) j*
          rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle))-
        rectangleCenter (productCharacterApprox grid P (-(Product.frequency grid n)) j)*
          rectangleCenter (rootSample grid s P j)‖ ≤ 8*(1/2 : ℝ)^P := by
    have hc := productCharacterApprox_error grid P (-(Product.frequency grid n)) j
    have hr := rootSample_error grid s hs P j
    have hp : (1/2 : ℝ)^P ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    apply Profile.wave_product_error (by positivity) hc
      (hr.trans (by nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) P]))
    · have ht := norm_sub_le_norm_sub_add_norm_sub
        (rectangleCenter (productCharacterApprox grid P (-(Product.frequency grid n)) j))
        (Product.character grid (-(Product.frequency grid n)) j) 0
      simp only [sub_zero, Product.character_norm] at ht
      rw [norm_sub_rev] at ht
      linarith
    · exact rootTorus_norm_le_one _ hs _
  rw [rationalRootCoefficient_center]
  simp only [Product.coefficient, Fintype.card_fin, smul_eq_mul, ← mul_sub,
    norm_mul]
  rw [norm_inv, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ((grid : ℝ)^3)⁻¹*∑ j : Fin 3 → ZMod grid,
        ‖Product.character grid (-(Product.frequency grid n)) j*
          rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle))-
        rectangleCenter (productCharacterApprox grid P (-(Product.frequency grid n)) j)*
          rectangleCenter (rootSample grid s P j)‖ := by
      gcongr
      convert! norm_sum_le Finset.univ (fun j : Fin 3 → ZMod grid =>
        Product.character grid (-(Product.frequency grid n)) j*
          rootTorus s hs (fun i => ((((j i).val : ℝ)/grid : ℝ) : UnitAddCircle))-
        rectangleCenter (productCharacterApprox grid P (-(Product.frequency grid n)) j)*
          rectangleCenter (rootSample grid s P j)) using 1
      rw [Finset.sum_sub_distrib]
      congr 2
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_univ]
      · intro j _
        rfl
    _ ≤ ((grid : ℝ)^3)⁻¹*∑ _j : Fin 3 → ZMod grid, 8*(1/2 : ℝ)^P := by
      gcongr with j _
      exact he j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, ZMod.card,
        Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (NeZero.ne (grid : ℝ))), one_mul]

#print axioms rationalRootCoefficient_error

end Maxwell.Continuum.Calibration
