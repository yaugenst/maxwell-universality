import Maxwell.Continuum.FourierSobolevCharacterization
import Maxwell.Continuum.FiberMultiplier
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! A concrete Bessel weight for simultaneous approximation of a field
and its three weak first derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform

def sobolevWeight (ξ : Space) : ℝ := Real.sqrt (1+‖ξ‖^2)

theorem sobolevWeight_pos (ξ : Space) : 0 < sobolevWeight ξ :=
  Real.sqrt_pos.mpr (by positivity)

theorem sobolevWeight_sq (ξ : Space) : sobolevWeight ξ^2 = 1+‖ξ‖^2 :=
  Real.sq_sqrt (by positivity)

theorem sobolevWeight_one_le (ξ : Space) : 1 ≤ sobolevWeight ξ :=
  Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg ‖ξ‖])

theorem sobolevWeight_norm_le (ξ : Space) : ‖ξ‖ ≤ sobolevWeight ξ :=
  Real.le_sqrt_of_sq_le (by linarith)

theorem sobolevWeight_continuous : Continuous sobolevWeight :=
  Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))

theorem inverseSobolevWeight_temperate :
    (fun ξ : Space => ((sobolevWeight ξ)⁻¹ : ℂ)).HasTemperateGrowth := by
  have he : (fun ξ : Space => ((sobolevWeight ξ)⁻¹ : ℂ)) =
      fun ξ : Space => (((1+‖ξ‖^2)^(-(1/2 : ℝ)) : ℝ) : ℂ) := by
    funext ξ
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+‖ξ‖^2), ← Real.sqrt_eq_rpow]
    simp only [sobolevWeight, Complex.ofReal_inv]
  rw [he]
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space _)

theorem derivativeFactor_norm (j : Fin 3) (ξ : Space) :
    ‖derivativeFactor j ξ‖ = 2*Real.pi*|ξ j| := by
  simp only [derivativeFactor, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem coordinateProduct_memLp (F : ScalarL2)
    (hF : ∀ j, MemLp (fun ξ => derivativeFactor j ξ*F ξ) 2 volume) (j : Fin 3) :
    MemLp (fun ξ => (ξ j : ℂ)*F ξ) 2 volume := by
  have hC : (2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  convert (hF j).const_smul (2*(Real.pi : ℂ)*Complex.I)⁻¹ using 1
  funext ξ
  simp only [Pi.smul_apply, smul_eq_mul, derivativeFactor]
  rw [← mul_assoc, inv_mul_cancel_left₀ hC]

theorem weightedProduct_memLp (F : ScalarL2)
    (hF : ∀ j, MemLp (fun ξ => derivativeFactor j ξ*F ξ) 2 volume) :
    MemLp (fun ξ => (sobolevWeight ξ : ℂ)*F ξ) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.continuous_ofReal.comp sobolevWeight_continuous).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable F))).mpr
  have he (ξ : Space) : ‖(sobolevWeight ξ : ℂ)*F ξ‖^2 =
      ‖F ξ‖^2+∑ j : Fin 3, ‖(ξ j : ℂ)*F ξ‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, sobolevWeight_sq,
      add_mul, one_mul, EuclideanSpace.norm_sq_eq, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [norm_mul, mul_pow, Complex.norm_real]
  change Integrable (fun ξ => ‖(sobolevWeight ξ : ℂ)*F ξ‖^2) volume
  rw [show (fun ξ => ‖(sobolevWeight ξ : ℂ)*F ξ‖^2) =
    (fun ξ => ‖F ξ‖^2+∑ j : Fin 3, ‖(ξ j : ℂ)*F ξ‖^2) from funext he]
  exact (Lp.memLp F).norm.integrable_sq.add
    (integrable_finsetSum _ fun j _ => (coordinateProduct_memLp F hF j).norm.integrable_sq)

def weightedL2 (F : ScalarL2)
    (hF : ∀ j, MemLp (fun ξ => derivativeFactor j ξ*F ξ) 2 volume) : ScalarL2 :=
  (weightedProduct_memLp F hF).toLp _

theorem weightedL2_ae (F : ScalarL2)
    (hF : ∀ j, MemLp (fun ξ => derivativeFactor j ξ*F ξ) 2 volume) :
    weightedL2 F hF =ᵐ[volume] fun ξ => (sobolevWeight ξ : ℂ)*F ξ :=
  MemLp.coeFn_toLp _

#print axioms weightedProduct_memLp

end Maxwell.Continuum.FourierSobolev
