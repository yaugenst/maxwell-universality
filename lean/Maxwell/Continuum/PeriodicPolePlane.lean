import Maxwell.Continuum.PeriodicPoleCubic
import Maxwell.Continuum.TransverseGaussianDiagonal

/-! The actual pole phase on the real transverse integration plane. Its
quadratic form is positive and diagonal in the two surviving coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric TransverseGaussian

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  transversePole transverseCoefficient poleQuadratic

def transverseMomentum (j : Fin 3) (x : Plane) : Momentum :=
  j.insertNth 0 (fun k => (x k : ℂ))

@[simp] theorem transverseMomentum_same (j : Fin 3) (x : Plane) :
    transverseMomentum j x j = 0 := Fin.insertNth_apply_same _ _ _

@[simp] theorem transverseMomentum_other (j : Fin 3) (x : Plane) (k : Fin 2) :
    transverseMomentum j x (j.succAbove k) = (x k : ℂ) := Fin.insertNth_apply_succAbove _ _ _ _

theorem transverseMomentum_norm (j : Fin 3) (x : Plane) : ‖transverseMomentum j x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro k
  by_cases hkj : k = j
  · subst k
    simp only [transverseMomentum_same, norm_zero, norm_nonneg]
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hkj
    simpa only [transverseMomentum_other, Complex.norm_real] using PiLp.norm_apply_le x l

theorem transverseMomentum_continuous (j : Fin 3) : Continuous (transverseMomentum j) := by
  apply continuous_pi
  intro k
  by_cases hkj : k = j
  · subst k
    simp only [transverseMomentum_same]
    exact continuous_const
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hkj
    simp only [transverseMomentum_other]
    exact Complex.continuous_ofReal.comp (PiLp.continuous_apply _ l)

theorem transverseMomentum_zero (j : Fin 3) : transverseMomentum j 0 = 0 := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp only [transverseMomentum_same, Pi.zero_apply]
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hkj
    simp only [transverseMomentum_other, PiLp.zero_apply, Complex.ofReal_zero, Pi.zero_apply]

def poleGaussianHessian {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Fin 2) : ℝ :=
  transverseHessian j (j.succAbove k) (imaginaryPole D hh j)

theorem poleGaussianHessian_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Fin 2) :
    (2 : ℝ)^98 < poleGaussianHessian D hh j k ∧ poleGaussianHessian D hh j k < (2 : ℝ)^110 :=
  imaginaryPole_transverseHessian_bounds D hh j _ (Fin.ne_succAbove j k)

theorem imaginaryPole_transverseCoefficient_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j k : Fin 3) (hjk : j ≠ k) :
    transverseCoefficient j k ((imaginaryPole D hh j : ℂ) * Complex.I) =
      ((transverseHessian j k (imaginaryPole D hh j) / 2 : ℝ) : ℂ) := by
  have hβ : |imaginaryPole D hh j| < analyticRadius := by
    rw [abs_of_pos (imaginaryPole_pos D hh j)]
    exact (imaginaryPole_mem_small D hh j).2.trans_lt
      ((imaginary_scale_bounds D.h_pos.le hh).1.trans_lt (by linarith only [analyticRadius_pos]))
  apply Complex.ext
  · simp only [Complex.ofReal_re, transverseHessian]
    ring
  · simp only [Complex.ofReal_im, transverseCoefficient_im_zero j k hjk hβ]

theorem poleQuadratic_real_plane {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (x : Plane) :
    poleQuadratic D hh j (transverseMomentum j x) =
      ((∑ k : Fin 2, poleGaussianHessian D hh j k * (x k)^2 / 2 : ℝ) : ℂ) := by
  unfold poleQuadratic
  rw [Fin.sum_univ_succAbove _ j]
  simp only [ite_true, zero_add, ite_eq_right (Fin.succAbove_ne j _), transverseMomentum_other]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [imaginaryPole_transverseCoefficient_real D hh j _ (Fin.ne_succAbove j k)]
  unfold poleGaussianHessian
  push_cast
  ring

theorem poleQuadraticPhase_real_plane {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (x : Plane) :
    poleQuadraticPhase D hh j (transverseMomentum j x) =
      Complex.I * (diagonalQuadratic (poleGaussianHessian D hh j) (poleSlope D hh j) x : ℝ) := by
  unfold poleQuadraticPhase
  rw [poleQuadratic_real_plane]
  unfold diagonalQuadratic
  rw [Finset.sum_div]
  push_cast
  have hc : (poleSlope D hh j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (lt_trans (by norm_num : (0 : ℝ) < 1) (poleSlope_bounds D hh j).1).ne'
  field_simp [hc, Complex.I_ne_zero]
  simp only [Complex.I_sq]
  ring

theorem poleGaussian_quadratic_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (x : Plane) :
    (2 : ℝ)^(-15 : ℤ) * ‖x‖^2 ≤
      diagonalQuadratic (poleGaussianHessian D hh j) (poleSlope D hh j) x := by
  have hs : (2 : ℝ)^98 * ‖x‖^2 ≤ ∑ k : Fin 2, poleGaussianHessian D hh j k * (x k)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
      (poleGaussianHessian_bounds D hh j k).1.le (sq_nonneg _)
  unfold diagonalQuadratic
  apply (le_div_iff₀ (by linarith only [(poleSlope_bounds D hh j).1] : 0 < 2 * poleSlope D hh j)).mpr
  apply le_trans _ hs
  have hc : (2 : ℝ)^(-15 : ℤ) * (2 * poleSlope D hh j) ≤ (2 : ℝ)^98 := by
    calc
      _ ≤ (2 : ℝ)^(-15 : ℤ) * (2 * (2 : ℝ)^112) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (poleSlope_bounds D hh j).2.le (by norm_num)) (by positivity)
      _ = _ := by norm_num
  nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)]

def polePlanePhase {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (x : Plane) : ℂ :=
  transversePole D hh j (transverseMomentum j x)

theorem polePlanePhase_cubic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {x : Plane} (hx : ‖x‖ < transversePoleRadius) :
    ‖polePlanePhase D hh j x - Complex.I *
      (diagonalQuadratic (poleGaussianHessian D hh j) (poleSlope D hh j) x : ℝ)‖ ≤
      (2 : ℝ)^246 * ‖x‖^3 := by
  have he := transversePole_cubic D hh j ((transverseMomentum_norm j x).trans_lt hx)
  rw [poleQuadraticPhase_real_plane] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (transverseMomentum_norm j x) 3) (by positivity))

def poleGaussianRadius : ℝ := (2^4096 : ℝ)⁻¹

theorem poleGaussianRadius_pos : 0 < poleGaussianRadius := by unfold poleGaussianRadius; positivity

theorem poleGaussianRadius_lt : poleGaussianRadius < transversePoleRadius := by
  norm_num [poleGaussianRadius, transversePoleRadius]

theorem polePlanePhase_damping {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {x : Plane} (hx : ‖x‖ ≤ poleGaussianRadius) :
    (2 : ℝ)^(-256 : ℤ) * ‖x‖^2 ≤ (polePlanePhase D hh j x).im := by
  have he := (Complex.abs_im_le_norm (polePlanePhase D hh j x - Complex.I *
    (diagonalQuadratic (poleGaussianHessian D hh j) (poleSlope D hh j) x : ℝ))).trans
    (polePlanePhase_cubic D hh j (hx.trans_lt poleGaussianRadius_lt))
  simp only [Complex.sub_im, Complex.I_mul_im, Complex.ofReal_re] at he
  have he' := (abs_le.mp he).1
  have hq := poleGaussian_quadratic_lower D hh j x
  have hc : (2 : ℝ)^246 * poleGaussianRadius ≤ (2 : ℝ)^(-15 : ℤ) - (2 : ℝ)^(-256 : ℤ) := by
    norm_num [poleGaussianRadius]
  have hb := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hx (by positivity)).trans hc) (sq_nonneg ‖x‖)
  nlinarith only [he', hq, hb]

end Maxwell.Continuum.PeriodicBand
