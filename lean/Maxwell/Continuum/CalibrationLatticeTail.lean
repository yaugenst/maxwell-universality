import Maxwell.Continuum.CalibrationLatticeDecay

/-! A quantitative complete three-dimensional Fourier-index tail. It
applies at every positive decay rate, including rescaled broad wells. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

def latticeTail (a R : ℝ) (j : Fin 3 → ℤ) : ℝ :=
  if R ≤ (imageRadius j : ℝ) then Real.exp (-a*Real.sqrt (imageRadius j)) else 0

theorem latticeTail_nonneg (a R : ℝ) (j : Fin 3 → ℤ) : 0 ≤ latticeTail a R j := by
  unfold latticeTail
  split_ifs <;> positivity

theorem latticeTail_majorant {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (j : Fin 3 → ℤ) :
    latticeTail a R j ≤ Real.exp (-(a/2)*Real.sqrt R)*latticeDecayConstant (a/2)*latticeWeight j := by
  by_cases hj : R ≤ (imageRadius j : ℝ)
  · rw [latticeTail, ite_eq_left hj]
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      have hz : imageRadius (0 : Fin 3 → ℤ) = 0 := by simp [imageRadius]
      rw [hz, Nat.cast_zero] at hj
      linarith
    have hs : Real.sqrt R ≤ Real.sqrt (imageRadius j) := Real.sqrt_le_sqrt hj
    have he : Real.exp (-a*Real.sqrt (imageRadius j)) ≤
        Real.exp (-(a/2)*Real.sqrt R)*Real.exp (-(a/2)*Real.sqrt (imageRadius j)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    exact he.trans ((mul_le_mul_of_nonneg_left
      (stretched_lattice_majorant (div_pos ha (by norm_num)) j hj0) (Real.exp_pos _).le).trans_eq
        (mul_assoc _ _ _).symm)
  · rw [latticeTail, ite_eq_right hj]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (latticeDecayConstant_nonneg (div_pos ha (by norm_num)))) (latticeWeight_nonneg j)

theorem latticeTail_summable {a R : ℝ} (ha : 0 < a) (hR : 0 < R) : Summable (latticeTail a R) :=
  Summable.of_nonneg_of_le (latticeTail_nonneg a R) (latticeTail_majorant ha hR)
    (latticeWeight_summable.mul_left (Real.exp (-(a/2)*Real.sqrt R)*latticeDecayConstant (a/2)))

theorem latticeTail_sum_bound {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ∑' j : Fin 3 → ℤ, latticeTail a R j ≤
      64*latticeDecayConstant (a/2)*Real.exp (-(a/2)*Real.sqrt R) := by
  calc
    _ ≤ ∑' j : Fin 3 → ℤ,
        (Real.exp (-(a/2)*Real.sqrt R)*latticeDecayConstant (a/2))*latticeWeight j :=
      (latticeTail_summable ha hR).tsum_le_tsum (latticeTail_majorant ha hR)
        (latticeWeight_summable.mul_left _)
    _ = (Real.exp (-(a/2)*Real.sqrt R)*latticeDecayConstant (a/2))*(∑' j, latticeWeight j) := tsum_mul_left
    _ ≤ (Real.exp (-(a/2)*Real.sqrt R)*latticeDecayConstant (a/2))*64 :=
      mul_le_mul_of_nonneg_left latticeWeight_tsum_le
        (mul_nonneg (Real.exp_pos _).le (latticeDecayConstant_nonneg (div_pos ha (by norm_num))))
    _ = _ := by ring

#print axioms latticeTail_sum_bound

end Maxwell.Continuum.Calibration
