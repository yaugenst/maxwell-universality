import Maxwell.Continuum.CellSourceRescaling

/-! Exact exponential phase and axial frequency after q=h k. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand EffectiveMass Auxiliary AlmostAnalytic

theorem complexPhase_shifted_value (R q β : Space) (s : ℝ) :
    complexPhase R (AlmostAnalytic.shiftedMomentum q β s) =
      (Real.exp (-s*inner ℝ β R) : ℂ)*OperatorFourier.angularPhase q (-R) := by
  rw [Complex.ofReal_exp, OperatorFourier.angularPhase, ← Complex.exp_add, complexPhase]
  congr 1
  simp only [AlmostAnalytic.shiftedMomentum, realMomentumMap, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, Complex.ofRealCLM_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, Fin.sum_univ_three, PiLp.neg_apply,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
  calc
    _ = (I*I)*((s : ℂ)*((β 0 : ℂ)*(R 0 : ℂ)+(β 1 : ℂ)*(R 1 : ℂ)+(β 2 : ℂ)*(R 2 : ℂ)))+
        I*((q 0 : ℂ)*(R 0 : ℂ)+(q 1 : ℂ)*(R 1 : ℂ)+(q 2 : ℂ)*(R 2 : ℂ)) := by ring
    _ = _ := by rw [I_mul_I]; ring

theorem poleAxialDisplacement_scaled {h : ℝ} (hh : 0 < h) (d : ℝ) (j : Fin 3) :
    h • poleAxialDisplacement h d j = (2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1 := by
  apply PiLp.ext
  intro i
  by_cases hij : i = j
  · subst i
    simp only [poleAxialDisplacement, PiLp.smul_apply, PiLp.single_apply, ↓reduceIte, smul_eq_mul, mul_one]
    field_simp
  · simp only [poleAxialDisplacement, PiLp.smul_apply, PiLp.single_apply,
      ite_eq_right hij, smul_eq_mul, mul_zero]

theorem angularPhase_rescale (h : ℝ) (k R : Space) :
    OperatorFourier.angularPhase (h • k) (-R) = OperatorFourier.angularPhase k (-(h • R)) := by
  unfold OperatorFourier.angularPhase
  rw [inner_neg_right, inner_neg_right, real_inner_smul_left, real_inner_smul_right]

theorem poleContour_scaled_phase {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (d : ℝ) (k : Space) :
    complexPhase (poleAxialDisplacement h d j)
      (AlmostAnalytic.shiftedMomentum (h • k) (poleContourShift D hh j) 1) =
      (Real.exp (-poleAction D hh j*d) : ℂ)*
        OperatorFourier.angularPhase k (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1) := by
  rw [complexPhase_shifted_value, poleContourShift_axial_phase, angularPhase_rescale,
    poleAxialDisplacement_scaled D.h_pos, neg_smul]
  congr 2
  simp only [neg_mul, one_mul]

#print axioms poleContour_scaled_phase

end Maxwell.Continuum.CellGauge
