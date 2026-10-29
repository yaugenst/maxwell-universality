import Maxwell.Continuum.CellSpatialTranslation

/-! Separation of the lattice Bloch phase into its fixed corner carrier
and the Euclidean Fourier phase of the cell displacement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier FreeFiber Bloch

theorem phase_neg_forward (a ξ : Space) : phase (-a) ξ = forwardPhase ξ a := by
  simp only [phase, forwardPhase, Real.fourierChar_apply, inner_neg_right, real_inner_comm ξ a,
    Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  ring

theorem latticePhase_angular (a : Bloch.Alias) (q : QuasiCell) :
    latticePhase a q = carrier (-latticeShift a) *
      Complex.exp ((-inner ℝ q.val (latticeShift a) : ℝ) * Complex.I) := by
  rw [latticePhase, phase_neg_forward, forwardPhase_alias]
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one]
  rw [carrier, ← Complex.exp_add]
  unfold spatialPhase
  congr 1
  simp only [quasiMomentum, CellGauge.corner, realMomentum, Pi.neg_apply, Pi.add_apply,
    PiLp.neg_apply, Finset.sum_neg_distrib, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, Fin.sum_univ_three, Complex.ofReal_add]
  ring

theorem star_carrier (x : Space) : star (carrier x) = carrier (-x) := by
  rw [carrier, carrier, Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, PiLp.neg_apply,
    Finset.sum_neg_distrib, mul_neg, Complex.ofReal_neg]
  congr 1
  ring

theorem star_realPhase (r : ℝ) :
    star (Complex.exp ((r : ℂ) * Complex.I)) = Complex.exp ((-r : ℝ) * Complex.I) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

theorem latticePhase_ratio (a b : Bloch.Alias) (q : QuasiCell) :
    star (latticePhase a q) * latticePhase b q =
      carrier (latticeShift a - latticeShift b) *
        Complex.exp ((-inner ℝ q.val (latticeShift b - latticeShift a) : ℝ) * Complex.I) := by
  rw [latticePhase_angular, latticePhase_angular, star_mul', star_carrier, neg_neg,
    star_realPhase, neg_neg]
  have hm (A B C D : ℂ) : (A * B) * (C * D) = (A * C) * (B * D) := by ring
  rw [hm, ← carrier_add, ← Complex.exp_add]
  congr 1
  congr 1
  simp only [inner_sub_right, Complex.ofReal_neg, Complex.ofReal_sub]
  ring

#print axioms latticePhase_ratio

end Maxwell.Continuum.CellGauge
