import Maxwell.Green.CalibrationBudget
import Maxwell.Green.CalibrationBitBounds
import Maxwell.Cost.CalibrationMatrix.Bounds

/-! Explicit bit growth of the requested coupling precision, including the
exponentially small nonzero axial coupling. -/
namespace Maxwell.Green
open Maxwell.Cost.CalibrationMatrix

/-- Reduction of a rational product cannot enlarge its common denominator. -/
theorem mul_den_size (q r : ℚ) : (q * r).den.size ≤ q.den.size + r.den.size := by
  have hd : (q * r).den ≤ q.den * r.den :=
    Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) (Rat.mul_den_dvd q r)
  apply (Nat.size_le_size hd).trans
  simpa only [pow_one, Nat.mul_one] using size_mul_pow_bound q.den r.den 1

theorem div_den_size (q r : ℚ) (hr : r ≠ 0) :
    (q / r).den.size ≤ q.den.size + r.num.natAbs.size := by
  simpa only [div_eq_mul_inv, Rat.den_inv_of_ne_zero hr] using mul_den_size q r⁻¹

theorem pow_den_size (q : ℚ) (n : ℕ) : (q ^ n).den.size ≤ 1 + q.den.size * n := by
  simpa only [Rat.den_pow, Nat.one_mul, Nat.size_one] using size_mul_pow_bound 1 q.den n

theorem min_den_size (q r : ℚ) : (min q r).den.size ≤ q.den.size + r.den.size := by
  by_cases h : q ≤ r
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (le_of_not_ge h)]
    omega

theorem axial_den_size (ζ c a : ℚ) (d : ℕ) :
    (min (ζ ^ 2) (c * a ^ d / 2)).den.size ≤
      2 * ζ.den.size + d * a.den.size + c.den.size + 4 := by
  have hm := min_den_size (ζ ^ 2) (c * a ^ d / 2)
  have hζ := pow_den_size ζ 2
  have ha := pow_den_size a d
  have hc := mul_den_size c (a ^ d)
  have hd := div_den_size (c * a ^ d) 2 (by norm_num)
  norm_num at hd
  have htwo : Nat.size 2 = 2 := by decide
  rw [htwo] at hd
  rw [Nat.mul_comm a.den.size d] at ha
  omega

end Maxwell.Green

namespace Maxwell.Composition.PhysicalPlatform

/-- Fixed platform overhead, independent of source position, precision and
axial distance. -/
def couplingBitOverhead (P : PhysicalPlatform) : ℕ :=
  P.spacing.c.den.size + 4 + P.couplingErrorConstant.num.natAbs.size

/-- Axial nonvanishing costs only linearly many precision bits in distance,
even though the true coupling may decay exponentially with that distance. -/
theorem couplingPrecision_axial_bound (P : PhysicalPlatform) (ζ : ℚ) (d : ℕ) :
    P.couplingPrecision (P.axialBudget ζ d) ≤
      2 * ζ.den.size + d * P.spacing.a.den.size + P.couplingBitOverhead := by
  have hd := Green.div_den_size (P.axialBudget ζ d) P.couplingErrorConstant
    P.couplingErrorConstant_pos.ne'
  have ha := Green.axial_den_size ζ P.spacing.c P.spacing.a d
  unfold couplingPrecision Green.denominatorPrecision
  unfold axialBudget at hd ⊢
  unfold couplingBitOverhead
  omega

/-- The certified polynomial degree inherits the same explicit linear bound. -/
theorem calibrationDegree_axial_bound (P : PhysicalPlatform) (ζ : ℚ) (d : ℕ) :
    P.calibrationDegree (P.couplingPrecision (P.axialBudget ζ d)) ≤
      Maxwell.Defect.FiniteStencil.precisionBlock P.calibrationGap P.rowBound
        P.calibrationGap_pos P.rowBound_pos P.calibrationGap_le *
      (2 * ζ.den.size + d * P.spacing.a.den.size + P.couplingBitOverhead + 1) := by
  unfold calibrationDegree Maxwell.Defect.FiniteStencil.precisionDegree
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (P.couplingPrecision_axial_bound ζ d) 1)

end Maxwell.Composition.PhysicalPlatform
