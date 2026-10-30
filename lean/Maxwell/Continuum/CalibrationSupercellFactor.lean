import Maxwell.Continuum.CalibrationSupercellEmbedding
import Maxwell.Continuum.RationalSquareRootWidths
import Maxwell.Continuum.RationalFiniteWidths

/-! Executable rational approximation of the physical Fourier
normalization, with linear word bounds and relative scaling accuracy. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber RationalWords

def physicalFactorSquare (M : ℕ) : ℚ := (8*(M : ℚ)^3)⁻¹

def physicalFactorApprox (M P : ℕ) : ℚ := sqrtRationalCenter (physicalFactorSquare M) P

variable (M : ℕ) [NeZero M]

omit [NeZero M] in
theorem physicalFactorSquare_nonneg : 0≤physicalFactorSquare M := by
  unfold physicalFactorSquare
  positivity

theorem physicalFactorSquare_width : Width (physicalFactorSquare M) (3*M.bits.length+8) := by
  have hm : Width (M : ℚ) (M.bits.length+1) := by
    simpa only [Int.natAbs_natCast,Int.cast_natCast] using width_int (M : ℤ)
  have h8 : Width 8 4 := by constructor <;> decide
  have hM : (0 : ℚ)<M := by exact_mod_cast NeZero.pos M
  exact ((h8.mul (hm.pow 3)).inv (by positivity)).mono (by omega)

theorem physicalFactorApprox_width (P : ℕ) :
    Width (physicalFactorApprox M P) (6*M.bits.length+P+19) := by
  exact (sqrtRationalCenter_width (physicalFactorSquare_width M) P).mono (by omega)

noncomputable section

theorem physicalFactor_sq_rational : physicalFactor M^2=(physicalFactorSquare M : ℝ) := by
  have hM : (0 : ℝ)<M := by exact_mod_cast NeZero.pos M
  simp only [physicalFactorSquare,Rat.cast_inv,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]
  apply (mul_eq_one_iff_eq_inv₀ (by positivity : (8 : ℝ)*(M : ℝ)^3≠0)).mp
  rw [← mul_assoc]
  exact physicalFactor_square M

theorem physicalFactor_sqrt : physicalFactor M=Real.sqrt (physicalFactorSquare M : ℝ) := by
  rw [← physicalFactor_sq_rational,Real.sqrt_sq (physicalFactor_pos M).le]

theorem physicalFactorApprox_error (P : ℕ) :
    |(physicalFactorApprox M P : ℝ)-physicalFactor M|≤(1/2 : ℝ)^P := by
  rw [physicalFactor_sqrt]
  exact sqrtRational_error (physicalFactorSquare M) (physicalFactorSquare_nonneg M) P

theorem physicalFactor_inv_bound : (physicalFactor M)⁻¹≤8*(M : ℝ)^3 := by
  have hm : (1 : ℝ)≤M := by exact_mod_cast NeZero.pos M
  rw [physicalFactor,cellFactor,gridFactor,mul_inv_rev,inv_inv,inv_inv,
    ← Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg M) 3),mul_comm ((M : ℝ)^3)]
  apply Real.sqrt_le_self_iff.mpr
  right
  have hc : (1 : ℝ)≤(M : ℝ)^3 := one_le_pow₀ hm
  linarith

theorem physicalFactorApprox_relative_error (P : ℕ) :
    |(physicalFactorApprox M P : ℝ)/physicalFactor M-1|≤8*(M : ℝ)^3*(1/2 : ℝ)^P := by
  have he : (physicalFactorApprox M P : ℝ)/physicalFactor M-1=
      ((physicalFactorApprox M P : ℝ)-physicalFactor M)*(physicalFactor M)⁻¹ := by
    field_simp [(physicalFactor_pos M).ne']
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr (physicalFactor_pos M))]
  calc
    _ ≤ (1/2 : ℝ)^P*(8*(M : ℝ)^3) :=
      mul_le_mul (physicalFactorApprox_error M P) (physicalFactor_inv_bound M)
        (inv_pos.mpr (physicalFactor_pos M)).le (by positivity)
    _ = _ := mul_comm _ _

theorem physicalFactorApprox_relative_requested (N ell P : ℕ)
    (hM : (M : ℝ)≤(2 : ℝ)^ell) (hP : N+3*ell+3≤P) :
    |(physicalFactorApprox M P : ℝ)/physicalFactor M-1|≤(1/2 : ℝ)^N := by
  apply (physicalFactorApprox_relative_error M P).trans
  have hm : 8*(M : ℝ)^3≤(2 : ℝ)^(3*ell+3) := by
    calc
      _ ≤ 8*((2 : ℝ)^ell)^3 := by gcongr
      _ = _ := by rw [pow_add,← pow_mul]; norm_num; ring_nf
  have hp : (1/2 : ℝ)^P≤(1/2 : ℝ)^(N+3*ell+3) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hP
  calc
    _ ≤ (2 : ℝ)^(3*ell+3)*(1/2 : ℝ)^(N+3*ell+3) := mul_le_mul hm hp (by positivity) (by positivity)
    _ = _ := by
      rw [show N+3*ell+3=N+(3*ell+3) by omega,pow_add (1/2 : ℝ)]
      rw [mul_left_comm,← mul_pow]
      norm_num

#print axioms physicalFactorApprox_width
#print axioms physicalFactorApprox_relative_requested

end
end Maxwell.Continuum.Calibration.Supercell
