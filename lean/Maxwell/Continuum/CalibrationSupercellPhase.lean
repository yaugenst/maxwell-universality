import Maxwell.Continuum.CalibrationFiniteData
import Maxwell.Continuum.CalibrationSupercellUnitary
import Maxwell.Continuum.PhaseEvaluation

/-! Finite rational phase multiplication for an actual period-2M
Fourier translation. The turn is reduced modulo M before evaluation,
so precision and scalar evaluation work are independent of frequency. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber Maxwell.Certificate

variable (M : ℕ) [NeZero M]

def phaseResidue (a ν : Alias) : ZMod M := ((∑ j, ν j*a j : ℤ) : ZMod M)

def phaseTurn (a ν : Alias) : ℚ := (phaseResidue M a ν).val/(M : ℚ)

theorem phaseTurn_bound (a ν : Alias) : |phaseTurn M a ν| ≤ 1 := by
  have hM : (0 : ℚ)<M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hj : ((phaseResidue M a ν).val : ℚ) ≤ M := by
    exact_mod_cast (ZMod.val_lt (phaseResidue M a ν)).le
  rw [phaseTurn,abs_of_nonneg (by positivity)]
  exact (div_le_one hM).mpr hj

noncomputable def exactPhase (a ν : Alias) : ℂ := ZMod.stdAddChar (phaseResidue M a ν)

theorem exactPhase_norm (a ν : Alias) : ‖exactPhase M a ν‖=1 := by
  simp only [exactPhase,ZMod.stdAddChar_apply,Circle.norm_coe]

theorem exactPhase_exp (a ν : Alias) :
    exactPhase M a ν = Complex.exp (2*(Real.pi : ℂ)*Complex.I*
      ((∑ j, ν j*a j : ℤ) : ℂ)/(M : ℂ)) := by
  rw [exactPhase,phaseResidue,ZMod.stdAddChar_coe]

theorem exactPhase_reduced (a ν : Alias) :
    exactPhase M a ν = Complex.exp ((2*Real.pi*(phaseTurn M a ν : ℝ) : ℝ)*Complex.I) := by
  have hj : (((phaseResidue M a ν).val : ℤ) : ZMod M)=phaseResidue M a ν := by simp
  rw [exactPhase,← hj,ZMod.stdAddChar_coe]
  congr 1
  simp only [phaseTurn,Rat.cast_div,Rat.cast_natCast,Complex.ofReal_mul,
    Complex.ofReal_div,Complex.ofReal_natCast,Int.cast_natCast,Complex.ofReal_ofNat]
  ring

def rationalPhaseCoefficient (a ν : Alias) (N : ℕ) : RationalComplex :=
  ((cosTurnApprox (phaseTurn M a ν) 1 (N+2)).center,
    (sinTurnApprox (phaseTurn M a ν) 1 (N+2)).center)

theorem rationalPhaseCoefficient_error (a ν : Alias) (N : ℕ) :
    ‖rationalComplexValue (rationalPhaseCoefficient M a ν N)-exactPhase M a ν‖ ≤
      (1/2 : ℝ)^N := by
  have hc := cosTurnApprox_contains (phaseTurn M a ν) 1 (N+2) (phaseTurn_bound M a ν)
  have hs := sinTurnApprox_contains (phaseTurn M a ν) 1 (N+2) (phaseTurn_bound M a ν)
  rw [Ball.Contains,cosTurnApprox_radius] at hc
  rw [Ball.Contains,sinTurnApprox_radius] at hs
  push_cast at hc hs
  rw [exactPhase_reduced,Complex.exp_ofReal_mul_I,rationalComplexValue_eq,rationalPhaseCoefficient]
  have he : (((cosTurnApprox (phaseTurn M a ν) 1 (N+2)).center : ℚ) : ℂ)+
      (((sinTurnApprox (phaseTurn M a ν) 1 (N+2)).center : ℚ) : ℂ)*Complex.I-
      ((Real.cos (2*Real.pi*(phaseTurn M a ν : ℝ)) : ℂ)+
        (Real.sin (2*Real.pi*(phaseTurn M a ν : ℝ)) : ℂ)*Complex.I) =
      ((((cosTurnApprox (phaseTurn M a ν) 1 (N+2)).center : ℝ)-
        Real.cos (2*Real.pi*(phaseTurn M a ν : ℝ)) : ℝ) : ℂ)+
      ((((sinTurnApprox (phaseTurn M a ν) 1 (N+2)).center : ℝ)-
        Real.sin (2*Real.pi*(phaseTurn M a ν : ℝ)) : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_sub_comm,abs_sub_comm _ (Real.sin _)]
  apply (add_le_add hc hs).trans
  rw [pow_add]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

theorem rationalPhaseCoefficient_norm (a ν : Alias) (N : ℕ) :
    ‖rationalComplexValue (rationalPhaseCoefficient M a ν N)‖ ≤ 2 := by
  have h := norm_le_norm_sub_add (rationalComplexValue (rationalPhaseCoefficient M a ν N))
    (exactPhase M a ν)
  rw [exactPhase_norm] at h
  have hε : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith [rationalPhaseCoefficient_error M a ν N]

#print axioms rationalPhaseCoefficient_error

end Maxwell.Continuum.Calibration.Supercell
