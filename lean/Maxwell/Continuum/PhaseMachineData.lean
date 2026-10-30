import Maxwell.Continuum.MachinProgram
import Maxwell.Continuum.RationalMagnitudeMachine
import Maxwell.Continuum.RationalTaylorFraction
import Maxwell.Continuum.PhaseEvaluation

/-! The unreduced natural input words for the literal Machin/Taylor phase evaluator. -/

namespace Maxwell.Continuum.PhaseMachine
open Maxwell.Certificate Maxwell.Cost RationalTaylor
set_option maxHeartbeats 1000000
attribute [local irreducible] Elementary.piApprox Elementary.cosApprox Elementary.sinApprox

theorem piApprox_center_pos (N : ℕ) : 0<(Elementary.piApprox N).center := by
  have h := Elementary.piApprox_contains N
  rw [Ball.Contains,Elementary.piApprox_radius] at h
  push_cast at h
  have he : (1/2:ℝ)^N≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp := Real.pi_gt_three
  have hc : (0:ℝ)<((Elementary.piApprox N).center:ℝ) := by
    have habs := (abs_le.mp h).2
    linarith
  exact_mod_cast hc

theorem machin_numerator_le (N : ℕ) : Machin.numeratorNegative N≤Machin.numeratorPositive N := by
  have hp := piApprox_center_pos N
  rw [Machin.piApprox_center] at hp
  have hd : (0:ℚ)<Machin.commonDenominator N := by exact_mod_cast Machin.commonDenominator_pos N
  have hn : (Machin.numeratorNegative N:ℚ)<Machin.numeratorPositive N := by
    have hh := (div_pos_iff_of_pos_right hd).mp hp
    linarith
  exact_mod_cast hn.le

def piMagnitude (N : ℕ) : ℕ := IntegerNormSquare.magnitude (Machin.numeratorPositive N) (Machin.numeratorNegative N)

theorem piMagnitude_eq (N : ℕ) :
    piMagnitude N=Machin.numeratorPositive N-Machin.numeratorNegative N := by
  unfold piMagnitude IntegerNormSquare.magnitude
  rw [← Int.natCast_sub (machin_numerator_le N),Int.natAbs_natCast]

theorem piMagnitude_center (N : ℕ) :
    (Elementary.piApprox N).center=(piMagnitude N:ℚ)/Machin.commonDenominator N := by
  rw [Machin.piApprox_center,piMagnitude_eq,Nat.cast_sub (machin_numerator_le N)]

def argumentNumerator (a Q N : ℕ) : ℕ := 2*piMagnitude (Calibration.phaseBits Q N)*a
def argumentDenominator (b Q N : ℕ) : ℕ := Machin.commonDenominator (Calibration.phaseBits Q N)*b
def order (Q N : ℕ) : ℕ := Calibration.taylorOrder (10*(Q+1)) (N+3)-1
def inputWidth (Q N W : ℕ) : ℕ := Machin.wordWidth (Calibration.phaseBits Q N)+W+4

theorem argumentDenominator_pos {b : ℕ} (hb : 0<b) (Q N : ℕ) :
    0<argumentDenominator b Q N := Nat.mul_pos (Machin.commonDenominator_pos _) hb

theorem phaseAngle_fraction (negative : Bool) (a b Q N : ℕ) :
    Calibration.phaseAngle (signedFraction negative a b) Q N=
      signedFraction negative (argumentNumerator a Q N) (argumentDenominator b Q N) := by
  unfold Calibration.phaseAngle
  rw [piMagnitude_center]
  cases negative <;> simp only [signedFraction,Bool.false_eq_true,ite_false,ite_true,
    argumentNumerator,argumentDenominator,Nat.cast_mul,Nat.cast_ofNat]
  all_goals ring

theorem cosTurnApprox_center (negative : Bool) (a b Q N : ℕ) (hb : 0<b) :
    (Calibration.cosTurnApprox (signedFraction negative a b) Q N).center=
      value (argumentNumerator a Q N) (argumentDenominator b Q N)
        (fractionSigns negative cosineSigns) (order Q N) := by
  unfold Calibration.cosTurnApprox
  rw [phaseAngle_fraction]
  exact fraction_cosApprox_center _ _ _ (argumentDenominator_pos hb Q N) _ _

theorem sinTurnApprox_center (negative : Bool) (a b Q N : ℕ) (hb : 0<b) :
    (Calibration.sinTurnApprox (signedFraction negative a b) Q N).center=
      value (argumentNumerator a Q N) (argumentDenominator b Q N)
        (fractionSigns negative sineSigns) (order Q N) := by
  unfold Calibration.sinTurnApprox
  rw [phaseAngle_fraction]
  exact fraction_sinApprox_center _ _ _ (argumentDenominator_pos hb Q N) _ _

theorem argument_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) :
    (argumentNumerator a Q N).bits.length ≤ inputWidth Q N W ∧
    (argumentDenominator b Q N).bits.length ≤ inputWidth Q N W := by
  have hp := Machin.parts_width (Calibration.phaseBits Q N)
  have hm := IntegerNormSquare.magnitude_bits_length_le
    (Machin.numeratorPositive (Calibration.phaseBits Q N)) (Machin.numeratorNegative (Calibration.phaseBits Q N))
  have hmag : (piMagnitude (Calibration.phaseBits Q N)).bits.length≤Machin.wordWidth (Calibration.phaseBits Q N)+1 := by
    exact hm.trans (Nat.add_le_add_right (max_le hp.1 hp.2.1) 1)
  have hn := RationalAccumulator.bits_mul_le (2*piMagnitude (Calibration.phaseBits Q N)) a
  have hn2 := RationalAccumulator.bits_mul_le 2 (piMagnitude (Calibration.phaseBits Q N))
  have hd := RationalAccumulator.bits_mul_le (Machin.commonDenominator (Calibration.phaseBits Q N)) b
  have htwo : (2:ℕ).bits.length=2 := by decide
  unfold inputWidth argumentNumerator argumentDenominator
  constructor <;> omega

#print axioms cosTurnApprox_center
#print axioms sinTurnApprox_center
#print axioms argument_width

end Maxwell.Continuum.PhaseMachine
