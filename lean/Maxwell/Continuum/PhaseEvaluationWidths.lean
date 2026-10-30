import Maxwell.Continuum.RationalTaylorSignedInputs
import Maxwell.Continuum.MachinData
import Maxwell.Continuum.ProfileSampleEvaluation

/-! Actual canonical rational widths throughout phase and profile sample evaluation. -/

namespace Maxwell.Continuum
open Maxwell.Certificate
set_option maxHeartbeats 1000000
attribute [local irreducible] Elementary.piApprox Elementary.expApprox Elementary.cosApprox Elementary.sinApprox

namespace RationalWords

theorem width_zero : Width 0 1 := by constructor <;> decide

def taylorCenterWidth (B P W : ℕ) : ℕ := RationalTaylor.width (Calibration.taylorOrder B P-1) W+1

theorem expApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (B P : ℕ) :
    Width (Elementary.expApprox q B P).center (taylorCenterWidth B P W) := by
  rw [RationalTaylor.signed_expApprox_center]
  exact RationalTaylor.signed_value_width hq _ _

theorem cosApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (B P : ℕ) :
    Width (Elementary.cosApprox q B P).center (taylorCenterWidth B P W) := by
  rw [RationalTaylor.signed_cosApprox_center]
  exact RationalTaylor.signed_value_width hq _ _

theorem sinApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (B P : ℕ) :
    Width (Elementary.sinApprox q B P).center (taylorCenterWidth B P W) := by
  rw [RationalTaylor.signed_sinApprox_center]
  exact RationalTaylor.signed_value_width hq _ _

end RationalWords

namespace Calibration
open RationalWords

def phaseInputWidth (Q N W : ℕ) : ℕ := 2+2^13*(phaseBits Q N+1)^2+W
def phaseOutputWidth (Q N W : ℕ) : ℕ := taylorCenterWidth (10*(Q+1)) (N+3) (phaseInputWidth Q N W)

theorem phaseAngle_width {q : ℚ} {W : ℕ} (hq : Width q W) (Q N : ℕ) :
    Width (phaseAngle q Q N) (phaseInputWidth Q N W) := by
  have hp := Machin.piApprox_word_bits (phaseBits Q N)
  exact (width_two.mul (show Width _ _ from ⟨hp.1,hp.2⟩)).mul hq

theorem cosTurnApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (Q N : ℕ) :
    Width (cosTurnApprox q Q N).center (phaseOutputWidth Q N W) := by
  unfold cosTurnApprox phaseOutputWidth
  exact cosApprox_width (phaseAngle_width hq Q N) _ _

theorem sinTurnApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (Q N : ℕ) :
    Width (sinTurnApprox q Q N).center (phaseOutputWidth Q N W) := by
  unfold sinTurnApprox phaseOutputWidth
  exact sinApprox_width (phaseAngle_width hq Q N) _ _

end Calibration

namespace Profile
open RationalWords

def glueOutputWidth (N W : ℕ) : ℕ := taylorCenterWidth (N+1) N W
def angularOutputWidth (P W : ℕ) : ℕ := glueOutputWidth (P+4) (Calibration.phaseOutputWidth 1 (P+4) W+2)

theorem glueApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (N : ℕ) :
    Width (glueApprox q N).center (glueOutputWidth N W) := by
  unfold glueApprox
  split_ifs with h
  · exact width_zero.mono (by unfold glueOutputWidth taylorCenterWidth; omega)
  · have hq0 : 0<q := lt_trans (by positivity : (0:ℚ)<1/((N:ℚ)+1)) (lt_of_not_ge h)
    have hi : Width (-1/q) W := by simpa only [neg_div,one_div] using (hq.inv hq0.ne').neg
    exact expApprox_width hi (N+1) N

theorem angularApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (P : ℕ) :
    Width (angularApprox q P).center (angularOutputWidth P W) := by
  have hcos := Calibration.cosTurnApprox_width hq 1 (P+4)
  have hs := width_one.sub hcos
  have hs' : Width (1-(Calibration.cosTurnApprox q 1 (P+4)).center)
      (Calibration.phaseOutputWidth 1 (P+4) W+2) := by
    convert hs using 1
    omega
  exact glueApprox_width hs' (P+4)

end Profile

#print axioms Calibration.phaseAngle_width
#print axioms Calibration.cosTurnApprox_width
#print axioms Profile.angularApprox_width

end Maxwell.Continuum
