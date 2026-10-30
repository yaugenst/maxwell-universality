import Maxwell.Continuum.ProfileEndpointData
import Maxwell.Continuum.RationalDataflowArrayMap

/-! Fixed runtime endpoint correction and dyadic scaling. Register 8 is a
stored descending index; the two exceptional coefficients are selected by
actual positivity tests. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def correctionFinish : Control := .step (.binary .mul 1 1 6) .done
def correctionSelect : Control := .positive 8
  (.step (.binary .sub 4 8 7)
    (.positive 4 correctionFinish (.step (.binary .sub 1 1 3) correctionFinish)))
  (.step (.binary .sub 4 3 0) (.step (.binary .add 1 1 4) correctionFinish))
def correctionControl : Control := .step (.binary .sub 8 8 7) correctionSelect
def correctionConstants : Finset ℕ := {0,3,6,7}
def correctedValue (endpoint slope scale x : ℚ) (j : ℕ) : ℚ :=
  ((x+(if j=0 then slope-endpoint else 0))-(if j=1 then slope else 0))*scale

theorem correctionControl_valid : correctionControl.Valid dftRegisters := by
  simp [correctionControl,correctionSelect,correctionFinish,Control.Valid,Instruction.Valid,dftRegisters]

theorem correctionControl_admissible (v : ℕ→Parts) : correctionControl.AdmissibleTrace v := by
  simp [correctionControl,correctionSelect,correctionFinish,Control.AdmissibleTrace,Instruction.Admissible]

theorem correctionControl_const (v : ℕ→Parts) (i : ℕ) (hi : i∈correctionConstants) :
    correctionControl.evaluate v i=v i := by
  have hn1 : i≠1 := by simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have hn4 : i≠4 := by simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have hn8 : i≠8 := by simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  simp only [correctionControl,correctionSelect,correctionFinish,Control.evaluate]
  split_ifs <;> simp only [Instruction.update,Function.update_of_ne hn1,
    Function.update_of_ne hn4,Function.update_of_ne hn8]

theorem correctionControl_index (v : ℕ→Parts) :
    correctionControl.evaluate v 8=(v 8).sub (v 7) := by
  simp only [correctionControl,correctionSelect,correctionFinish,Control.evaluate]
  split_ifs <;> simp [Instruction.update,BinaryOp.eval]

theorem correctionControl_value (v : ℕ→Parts) (hv : Good dftRegisters v) (j : ℕ)
    (h7 : (v 7).value=1) (h8 : (v 8).value=(j:ℚ)+1) :
    (correctionControl.evaluate v 1).value=
      correctedValue (v 0).value (v 3).value (v 6).value (v 1).value j := by
  have he := congrFun (correctionControl.evaluate_value dftRegisters correctionControl_valid v hv
    (correctionControl_admissible v)) 1
  change (correctionControl.evaluate v 1).value=(correctionControl.rationalEvaluate (valueBank v)) 1 at he
  rw [he]
  by_cases h0 : j=0
  · subst j
    simp [correctionControl,correctionSelect,correctionFinish,Control.rationalEvaluate,
      Instruction.rationalUpdate,valueBank,h7,h8,correctedValue]
  · have hj : (0:ℚ)<j := by exact_mod_cast Nat.pos_of_ne_zero h0
    by_cases h1 : j=1
    · subst j
      simp [correctionControl,correctionSelect,correctionFinish,Control.rationalEvaluate,
        Instruction.rationalUpdate,valueBank,h7,h8,correctedValue]
    · have hj1 : (0:ℚ)<(j:ℚ)-1 := by
        have hjnat : 1<j := by omega
        exact sub_pos.mpr (by exact_mod_cast hjnat)
      simp [correctionControl,correctionSelect,correctionFinish,Control.rationalEvaluate,
        Instruction.rationalUpdate,valueBank,h7,h8,correctedValue,h0,h1,hj,hj1]

#print axioms correctionControl_value
end Maxwell.Continuum.Profile.Runtime
