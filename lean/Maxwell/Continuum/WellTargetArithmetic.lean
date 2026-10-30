import Maxwell.Continuum.WellStrengthExecution

/-! Fixed raw arithmetic for the three classes of target diagonal. The
original record reads a four-bit signed-half-integer code and its degree;
internal records use their proved degree two. The mediator consumes the
coupling on the coordinate changed by its consecutive path samples. -/
namespace Maxwell.Continuum.RationalDataflow.WellTarget
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000

/-- Bank1 is the calibrated midpoint,4 the common alpha,8 the original
four-bit diagonal code,9 its saved incidence count. -/
def original : Control :=
  .step (.literal 10 8) (.step (.binary .sub 2 8 10)
    (.step (.literal 10 (1/2)) (.step (.binary .mul 2 2 10)
      (.step (.binary .sub 2 2 9) (.step (.binary .mul 2 4 2) .done)))))

def internal : Control := .step (.literal 2 (-2)) (.step (.binary .mul 2 4 2) .done)

/-- Bank8 holds the actual axis coupling selected from the two samples. -/
def mediator : Control :=
  .step (.inverse 13 4) (.step (.binary .mul 2 8 8)
    (.step (.binary .mul 2 2 13) (.step (.literal 10 (-1))
      (.step (.binary .mul 2 10 2) .done))))

theorem original_valid : original.Valid WellStrength.bank := by
  simp [original,Control.Valid,Instruction.Valid,WellStrength.bank]
theorem internal_valid : internal.Valid WellStrength.bank := by
  simp [internal,Control.Valid,Instruction.Valid,WellStrength.bank]
theorem mediator_valid : mediator.Valid WellStrength.bank := by
  simp [mediator,Control.Valid,Instruction.Valid,WellStrength.bank]

theorem original_admissible (v : ℕ→Parts) : original.AdmissibleTrace v := by trivial
theorem internal_admissible (v : ℕ→Parts) : internal.AdmissibleTrace v := by trivial
theorem mediator_admissible (v : ℕ→Parts) (ha : (v 4).value≠0) : mediator.AdmissibleTrace v := by
  exact ⟨ha,trivial,trivial,trivial,trivial,trivial⟩

theorem original_value (v : ℕ→Parts) (hg : Good WellStrength.bank v) :
    (original.evaluate v 2).value=(v 4).value*(((v 8).value-8)/2-(v 9).value) := by
  have he := congrFun (original.evaluate_value WellStrength.bank original_valid v hg (original_admissible v)) 2
  simpa [original,Control.rationalEvaluate,Instruction.rationalUpdate,valueBank,div_eq_mul_inv] using he

theorem internal_value (v : ℕ→Parts) (hg : Good WellStrength.bank v) :
    (internal.evaluate v 2).value= -2*(v 4).value := by
  have he := congrFun (internal.evaluate_value WellStrength.bank internal_valid v hg (internal_admissible v)) 2
  simpa [internal,Control.rationalEvaluate,Instruction.rationalUpdate,valueBank,mul_comm] using he

theorem mediator_value (v : ℕ→Parts) (hg : Good WellStrength.bank v) (ha : (v 4).value≠0) :
    (mediator.evaluate v 2).value= -(v 8).value^2/(v 4).value := by
  have he := congrFun (mediator.evaluate_value WellStrength.bank mediator_valid v hg (mediator_admissible v ha)) 2
  simpa [mediator,Control.rationalEvaluate,Instruction.rationalUpdate,valueBank,pow_two,div_eq_mul_inv] using he

theorem original_midpoint (v : ℕ→Parts) : original.evaluate v 1=v 1 := by
  simp [original,Control.evaluate,Instruction.update]
theorem internal_midpoint (v : ℕ→Parts) : internal.evaluate v 1=v 1 := by
  simp [internal,Control.evaluate,Instruction.update]
theorem mediator_midpoint (v : ℕ→Parts) : mediator.evaluate v 1=v 1 := by
  simp [mediator,Control.evaluate,Instruction.update]

#print axioms original_value
#print axioms mediator_value
end Maxwell.Continuum.RationalDataflow.WellTarget
