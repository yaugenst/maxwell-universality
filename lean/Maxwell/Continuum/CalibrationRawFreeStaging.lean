import Maxwell.Continuum.CalibrationRawFreeComplete
import Maxwell.Continuum.RationalDataflowSequence

/-! Literal direction construction and runtime polarization selection for
the free block evaluator. Coordinates and polarization indices are inputs;
neither selected matrix entries nor a Kronecker-delta flag are inputs. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def quasiParts (v : ℕ → Parts) : Fin 3 → Parts := ![v 16,v 17,v 18]
def stageInstructions : List Instruction :=
  [.literal 19 (1/2),.literal 20 1,
   .binary .add 2 13 19,.binary .add 2 2 16,
   .binary .add 3 14 19,.binary .add 3 3 17,
   .binary .add 4 15 19,.binary .add 4 4 18,
   .binary .sub 25 23 20,.binary .sub 26 24 20,
   .binary .sub 27 23 24,.binary .mul 27 27 27]
def staged (v : ℕ → Parts) : ℕ → Parts := RationalDataflow.evaluate stageInstructions v

def selectDirection (target index minusOne : ℕ) : Control :=
  .positive index
    (.positive minusOne (.step (.binary .mul target 4 20) .done)
      (.step (.binary .mul target 3 20) .done))
    (.step (.binary .mul target 2 20) .done)

def selectDelta : Control :=
  .positive 27 (.step (.literal 7 0) .done) (.step (.literal 7 1) .done)
def stageTail : Control :=
  (selectDirection 5 23 25).andThen ((selectDirection 6 24 26).andThen selectDelta)
def stageControl : Control := stageTail.prepend stageInstructions
def stageRegisters : Finset ℕ := Finset.range 28

theorem mul_literal_one (p : Parts) : p.mul (Parts.literal 1)=p := by
  cases p
  simp [Parts.mul,Parts.literal]

theorem staged_keep (v : ℕ → Parts) (k : ℕ)
    (hk : k≠2 ∧ k≠3 ∧ k≠4 ∧ k≠19 ∧ k≠20 ∧ k≠25 ∧ k≠26 ∧ k≠27) :
    staged v k=v k := by
  simp [staged,stageInstructions,RationalDataflow.evaluate,Instruction.update,hk.1,hk.2.1,
    hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.1,hk.2.2.2.2.2.1,hk.2.2.2.2.2.2.1,
    hk.2.2.2.2.2.2.2]

theorem staged_one (v : ℕ → Parts) : staged v 20=Parts.literal 1 := by
  simp [staged,stageInstructions,RationalDataflow.evaluate,Instruction.update]

theorem staged_directions (v : ℕ → Parts) :
    directions (staged v)=direction (coordinates v) (quasiParts v) := by
  funext k
  fin_cases k <;>
    simp [directions,staged,stageInstructions,RationalDataflow.evaluate,Instruction.update,
      BinaryOp.eval,direction,coordinates,quasiParts]

theorem staged_minus_left (v : ℕ → Parts) : staged v 25=(v 23).sub (Parts.literal 1) := by
  simp [staged,stageInstructions,RationalDataflow.evaluate,Instruction.update,BinaryOp.eval]
theorem staged_minus_right (v : ℕ → Parts) : staged v 26=(v 24).sub (Parts.literal 1) := by
  simp [staged,stageInstructions,RationalDataflow.evaluate,Instruction.update,BinaryOp.eval]
theorem staged_delta (v : ℕ → Parts) : staged v 27=((v 23).sub (v 24)).mul ((v 23).sub (v 24)) := by
  simp [staged,stageInstructions,RationalDataflow.evaluate,Instruction.update,BinaryOp.eval]

theorem selectDirection_evaluate (v : ℕ → Parts) (target index minusOne : ℕ) (i : Fin 3)
    (hindex : (v index).value=(i.val : ℚ)) (hminus : (v minusOne).value=(i.val : ℚ)-1)
    (hone : v 20=Parts.literal 1) :
    (selectDirection target index minusOne).evaluate v=
      Function.update v target (directions v i) := by
  fin_cases i <;>
    simp [selectDirection,Control.evaluate,hindex,hminus,Instruction.update,
      BinaryOp.eval,hone,mul_literal_one,directions]

theorem selectDelta_evaluate (v : ℕ → Parts) (i j : Fin 3)
    (hdelta : (v 27).value=((i.val : ℚ)-j.val)^2) :
    selectDelta.evaluate v=Function.update v 7 (Parts.literal (if i=j then 1 else 0)) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [selectDelta,Control.evaluate,hdelta,Instruction.update]

theorem stageControl_evaluate (v : ℕ → Parts) (i j : Fin 3)
    (hg : Good stageRegisters v) (hi : (v 23).value=(i.val : ℚ))
    (hj : (v 24).value=(j.val : ℚ)) :
    stageControl.evaluate v=Function.update (Function.update (Function.update (staged v)
      5 (directions (staged v) i)) 6 (directions (staged v) j))
      7 (Parts.literal (if i=j then 1 else 0)) := by
  have hi' : (staged v 23).value=(i.val : ℚ) := by rw [staged_keep v 23 (by omega)]; exact hi
  have hj' : (staged v 24).value=(j.val : ℚ) := by rw [staged_keep v 24 (by omega)]; exact hj
  have hm : (staged v 25).value=(i.val : ℚ)-1 := by
    rw [staged_minus_left,Parts.sub_value _ _ (hg 23 (by decide)) (Parts.literal_valid _),Parts.literal_value,hi]
  have hn : (staged v 26).value=(j.val : ℚ)-1 := by
    rw [staged_minus_right,Parts.sub_value _ _ (hg 24 (by decide)) (Parts.literal_valid _),Parts.literal_value,hj]
  have hd : (staged v 27).value=((i.val : ℚ)-j.val)^2 := by
    rw [staged_delta,Parts.mul_value,Parts.sub_value _ _ (hg 23 (by decide)) (hg 24 (by decide)),hi,hj,pow_two]
  rw [stageControl,Control.prepend_evaluate]
  change stageTail.evaluate (staged v)=_
  rw [stageTail,Control.andThen_evaluate,Control.andThen_evaluate,
    selectDirection_evaluate (staged v) 5 23 25 i hi' hm (staged_one v)]
  rw [selectDirection_evaluate _ 6 24 26 j (by simpa using hj') (by simpa using hn)
    (by simpa using staged_one v)]
  rw [selectDelta_evaluate _ i j (by simpa using hd)]
  simp only [directions,Function.update_of_ne (by decide : (2:ℕ)≠5),
    Function.update_of_ne (by decide : (3:ℕ)≠5),Function.update_of_ne (by decide : (4:ℕ)≠5)]

theorem stageControl_valid : stageControl.Valid stageRegisters := by
  simp [stageControl,stageInstructions,stageTail,selectDirection,selectDelta,Control.andThen,
    Control.prepend,Control.Valid,Instruction.Valid,stageRegisters]
theorem stageControl_admissible (v : ℕ → Parts) : stageControl.AdmissibleTrace v := by
  simp [stageControl,stageInstructions,stageTail,selectDirection,selectDelta,Control.andThen,
    Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]
theorem stageControl_steps : stageControl.steps=20 := by decide

#print axioms stageControl_evaluate

end Maxwell.Continuum.Calibration.RawFree
