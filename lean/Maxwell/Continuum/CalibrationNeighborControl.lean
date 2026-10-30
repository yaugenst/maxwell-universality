import Maxwell.Continuum.CalibrationNeighborMetric
import Maxwell.Continuum.CalibrationRawFreeStaging
import Maxwell.Continuum.RationalDataflowSubbank

/-! Each of the six neighbor tests is a fixed arithmetic-and-comparison
fragment on actual signed rational coordinates. -/

namespace Maxwell.Continuum.Calibration.RawFree

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def columnCoordinates (v : ℕ → Parts) : Fin 3 → Parts := ![v 28,v 29,v 30]
def neighborRegisters : Finset ℕ := Finset.range 41

def neighborBody (d : Fin 3) (plus : Bool) : List Instruction :=
  [.literal 32 (neighborOffset d plus 0),.binary .add 33 13 32,
   .binary .sub 33 33 28,.binary .mul 33 33 33,
   .literal 32 (neighborOffset d plus 1),.binary .add 34 14 32,
   .binary .sub 34 34 29,.binary .mul 34 34 34,
   .literal 32 (neighborOffset d plus 2),.binary .add 35 15 32,
   .binary .sub 35 35 30,.binary .mul 35 35 35,
   .binary .add 33 33 34,.binary .add 33 33 35]

def neighborPrefix (d : Fin 3) (plus : Bool) (v : ℕ → Parts) : ℕ → Parts :=
  RationalDataflow.evaluate (neighborBody d plus) v

def neighborTail (d : Fin 3) : Control :=
  .positive 33 .done (.step (.literal 40 (rationalWeight d))
    (.step (.binary .add 36 36 40) .done))
def neighborControl (d : Fin 3) (plus : Bool) : Control :=
  (neighborTail d).prepend (neighborBody d plus)

theorem neighborPrefix_other (d : Fin 3) (plus : Bool) (v : ℕ → Parts) (k : ℕ)
    (hk : k≠32 ∧ k≠33 ∧ k≠34 ∧ k≠35) : neighborPrefix d plus v k=v k := by
  simp [neighborPrefix,neighborBody,RationalDataflow.evaluate,Instruction.update,
    hk.1,hk.2.1,hk.2.2.1,hk.2.2.2]

theorem neighborPrefix_metric (d : Fin 3) (plus : Bool) (v : ℕ → Parts) :
    neighborPrefix d plus v 33=neighborMetric (coordinates v) (columnCoordinates v) d plus := by
  simp [neighborPrefix,neighborBody,RationalDataflow.evaluate,Instruction.update,
    BinaryOp.eval,neighborMetric,neighborDifference,sumThree,coordinates,columnCoordinates]

theorem neighborControl_other (d : Fin 3) (plus : Bool) (v : ℕ → Parts) (k : ℕ)
    (hk : k≠32 ∧ k≠33 ∧ k≠34 ∧ k≠35 ∧ k≠36 ∧ k≠40) :
    (neighborControl d plus).evaluate v k=v k := by
  rw [neighborControl,Control.prepend_evaluate]
  change (neighborTail d).evaluate (neighborPrefix d plus v) k=_
  simp only [neighborTail,Control.evaluate]
  split_ifs
  · exact neighborPrefix_other d plus v k ⟨hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1⟩
  · simp only [Instruction.update,Function.update_of_ne hk.2.2.2.2.1,
      Function.update_of_ne hk.2.2.2.2.2]
    exact neighborPrefix_other d plus v k ⟨hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1⟩

theorem neighborControl_output (d : Fin 3) (plus : Bool) (v : ℕ → Parts) :
    (neighborControl d plus).evaluate v 36=
      if 0<(neighborMetric (coordinates v) (columnCoordinates v) d plus).value then v 36
      else (v 36).add (Parts.literal (rationalWeight d)) := by
  rw [neighborControl,Control.prepend_evaluate]
  change (neighborTail d).evaluate (neighborPrefix d plus v) 36=_
  simp only [neighborTail,Control.evaluate,neighborPrefix_metric]
  split_ifs
  · exact neighborPrefix_other d plus v 36 (by omega)
  · simp only [Instruction.update,Function.update_self,BinaryOp.eval,
      Function.update_of_ne (by decide : (36:ℕ)≠40),neighborPrefix_other d plus v 36 (by omega)]

theorem neighborControl_valid (d : Fin 3) (plus : Bool) :
    (neighborControl d plus).Valid neighborRegisters := by
  simp [neighborControl,neighborBody,neighborTail,Control.prepend,Control.Valid,
    Instruction.Valid,neighborRegisters]

theorem neighborControl_admissible (d : Fin 3) (plus : Bool) (v : ℕ → Parts) :
    (neighborControl d plus).AdmissibleTrace v := by
  simp [neighborControl,neighborBody,neighborTail,Control.prepend,Control.AdmissibleTrace,
    Instruction.Admissible]

theorem neighborControl_steps (d : Fin 3) (plus : Bool) :
    (neighborControl d plus).steps=17 := by
  simp [neighborControl,neighborBody,neighborTail,Control.prepend,Control.steps]

theorem neighborControl_value (d : Fin 3) (plus : Bool) (v : ℕ → Parts)
    (hg : Good neighborRegisters v) (ν μ : Alias)
    (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ)) :
    ((neighborControl d plus).evaluate v 36).value=
      (v 36).value+(if shiftedAlias ν d plus=μ then rationalWeight d else 0) := by
  have hc (k : Fin 3) : (coordinates v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hm (k : Fin 3) : (columnCoordinates v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hp := neighborMetric_pos (coordinates v) (columnCoordinates v) d plus hc hm ν μ hν hμ
  rw [neighborControl_output]
  by_cases he : shiftedAlias ν d plus=μ
  · have hn : ¬0<(neighborMetric (coordinates v) (columnCoordinates v) d plus).value :=
      fun h => hp.mp h he
    simp only [hn,ite_false,he,ite_true,
      Parts.add_value _ _ (hg 36 (by decide)) (Parts.literal_valid _),Parts.literal_value]
  · have hpos := hp.mpr he
    simp only [hpos,ite_true,he,ite_false,add_zero]

theorem neighborControl_literals (d : Fin 3) (plus : Bool) (B : ℕ) (hB : 2≤B) :
    (neighborControl d plus).LiteralsFit B := by
  have hsmall (q : ℚ) (hq : q=0 ∨ q=1 ∨ q= -1 ∨ q=1/2 ∨ q=2) : (Parts.literal q).Width B := by
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals
      apply Parts.Width.mono (B:=2) ?_ hB
      norm_num [Parts.Width,Parts.literal,Int.sign] <;> decide
  simp only [neighborControl,neighborBody,neighborTail,Control.prepend,List.foldr_cons,List.foldr_nil,
    Control.LiteralsFit,Instruction.LiteralFits,true_and,and_true]
  refine ⟨hsmall _ ?_,hsmall _ ?_,hsmall _ ?_,hsmall _ ?_⟩
  · unfold neighborOffset; split_ifs <;> tauto
  · unfold neighborOffset; split_ifs <;> tauto
  · unfold neighborOffset; split_ifs <;> tauto
  · fin_cases d <;> simp [rationalWeight]

#print axioms neighborControl_value

end Maxwell.Continuum.Calibration.RawFree
