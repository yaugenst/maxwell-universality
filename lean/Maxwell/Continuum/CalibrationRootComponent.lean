import Maxwell.Continuum.CalibrationRootGridEmission

/-! A genuine runtime branch selects a coefficient's real or imaginary part.
The selector reads the parity saved from the flat array index. -/
namespace Maxwell.Continuum.RationalDataflow.RootComponent
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

def inputs : Finset ℕ := {8,10,11,12}
def control : Control := .step (.literal 12 0)
  (.positive 8 (.step (.binary .add 12 11 12) .done)
    (.step (.binary .add 12 10 12) .done))
def values (v : ℕ→Parts) := control.evaluate v
def width (W : ℕ) : ℕ := 8*(W+1)

theorem valid (S : Finset ℕ) (hS : inputs⊆S) : control.Valid S := by
  have h8 := hS (show 8∈inputs by decide)
  have h10 := hS (show 10∈inputs by decide)
  have h11 := hS (show 11∈inputs by decide)
  have h12 := hS (show 12∈inputs by decide)
  simp [control,Control.Valid,Instruction.Valid,h8,h10,h11,h12]

theorem admissible (v : ℕ→Parts) : control.AdmissibleTrace v := by
  simp [control,Control.AdmissibleTrace,Instruction.Admissible]

theorem literals (W : ℕ) (hW : 1≤W) : control.LiteralsFit W := by
  have hz : (Parts.literal 0).Width W :=
    (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hW
  simpa only [control,Control.LiteralsFit,Instruction.LiteralFits,and_true,true_and] using hz

theorem steps : control.steps=3 := rfl

theorem selected (v : ℕ→Parts) : values v 12=
    if 0<(v 8).value then (v 11).add (Parts.literal 0) else (v 10).add (Parts.literal 0) := by
  let v0 := (Instruction.literal 12 0).update v
  let yes : Control := .step (.binary .add 12 11 12) .done
  let no : Control := .step (.binary .add 12 10 12) .done
  have h8 : v0 8=v 8 := by
    simp only [v0,Instruction.update,Function.update_of_ne (by decide : (8:ℕ)≠12)]
  change (Control.positive 8 yes no).evaluate v0 12= _
  by_cases hp : 0<(v 8).value
  · rw [RootGridCenter.positive_true 8 yes no v0 (by simpa only [h8] using hp),ite_eq_left hp]
    simp only [yes,Control.evaluate,v0,Instruction.update,BinaryOp.eval,Function.update_self,
      Function.update_of_ne (by decide : (11:ℕ)≠12)]
  · rw [RootGridCenter.positive_false 8 yes no v0 (by simpa only [h8] using hp),ite_eq_right hp]
    simp only [no,Control.evaluate,v0,Instruction.update,BinaryOp.eval,Function.update_self,
      Function.update_of_ne (by decide : (10:ℕ)≠12)]

theorem other (v : ℕ→Parts) (i : ℕ) (hi : i≠12) : values v i=v i := by
  let v0 := (Instruction.literal 12 0).update v
  let yes : Control := .step (.binary .add 12 11 12) .done
  let no : Control := .step (.binary .add 12 10 12) .done
  change (Control.positive 8 yes no).evaluate v0 i=v i
  by_cases hp : 0<(v0 8).value
  · rw [RootGridCenter.positive_true 8 yes no v0 hp]
    simp only [yes,Control.evaluate,v0,Instruction.update,Function.update_of_ne hi]
  · rw [RootGridCenter.positive_false 8 yes no v0 hp]
    simp only [no,Control.evaluate,v0,Instruction.update,Function.update_of_ne hi]

theorem selected_value (v : ℕ→Parts) (h10 : (v 10).Valid) (h11 : (v 11).Valid) :
    (values v 12).value=if 0<(v 8).value then (v 11).value else (v 10).value := by
  rw [selected]
  split_ifs <;> rw [Parts.add_value _ _ (by assumption) (Parts.literal_valid 0),Parts.literal_value,add_zero]

theorem selected_parity (v : ℕ→Parts) (index : ℕ) (hv : (v 8).value=(index%2:ℕ))
    (h10 : (v 10).Valid) (h11 : (v 11).Valid) :
    (values v 12).value=if index%2=0 then (v 10).value else (v 11).value := by
  rw [selected_value v h10 h11,hv]
  by_cases he : index%2=0
  · simp [he]
  · have hp : (0:ℚ)<(index%2:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero he
    simp [he,hp]

theorem executes (S : Finset ℕ) (hS : inputs⊆S) (v : ℕ→Parts)
    (W : ℕ) (hW : 1≤W) (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃cost t,Executes input tape control.code cost s t ∧ cost≤3*operationCost (width W)+1 ∧
      Ready S (values v) t ∧ Good S (values v) ∧ WidthBank S (width W) (values v) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have ht : control.WidthTrace S (width W) v := by
    simpa only [steps,width,show 2^3=8 by rfl] using
      control.automatic_widthTrace S (valid S hS) v W hw (literals W hW)
  obtain ⟨c,t,e,hc,hr,hf⟩ := control.executes S (valid S hS) v (width W) ht hg
    (admissible v) input tape s hs
  exact ⟨c,t,e,by simpa only [steps] using hc,hr,
    control.evaluate_good S (valid S hS) v hg (admissible v),ht.result,hf⟩

#print axioms executes
#print axioms selected_parity
end Maxwell.Continuum.RationalDataflow.RootComponent
