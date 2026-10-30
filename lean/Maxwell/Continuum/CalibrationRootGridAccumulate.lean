import Maxwell.Continuum.CalibrationRootGridWidths
import Maxwell.Continuum.CalibrationRootGridSampleMachine

/-! Exact real and imaginary accumulation with an additive raw-word
bound. The existing partial sum is never repeatedly squared in the bound. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def sumInputs : Finset ℕ := RootGridCenter.inputs∪{10,11}
def accumulate : Control := Control.prepend [.binary .add 10 10 6,.binary .add 11 11 7] .done
def accumulated (N : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) := accumulate.evaluate (sampleParts N n v)

theorem accumulate_valid (S : Finset ℕ) (hS : sumInputs⊆S) : accumulate.Valid S := by
  have h6 := hS (show 6∈sumInputs by decide)
  have h7 := hS (show 7∈sumInputs by decide)
  have h10 := hS (show 10∈sumInputs by decide)
  have h11 := hS (show 11∈sumInputs by decide)
  simp [accumulate,Control.prepend,Control.Valid,Instruction.Valid,h6,h7,h10,h11]

theorem accumulate_admissible (v : ℕ→Parts) : accumulate.AdmissibleTrace v := by
  simp [accumulate,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]

theorem accumulate_real (v : ℕ→Parts) : accumulate.evaluate v 10=(v 10).add (v 6) := by
  simp [accumulate,Control.prepend,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem accumulate_imag (v : ℕ→Parts) : accumulate.evaluate v 11=(v 11).add (v 7) := by
  simp [accumulate,Control.prepend,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem accumulate_other (v : ℕ→Parts) (i : ℕ) (hi : i≠10 ∧ i≠11) :
    accumulate.evaluate v i=v i := by
  simp [accumulate,Control.prepend,Control.evaluate,Instruction.update,hi.1,hi.2]

theorem accumulate_widthTrace (S : Finset ℕ) (hS : sumInputs⊆S) (v : ℕ→Parts)
    (W C : ℕ) (hw : WidthBank S W v) (h6 : (v 6).Width C) (h7 : (v 7).Width C) :
    accumulate.WidthTrace S (W+C+1) v := by
  have base := hw.mono (show W≤W+C+1 by omega)
  have hr := (hw 10 (hS (by decide))).add h6
  have hi := (hw 11 (hS (by decide))).add h7
  have wr := base.update 10 hr
  have wi := wr.update 11 hi
  simpa only [accumulate,Control.prepend,List.foldr_cons,List.foldr_nil,Control.WidthTrace,
    Instruction.LiteralFits,Instruction.update,BinaryOp.eval,
    Function.update_of_ne (by decide : (11:ℕ)≠10),
    Function.update_of_ne (by decide : (7:ℕ)≠10)] using
    (show WidthBank S (W+C+1) v ∧ True ∧
      WidthBank S (W+C+1) (Function.update v 10 ((v 10).add (v 6))) ∧ True ∧
      WidthBank S (W+C+1) (Function.update (Function.update v 10 ((v 10).add (v 6))) 11 ((v 11).add (v 7)))
      from ⟨base,trivial,wr,trivial,wi⟩)

theorem accumulate_executes (S : Finset ℕ) (hS : sumInputs⊆S) (v : ℕ→Parts)
    (W C : ℕ) (hw : WidthBank S W v) (h6 : (v 6).Width C) (h7 : (v 7).Width C)
    (hg : Good S v) (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃cost t,Executes input tape accumulate.code cost s t ∧ cost≤2*operationCost (W+C+1)+1 ∧
      Ready S (accumulate.evaluate v) t ∧ Good S (accumulate.evaluate v) ∧
      WidthBank S (W+C+1) (accumulate.evaluate v) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have ht := accumulate_widthTrace S hS v W C hw h6 h7
  obtain ⟨c,t,e,hc,hr,hf⟩ := accumulate.executes S (accumulate_valid S hS) v (W+C+1) ht
    hg (accumulate_admissible v) input tape s hs
  exact ⟨c,t,e,hc,hr,accumulate.evaluate_good S (accumulate_valid S hS) v hg
    (accumulate_admissible v),ht.result,hf⟩

theorem accumulated_other (N : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (i : ℕ)
    (hi : 8 ≤ i ∧ i≠10 ∧ i≠11) : accumulated N n v i=v i := by
  rw [accumulated,accumulate_other _ i hi.2,sampleParts_other _ _ _ i hi.1]

#print axioms accumulate_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
