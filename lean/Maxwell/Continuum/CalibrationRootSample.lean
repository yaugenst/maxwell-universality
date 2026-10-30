import Maxwell.Continuum.CalibrationBumpEvaluation
import Maxwell.Continuum.GlueDataflowWidth
import Maxwell.Continuum.RationalDataflowControlResults

/-! Literal compact-root samples from three stored rational coordinates.  The
arithmetic recipe is fixed, and its raw output widths depend on the coordinate
words rather than on unrelated accumulators in the surrounding bank. -/

namespace Maxwell.Continuum.RationalDataflow.RootSample
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def inputs : Finset ℕ := {0,1,2,3,4}

def rawArgument (y : Fin 3 → Parts) : Parts :=
  (Parts.literal 2).mul ((Parts.literal 1).sub
    ((((y 0).mul (y 0)).add ((y 1).mul (y 1))).add ((y 2).mul (y 2))))

def argument : Control := Control.prepend
  [.binary .mul 3 0 0, .binary .mul 4 1 1, .binary .add 3 3 4,
   .binary .mul 4 2 2, .binary .add 3 3 4, .literal 4 1,
   .binary .sub 3 4 3, .literal 4 2, .binary .mul 3 4 3] .done

def coordinates (v : ℕ → Parts) (i : Fin 3) : Parts := v i

def values (N : ℕ) (v : ℕ → Parts) : ℕ → Parts :=
  Function.update (argument.evaluate v) 4 (Glue.result N (rawArgument (coordinates v)))

def code : Code := .seq argument.code (Glue.code 4 3)

theorem rawArgument_valid (y : Fin 3 → Parts) (hy : ∀i,(y i).Valid) :
    (rawArgument y).Valid :=
  Parts.mul_valid (Parts.literal_valid 2) (Parts.sub_valid (Parts.literal_valid 1)
    (Parts.add_valid (Parts.add_valid (Parts.mul_valid (hy 0) (hy 0))
      (Parts.mul_valid (hy 1) (hy 1))) (Parts.mul_valid (hy 2) (hy 2))))

theorem rawArgument_value (y : Fin 3 → Parts) (hy : ∀i,(y i).Valid) :
    (rawArgument y).value = Calibration.rootArgument (fun i => (y i).value) := by
  have h0 := Parts.mul_valid (hy 0) (hy 0)
  have h1 := Parts.mul_valid (hy 1) (hy 1)
  have h2 := Parts.mul_valid (hy 2) (hy 2)
  rw [rawArgument,Parts.mul_value,
    Parts.sub_value _ _ (Parts.literal_valid 1) (Parts.add_valid (Parts.add_valid h0 h1) h2),
    Parts.add_value _ _ (Parts.add_valid h0 h1) h2,Parts.add_value _ _ h0 h1]
  simp only [Parts.mul_value,Parts.literal_value,Calibration.rootArgument,Fin.sum_univ_three]
  ring

theorem rawArgument_width (y : Fin 3 → Parts) (B : ℕ) (hy : ∀i,(y i).Width B) :
    (rawArgument y).Width (6*B+10) := by
  have h1 : (Parts.literal 1).Width 1 := by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega
  have h2 : (Parts.literal 2).Width 2 := by change 2≤2 ∧ 0≤2 ∧ 1≤2;omega
  simpa only [rawArgument,show 2+(1+((B+B+1)+(B+B+1)+1+(B+B+1)+1)+1)+1=6*B+10 by omega]
    using h2.mul (h1.sub ((((hy 0).mul (hy 0)).add ((hy 1).mul (hy 1))).add
      ((hy 2).mul (hy 2))))

theorem argument_valid (S : Finset ℕ) (hS : inputs ⊆ S) : argument.Valid S := by
  have h0 := hS (show 0∈inputs by decide)
  have h1 := hS (show 1∈inputs by decide)
  have h2 := hS (show 2∈inputs by decide)
  have h3 := hS (show 3∈inputs by decide)
  have h4 := hS (show 4∈inputs by decide)
  simp [argument,Control.prepend,Control.Valid,Instruction.Valid,h0,h1,h2,h3,h4]

theorem argument_admissible (v : ℕ → Parts) : argument.AdmissibleTrace v := by
  simp [argument,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]

theorem argument_literals (W : ℕ) (hW : 2≤W) : argument.LiteralsFit W := by
  have h1 := (show (Parts.literal 1).Width 1 by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega).mono (show 1≤W by omega)
  have h2 := (show (Parts.literal 2).Width 2 by change 2≤2 ∧ 0≤2 ∧ 1≤2;omega).mono hW
  simp [argument,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits,h1,h2]

theorem argument_steps : argument.steps=9 := rfl

theorem argument_output (v : ℕ → Parts) :
    argument.evaluate v 3=rawArgument (coordinates v) := by
  simp [argument,Control.prepend,Control.evaluate,Instruction.update,BinaryOp.eval,
    rawArgument,coordinates]

theorem argument_unchanged (v : ℕ → Parts) (i : ℕ) (hi : i≠3 ∧ i≠4) :
    argument.evaluate v i=v i := by
  simp [argument,Control.prepend,Control.evaluate,Instruction.update,hi.1,hi.2]

theorem values_value (N : ℕ) (v : ℕ → Parts) (hv : ∀i,(coordinates v i).Valid) :
    (values N v 4).value =
      (Calibration.rootApprox (fun i => (coordinates v i).value) N).center := by
  simp only [values,Function.update_self]
  rw [Glue.result_value _ _ (rawArgument_valid _ hv),rawArgument_value _ hv]
  rfl

theorem values_width (N B : ℕ) (v : ℕ → Parts) (hv : ∀i,(coordinates v i).Width B) :
    (values N v 4).Width (2^28*(N+6*B+19)^4) := by
  simpa only [values,Function.update_self,show N+(6*B+10)+9=N+6*B+19 by omega]
    using Glue.result_width N (6*B+10) _ (rawArgument_width _ B hv)

theorem values_unchanged (N : ℕ) (v : ℕ → Parts) (i : ℕ) (hi : i≠3 ∧ i≠4) :
    values N v i=v i := by
  rw [values,Function.update_of_ne hi.2,argument_unchanged v i hi]

#print axioms rawArgument_value
#print axioms values_value
#print axioms values_width
end Maxwell.Continuum.RationalDataflow.RootSample
