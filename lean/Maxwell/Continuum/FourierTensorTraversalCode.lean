import Maxwell.Continuum.FourierTensorRepeatedCoefficient
import Maxwell.Continuum.FourierTensorTraversalCursor
import Maxwell.Continuum.StructuredForwardTraversal

/-! The outer tensor compiler is a fixed three-level program. The list of
axes is fixed by the representation; every growing dimension is read from
the stored degree on tape 1110. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def tensorTraversalCode : List (Fin 3)→Code
  | [] => repeatedCoefficientCode
  | i::is => .seq (resetCursorCode i) (.seq (WordReplace.code 1110 (1101+i.val))
      (countedProgram (1101+i.val) (.seq (tensorTraversalCode is) (cursorCode i))))

def tensorComponentCode : Code := tensorTraversalCode [0,1,2]

def tensorTraversalCost (Q N n W D : ℕ) : ℕ→ℕ
  | 0 => repeatedCoefficientCost Q N n W
  | k+1 => stageCost W+(21*W+21)+
      ((D+1)*(13*W+15)+D*(tensorTraversalCost Q N n W D k+(2*operationCost W+1)))

def TensorBuffers (W : ℕ) (axes : Finset (Fin 3)) (s : Store) : Prop :=
  ∀i∈axes,BoundedTape W s (1101+i.val)

theorem TensorBuffers.frame {W : ℕ} {axes : Finset (Fin 3)} {s t : Store}
    (h : TensorBuffers W axes s)
    (ht : ∀i∈axes,t.val.tapes (1101+i.val)=s.val.tapes (1101+i.val)) : TensorBuffers W axes t :=
  fun i hi => (h i hi).of_eq (ht i hi)

theorem TensorBuffers.restrict {W : ℕ} {a b : Finset (Fin 3)} {s : Store}
    (h : TensorBuffers W b s) (hab : a ⊆ b) : TensorBuffers W a s :=
  fun i hi => h i (hab hi)

theorem TensorBuffers.count_frame {W : ℕ} {axes : Finset (Fin 3)} {s t : Store}
    (h : TensorBuffers W axes s) (i : Fin 3) (hi : i∉axes)
    (f : CountedShifted.Frame (1101+i.val) s t) : TensorBuffers W axes t := by
  apply h.frame
  intro j hj
  apply f.2.2.2.2.2.1
  intro he
  have hji : j=i := by apply Fin.ext;omega
  subst j
  exact hi hj

theorem tensorTraversal_protects_counter (axes : List (Fin 3)) (j : Fin 3) (hj : j∉axes) :
    (tensorTraversalCode axes).protectsTape (1101+j.val)=true := by
  induction axes with
  | nil => exact Code.tapesBelow_protects repeatedCoefficient_tapesBelow (by omega)
  | cons i is ih =>
    have hh : j≠i ∧ j∉is := by simpa only [List.mem_cons,not_or] using hj
    have hji := hh.1
    have hjs := hh.2
    have reset := Code.tapesBelow_protects (resetCursor_tapesBelow i)
      (by omega : 1100 ≤ 1101+j.val)
    have cursor := Code.tapesBelow_protects (cursor_tapesBelow i)
      (by omega : 1100 ≤ 1101+j.val)
    have load : (WordReplace.code 1110 (1101+i.val)).protectsTape (1101+j.val)=true := by
      fin_cases i <;> fin_cases j <;> first | exact False.elim (hji rfl) | decide
    have test : (CountedShifted.test (1101+i.val)).protectsTape (1101+j.val)=true := by
      fin_cases i <;> fin_cases j <;> first | exact False.elim (hji rfl) | decide
    simp only [tensorTraversalCode,countedProgram,Counted.code,Code.protectsTape,Bool.and_eq_true]
    exact ⟨reset,load,test,⟨ih hjs,cursor⟩,test⟩

namespace TensorInput
variable {n B Q N W : ℕ} (d : TensorInput n B Q N W)

def numeratorAt (j : Fin 3→ℕ) : ℤ :=
  if hj : ∀i,j i<d.degree then d.coefficient (fun i => ⟨j i,hj i⟩) else 0

def payload (d : TensorInput n B Q N W) : List (Fin 3)→(Fin 3→ℕ)→List Bool
  | [],j => Codec.int (d.numeratorAt j)
  | i::is,j => (List.range d.degree).flatMap fun r => payload d is (Function.update j i r)

end TensorInput

#print axioms tensorTraversal_protects_counter
end Maxwell.Continuum.Profile.WaveMachine.Runtime
