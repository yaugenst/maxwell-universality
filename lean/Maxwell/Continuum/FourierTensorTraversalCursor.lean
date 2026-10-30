import Maxwell.Continuum.FourierTensorTraversalData
import Maxwell.Continuum.FourierTensorCursor

/-! Actual reset and advance of tensor indices, preserving the finite
input, the wave workspace, and the stored runtime dimensions. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace TensorState
variable {n B Q N W : ℕ} {d : TensorInput n B Q N W} {s t : Store}

def index (h : TensorState d s) (i : Fin 3) : ℕ := (h.values (17+i.val)).positive

def arithmetic_frame (h : TensorState d s) (w : ℕ→Parts)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val)
    (hr : Ready termBank w t) (hw : WidthBank termBank W w) : TensorState d t := {
  values := w
  table := h.table
  factor := h.factor.term_frame f hr
  ready := hr
  width := hw
  metadata := h.metadata
  query := h.query
  queryWidth := h.queryWidth
  queryWord := word_of_eq (f.tapes 1048 (by decide)) h.queryWord
  aliasBuffer := h.aliasBuffer.of_eq (f.tapes 1099 (by decide))
  storedAliases := word_of_eq (f.tapes 1100 (by decide)) h.storedAliases
  storedDegree := word_of_eq (f.tapes 1110 (by decide)) h.storedDegree }

end TensorState

def resetCursorCode (i : Fin 3) : Code :=
  NatAssign.code (literalStage (17+i.val) (Parts.literal 0))

theorem resetCursor_tapesBelow (i : Fin 3) : (resetCursorCode i).tapesBelow 1100=true := by
  fin_cases i <;> decide

theorem cursor_tapesBelow (i : Fin 3) : (cursorCode i).tapesBelow 1100=true := by
  fin_cases i <;> decide

theorem resetCursor_executes {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (i : Fin 3) (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : TensorState d s) :
    ∃cost t,∃next : TensorState d t,Executes input tape (resetCursorCode i) cost s t ∧
      cost ≤ stageCost W ∧ next.index=Function.update h.index i 0 ∧
      BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val := by
  have hi : 17+i.val∈termBank := by
    have := i.isLt
    simp only [termBank,tensorBank,Finset.mem_insert,Finset.mem_union,Finset.mem_Ico]
    exact Or.inr (Or.inr ⟨by omega,by omega⟩)
  have hw : (Parts.literal (0:ℚ)).Width W :=
    naturalLiteral_width 0 W (by simp) (by have := d.smallWidth;omega)
  obtain ⟨c,t,e,hc,hr,f⟩ := literal_executes termBank (17+i.val) hi
    (Parts.literal 0) h.values W hw h.width input tape s h.ready
  let next := h.arithmetic_frame _ f hr (h.width.update _ hw)
  refine ⟨c,t,next,e,hc,?_,f⟩
  funext j
  by_cases hji : j=i
  · subst j
    simp [next,TensorState.index,TensorState.arithmetic_frame,Parts.literal]
  · have hv : 17+j.val≠17+i.val := by intro he;apply hji;apply Fin.ext;omega
    simp only [next,TensorState.index,TensorState.arithmetic_frame,Function.update_of_ne hv,
      Function.update_of_ne hji]

theorem advanceCursor_executes {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (i : Fin 3) (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : TensorState d s)
    (hj : h.index i<d.degree) :
    ∃cost t,∃next : TensorState d t,Executes input tape (cursorCode i) cost s t ∧
      cost ≤ 2*operationCost W+1 ∧ next.index=Function.update h.index i (h.index i+1) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val := by
  have hbits : (h.index i+1).bits.length ≤ W :=
    (RationalWords.bits_mono (by omega : h.index i+1 ≤ d.degree)).trans d.degreeWidth
  obtain ⟨c,t,e,hc,_hf,hr,hw,f⟩ := cursor_executes i (h.index i) W h.values h.width
    (by have := d.smallWidth;omega) hbits rfl input tape s h.factor h.ready
  let next := h.arithmetic_frame _ f hr hw
  refine ⟨c,t,next,e,hc,?_,f⟩
  funext j
  have hj0 : 17+j.val≠0 := by omega
  by_cases hji : j=i
  · subst j
    simp [next,TensorState.index,TensorState.arithmetic_frame,cursorValues,
      NaturalChannel.replace]
  · have hv : 17+j.val≠17+i.val := by intro he;apply hji;apply Fin.ext;omega
    simp only [next,TensorState.index,TensorState.arithmetic_frame,cursorValues,
      Function.update_of_ne hv,Function.update_of_ne hj0,Function.update_of_ne hji]

#print axioms resetCursor_executes
#print axioms advanceCursor_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
