import Maxwell.Continuum.CalibrationRootGridCoefficient
import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! Actual output-table metadata survives root coefficient evaluation, and
indexed writes preserve the complete retained elementary-call state. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem small_outside_coefficient (S : Finset ℕ) (i : ℕ) (hi : i<1000)
    (ho : i∉coefficientWorkspace ∅) : i∉coefficientWorkspace S := by
  have hp := RootSample.small_not_ports S i hi
  have hp0 := RootSample.small_not_ports ∅ i hi
  simp only [coefficientWorkspace,startWorkspace,sumWorkspace,sampleWorkspace,decodeWorkspace,
    RootProduct.workspace,Glue.workspace,Glue.allIds,Phase.Runtime.workspace,
    Phase.Runtime.allIds,RationalDataflow.workspace,RationalDataflow.ids,Finset.mem_union] at *
  tauto

theorem coefficient_protected (S : Finset ℕ) :
    ∀i∈([5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]:List ℕ),
      i∉coefficientWorkspace S := by
  intro i hi
  apply small_outside_coefficient S i
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  · have all : ∀i∈([5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]:List ℕ),
        i∉coefficientWorkspace ∅ := by decide
    exact all i hi

theorem coefficient_outputReady {T : ℕ} (a : PartArray.Table T) {S : Finset ℕ}
    {v : ℕ→Parts} {s t : Store} (ha : a.OutputReady s)
    (f : BinaryPrecision.Frame (coefficientWorkspace S) s.val t.val)
    (hr : Ready S v t) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i∈([5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]:List ℕ)) :=
    f.tapes i (coefficient_protected S i hi)
  apply ha.transfer f.memory ?_ ?_ (blank_of_eq (keep 7 (by simp)) ha.seven)
  · intro i hi
    apply keep i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  · exact ⟨hr.2 0 (by decide),hr.2 1 (by decide),hr.2 2 (by decide),hr.2 3 (by decide),
      blank_of_eq (keep 5 (by simp)) ha.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by simp)) ha.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by simp)) ha.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by simp)) ha.scratch.2.2.2.2.2.2.2⟩

def CoefficientState.write_frame {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s t : Store}
    (h : CoefficientState S grid N frequency B I initial s)
    (f : BankArray.FrameExcept 37 s.val t.val) (hr : Ready S h.parts t) :
    CoefficientState S grid N frequency B I initial t where
  parts := h.parts
  naturals := h.naturals
  rational_bank := hr
  good := h.good
  width := h.width
  facts := h.facts
  natural_bank i hi := word_of_eq (f.2.2.2.1 i (Or.inr (by have := ids_bounds i hi;omega))
    (by have := ids_bounds i hi;omega)) (h.natural_bank i hi)
  external := h.external
  real_value := h.real_value
  imag_value := h.imag_value
  scratch i hi := by
    by_cases h4 : i<4
    · exact hr.2 i h4
    have he : i=4 := by omega
    subst i
    exact blank_of_eq (f.2.2.2.1 4 (Or.inl rfl) (by decide)) (h.scratch 4 (by decide))
  glue i hi := by
    have hh : 10 ≤ i ∧ i≠37 := (show ∀i∈GlueMachine.Runtime.ids,10 ≤ i ∧ i≠37 by decide)
      i (Finset.mem_of_mem_erase hi)
    exact blank_of_eq (f.2.2.2.1 i (Or.inr hh.1) hh.2) (h.glue i hi)
  phase i hi := by
    have hh : 10 ≤ i ∧ i≠37 := (show ∀i∈PhaseMachine.Runtime.ids,10 ≤ i ∧ i≠37 by decide)
      i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
    exact blank_of_eq (f.2.2.2.1 i (Or.inr hh.1) hh.2) (h.phase i hi)
  precision_glue := word_of_eq (f.2.2.2.1 640 (Or.inr (by decide)) (by decide)) h.precision_glue
  phase_range := word_of_eq (f.2.2.2.1 652 (Or.inr (by decide)) (by decide)) h.phase_range
  precision_phase := word_of_eq (f.2.2.2.1 653 (Or.inr (by decide)) (by decide)) h.precision_phase
  cube := word_of_eq (f.2.2.2.1 343 (Or.inr (by decide)) (by decide)) h.cube
  one := word_of_eq (f.2.2.2.1 344 (Or.inr (by decide)) (by decide)) h.one
  counterWord := h.counterWord
  counter := BankArray.word_of_eq (f.2.2.2.1 342 (Or.inr (by decide)) (by decide)) h.counter
  counter_length := h.counter_length

#print axioms coefficient_outputReady
#print axioms CoefficientState.write_frame
end Maxwell.Continuum.RationalDataflow.RootGrid
