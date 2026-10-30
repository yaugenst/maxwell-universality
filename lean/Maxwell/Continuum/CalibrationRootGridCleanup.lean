import Maxwell.Continuum.CalibrationRootGridCoefficient
import Maxwell.Continuum.RuntimeCounterClear

/-! The quadrature countdown is cleared by actual charged code, so its
return contract can be reused by the next coefficient evaluation. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def CoefficientState.clear_frame {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s t : Store}
    (h : CoefficientState S grid N frequency B I initial s)
    (f : BinaryPrecision.Frame {342} s.val t.val) (hz : Blank t.val 342) :
    CoefficientState S grid N frequency B I initial t where
  parts := h.parts
  naturals := h.naturals
  rational_bank := by
    refine ⟨?_,?_⟩
    · intro i hi
      have hout : i≠342 := by
        intro he;subst i
        exact FractionWord.outside S 342 (by decide) (Finset.mem_union_right _ hi)
      exact word_of_eq (f.tapes i (by simpa only [Finset.mem_singleton] using hout)) (h.rational_bank.1 i hi)
    · intro i hi
      exact blank_of_eq (f.tapes i (by simp only [Finset.mem_singleton];omega)) (h.rational_bank.2 i hi)
  good := h.good
  width := h.width
  facts := h.facts
  natural_bank i hi := word_of_eq
    (f.tapes i (by have := ids_bounds i hi;simp only [Finset.mem_singleton];omega)) (h.natural_bank i hi)
  external := h.external
  real_value := h.real_value
  imag_value := h.imag_value
  scratch i hi := blank_of_eq (f.tapes i (by simp only [Finset.mem_singleton];omega)) (h.scratch i hi)
  glue i hi := blank_of_eq (f.tapes i (by
    intro he
    have hi342 : i=342 := by simpa only [Finset.mem_singleton] using he
    subst i
    exact (show 342∉GlueMachine.Runtime.ids.erase 640 by decide) hi)) (h.glue i hi)
  phase i hi := blank_of_eq (f.tapes i (by
    intro he
    have hi342 : i=342 := by simpa only [Finset.mem_singleton] using he
    subst i
    exact (show 342∉(PhaseMachine.Runtime.ids.erase 652).erase 653 by decide) hi)) (h.phase i hi)
  precision_glue := word_of_eq (f.tapes 640 (by decide)) h.precision_glue
  phase_range := word_of_eq (f.tapes 652 (by decide)) h.phase_range
  precision_phase := word_of_eq (f.tapes 653 (by decide)) h.precision_phase
  cube := word_of_eq (f.tapes 343 (by decide)) h.cube
  one := word_of_eq (f.tapes 344 (by decide)) h.one
  counterWord := []
  counter := (zero_word_iff_blank _ _).mpr hz
  counter_length := Nat.zero_le _

theorem CoefficientState.clear_executes {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CoefficientState S grid N frequency B I initial s) :
    ∃ (cost : ℕ) (t : Store) (out : CoefficientState S grid N frequency B I initial t),
      Executes input tape (.call (TapeOps.clear 342)) cost s t ∧
      cost≤6*(grid^3).bits.length+4 ∧ out.parts=h.parts ∧ out.naturals=h.naturals ∧
      Blank t.val 342 ∧ BinaryPrecision.Frame {342} s.val t.val := by
  rcases h.counter with ⟨origin,ho⟩
  obtain ⟨t,e,z,f⟩ := RuntimeCounter.clear_executes 342 input tape h.counterWord origin s ho
  exact ⟨6*h.counterWord.length+4,t,h.clear_frame f z,e,
    by have := h.counter_length;omega,rfl,rfl,z,f⟩

def completeNaturals {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : CoefficientState S grid N frequency B I initial s) : ℕ→ℕ :=
  Function.update (Function.update (Function.update h.naturals 342 0) 343 (grid^3)) 344 1

theorem CoefficientState.complete_bank {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : CoefficientState S grid N frequency B I initial s) (hz : Blank s.val 342) :
    NatAssign.Bank (ids∪clockIds) (completeNaturals h) s.val := by
  intro i hi
  by_cases h344 : i=344
  · subst i;simpa only [completeNaturals,Function.update_self] using h.one
  by_cases h343 : i=343
  · subst i
    simpa only [completeNaturals,Function.update_of_ne (by decide : (343:ℕ)≠344),Function.update_self] using h.cube
  by_cases h342 : i=342
  · subst i
    simpa only [completeNaturals,Function.update_of_ne (by decide : (342:ℕ)≠344),
      Function.update_of_ne (by decide : (342:ℕ)≠343),Function.update_self]
      using (zero_word_iff_blank _ _).mpr hz
  have hid : i∈ids := by
    rcases Finset.mem_union.mp hi with hi|hi
    · exact hi
    · simp only [clockIds,Finset.mem_insert,Finset.mem_singleton] at hi
      have he : i=331 := by omega
      subst i;decide
  simpa only [completeNaturals,Function.update_of_ne h344,Function.update_of_ne h343,
    Function.update_of_ne h342] using h.natural_bank i hid

#print axioms CoefficientState.clear_executes
#print axioms CoefficientState.complete_bank
end Maxwell.Continuum.RationalDataflow.RootGrid
