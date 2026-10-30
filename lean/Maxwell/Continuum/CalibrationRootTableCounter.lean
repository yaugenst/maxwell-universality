import Maxwell.Continuum.CalibrationRootTablePrepared

/-! The outer coefficient count is copied from its computed runtime word,
and its padded countdown is cleared by charged tape scans. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem Context.counter_word_frame {S : Finset ℕ} {N : ℕ} {n : ℕ→ℕ} {v : ℕ→Parts}
    {s t : Store} (h : Context S N n v s) (f : BinaryPrecision.Frame {201} s.val t.val) :
    Context S N n v t := by
  have keep (i : ℕ) (hi : i≠201) := f.tapes i (by simpa only [Finset.mem_singleton] using hi)
  have rational : Ready S v t := by
    constructor
    · intro i hi
      have hout : i≠201 := by
        intro he;subst i
        exact outside_workspace S 201 (Or.inr (by decide)) (Finset.mem_union_right _ hi)
      exact word_of_eq (keep i hout) (h.rational.1 i hi)
    · intro i hi
      exact blank_of_eq (keep i (by omega)) (h.rational.2 i hi)
  refine ⟨rational,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hh := RootFrequency.ids_bounds i hi
    exact word_of_eq (keep i (by omega)) (h.natural i hi)
  · intro i hi
    exact blank_of_eq (keep i (by omega)) (h.scratch i hi)
  · intro i hi
    have hout : i≠201 := by
      intro he;subst i
      exact (show 201∉GlueMachine.Runtime.ids.erase 640 by decide) hi
    exact blank_of_eq (keep i hout) (h.glue i hi)
  · intro i hi
    have hout : i≠201 := by
      intro he;subst i
      exact (show 201∉(PhaseMachine.Runtime.ids.erase 652).erase 653 by decide) hi
    exact blank_of_eq (keep i hout) (h.phase i hi)
  · exact word_of_eq (keep 640 (by decide)) h.glue_precision
  · exact word_of_eq (keep 652 (by decide)) h.phase_range
  · exact word_of_eq (keep 653 (by decide)) h.phase_precision

theorem output_counter_frame {T : ℕ} {a : PartArray.Table T} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame {201} s.val t.val) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i≠201) := f.tapes i (by simpa only [Finset.mem_singleton] using hi)
  have z : BankArray.Scratch t.val :=
    ⟨blank_of_eq (keep 0 (by decide)) h.scratch.1,
      blank_of_eq (keep 1 (by decide)) h.scratch.2.1,
      blank_of_eq (keep 2 (by decide)) h.scratch.2.2.1,
      blank_of_eq (keep 3 (by decide)) h.scratch.2.2.2.1,
      blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ z (blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

def TableState.counter_word_frame {T grid N B I W : ℕ} [NeZero grid]
    {scale : Parts} {remaining : ℕ} {s t : Store}
    (h : TableState T grid N B I W scale remaining s)
    (f : BinaryPrecision.Frame {201} s.val t.val) : TableState T grid N B I W scale remaining t where
  table := h.table
  remaining_le := h.remaining_le
  context := h.context.counter_word_frame f
  ready := output_counter_frame h.ready f
  metadata := h.metadata
  fit := h.fit
  separated := h.separated
  correct := h.correct

theorem counter_executes (T : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hT : Word s.val 570 T) (hz : Blank s.val 201) :
    ∃cost t,Executes input tape (NaturalImport.code 570 201) cost s t ∧
      cost≤31*T.bits.length+39 ∧ Word t.val 201 T ∧
      BinaryPrecision.Frame {201} s.val t.val := by
  have bank : NatAssign.Bank {201} (fun _ => 0) s.val := by
    intro i hi
    have he : i=201 := by simpa only [Finset.mem_singleton] using hi
    subst i
    exact (zero_word_iff_blank _ _).mpr hz
  obtain ⟨c,t,e,hc,b,f⟩ := NaturalImport.executes {201} 570 201 (by decide) (by decide)
    (fun _ => 0) T.bits input tape s bank hT
  refine ⟨c,t,e,?_,?_,f⟩
  · simpa only [show (0:ℕ).bits.length=0 by rfl,Nat.mul_zero,zero_add] using hc
  · simpa only [Function.update_self,addressValue_bits] using b 201 (by decide)

#print axioms counter_executes
end Maxwell.Continuum.RationalDataflow.RootTable
