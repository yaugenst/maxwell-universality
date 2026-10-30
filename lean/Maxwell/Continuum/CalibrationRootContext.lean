import Maxwell.Continuum.CalibrationRootIndexedCoefficient
import Maxwell.Continuum.CalibrationRootReset

/-! The actual retained banks of a reusable root-coefficient call. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

structure Context (S : Finset ℕ) (N : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (s : Store) : Prop where
  rational : Ready S v s
  natural : NatAssign.Bank RootFrequency.ids n s.val
  scratch : ∀i,i<5 → Blank s.val i
  glue : Glue.Clean s.val
  phase : Phase.Runtime.Clean s.val
  glue_precision : Word s.val 640 N
  phase_range : Word s.val 652 1
  phase_precision : Word s.val 653 N

theorem Context.arithmetic_frame {S : Finset ℕ} {N : ℕ} {n : ℕ→ℕ} {v w : ℕ→Parts}
    {s t : Store} (h : Context S N n v s) (f : BinaryPrecision.Frame (workspace S) s.val t.val)
    (hr : Ready S w t) : Context S N n w t := by
  refine ⟨hr,?_,?_,RootSample.glue_clean_arithmetic h.glue f hr,
    Phase.Runtime.Clean.arithmetic_frame h.phase f hr,?_,?_,?_⟩
  · intro i hi
    exact word_of_eq (f.tapes i (RootFrequency.ids_outside_rational S i hi)) (h.natural i hi)
  · intro i hi
    by_cases h4 : i<4
    · exact hr.2 i h4
    have he : i=4 := by omega
    subst i
    have ho : 4∉workspace S := fun hh => RootGrid.four_outside_product S (RootGrid.rational_subset_product S hh)
    exact blank_of_eq (f.tapes 4 ho) (h.scratch 4 (by decide))
  · exact word_of_eq (f.tapes 640 (FractionWord.outside S 640 (by decide))) h.glue_precision
  · exact word_of_eq (f.tapes 652 (FractionWord.outside S 652 (by decide))) h.phase_range
  · exact word_of_eq (f.tapes 653 (FractionWord.outside S 653 (by decide))) h.phase_precision

theorem Context.natural_frame {S : Finset ℕ} {N : ℕ} {n m : ℕ→ℕ} {v : ℕ→Parts}
    {s t : Store} (h : Context S N n v s)
    (f : BinaryPrecision.Frame RootFrequency.changed s.val t.val)
    (hb : NatAssign.Bank RootFrequency.ids m t.val) (hz : ∀i,i<5 → Blank t.val i) :
    Context S N m v t :=
  ⟨RootFrequency.rational_frame h.rational f hz,hb,hz,
    RootFrequency.glue_frame h.glue f hz,RootFrequency.phase_frame h.phase f hz,
    word_of_eq (f.tapes 640 (by decide)) h.glue_precision,
    word_of_eq (f.tapes 652 (by decide)) h.phase_range,
    word_of_eq (f.tapes 653 (by decide)) h.phase_precision⟩

theorem Context.write_frame {S : Finset ℕ} {N : ℕ} {n : ℕ→ℕ} {v : ℕ→Parts}
    {s t : Store} (h : Context S N n v s) (f : BankArray.FrameExcept 37 s.val t.val)
    (hr : Ready S v t) : Context S N n v t := by
  have keep (i : ℕ) (hi : 10 ≤ i ∧ i≠37) := f.2.2.2.1 i (Or.inr hi.1) hi.2
  refine ⟨hr,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hh := RootFrequency.ids_bounds i hi
    exact word_of_eq (keep i ⟨by omega,by omega⟩) (h.natural i hi)
  · intro i hi
    by_cases h4 : i<4
    · exact hr.2 i h4
    have he : i=4 := by omega
    subst i
    exact blank_of_eq (f.2.2.2.1 4 (Or.inl rfl) (by decide)) (h.scratch 4 (by decide))
  · intro i hi
    have hh : 10 ≤ i ∧ i≠37 := (show ∀i∈GlueMachine.Runtime.ids,10 ≤ i ∧ i≠37 by decide)
      i (Finset.mem_of_mem_erase hi)
    exact blank_of_eq (keep i hh) (h.glue i hi)
  · intro i hi
    have hh : 10 ≤ i ∧ i≠37 := (show ∀i∈PhaseMachine.Runtime.ids,10 ≤ i ∧ i≠37 by decide)
      i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
    exact blank_of_eq (keep i hh) (h.phase i hi)
  · exact word_of_eq (keep 640 (by decide)) h.glue_precision
  · exact word_of_eq (keep 652 (by decide)) h.phase_range
  · exact word_of_eq (keep 653 (by decide)) h.phase_precision

theorem coefficient_context {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : RootGrid.CoefficientState S grid N frequency B I initial s) (hz : Blank s.val 342) :
    Context S N (RootGrid.completeNaturals h) h.parts s := by
  have hb := h.complete_bank hz
  have hi : RootGrid.ids∪RootGrid.clockIds=RootFrequency.ids := by decide
  rw [hi] at hb
  exact ⟨h.rational_bank,hb,h.scratch,h.glue,h.phase,h.precision_glue,h.phase_range,h.precision_phase⟩

theorem complete_grid {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : RootGrid.CoefficientState S grid N frequency B I initial s) : RootGrid.completeNaturals h 331=grid := by
  simpa only [RootGrid.completeNaturals,Function.update_of_ne (by decide : (331:ℕ)≠344),
    Function.update_of_ne (by decide : (331:ℕ)≠343),Function.update_of_ne (by decide : (331:ℕ)≠342)]
    using h.facts.grid_eq

theorem complete_zero {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : RootGrid.CoefficientState S grid N frequency B I initial s) :
    ∀i∈NaturalQuotient.workPorts,RootGrid.completeNaturals h i=0 := by
  intro i hi
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  simpa only [RootGrid.completeNaturals,Function.update_of_ne (by omega : i≠344),
    Function.update_of_ne (by omega : i≠343),Function.update_of_ne (by omega : i≠342)]
    using h.facts.work_zero i hi

def returnWidth (grid B : ℕ) : ℕ := RootGrid.naturalWidth (RootGrid.runtimeWidth B)+(grid^3).bits.length+1

theorem complete_width {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : RootGrid.CoefficientState S grid N frequency B I initial s) :
    ∀i∈RootFrequency.ids,(RootGrid.completeNaturals h i).bits.length≤returnWidth grid B := by
  intro i hi
  by_cases h344 : i=344
  · subst i
    simp only [RootGrid.completeNaturals,Function.update_self,show (1:ℕ).bits.length=1 by rfl]
    unfold returnWidth
    omega
  by_cases h343 : i=343
  · subst i
    simp only [RootGrid.completeNaturals,Function.update_of_ne h344,Function.update_self]
    unfold returnWidth
    omega
  by_cases h342 : i=342
  · subst i
    simp only [RootGrid.completeNaturals,Function.update_of_ne h344,
      Function.update_of_ne h343,Function.update_self,show (0:ℕ).bits.length=0 by rfl]
    omega
  have hid : i∈RootGrid.ids := by
    simp only [RootFrequency.ids,RootGrid.ids,Finset.mem_union,Finset.mem_Icc] at hi ⊢
    rcases hi with hi|hi
    · exact Or.inl hi
    · exact Or.inr ⟨hi.1,by omega⟩
  simp only [RootGrid.completeNaturals,Function.update_of_ne h344,
    Function.update_of_ne h343,Function.update_of_ne h342]
  exact (h.facts.all_width i hid).trans (by unfold returnWidth;omega)

#print axioms coefficient_context
#print axioms complete_width
end Maxwell.Continuum.RationalDataflow.RootTable
