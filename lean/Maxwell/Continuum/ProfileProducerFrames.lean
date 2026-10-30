import Maxwell.Continuum.ProfileRoundedExecution
import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowArrayOutputCost
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! The profile evaluator and literal memory writes preserve one another's
scratch, dimensions, and saved coefficient. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem rounded_metadata_outside (i : ℕ)
    (hi : i∈({5,6,7,8,9,37,210,212,213,214,215,664,700}:Finset ℕ)) : i∉roundedWorkspace := by
  have hd : Disjoint ({5,6,7,8,9,37,210,212,213,214,215,664,700}:Finset ℕ) roundedWorkspace := by decide
  exact fun hm => Finset.disjoint_left.mp hd hi hm

theorem outputReady_rounded_frame {n : ℕ} {a : PartArray.Table n} {s t : Store} {v : ℕ→Parts}
    (h : a.OutputReady s) (hr : Ready dftRegisters v t)
    (f : BinaryPrecision.Frame roundedWorkspace s.val t.val) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37,210,212,213,214,215,664,700}:Finset ℕ)) :=
    f.tapes i (rounded_metadata_outside i hi)
  have scratch : BankArray.Scratch t.val :=
    ⟨hr.2 0 (by decide),hr.2 1 (by decide),hr.2 2 (by decide),hr.2 3 (by decide),
      blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem phaseClean_write {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BankArray.FrameExcept 37 s.val t.val) : Phase.Runtime.Clean t.val := by
  have hd : Disjoint (Finset.range 10∪{37}) PhaseMachine.Runtime.ids := by decide
  intro i hi
  have him := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have h10 : 10 ≤ i := by
    by_contra hn
    exact Finset.disjoint_left.mp hd (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))) him
  have h37 : i≠37 := by intro he;subst i;exact Finset.disjoint_left.mp hd (by simp) him
  exact blank_of_eq (f.2.2.2.1 i (Or.inr h10) h37) (h i hi)

theorem glueClean_write {s t : Store} (h : Glue.Clean s.val)
    (f : BankArray.FrameExcept 37 s.val t.val) : Glue.Clean t.val := by
  have hd : Disjoint (Finset.range 10∪{37}) GlueMachine.Runtime.ids := by decide
  intro i hi
  have him := Finset.mem_of_mem_erase hi
  have h10 : 10 ≤ i := by
    by_contra hn
    exact Finset.disjoint_left.mp hd (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))) him
  have h37 : i≠37 := by intro he;subst i;exact Finset.disjoint_left.mp hd (by simp) him
  exact blank_of_eq (f.2.2.2.1 i (Or.inr h10) h37) (h i hi)

theorem floorClean_write {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BankArray.FrameExcept 37 s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨blank_of_eq (f.2.2.2.1 4 (Or.inl rfl) (by decide)) h.1,?_⟩
  intro i hi
  have bounds : 10 ≤ i ∧ i≠37 := by
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact blank_of_eq (f.2.2.2.1 i (Or.inr bounds.1) bounds.2) (h.2 i hi)

theorem DFTParameters.write_frame {D P : ℕ} {s t : Store} (h : DFTParameters D P s)
    (f : BankArray.FrameExcept 37 s.val t.val) : DFTParameters D P t :=
  ⟨word_of_eq (f.2.2.2.1 663 (by decide) (by decide)) h.precision,
    word_of_eq (f.2.2.2.1 667 (by decide) (by decide)) h.one,
    word_of_eq (f.2.2.2.1 668 (by decide) (by decide)) h.guard,
    word_of_eq (f.2.2.2.1 669 (by decide) (by decide)) h.range,
    word_of_eq (f.2.2.2.1 652 (by decide) (by decide)) h.phaseRange,
    word_of_eq (f.2.2.2.1 653 (by decide) (by decide)) h.phasePrecision,
    word_of_eq (f.2.2.2.1 640 (by decide) (by decide)) h.gluePrecision⟩

theorem stored701_write {x : Parts} {s t : Store} (h : StoredParts.Stored 701 x s.val)
    (f : BankArray.FrameExcept 37 s.val t.val) : StoredParts.Stored 701 x t.val :=
  ⟨word_of_eq (f.2.2.2.1 701 (by decide) (by decide)) h.1,
    word_of_eq (f.2.2.2.1 702 (by decide) (by decide)) h.2.1,
    word_of_eq (f.2.2.2.1 703 (by decide) (by decide)) h.2.2⟩

def RoundedResult.write_frame {grid D P U j : ℕ} {s t : Store}
    (h : RoundedResult grid D P U j s) (hr : Ready dftRegisters h.values t)
    (f : BankArray.FrameExcept 37 s.val t.val) : RoundedResult grid D P U j t :=
  ⟨h.values,hr,h.width,h.good,h.resultWidth,h.resultDenominator,h.resultValue,
    phaseClean_write h.phaseClean f,glueClean_write h.glueClean f,floorClean_write h.floorClean f,
    h.parameters.write_frame f,word_of_eq (f.2.2.2.1 144 (by decide) (by decide)) h.power⟩

#print axioms outputReady_rounded_frame
#print axioms RoundedResult.write_frame
end Maxwell.Continuum.Profile.Runtime
