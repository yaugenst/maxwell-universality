import Maxwell.Continuum.CalibrationRootGridIndex

/-! Decoder output widths are controlled by its five actual inputs.
Temporary words from earlier samples cannot cause iterative width growth. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.ArrayDecodeMachine (divModValues)
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def sourceIds : Finset ℕ := {330,331,336,337,338}
def cleanInputs (n : ℕ→ℕ) : ℕ→ℕ := fun i => if i∈sourceIds then n i else 0

theorem values_work (n : ℕ→ℕ) (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : values n i=n i := by
  apply values_keep n i
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

theorem values_clean (n : ℕ→ℕ) (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (i : ℕ) (hi : i∈ids) : values n i=values (cleanInputs n) i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · rw [values_work n i hi,values_work (cleanInputs n) i hi,hz i hi]
    have he : i∉sourceIds := by
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [sourceIds,Finset.mem_insert,Finset.mem_singleton]
      omega
    simp only [cleanInputs,ite_eq_right he]
  · obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hi
    interval_cases i <;> simp [values,dotted,dot,third,second,first,divModValues,
      NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,cleanInputs,sourceIds]

theorem values_source_width (n : ℕ→ℕ) (B : ℕ)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (hw : ∀i∈sourceIds,(n i).bits.length≤B) :
    ∀i∈ids,(values n i).bits.length≤2^8*(B+1) := by
  have hc : ∀i∈ids,(cleanInputs n i).bits.length≤B := by
    intro i _
    by_cases hs : i∈sourceIds
    · simpa only [cleanInputs,ite_eq_left hs] using hw i hs
    · simp only [cleanInputs,ite_eq_right hs,show (0:ℕ).bits.length=0 by rfl]
      exact Nat.zero_le B
  intro i hi
  rw [values_clean n hz i hi]
  exact values_width (cleanInputs n) B hc i hi

theorem values_sources (n : ℕ→ℕ) (i : ℕ) (hi : i∈sourceIds) : values n i=n i := by
  apply values_keep n i
  simp only [sourceIds,Finset.mem_insert,Finset.mem_singleton] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

#print axioms values_source_width
end Maxwell.Continuum.RationalDataflow.RootGrid
