import Maxwell.Continuum.CalibrationSeedRootReset
import Maxwell.Continuum.CalibrationSeedRootDestination
import Maxwell.Continuum.RationalDataflowArrayTransfer

/-! Stable data and descriptor invariants between the six fixed seed
producers. All natural scratch and rational accumulation registers reset. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def producerCode (j : Fin 3) (part : Fin 2) : Code :=
  .seq (NatAssign.code (destinationPlan j part)) (.seq (emissionCode j part) resetCode)
def producerWidth (B : ℕ) : ℕ := emissionWidth (destinationWidth B)
def producerCost (B : ℕ) : ℕ := destinationCost B+emissionCost (destinationWidth B)+resetCost (producerWidth B)
def producerChanged : Finset ℕ := rowWorkspace∪RationalDataflow.workspace slots∪{37}
def entryParts (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3)) (u : Fin 3→ℕ)
    (j : Fin 3) (part : Fin 2) (v : ℕ→Parts) : Parts :=
  termsValues M D a u j part parities (resetParts v) 27

theorem destinationWidth_ge (B : ℕ) : B≤destinationWidth B := by
  change B≤512*(B+1)
  omega
theorem producerWidth_ge_destination (B : ℕ) : destinationWidth B≤producerWidth B :=
  termsWidth_ge _ _
theorem producerWidth_ge (B : ℕ) : B≤producerWidth B :=
  (destinationWidth_ge B).trans (producerWidth_ge_destination B)

theorem terms_keep (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (j : Fin 3) (part : Fin 2) (ps : List Corner.Parity) (v : ℕ→Parts)
    (i : ℕ) (hi : i∉([24,25,26,27]:List ℕ)) : termsValues M D a u j part ps v i=v i := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih =>
    rw [termsValues,ih]
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    unfold guardedValues
    split_ifs
    · rw [term_keep p j part _ _ ⟨hi.2.1,hi.2.2.1,hi.2.2.2⟩,Function.update_of_ne hi.1]
    · rfl

theorem resetParts_terms (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts) :
    resetParts (termsValues M D a u j part parities (resetParts v))=resetParts v := by
  funext i
  by_cases hi : i∈([24,25,26,27]:List ℕ)
  · simp [resetParts,resetList_values,hi]
  · rw [resetParts,resetList_values,ite_eq_right hi,terms_keep _ _ _ _ _ _ _ _ _ hi]

theorem fixed_destination_keep (j : Fin 3) (part : Fin 2) (n : ℕ→ℕ) (i : ℕ)
    (hi : i∈fixedFields) : destinationValues j part n i=n i := by
  apply destinationValues_keep
  have hd : Disjoint fixedFields ({772,773,783,789,790}:Finset ℕ) := by decide
  exact fun hm=>Finset.disjoint_left.mp hd hi hm

theorem destination_coordinates (j : Fin 3) (part : Fin 2) (n : ℕ→ℕ) :
    coordinates (destinationValues j part n)=coordinates n := by
  funext k
  fin_cases k <;> simp [coordinates,fixed_destination_keep j part n 753 (by decide),
    fixed_destination_keep j part n 754 (by decide),fixed_destination_keep j part n 755 (by decide)]

theorem arrays_after_reset {T U : ℕ} {a : PartArray.Table T} {b : PartArray.Table U} {s t : Store}
    (cache : a.Ready s) (output : b.OutputReady s)
    (frame : BinaryPrecision.Frame (rowWorkspace∪RationalDataflow.workspace slots) s.val t.val)
    (scratch : NatAssign.Scratch t.val) : a.Ready t ∧ b.OutputReady t := by
  have z : BankArray.Scratch t.val :=
    ⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),scratch 3 (by decide),
     RationalAccumulator.blank_of_eq (frame.tapes 5 (by decide)) cache.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (frame.tapes 6 (by decide)) cache.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (frame.tapes 8 (by decide)) cache.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (frame.tapes 9 (by decide)) cache.scratch.2.2.2.2.2.2.2⟩
  have seven := RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) cache.seven
  constructor
  · apply cache.transfer frame.memory _ z seven
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact frame.tapes _ (by decide)
  · apply output.transfer frame.memory _ z seven
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact frame.tapes _ (by decide)

#print axioms resetParts_terms
end Maxwell.Continuum.Calibration.SeedRoot
