import Maxwell.Continuum.CalibrationInverseDescriptorInput
import Maxwell.Continuum.RationalDataflowArrayTransfer

/-! Concrete layout and array preservation for the computed descriptor stage. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] budget rawWidth dimension slotWidth bankWidth values

def selected (R slot base Q : ℕ) (cold : ℕ→ℕ) : ℕ→ℕ := initial (inputs R slot base Q cold)

theorem selected_parameters (R slot base Q : ℕ) (cold : ℕ→ℕ) :
    selected R slot base Q cold 311=R ∧ selected R slot base Q cold 570=tableSize (aliasArraySize R) ∧
    selected R slot base Q cold 571=slot ∧ selected R slot base Q cold 572=base ∧
    selected R slot base Q cold 304=R-3 := by
  simp [selected,initial,inputs]

theorem selected_headers (R slot base Q : ℕ) (cold : ℕ→ℕ) :
    selected R slot base Q cold 210=slot ∧ selected R slot base Q cold 212=base ∧
    selected R slot base Q cold 213=base+tableSize (aliasArraySize R)*slot ∧
    selected R slot base Q cold 214=base+2*tableSize (aliasArraySize R)*slot := by
  simp [selected,initial,inputs]

theorem selected_dimension (R slot base Q : ℕ) (cold : ℕ→ℕ) :
    dimension (selected R slot base Q cold)=aliasArraySize R := by
  rw [dimension,(selected_parameters R slot base Q cold).1]

theorem selected_heap (R slot base Q : ℕ) (cold : ℕ→ℕ) :
    heap (selected R slot base Q cold)=base+3*tableSize (aliasArraySize R)*slot := by
  rw [heap,(selected_parameters R slot base Q cold).2.1,
    (selected_parameters R slot base Q cold).2.2.1,(selected_parameters R slot base Q cold).2.2.2.1]

theorem selected_metadata (R slot base Q : ℕ) (cold : ℕ→ℕ)
    (a : Table (tableSize (aliasArraySize R))) (layout:SourceLayout a base)
    (width:addressValue a.width=slot) : a.MetadataWidth (rawWidth (selected R slot base Q cold)) := by
  have w:=budget_bound (selected R slot base Q cold) 210 (by decide)
  have p:=budget_bound (selected R slot base Q cold) 212 (by decide)
  have n:=budget_bound (selected R slot base Q cold) 213 (by decide)
  have d:=budget_bound (selected R slot base Q cold) 214 (by decide)
  rw [(selected_headers R slot base Q cold).1] at w
  rw [(selected_headers R slot base Q cold).2.1] at p
  rw [(selected_headers R slot base Q cold).2.2.1] at n
  rw [(selected_headers R slot base Q cold).2.2.2] at d
  have bound:budget (selected R slot base Q cold)≤rawWidth (selected R slot base Q cold):=by
    unfold rawWidth
    omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · have canonical:a.width=slot.bits:=layout.canonical.trans (congrArg Nat.bits width)
    simpa only [canonical] using w.trans bound
  · simpa only [layout.positive] using p.trans bound
  · simpa only [layout.negative,width] using n.trans bound
  · simpa only [layout.denominator,width] using d.trans bound
  · rw [a.clock_length,width,rawWidth,(selected_parameters R slot base Q cold).2.2.1]
    omega

theorem ready_transfer {n m : ℕ} (a : Table n) (b : Table m) (s t : Store)
    (source:a.Ready s) (target:b.OutputReady s) (scratch:NatAssign.Scratch t.val)
    (frame:BinaryPrecision.Frame startChanged s.val t.val) : a.Ready t ∧ b.OutputReady t := by
  have keep (k : ℕ) (hk:k∈([5,6,7,8,9,37,200,202,203,204,205,210,212,213,214,215]:List ℕ)) :
      t.val.tapes k=s.val.tapes k := by
    apply frame.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    simp only [startChanged,changed,Finset.mem_insert,Finset.mem_singleton]
    omega
  have ws:BankArray.Scratch t.val:=⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),scratch 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by simp)) source.scratch.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by simp)) source.scratch.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by simp)) source.scratch.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by simp)) source.scratch.2.2.2.2.2.2.2⟩
  have seven:=RationalAccumulator.blank_of_eq (keep 7 (by simp)) source.seven
  constructor
  · exact source.transfer frame.memory (fun k hk=>keep k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢;omega)) ws seven
  · exact target.transfer frame.memory (fun k hk=>keep k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢;omega)) ws seven

#print axioms selected_metadata
#print axioms ready_transfer
end Maxwell.Continuum.Calibration.InverseDescriptor
