import Maxwell.Continuum.CalibrationCoefficientHeader

/-! Continuation words are returned by the actual coefficient execution
proof, including restored heads after source reads. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow

theorem ContinuationFrame.blank206 {s t : BitRAMState}
    (h : ContinuationFrame s t) (hs : RationalAccumulator.Blank s 206) :
    RationalAccumulator.Blank t 206 :=
  RationalAccumulator.blank_of_eq (h 206 (by decide)) hs

theorem ContinuationFrame.blank216 {s t : BitRAMState}
    (h : ContinuationFrame s t) (hs : RationalAccumulator.Blank s 216) :
    RationalAccumulator.Blank t 216 :=
  RationalAccumulator.blank_of_eq (h 216 (by decide)) hs

theorem ContinuationFrame.naturalInputs {s t : BitRAMState} {v : ℕ → ℕ}
    (h : ContinuationFrame s t) (hs : NatAssign.Bank (Finset.Icc 300 309) v s) :
    NatAssign.Bank (Finset.Icc 300 309) v t := by
  intro k hk
  exact RationalAccumulator.word_of_eq (h k (Finset.mem_union_left _ (Finset.mem_union_right _ hk)))
    (hs k hk)

theorem ContinuationFrame.descriptorUnused {s t : BitRAMState} {v : ℕ → ℕ}
    (h : ContinuationFrame s t) (hs : NatAssign.Bank (Finset.Icc 107 140) v s) :
    NatAssign.Bank (Finset.Icc 107 140) v t := by
  intro k hk
  exact RationalAccumulator.word_of_eq (h k (Finset.mem_union_left _ (Finset.mem_union_left _ hk)))
    (hs k hk)

#print axioms ContinuationFrame.naturalInputs

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
