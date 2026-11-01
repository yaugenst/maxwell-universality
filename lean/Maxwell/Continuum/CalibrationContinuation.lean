import Maxwell.Cost.Structured.NatAssign

/-! The descriptor bank carried between array-generation stages. Its frame
lemmas are independent of any coefficient-generation implementation. -/
namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost

/-- Disjoint ports carried from coefficient generation into inverse setup. -/
def continuationPorts : Finset ℕ := Finset.Icc 107 140 ∪ Finset.Icc 300 309 ∪
  ({206,216} ∪ Finset.Icc 530 534)
def ContinuationFrame (s t : BitRAMState) : Prop :=
  ∀ k∈continuationPorts, t.tapes k=s.tapes k

theorem ContinuationFrame.refl (s : BitRAMState) : ContinuationFrame s s := fun _ _ => rfl
theorem ContinuationFrame.trans {s t u : BitRAMState}
    (h : ContinuationFrame s t) (g : ContinuationFrame t u) : ContinuationFrame s u :=
  fun k hk => (g k hk).trans (h k hk)
end Maxwell.Continuum.Calibration.ArrayDecodeMachine
