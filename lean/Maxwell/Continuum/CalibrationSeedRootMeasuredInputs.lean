import Maxwell.Continuum.CalibrationSeedRootAllocationBounds
import Maxwell.Continuum.RationalDataflowStoredWidths

/-! The measured budget bounds the actual cached headers and raw channels.
Canonical-word equality derives these facts from the concrete input store. -/
namespace Maxwell.Continuum.Calibration.SeedRoot.Allocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

theorem cache_words {T : ℕ} (a : PartArray.Table T) (n : ℕ→ℕ) (s : Store)
    (bank : NatAssign.Bank sourceIds n s.val) (ready : a.Ready s) :
    a.width=(n 200).bits ∧ a.basePositive=(n 202).bits ∧
    a.baseNegative=(n 203).bits ∧ a.baseDenominator=(n 204).bits :=
  a.words_of_bank sourceIds n (by decide) s bank ready

theorem cache_metadata {T : ℕ} (a : PartArray.Table T) (n : ℕ→ℕ) (s : Store)
    (bank : NatAssign.Bank sourceIds n s.val) (ready : a.Ready s) : a.MetadataWidth (budget n) :=
  a.metadata_of_bank sourceIds n (budget n) (by decide) (budget_bound n) (budget_cache n) s bank ready

theorem raw_width (n : ℕ→ℕ) (v : ℕ→Parts) (s : Store)
    (bank : NatAssign.Bank sourceIds n s.val) (ready : Ready slots v s) : WidthBank slots (budget n) v :=
  raw_width_of_bank slots sourceIds n v (budget n) (by decide) (budget_bound n) s bank ready

theorem cache_disjoint {T : ℕ} (a : PartArray.Table T) (n : ℕ→ℕ) (s : Store)
    (bank : NatAssign.Bank sourceIds n s.val) (ready : a.Ready s)
    (count : T=2*(2*n 751+1)^3) (memory : ℕ→Bool) : a.SeparatedFrom (table n memory) := by
  obtain ⟨w,p,q,d⟩:=cache_words a n s bank ready
  exact table_disjoint a n count
    (by rw [w,addressValue_bits]) (by rw [p,addressValue_bits])
    (by rw [q,addressValue_bits]) (by rw [d,addressValue_bits]) memory

#print axioms cache_metadata
#print axioms raw_width
end Maxwell.Continuum.Calibration.SeedRoot.Allocation
