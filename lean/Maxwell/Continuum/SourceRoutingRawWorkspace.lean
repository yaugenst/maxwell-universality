import Maxwell.Continuum.SourceRoutingTreeWorkspace

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Workspace
open Structured
open RationalAccumulator (Blank)

theorem raw_of_frame {s t : BitRAMState} {changed : Finset ℕ} (hs : NodeVisit.Clean s)
    (hz : NatAssign.Scratch t) (hf : BinaryPrecision.Frame changed s t)
    (hkeep : ∀i∈raw,4 ≤ i→i∉changed) : NodeVisit.Clean t := by
  apply (raw_iff t).mpr
  intro i hi
  by_cases hlo : i<4
  · exact hz i hlo
  · exact RationalAccumulator.blank_of_eq (hf.tapes i (hkeep i hi (by omega))) ((raw_iff s).mp hs i hi)

#print axioms raw_of_frame
end Maxwell.Cost.RoutingPorts.Complete.Tree.Workspace
