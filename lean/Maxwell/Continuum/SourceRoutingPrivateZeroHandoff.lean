import Maxwell.Continuum.SourceRoutingPrivateZero
import Maxwell.Continuum.SourceRoutingTreeDivision

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateZero
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem clean_of_binary {s t : Store} {changed : Finset ℕ} (hs : Clean s)
    (hf : BinaryPrecision.Frame changed s.val t.val) (hchange : changed⊆Division.work) : Clean t := by
  intro i hi
  have disjoint : Disjoint banks Division.work := by decide
  exact RationalAccumulator.blank_of_eq
    (hf.tapes i (fun hm => Finset.disjoint_left.mp disjoint hi (hchange hm))) (hs i hi)

theorem bank_of_frame {s t : Store} {v : ℕ→ℕ} (hs : NatAssign.Bank Division.ids v s.val)
    (hf : Frame s.val t.val) : NatAssign.Bank Division.ids v t.val := by
  intro i hi
  apply RationalAccumulator.word_of_eq (hf.tapes i (Or.inr (Division.ids_lower i hi)) ?_ ?_) (hs i hi)
  · intro he;subst i;exact (show (37 : ℕ)∉Division.ids by decide) hi
  · have disjoint : Disjoint Division.ids banks := by decide
    exact Finset.disjoint_left.mp disjoint hi

theorem Frame.archive {s t : BitRAMState} (hf : Frame s t) : ArchiveFrame ({37}∪banks) s t := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_⟩
  intro i hi hn
  have h37 : i≠37 := by intro he;subst i;exact hn (by simp)
  exact hf.tapes i hi h37 (fun hh => hn (Finset.mem_union_right _ hh))

#print axioms bank_of_frame
end Maxwell.Cost.RoutingPorts.Complete.Tree.PrivateZero
