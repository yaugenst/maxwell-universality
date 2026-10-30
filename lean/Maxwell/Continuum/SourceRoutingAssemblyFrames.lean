import Maxwell.Continuum.SourceRoutingAssemblyCleanup

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem frame_trans {s t u : BitRAMState} (h : Node.Frame s t) (j : Node.Frame t u) : Node.Frame s u :=
  ⟨j.inputHead.trans h.inputHead,j.randomCursor.trans h.randomCursor,j.output.trans h.output,
    fun i hi h37 hn => (j.tapes i hi h37 hn).trans (h.tapes i hi h37 hn)⟩

theorem setup_frame {s t : BitRAMState} (hf : BinaryPrecision.Frame setupWork s t) : Node.Frame s t := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_⟩
  intro i hi _ hn
  apply hf.tapes
  have subset : setupWork⊆({0,1,2,3}:Finset ℕ)∪NodeCleanup.banks.toFinset := by decide
  intro hm
  rcases Finset.mem_union.mp (subset hm) with hm|hm
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hm;omega
  · exact hn (List.mem_toFinset.mp hm)

theorem metadata_frame {s t : BitRAMState} (hf : ChildPermutation.MetadataFrame s t) : Node.Frame s t := by
  refine ⟨hf.1,hf.2.2.1,hf.2.2.2.1,?_⟩
  intro i _ _ hn
  apply hf.2.2.2.2.1
  intro hi
  simp only [ChildPermutation.MetadataPrivate] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals exact hn (by decide)

theorem pass_frame {s t : BitRAMState} (hf : ChildPermutation.LoopFrame s t) : Node.Frame s t := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_⟩
  intro i hi h37 hn
  apply hf.2.2.2.1 i hi
  · intro he;subst i;exact hn (by decide)
  · intro he;subst i;exact hn (by decide)
  · simp only [ChildPermutation.Private,DoublingInit.Private,DoublingPass.Private]
    intro hp
    rcases hp with hp|hp
    · exact h37 hp
    · apply hn
      simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false];omega

theorem cleanup_frame {s t : BitRAMState} (hf : BinaryPrecision.Frame live.toFinset s t) : Node.Frame s t := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_⟩
  intro i _ _ hn
  apply hf.tapes
  have subset : live.toFinset⊆NodeCleanup.banks.toFinset := by decide
  exact fun hi => hn (List.mem_toFinset.mp (subset hi))

#print axioms pass_frame
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
