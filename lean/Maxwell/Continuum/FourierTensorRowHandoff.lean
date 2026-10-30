import Maxwell.Continuum.FourierTensorModeStored
import Maxwell.Continuum.RationalDataflowTableHeaderSwap

/-! The generated Fourier rows become the next input table by charged
counter cleanup and an actual exchange of the two array headers. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.RowHandoff
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def cleared : List ℕ := [144,145,201,725,726,727,728]
def changed : Finset ℕ := cleared.toFinset∪insert 216 headerSlots
def code : Code := .seq (WordCleanup.code cleared) headerSwapCode

theorem ready_cleanup {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s) (f : BinaryPrecision.Frame cleared.toFinset s.val t.val) :
    RationalDataflow.Ready S v t := by
  refine ⟨?_,?_⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq (f.tapes i _) (h.1 i hi)
    intro him
    have bounds : 107 ≤ i ∧ i<1000 := by
      simp only [List.mem_toFinset,cleared,List.mem_cons,List.not_mem_nil,or_false] at him
      omega
    exact outside_workspace S i (Or.inr bounds) (Finset.mem_union_right _ hi)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (f.tapes i (by
      simp only [List.mem_toFinset,cleared,List.mem_cons,List.not_mem_nil,or_false]
      omega)) (h.2 i hi)

theorem table_cleanup {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame cleared.toFinset s.val t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈({0,1,2,3,5,6,7,8,9,200,202,203,204,205}:Finset ℕ)) :=
    f.tapes i (Finset.disjoint_left.mp (by decide : Disjoint
      ({0,1,2,3,5,6,7,8,9,200,202,203,204,205}:Finset ℕ) cleared.toFinset) hi)
  have scratch : BankArray.Scratch t.val :=
    ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h.scratch.1,
     RationalAccumulator.blank_of_eq (keep 1 (by decide)) h.scratch.2.1,
     RationalAccumulator.blank_of_eq (keep 2 (by decide)) h.scratch.2.2.1,
     RationalAccumulator.blank_of_eq (keep 3 (by decide)) h.scratch.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

theorem floor_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) changed) hi)) (h.2 i hi)

theorem executes {n m : ℕ} (a : Table n) (b : Table m) (S : Finset ℕ) (v : ℕ→Parts)
    (P W H : ℕ) (hma : a.MetadataWidth W) (hmb : b.MetadataWidth W)
    (allocation : ℕ→ℕ) (haw : ∀i∈Profile.Runtime.CacheAllocation.inputs,(allocation i).bits.length≤H)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hf : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) (hpp : Word s.val 145 P)
    (hcount : ∃xs : List Bool,xs.length≤W ∧ BankArray.Word s.val 201 xs)
    (hall : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs allocation s.val)
    (h216 : Blank s.val 216) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^12*(P+W+H+4)^2 ∧
      RationalDataflow.Ready S v t ∧ b.Ready t ∧ a.OutputReady t ∧ DyadicFloor.Clean t.val ∧
      (∀i∈cleared,Blank t.val i) ∧ Blank t.val 216 ∧ BinaryPrecision.Frame changed s.val t.val := by
  have bounded : WordCleanup.Bounded cleared (P+W+H+1) s.val := by
    intro i hi
    simp only [cleared,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · refine ⟨(2^P:ℕ).bits,?_,hp⟩
      rw [Nat.size_eq_bits_len,Nat.size_pow]
      omega
    · exact ⟨P.bits,(Machin.Runtime.nat_bits_le_self P).trans (by omega),hpp⟩
    · obtain ⟨xs,hx,word⟩ := hcount
      exact ⟨xs,hx.trans (by omega),word⟩
    · exact ⟨(allocation 725).bits,(haw 725 (by decide)).trans (by omega),hall 725 (by decide)⟩
    · exact ⟨(allocation 726).bits,(haw 726 (by decide)).trans (by omega),hall 726 (by decide)⟩
    · exact ⟨(allocation 727).bits,(haw 727 (by decide)).trans (by omega),hall 727 (by decide)⟩
    · exact ⟨(allocation 728).bits,(haw 728 (by decide)).trans (by omega),hall 728 (by decide)⟩
  obtain ⟨c0,u,e0,hc0,z0,f0⟩ := WordCleanup.executes cleared (P+W+H+1) input tape s bounded
  have a0 := table_cleanup ha f0
  have b0 : b.OutputReady u := by
    apply hb.transfer f0.memory _ a0.scratch a0.seven
    intro i hi
    apply f0.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [List.mem_toFinset,cleared,List.mem_cons,List.not_mem_nil,or_false]
    omega
  obtain ⟨c1,t,e1,hc1,r1,b1,a1,z216,f1⟩ := headerSwap_executes a b W hma hmb S v
    input tape u (ready_cleanup hr f0) a0 b0
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) h216)
  have frame := (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  refine ⟨c0+c1,t,e0.seq e1,?_,r1,b1,a1,floor_frame hf frame,?_,z216,frame⟩
  · simp only [cleared,List.length_cons,List.length_nil] at hc0
    have hx : P+W+H+4≤(P+W+H+4)^2 := Nat.le_self_pow (by decide) _
    nlinarith only [hc0,hc1,hx,Nat.zero_le P,Nat.zero_le H]
  · intro i hi
    apply RationalAccumulator.blank_of_eq (f1.tapes i _) (z0 i hi)
    simp only [cleared,List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [headerSlots,Finset.mem_insert,Finset.mem_singleton]
    omega

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.RowHandoff
