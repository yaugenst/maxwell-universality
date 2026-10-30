import Maxwell.Continuum.FourierTensorModeAllocationSetup

/-! The Fourier row destination is allocated over the actual memory.
Its source-disjoint layout and represented runtime countdown are returned
alongside the unchanged calibrated source table. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def allocatedCode : Code := .seq code Profile.Runtime.CacheAllocation.code
def allocatedChanges : Finset ℕ := setupChanged∪Profile.Runtime.CacheAllocation.changed
def buffer (M L R P : ℕ) (a : Table (2*aliasArraySize R)) (memory : ℕ→Bool) :
    Table (5*RowArithmetic.rowCount R) :=
  Profile.Runtime.memoryTable (5*RowArithmetic.rowCount R) (slotWidth M L R P)
    (heap R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) (slotWidth_pos M L R P) memory

theorem setup_table_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame setupChanged s.val t.val) (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,200,202,203,204,205}:Finset ℕ)) :=
    f.tapes i (Finset.disjoint_left.mp (by decide : Disjoint
      ({5,6,7,8,9,200,202,203,204,205}:Finset ℕ) setupChanged) hi)
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven,
    BankArray.word_of_eq (keep 200 (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem allocated_ready_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s) (f : BinaryPrecision.Frame allocatedChanges s.val t.val)
    (hz : NatAssign.Scratch t.val) : RationalDataflow.Ready S v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hout : i∉allocatedChanges := by
    intro hm
    have bounds : i<4 ∨ 107 ≤ i ∧ i<1000 := by
      simp only [allocatedChanges,setupChanged,Profile.Runtime.CacheAllocation.changed,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    rcases bounds with hz'|hs
    · have := RationalDataflow.ids_ge S i hi;omega
    · exact outside_workspace S i (Or.inr hs) (Finset.mem_union_right _ hi)
  exact RationalAccumulator.word_of_eq (f.tapes i hout) (h.1 i hi)

theorem allocated_cost (W H Z : ℕ) :
    2^116*(W+2)^2+2^60*(2^32*(W+1)+H+Z+3)^2≤2^140*(W+H+Z+3)^2 := by
  have h0 := Nat.pow_le_pow_left (show W+2≤W+H+Z+3 by omega) 2
  have h1 : 2^32*(W+1)+H+Z+3≤2^33*(W+H+Z+3) := by omega
  have h2 := Nat.pow_le_pow_left h1 2
  rw [mul_pow] at h2
  nlinarith only [h0,h2,Nat.zero_le ((W+H+Z+3)^2)]

theorem allocated_executes {p : ℕ} (M L R P W H : ℕ) (hW : 5≤W)
    (a : Table (2*aliasArraySize R)) (old : Table p)
    (h : InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) W) (hmeta : old.MetadataWidth H)
    (S : Finset ℕ) (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (ho : old.OutputReady s) (hz216 : Blank s.val 216) :
    ∃cost t,Executes input tape allocatedCode cost s t ∧
      cost≤2^140*(W+H+slotWidth M L R P+3)^2 ∧
      RationalDataflow.Ready S v t ∧ a.Ready t ∧ (buffer M L R P a s.val.memory).OutputReady t ∧
      NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) t.val ∧
      Word t.val 201 (RowArithmetic.rowCount R) ∧ Word t.val 145 P ∧ Blank t.val 216 ∧
      BinaryPrecision.Frame allocatedChanges s.val t.val := by
  let vals := values M L R P (addressValue a.width) (addressValue a.basePositive)
    (addressValue a.baseNegative) (addressValue a.baseDenominator)
  obtain ⟨c0,u,e0,hc0,b0,w0,z0,f0⟩ := executes M L R P _ _ _ _ W hW h input tape s hb hs.2
  have source0 := setup_table_frame ha f0 z0
  have target0 : old.OutputReady u := by
    apply ho.transfer f0.memory _ source0.scratch source0.seven
    intro i hi
    exact f0.tapes i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [setupChanged,Finset.mem_insert,Finset.mem_singleton]
      omega)
  have allocBank : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs vals u.val := by
    intro i hi
    exact b0 i ((by decide : Profile.Runtime.CacheAllocation.inputs⊆ids) hi)
  have allocWidth : ∀i∈Profile.Runtime.CacheAllocation.inputs,(vals i).bits.length≤2^32*(W+1) :=
    fun i hi => w0 i ((by decide : Profile.Runtime.CacheAllocation.inputs⊆ids) hi)
  have awidth : vals 726=slotWidth M L R P := values_width _ _ _ _ _ _ _ _
  obtain ⟨c1,t,e1,hc1,source1,target1,_,_,z216,f1⟩ := Profile.Runtime.CacheAllocation.executes a old vals
    (2^32*(W+1)) H (by rw [awidth];exact slotWidth_pos M L R P) allocWidth hmeta
    input tape u allocBank source0 target0 (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) hz216)
  have target : (buffer M L R P a s.val.memory).OutputReady t := by
    have hlen : vals 725=5*RowArithmetic.rowCount R := values_length _ _ _ _ _ _ _ _
    rw [hlen] at target1
    simpa only [vals,values_width,values_heap,f0.memory,buffer] using target1
  have hz : NatAssign.Scratch t.val := by
    intro i hi
    interval_cases i
    · exact source1.scratch.1
    · exact source1.scratch.2.1
    · exact source1.scratch.2.2.1
    · exact source1.scratch.2.2.2.1
  have frame := (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  refine ⟨c0+c1,t,e0.seq e1,?_,allocated_ready_frame hs frame hz,source1,target,?_,?_,?_,z216,frame⟩
  · rw [awidth] at hc1
    exact (Nat.add_le_add hc0 hc1).trans (allocated_cost W H (slotWidth M L R P))
  · intro i hi
    have hh := b0 i ((by decide : ModeIndex.ports⊆ids) hi)
    rw [values_modeIndex _ _ _ _ _ _ _ _ i hi] at hh
    apply RationalAccumulator.word_of_eq (f1.tapes i _) hh
    have bounds := Finset.mem_Icc.mp hi
    simp only [Profile.Runtime.CacheAllocation.changed,Finset.mem_insert,Finset.mem_singleton]
    omega
  · have hh := b0 201 (by simp [ids])
    rw [values_rowCount] at hh
    exact RationalAccumulator.word_of_eq (f1.tapes 201 (by decide)) hh
  · have hh := b0 145 (by simp [ids])
    rw [values_precision] at hh
    exact RationalAccumulator.word_of_eq (f1.tapes 145 (by decide)) hh

#print axioms allocated_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
