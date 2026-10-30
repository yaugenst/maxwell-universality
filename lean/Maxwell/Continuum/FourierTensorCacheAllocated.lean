import Maxwell.Continuum.FourierTensorCacheAllocationSetup
import Maxwell.Continuum.FourierTensorTraversalData
import Maxwell.Continuum.RationalDataflowArrayTransfer

/-! A complete cache handoff computes the sizes, allocates disjoint
storage, and clears its temporary words. The tensor parameters persist. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def code : Code := .seq setupCode (.seq Profile.Runtime.CacheAllocation.code (WordCleanup.code cleared))

theorem ready_frame {v : ℕ→Parts} {s t : Store} (h : RationalDataflow.Ready termBank v s)
    (f : BinaryPrecision.Frame changed s.val t.val) (hz : NatAssign.Scratch t.val) :
    RationalDataflow.Ready termBank v t := by
  refine ⟨?_,hz⟩
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint (RationalDataflow.ids termBank) changed) hi)) (h.1 i hi)

theorem table_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame changed s.val t.val) (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,200,202,203,204,205}:Finset ℕ)) :=
    f.tapes i (Finset.disjoint_left.mp (by decide : Disjoint
      ({5,6,7,8,9,200,202,203,204,205}:Finset ℕ) changed) hi)
  have scratch : BankArray.Scratch t.val :=
    ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
     RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

theorem values_dimension (Q N R width bp bn bd i : ℕ) (hi : i∈dimensionIds) :
    values Q N R width bp bn bd i=finalDimensions Q N i := by
  rw [values,values_unchanged plan _ i (by
    simp only [dimensionIds,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [plan,NatAssign.Instruction.target]
    omega),afterDimensions,ite_eq_left hi]

theorem cost_bound (W H Z : ℕ) :
    2^156*(W+2)^2+(2^60*(setupWidth W+H+Z+3)^2+
      (12*(6*(2^8*(setupWidth W+1))+4)+1))≤2^180*(W+H+Z+4)^2 := by
  let X := W+H+Z+4
  have h0 : (W+2)^2≤X^2 := Nat.pow_le_pow_left (by dsimp [X];omega) 2
  have h1 : setupWidth W+H+Z+3≤2^55*X := by unfold setupWidth;dsimp [X];omega
  have h2 := Nat.pow_le_pow_left h1 2
  rw [mul_pow] at h2
  have hX : X≤X^2 := Nat.le_self_pow (by decide) _
  have hc : 12*(6*(2^8*(setupWidth W+1))+4)+1≤2^72*X := by unfold setupWidth;dsimp [X];omega
  change _≤2^180*X^2
  nlinarith only [h0,h2,hX,hc,Nat.zero_le (X^2)]

theorem executes {p : ℕ} (Q N R W H : ℕ) (hW : 6≤W)
    (a : Table (5*RowArithmetic.rowCount R)) (old : Table p) (v : ℕ→Parts)
    (hw : ∀i∈ids,(initial Q N R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) i).bits.length≤W)
    (hm : old.MetadataWidth H) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hn : NatAssign.Bank ids (initial Q N R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hr : RationalDataflow.Ready termBank v s) (ha : a.Ready s) (ho : old.OutputReady s)
    (h216 : Blank s.val 216) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^180*(W+H+slotWidth Q N+4)^2 ∧
      RationalDataflow.Ready termBank v t ∧ a.Ready t ∧ (buffer Q N R a s.val.memory).OutputReady t ∧
      NatAssign.Bank dimensionIds (initialDimensions Q N) t.val ∧
      Word t.val 1100 (RowArithmetic.rowCount R) ∧ Word t.val 1110 (waveDegree (8*Q) N) ∧
      (∀i∈cleared,Blank t.val i) ∧ Blank t.val 216 ∧ BinaryPrecision.Frame changed s.val t.val := by
  let vals := values Q N R (addressValue a.width) (addressValue a.basePositive)
    (addressValue a.baseNegative) (addressValue a.baseDenominator)
  obtain ⟨c0,u,e0,hc0,b0,w0,z0,f0⟩ := setup_executes Q N R _ _ _ _ W hW hw input tape s hn hr.2
  have sub0 : setupChanges⊆changed := by decide
  have source0 := table_frame ha (f0.mono sub0) z0
  have target0 : old.OutputReady u := by
    apply ho.transfer f0.memory _ source0.scratch source0.seven
    intro i hi
    apply f0.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [setupChanges,dimensionWorkspace,dimensionIds,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    omega
  have bank0 : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs vals u.val :=
    fun i hi => b0 i ((by decide : Profile.Runtime.CacheAllocation.inputs⊆ids) hi)
  have widths0 : ∀i∈Profile.Runtime.CacheAllocation.inputs,(vals i).bits.length≤setupWidth W :=
    fun i hi => w0 i ((by decide : Profile.Runtime.CacheAllocation.inputs⊆ids) hi)
  have positive : 0<vals 726 := by rw [show vals 726=slotWidth Q N from values_width _ _ _ _ _ _ _];unfold slotWidth;omega
  obtain ⟨c1,w,e1,hc1,source1,target1,b1,w1,z216,f1⟩ := Profile.Runtime.CacheAllocation.executes a old vals
    (setupWidth W) H positive widths0 hm input tape u bank0 source0 target0
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) h216)
  have bounded : WordCleanup.Bounded cleared (2^8*(setupWidth W+1)) w.val := by
    intro i hi
    by_cases hia : i∈Profile.Runtime.CacheAllocation.inputs
    · exact ⟨_,w1 i (Finset.mem_union_left _ hia),b1 i (Finset.mem_union_left _ hia)⟩
    · have hid : i∈ids := by
        simp only [cleared,List.mem_cons,List.not_mem_nil,or_false] at hi
        simp only [ids,dimensionIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        omega
      refine ⟨(vals i).bits,(w0 i hid).trans (by omega),?_⟩
      apply RationalAccumulator.word_of_eq (f1.tapes i _) (b0 i hid)
      simp only [cleared,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [Profile.Runtime.CacheAllocation.inputs,Finset.mem_Icc] at hia
      simp only [Profile.Runtime.CacheAllocation.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
  obtain ⟨c2,t,e2,hc2,z2,f2⟩ := WordCleanup.executes cleared (2^8*(setupWidth W+1)) input tape w bounded
  have sub1 : Profile.Runtime.CacheAllocation.changed⊆changed := Finset.subset_union_right
  have sub2 : cleared.toFinset⊆changed := by decide
  have frame := (f0.mono sub0).trans ((f1.mono sub1).trans (f2.mono sub2))
  have scratch : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f2.tapes i (by
      simp only [List.mem_toFinset,cleared,List.mem_cons,List.not_mem_nil,or_false];omega))
    interval_cases i
    · exact source1.scratch.1
    · exact source1.scratch.2.1
    · exact source1.scratch.2.2.1
    · exact source1.scratch.2.2.2.1
  have source := table_frame ha frame scratch
  have target : (buffer Q N R a s.val.memory).OutputReady t := by
    have hlen : vals 725=2*(waveDegree (8*Q) N+1) := values_length _ _ _ _ _ _ _
    rw [hlen] at target1
    have target' : (buffer Q N R a s.val.memory).OutputReady w := by
      simpa only [vals,values_width,values_heap,f0.memory,buffer] using target1
    apply target'.transfer f2.memory _ source.scratch source.seven
    intro i hi
    apply f2.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [List.mem_toFinset,cleared,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have retained (i : ℕ) (hi : i=710 ∨ i=711 ∨ i=1100 ∨ i=1110) : Word t.val i (vals i) := by
    apply RationalAccumulator.word_of_eq
      ((f2.tapes i (by simp only [List.mem_toFinset,cleared,List.mem_cons,List.not_mem_nil,or_false];omega)).trans
        (f1.tapes i (by simp only [Profile.Runtime.CacheAllocation.changed,Finset.mem_insert,Finset.mem_singleton];omega)))
    apply b0
    simp only [ids,dimensionIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,ready_frame hr frame scratch,source,target,?_,?_,?_,z2,
    RationalAccumulator.blank_of_eq (f2.tapes 216 (by decide)) z216,frame⟩
  · rw [show vals 726=slotWidth Q N from values_width _ _ _ _ _ _ _] at hc1
    simp only [cleared,List.length_cons,List.length_nil] at hc2
    exact (Nat.add_le_add hc0 (Nat.add_le_add hc1 hc2)).trans (cost_bound W H (slotWidth Q N))
  · intro i hi
    by_cases hQ : i=710
    · subst i
      simpa [vals,values_dimension _ _ _ _ _ _ _ 710 (by decide),finalDimensions_eq,scannedValues,
        degreeValues_eq,initialDimensions] using retained 710 (by omega)
    by_cases hN : i=711
    · subst i
      simpa [vals,values_dimension _ _ _ _ _ _ _ 711 (by decide),finalDimensions_eq,scannedValues,
        degreeValues_eq,initialDimensions] using retained 711 (by omega)
    have hic : i∈cleared := by
      simp only [dimensionIds,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [cleared,List.mem_cons,List.not_mem_nil,or_false]
      omega
    simpa [initialDimensions,hQ,hN,RationalAccumulator.zero_word_iff_blank] using z2 i hic
  · simpa only [vals,values_aliases] using retained 1100 (by omega)
  · simpa only [vals,values_degree] using retained 1110 (by omega)

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
