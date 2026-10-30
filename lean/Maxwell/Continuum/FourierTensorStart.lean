import Maxwell.Continuum.FourierTensorStartData
import Maxwell.Continuum.FourierTensorTraversalCode

/-! Charged initialization of the complete tensor compiler state from
the generated Fourier-row input and retained runtime parameters. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorStart
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def code : Code := .seq TensorRegisters.code TensorSetup.code
def changed : Finset ℕ := TensorRegisters.changed∪TensorSetup.changed
def freshPorts : Finset ℕ := TensorRegisters.ports∪Profile.Runtime.CacheAllocation.inputs∪savedPorts∪
  {144,146,680,216,1099,1100,1101,1102,1103,1110}

theorem register_table_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame TensorRegisters.changed s.val t.val) (hz : NatAssign.Scratch t.val) :
    a.Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,200,202,203,204,205}:Finset ℕ)) :=
    f.tapes i (Finset.disjoint_left.mp (by decide : Disjoint
      ({5,6,7,8,9,200,202,203,204,205}:Finset ℕ) TensorRegisters.changed) hi)
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

theorem phase_frame {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) : Phase.Runtime.Clean t.val := by
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint ((PhaseMachine.Runtime.ids.erase 652).erase 653) changed) hi)) (h i hi)

theorem floor_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) changed) hi)) (h.2 i hi)

theorem cost_bound (Q N W H : ℕ) : 2^100+2^180*(W+H+TensorSetup.slotWidth Q N+4)^2≤
    2^184*(W+H+waveWorkBits (8*Q) N+16)^2 := by
  have hs : (W+H+TensorSetup.slotWidth Q N+4)^2≤(W+H+waveWorkBits (8*Q) N+16)^2 :=
    Nat.pow_le_pow_left (by unfold TensorSetup.slotWidth;omega) 2
  have hp : 1≤(W+H+waveWorkBits (8*Q) N+16)^2 := one_le_pow₀ (by omega)
  nlinarith only [hs,hp]

theorem executes {R B Q N W p : ℕ} (d : TensorInput (RowArithmetic.rowCount R) B Q N W)
    (old : Table p) (H : ℕ) (hm : old.MetadataWidth H) (v : ℕ→Parts)
    (hw : WidthBank RowArithmetic.bank W v) (hR : R.bits.length≤W)
    (hheaders : TensorSetup.CanonicalHeaders d.source)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hcache : d.cache=TensorSetup.buffer Q N R d.source s.val.memory)
    (hr : Ready RowArithmetic.bank (ModePrepare.canonical v) s)
    (ha : d.source.Ready s) (ho : old.OutputReady s)
    (hphase : Phase.Runtime.Clean s.val) (hfloor : DyadicFloor.Clean s.val)
    (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val) (hradius : Word s.val 311 R)
    (hfresh : ∀i∈freshPorts,Blank s.val i) :
    ∃cost t,Executes input tape code cost s t ∧
      cost≤2^184*(W+H+waveWorkBits (8*Q) N+16)^2 ∧
      Nonempty (TensorState d t) ∧ TensorBuffers W Finset.univ t ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,r0,query0,f0⟩ := TensorRegisters.executes v input tape s hr
    (fun i hi => hfresh i (by simp only [freshPorts,Finset.mem_union];exact Or.inl (Or.inl (Or.inl hi))))
  have source0 := register_table_frame ha f0 r0.2
  have target0 : old.OutputReady u := by
    apply ho.transfer f0.memory _ source0.scratch source0.seven
    intro i hi
    apply f0.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [TensorRegisters.changed,TensorRegisters.ports,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  have setup0 : NatAssign.Bank setupIds (initialSetup Q N) u.val := by
    intro i hi
    exact RationalAccumulator.word_of_eq (f0.tapes i (Finset.disjoint_left.mp
      (by decide : Disjoint setupIds TensorRegisters.changed) hi)) (hsetup i hi)
  have zero0 (i : ℕ) (hi : i∈Profile.Runtime.CacheAllocation.inputs ∨ i=1100 ∨ i=1110 ∨ i=216) :
      Blank u.val i := by
    have hsmall : i∉TensorRegisters.changed := by
      simp only [Profile.Runtime.CacheAllocation.inputs,Finset.mem_Icc] at hi
      simp only [TensorRegisters.changed,TensorRegisters.ports,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
    apply RationalAccumulator.blank_of_eq (f0.tapes i hsmall) (hfresh i _)
    simp only [freshPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have bank0 := TensorSetup.initial_bank d.source hheaders u source0 setup0
    (RationalAccumulator.word_of_eq (f0.tapes 311 (by decide)) hradius)
    (fun i hi => zero0 i (Or.inl hi)) (zero0 1100 (by tauto)) (zero0 1110 (by tauto))
  obtain ⟨c1,t,e1,hc1,r1,source1,target1,dim1,aliases1,degree1,_,_,f1⟩ := TensorSetup.executes Q N R W H
    d.smallWidth d.source old (TensorRegisters.values v)
    (fun i _ => TensorSetup.initial_width d.source d.sourceWidth d.qWidth d.nWidth hR i)
    hm input tape u bank0 r0 source0 target0 (zero0 216 (by tauto))
  have frame := (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have target : d.cache.OutputReady t := by
    rw [hcache]
    simpa only [f0.memory] using target1
  have finalSetup : NatAssign.Bank setupIds (initialSetup Q N) t.val := by
    intro i hi
    by_cases hdim : i∈dimensionIds
    · exact dim1 i hdim
    · have hout : i∉changed := by
        have hs := hi
        simp only [setupIds,dimensionIds,parameterIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs hdim
        simp only [changed,TensorRegisters.changed,TensorRegisters.ports,TensorSetup.changed,
          dimensionWorkspace,dimensionIds,Profile.Runtime.CacheAllocation.changed,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
        omega
      exact RationalAccumulator.word_of_eq (frame.tapes i hout) (hsetup i hi)
  have zero (i : ℕ) (hi : i∈({144,146,680,1099,1101,1102,1103}:Finset ℕ) ∨ i∈savedPorts) :
      Blank t.val i := by
    have hout : i∉changed := Finset.disjoint_left.mp
      (by decide : Disjoint (({144,146,680,1099,1101,1102,1103}:Finset ℕ)∪savedPorts) changed)
      (Finset.mem_union.mpr hi)
    apply RationalAccumulator.blank_of_eq (frame.tapes i hout) (hfresh i _)
    simp only [freshPorts,Finset.mem_union]
    rcases hi with hi|hi
    · exact Or.inr ((by decide : ({144,146,680,1099,1101,1102,1103}:Finset ℕ)⊆
        {144,146,680,216,1099,1100,1101,1102,1103,1110}) hi)
    · exact Or.inl (Or.inr hi)
  have state : TensorState d t :=
    { values := TensorRegisters.values v
      table := d.cache
      factor :=
        { ready := r1.restrict (Finset.subset_insert _ _)
          phase := phase_frame hphase frame
          floor := floor_frame hfloor frame
          setup := finalSetup
          source := source1
          output := target
          power := zero 144 (by simp)
          powerCount := zero 146 (by simp)
          inner := zero 680 (by simp)
          saved := fun i hi => zero i (Or.inr hi) }
      ready := r1
      width := TensorRegisters.width v W (by have := d.smallWidth;omega) hw
      metadata := CacheTableMetadata.refl _
      query := 0
      queryWidth := by simp
      queryWord := RationalAccumulator.word_of_eq (f1.tapes 1048 (by decide)) query0
      aliasBuffer := ⟨[],by simp,(RationalAccumulator.zero_word_iff_blank _ _).mpr (zero 1099 (by simp))⟩
      storedAliases := aliases1
      storedDegree := degree1 }
  refine ⟨c0+c1,t,e0.seq e1,(Nat.add_le_add hc0 hc1).trans (cost_bound Q N W H),⟨state⟩,?_,frame⟩
  intro i _
  refine ⟨[],by simp,(RationalAccumulator.zero_word_iff_blank _ _).mpr (zero (1101+i.val) ?_)⟩
  left
  have := i.isLt
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorStart
