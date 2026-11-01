import Maxwell.Continuum.CalibrationBasisForcingPrepare
import Maxwell.Continuum.CalibrationContinuation
import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! The forcing entry computed from a runtime alias index is written to the
allocated raw array. Existing array values are not hypotheses of correctness. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray
open ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048

def storeCode (column : Fin 24) : Code := .seq (prepareCode column) (writeAtCode 310 32)
def protectedPorts : List ℕ := [5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]
attribute [local irreducible] bank code prepareCode

theorem outside_bank (k : ℕ) (hk : k<1000) (hw : k∉workPorts) : k∉ids bank := by
  intro h
  rcases Finset.mem_union.mp h with hp|hwork
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    have h0 := positivePort_ge i
    have h1 := negativePort_ge i
    have h2 := denominatorPort_ge i
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  · exact hw hwork

theorem protected_external (k : ℕ) (hk : k∈protectedPorts) : k∉changed := by
  have hp : 5≤k ∧ k<1000 ∧ k∉workPorts ∧ k∉ArrayDecodeMachine.ports ∧
      k∉NaturalQuotient.workPorts := by
    simp only [protectedPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [changed,naturalIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨by omega,⟨outside_bank k hp.2.1 hp.2.2.1,hp.2.2.2.1⟩,hp.2.2.2.2⟩

def inversePorts : Finset ℕ := continuationPorts∪(Finset.Icc 321 332∪Finset.Icc 580 584)
def sourceContinuationPorts : Finset ℕ := inversePorts∪{200,202,203,204,205}
def sourceLoopPorts : Finset ℕ := sourceContinuationPorts∪{376,570,571,572,573}
def SourceFrame (s t : BitRAMState) : Prop := ∀k∈sourceLoopPorts,t.tapes k=s.tapes k
theorem SourceFrame.refl (s : BitRAMState) : SourceFrame s s := fun _ _ => rfl
theorem SourceFrame.trans {s t u : BitRAMState} (h : SourceFrame s t) (g : SourceFrame t u) :
    SourceFrame s u := fun k hk => (g k hk).trans (h k hk)
theorem SourceFrame.continuation {s t : BitRAMState} (h : SourceFrame s t) : ContinuationFrame s t :=
  fun k hk => h k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hk)))

theorem continuation_outside (k : ℕ) (hk : k∈sourceLoopPorts) :
    10≤k ∧ k∉changed ∧ k≠37 ∧ k≠201 := by
  have bounds : 10≤k ∧ k<1000 ∧ k∉workPorts ∧ k∉ArrayDecodeMachine.ports ∧
      k∉NaturalQuotient.workPorts ∧ k≠37 ∧ k≠201 := by
    simp only [sourceLoopPorts,sourceContinuationPorts,inversePorts,continuationPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [workPorts,temporaryPorts,RationalMagnitude.ids,ArrayDecodeMachine.ports,
      NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨bounds.1,?_,bounds.2.2.2.2.2⟩
  simp only [changed,naturalIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨by omega,⟨outside_bank k bounds.2.1 bounds.2.2.1,bounds.2.2.2.1⟩,bounds.2.2.2.2.1⟩

theorem coordinateLoad_low (n : ℕ → ℕ) (k : ℕ) (hk : k<1000) :
    NatAssign.values coordinateLoad n k=n k := by
  rw [coordinateLoad_values]
  simp (disch := omega) only [writeParts,positivePort,negativePort,denominatorPort,Function.update_of_ne]

theorem prepared_index (n : ℕ → ℕ) (out : ℕ → Parts) : preparedNaturals n out 310=n 310 := by
  rw [preparedNaturals,ite_eq_right (outside_bank 310 (by decide) (by decide)),coordinateLoad_low _ _ (by decide)]
  simp only [output,second,first,divModValues,
    Function.update_of_ne (by decide : (310:ℕ)≠320),Function.update_of_ne (by decide : (310:ℕ)≠319),
    Function.update_of_ne (by decide : (310:ℕ)≠318),Function.update_of_ne (by decide : (310:ℕ)≠317),
    Function.update_of_ne (by decide : (310:ℕ)≠316),Function.update_of_ne (by decide : (310:ℕ)≠315)]
  exact prepared_other n 310 (by decide) (by decide) (by decide)

theorem prepared_radius (n : ℕ → ℕ) (out : ℕ → Parts) : preparedNaturals n out 311=n 311 := by
  rw [preparedNaturals,ite_eq_right (outside_bank 311 (by decide) (by decide)),coordinateLoad_low _ _ (by decide),output_radius]

theorem prepared_work (n : ℕ → ℕ) (out : ℕ → Parts) (k : ℕ) (hk : k∈NaturalQuotient.workPorts) :
    preparedNaturals n out k=n k := by
  have bounds : k<1000 ∧ k∉workPorts ∧ k∉ArrayDecodeMachine.ports := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> decide
  rw [preparedNaturals,ite_eq_right (outside_bank k bounds.1 bounds.2.1),
    coordinateLoad_low _ _ bounds.1,output_outside _ _ bounds.2.2]

theorem output_frame {T : ℕ} (a : Table T) (s t : Store) (ha : a.OutputReady s)
    (out : ℕ → Parts) (ready : Ready bank out t) (frame : BinaryPrecision.Frame changed s.val t.val) :
    a.OutputReady t := by
  have keep (k : ℕ) (hk : k∈protectedPorts) := frame.tapes k (protected_external k hk)
  apply ha.transfer frame.memory ?_ ?_ (RationalAccumulator.blank_of_eq (keep 7 (by simp [protectedPorts])) ha.seven)
  · intro k hk
    apply keep k
    simp only [List.mem_cons,List.not_mem_nil,or_false,protectedPorts] at hk ⊢
    tauto
  · exact ⟨ready.2 0 (by decide),ready.2 1 (by decide),ready.2 2 (by decide),ready.2 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by simp [protectedPorts])) ha.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by simp [protectedPorts])) ha.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by simp [protectedPorts])) ha.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by simp [protectedPorts])) ha.scratch.2.2.2.2.2.2.2⟩

theorem store_executes (column : Fin 24) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀k∈ids bank,n k=dataValues v k)
    (hzwork : ∀k∈NaturalQuotient.workPorts,n k=0) (hg : Good bank v)
    (B W : ℕ) (hB : 103≤B) (hw : ∀k∈naturalIds,(n k).bits.length≤B)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 310=i.val)
    (a : Table (aliasArraySize R)) (hm : a.MetadataWidth W)
    (hfit : 625≤addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank naturalIds n s.val)
    (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k) (ha : a.OutputReady s) :
    ∃cost t out,Executes input tape (storeCode column) cost s t ∧
      cost≤2^655*(B+5)^2+2^20*(max B W+5)^2 ∧
      Ready bank out t ∧ Good bank out ∧ WidthBank bank (prepareWidth B) out ∧ (out 32).Width 625 ∧
      NatAssign.Bank naturalIds (preparedNaturals n out) t.val ∧
      (∀k∈naturalIds,(preparedNaturals n out k).bits.length≤prepareWidth B) ∧
      (a.set i (out 32)).OutputReady t ∧
      (out 32).value=rationalRightCoupling (rationalBasisField column)
        (arrayAliasAt R i) (arrayPolarizationAt R i) ∧
      (∀k,k<32 → k≠13 → k≠14 → k≠15 → k≠23 → out k=v k) ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      t.val.memory=a.writeMemory i (out 32) s.val.memory ∧
      t.val.tapes 201=s.val.tapes 201 ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧ SourceFrame s.val t.val := by
  obtain ⟨c0,u,out,e0,hc0,r0,g0,w0,entryWidth,b0,nw,value,keep,z0,f0⟩ := prepare_executes column n v hn hzwork hg
    B hB hw R i hR hi input tape s hs hz
  have au := output_frame a s u ha out r0 f0
  have index : RationalAccumulator.Word u.val 310 i.val := by
    have hh := b0 310 (naturalIds_decode (by decide))
    simpa only [prepared_index,hi] using hh
  have positive : 0<addressValue a.width := by omega
  have member : 32∈bank := by simp only [bank,Finset.mem_range];omega
  obtain ⟨c1,t,e1,hc1,r1,oa,memory,frame⟩ := writeAt_executes a bank 310 (by decide) 32 member out i
    positive (entryWidth.mono hfit) hsep input tape i.val.bits (addressValue_bits _) u r0 au index
  have naturalBank : NatAssign.Bank naturalIds (preparedNaturals n out) t.val := by
    intro k hk
    have h37 : k≠37 := by
      intro he
      subst k
      exact (protected_external 37 (by simp [protectedPorts])) (Finset.mem_union_right _ hk)
    exact RationalAccumulator.word_of_eq (frame.2.2.2.1 k (Or.inr (naturalIds_ge k hk)) h37) (b0 k hk)
  have blank (k : ℕ) (hk : k<5) : RationalAccumulator.Blank t.val k := by
    by_cases h4 : k<4
    · exact r1.2 k h4
    · have he : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq (frame.2.2.2.1 4 (Or.inl rfl) (by decide)) (z0 4 (by decide))
  refine ⟨c0+c1,t,out,e0.seq e1,?_,r1,g0,w0,entryWidth,naturalBank,nw,oa,value,keep,blank,?_,?_,
    frame.1.trans f0.inputHead,frame.2.1.trans f0.randomCursor,frame.2.2.1.trans f0.output,?_⟩
  · have indexWidth : i.val.bits.length≤max B W := by
      rw [← hi]
      exact (hw 310 (naturalIds_decode (by decide))).trans (le_max_left B W)
    have cb := a.writeCost_bound (max B W) (hm.mono (le_max_right B W)) i.val.bits indexWidth (out 32)
    change c1≤a.writeCost i.val.bits (out 32) at hc1
    omega
  · rw [memory,f0.memory]
  · exact (frame.2.2.2.1 201 (Or.inr (by decide)) (by decide)).trans
      (f0.tapes 201 (protected_external 201 (by simp [protectedPorts])))

  · intro k hk
    have h := continuation_outside k hk
    exact (frame.2.2.2.1 k (Or.inr h.1) h.2.2.1).trans (f0.tapes k h.2.1)

#print axioms store_executes
end Maxwell.Continuum.Calibration.BasisForcing
