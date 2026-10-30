import Maxwell.Continuum.CalibrationCoefficientPreservation
import Maxwell.Continuum.CalibrationInverseAllocationBounds

/-! Actual transition from a generated raw table to the shared-denominator
converter: reset arithmetic temporaries, allocate its wider destination,
and install the computed table length as the runtime countdown. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow ArrayDecodeMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

def inversePrepareCode : Code := .seq runtimeResetCode
  (.seq Allocation.code (WordReplace.code 306 201))
def allocationInputs (v : ℕ → ℕ) : ℕ → ℕ := Function.update v 310 0
def inversePreparedValues {n : ℕ} (a : PartArray.Table n) (v unused : ℕ → ℕ) : ℕ → ℕ :=
  assembledValues a (Allocation.outputValues (allocationInputs v)) unused

def inversePrepareCost (U B H width countLength count : ℕ) : ℕ :=
  2^108*(U+3)^2+2^60*(B+H+width+3)^2+6*countLength+15*count.bits.length+21

theorem allocationInputs_fixed (v : ℕ → ℕ) (k : ℕ) (hk : k≠310) : allocationInputs v k=v k :=
  Function.update_of_ne hk _ _

theorem inverse_prepare_executes {n m : ℕ} (a : PartArray.Table (tableSize n))
    (old : PartArray.Table m) (rawHeap : ℕ) (hc : SourceLayout a rawHeap)
    (logical : ℕ → Parts) (natural d unused : ℕ → ℕ) (U B H W : ℕ)
    (hU : 1≤U) (hUW : U≤W) (haMeta : a.MetadataWidth W) (hoMeta : old.MetadataWidth H)
    (hn : ∀ k∈ids RawFree.neighborRegisters, natural k=dataValues logical k)
    (hw : ∀ k∈emissionIds, (natural k).bits.length≤U)
    (hp : ∀ k∈matrixParameters, (logical k).Width U ∧ (logical k).Valid)
    (hd : ∀ k∈Finset.Icc 300 309, (d k).bits.length≤B)
    (hu : ∀ k∈Finset.Icc 107 140, (unused k).bits.length≤B) (hwidth : 0<d 301)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (s : Store)
    (hbank : NatAssign.Bank emissionIds natural s.val)
    (hinputs : NatAssign.Bank (Finset.Icc 300 309) d s.val)
    (hunused : NatAssign.Bank (Finset.Icc 107 140) unused s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (ho : old.OutputReady s) (hcounter : BankArray.Word s.val 201 xs)
    (h206 : RationalAccumulator.Blank s.val 206) (h216 : RationalAccumulator.Blank s.val 216) :
    ∃ cost t, Executes input tape inversePrepareCode cost s t ∧
      cost ≤ inversePrepareCost U B H (d 301) xs.length (tableSize (d 300)) ∧
      a.Ready t ∧ (Allocation.table (d 300) (d 301) (d 302) hwidth s.val.memory).OutputReady t ∧
      SharedConversion.Ready PartArray.sharedSlots (resetParts logical) t ∧
      WidthBank PartArray.sharedSlots W (resetParts logical) ∧
      NatAssign.Bank Descriptors.ids (inversePreparedValues a d unused) t.val ∧
      Descriptors.Inputs (inversePreparedValues a d unused) (d 300) (d 301) (d 302) 0 (d 304) ∧
      (∀ k∈Descriptors.ids, (inversePreparedValues a d unused k).bits.length≤max W (2^14*(B+1))) ∧
      BankArray.Word t.val 201 (tableSize (d 300)).bits ∧
      RationalAccumulator.Blank t.val 206 ∧ RationalAccumulator.Blank t.val 216 := by
  obtain ⟨c0,u0,e0,hc0,bank0,ready0,_,width0,z0,f0⟩ := runtimeReset_executes logical natural hn
    U U hU le_rfl hw hp (hw 311 (by decide)) (hw 330 (by decide)) input tape s hbank hz
  have a0 := inputReady_emission_frame a s u0 ha _ ready0 f0
  have old0 := outputReady_emission_frame old s u0 ho _ ready0 f0
  have inputs0 : NatAssign.Bank Allocation.inputs (allocationInputs d) u0.val := by
    intro k hk
    by_cases h310 : k=310
    · subst k
      rw [allocationInputs,Function.update_self]
      have hb := bank0 310 (by decide)
      rw [cleanNaturals_apply,ite_eq_left (by decide : 310∈cleanupSlots)] at hb
      exact hb
    · have hk' : k∈Finset.Icc 300 309 := by
        simp only [Allocation.inputs,Finset.mem_Icc] at hk
        simp only [Finset.mem_Icc]
        omega
      rw [allocationInputs_fixed d k h310]
      exact RationalAccumulator.word_of_eq (continuation_of_frame f0 k
        (Finset.mem_union_left _ (Finset.mem_union_right _ hk'))) (hinputs k hk')
  have inputsWidth : ∀ k∈Allocation.inputs, (allocationInputs d k).bits.length≤B := by
    intro k hk
    by_cases h310 : k=310
    · subst k; simp [allocationInputs]
    · rw [allocationInputs_fixed d k h310]
      apply hd k
      simp only [Allocation.inputs,Finset.mem_Icc] at hk
      simp only [Finset.mem_Icc]
      omega
  have h301 : allocationInputs d 301=d 301 := allocationInputs_fixed d _ (by decide)
  have h300 : allocationInputs d 300=d 300 := allocationInputs_fixed d _ (by decide)
  have h302 : allocationInputs d 302=d 302 := allocationInputs_fixed d _ (by decide)
  have h304 : allocationInputs d 304=d 304 := allocationInputs_fixed d _ (by decide)
  have temp0 := RationalAccumulator.blank_of_eq (continuation_of_frame f0 216 (by decide)) h216
  obtain ⟨c1,u1,e1,hc1,a1,target1,allocated1,allocatedWidth,temp1,f1⟩ := Allocation.executes a old
    (allocationInputs d) B H (by simpa only [h301] using hwidth) inputsWidth hoMeta
      input tape u0 inputs0 a0 old0 temp0
  have target1' : (Allocation.table (d 300) (d 301) (d 302) hwidth s.val.memory).OutputReady u1 := by
    change (Allocation.table (d 300) (d 301) (d 302) hwidth u0.val.memory).OutputReady u1 at target1
    simpa only [f0.memory] using target1
  have countValue : Allocation.outputValues (allocationInputs d) 306=tableSize (d 300) := by
    simp [Allocation.outputValues,Allocation.plan,Allocation.clearedValues,Allocation.headerIds,
      NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      allocationInputs,tableSize]
    ring
  have count1 : RationalAccumulator.Word u1.val 306 (tableSize (d 300)) := by
    simpa only [countValue] using allocated1 306 (by simp [Allocation.ids,Allocation.inputs])
  have oldCounter : BankArray.Word u1.val 201 xs := BankArray.word_of_eq
    ((f1.tapes 201 (by decide)).trans (f0.tapes 201 (by decide))) hcounter
  obtain ⟨t,e2,count2,f2⟩ := WordReplace.executes 306 201 (by decide) input tape
    (tableSize (d 300)).bits xs u1 count1 oldCounter
  have a2 := a1.copy_frame (Or.inl rfl) f2
  have shared0 : SharedConversion.Ready PartArray.sharedSlots (resetParts logical) u0 := by
    refine ⟨?_,z0⟩
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact ready0.1 k ((show ids PartArray.sharedSlots⊆ids RawFree.neighborRegisters by decide) hk)
    · have h := bank0 k (emissionIds_work hk)
      rw [(cleanNaturals_parameters logical natural).2.2 k hk] at h
      simpa only [SharedConversion.work_values_zero (resetParts logical) k hk] using h
  have shared1 : SharedConversion.Ready PartArray.sharedSlots (resetParts logical) u1 := by
    refine ⟨?_,?_⟩
    · intro k hk
      have hout : k∉Allocation.changed := fun he => Finset.disjoint_left.mp
        (show Disjoint (SharedConversion.bankIds PartArray.sharedSlots) Allocation.changed by decide) hk he
      exact RationalAccumulator.word_of_eq (f1.tapes k hout) (shared0.1 k hk)
    · intro k hk
      interval_cases k
      · exact a1.scratch.1
      · exact a1.scratch.2.1
      · exact a1.scratch.2.2.1
      · exact a1.scratch.2.2.2.1
      · exact RationalAccumulator.blank_of_eq (f1.tapes 4 (by decide)) (z0 4 (by decide))
  have shared2 := PartArray.sharedReady_copy_frame shared1 (Or.inl rfl) f2
  have allocated2 : NatAssign.Bank Allocation.ids (Allocation.outputValues (allocationInputs d)) t.val := by
    intro k hk
    have hne : k≠201 := by
      simp only [Allocation.ids,Allocation.inputs,Allocation.headerIds,Finset.mem_union,Finset.mem_Icc,
        Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    exact RationalAccumulator.word_of_eq (f2.2.2.2.2.2.1 k hne) (allocated1 k hk)
  have unused2 : NatAssign.Bank (Finset.Icc 107 140) unused t.val := by
    intro k hk
    have hk' : k∈continuationPorts := Finset.mem_union_left _ (Finset.mem_union_left _ hk)
    have hout : k∉Allocation.changed := by
      simp only [Finset.mem_Icc] at hk
      simp only [Allocation.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    have hne : k≠201 := by have := Finset.mem_Icc.mp hk; omega
    exact RationalAccumulator.word_of_eq
      ((f2.2.2.2.2.2.1 k hne).trans ((f1.tapes k hout).trans (continuation_of_frame f0 k hk')))
      (hunused k hk)
  refine ⟨c0+(c1+(6*xs.length+15*(tableSize (d 300)).bits.length+21)),t,
    e0.seq (e1.seq e2),?_,a2,target1'.copy_frame (Or.inl rfl) f2 a2.scratch a2.seven,
    shared2,?_,assembled_bank a rawHeap hc _ unused _ t a2 allocated2 unused2 shared2.rational,?_,?_,count2,?_,?_⟩
  · unfold inversePrepareCost
    rw [h301] at hc1
    omega
  · intro k hk
    exact (reset_width logical U hU (fun k hk => (hp k hk).1) k
      ((show PartArray.sharedSlots⊆RawFree.neighborRegisters by decide) hk)).mono hUW
  · simpa only [inversePreparedValues,h300,h301,h302,h304] using assembled_values_inputs a (allocationInputs d) unused
  · exact assembled_width a _ unused _ (haMeta.mono (le_max_left _ _))
      (fun k hk => (allocatedWidth k hk).trans (le_max_right _ _))
      (fun k hk => (hu k hk).trans (by omega))
  · exact RationalAccumulator.blank_of_eq ((f2.2.2.2.2.2.1 206 (by decide)).trans
      ((f1.tapes 206 (by decide)).trans (continuation_of_frame f0 206 (by decide)))) h206
  · exact RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 216 (by decide)) temp1

#print axioms inverse_prepare_executes

end Maxwell.Continuum.Calibration.NeumannMachine
