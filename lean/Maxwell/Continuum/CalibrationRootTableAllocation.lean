import Maxwell.Continuum.CalibrationRootTableStorage

/-! Actual allocation of the root-coefficient table from runtime parameters.
The destination starts in arbitrary memory; every coefficient is overwritten
by the following fixed traversal. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] storageValues storageWidth Profile.Runtime.memoryTable

def allocatedCode : Code := .seq (NatAssign.code storagePlan) Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.code
def allocatedChanged : Finset ℕ := NatAssign.changes storagePlan∪Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.changed
def storageNaturalWidth (C : ℕ) : ℕ := 2^25*(C+1)
def allocatedCost (grid N B I C H : ℕ) : ℕ :=
  stageCost C+2^60*(storageNaturalWidth C+H+storageWidth grid N B I+3)^2

theorem storage_values_width (v : ℕ→ℕ) (C : ℕ) (hC : 257≤C)
    (hw : ∀i∈allocationIds,(v i).bits.length≤C) :
    ∀i∈allocationIds,(storageValues v i).bits.length≤storageNaturalWidth C := by
  have h := NatAssign.values_width_bound allocationIds storagePlan storagePlan_valid v C hw
    (storagePlan_literals C hC)
  intro i hi
  have hh := h i hi
  unfold storageValues storageNaturalWidth
  simpa only [storagePlan_length] using (Nat.le_add_right _ _).trans hh

theorem storageChanges_eq : NatAssign.changes storagePlan=
    {0,1,2,3,343,348,349,570,571,572,573} := by decide

theorem allocatedChanged_eq : allocatedChanged=
    {0,1,2,3,210,212,213,214,215,216,343,348,349,570,571,572,573} := by decide

theorem memoryTable_output_transport (n n' width width' heap heap' : ℕ)
    (hw : 0<width) (hw' : 0<width') (memory memory' : ℕ→Bool)
    (hn : n=n') (hwidth : width=width') (hheap : heap=heap') (hmemory : memory=memory')
    (s : Store) (h : (Profile.Runtime.memoryTable n width heap hw memory).OutputReady s) :
    (Profile.Runtime.memoryTable n' width' heap' hw' memory').OutputReady s := by
  rcases hn with rfl
  rcases hwidth with rfl
  rcases hheap with rfl
  rcases hmemory with rfl
  exact h

theorem allocated_executes (v : ℕ→ℕ) (C H : ℕ) (hC : 257≤C)
    (hw : ∀i∈allocationIds,(v i).bits.length≤C)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val) (hz : BankArray.Scratch s.val)
    (h4 : Blank s.val 4) (h7 : Blank s.val 7) (h37 : Blank s.val 37) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape allocatedCode cost s t ∧
      cost≤allocatedCost (v 331) (v 640) (v 345) (v 346) C H ∧
      (Profile.Runtime.memoryTable (2*(v 331)^3) (storageWidth (v 331) (v 640) (v 345) (v 346))
        (v 347) (storageWidth_pos _ _ _ _) s.val.memory).OutputReady t ∧
      NatAssign.Bank RootFrequency.ids (storageValues v) t.val ∧
      NatAssign.Bank Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.ids (Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.outputValues (storageValues v)) t.val ∧
      (∀i,i<5 → Blank t.val i) ∧ Blank t.val 216 ∧
      BinaryPrecision.Frame allocatedChanged s.val t.val := by
  have hs : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2.1
  obtain ⟨c0,u,e0,h0,b0,z0,f0⟩ := storage_executes v C hC hw input tape s hb hs
  have keep0 (i : ℕ)
      (hi : i≠0 ∧ i≠1 ∧ i≠2 ∧ i≠3 ∧ i≠343 ∧ i≠348 ∧ i≠349 ∧
        i≠570 ∧ i≠571 ∧ i≠572 ∧ i≠573) : u.val.tapes i=s.val.tapes i := by
    apply f0.tapes i
    rw [storageChanges_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have scratch0 : BankArray.Scratch u.val :=
    ⟨z0 0 (by decide),z0 1 (by decide),z0 2 (by decide),z0 3 (by decide),
      blank_of_eq (keep0 5 (by decide)) hz.2.2.2.2.1,
      blank_of_eq (keep0 6 (by decide)) hz.2.2.2.2.2.1,
      blank_of_eq (keep0 8 (by decide)) hz.2.2.2.2.2.2.1,
      blank_of_eq (keep0 9 (by decide)) hz.2.2.2.2.2.2.2⟩
  have headers0 : WordCleanup.Bounded Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders H u.val := by
    intro i hi
    have hh : i=210 ∨ i=212 ∨ i=213 ∨ i=214 ∨ i=215 := by
      simpa only [Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] using hi
    obtain ⟨bits,hl,hw⟩ := hheaders i hi
    exact ⟨bits,hl,BankArray.word_of_eq (keep0 i (by omega)) hw⟩
  have inputSubset : Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.inputs⊆allocationIds := by decide
  have inputBank : NatAssign.Bank Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.inputs (storageValues v) u.val :=
    fun i hi => b0 i (inputSubset hi)
  have out := storageValues_outputs v
  have width0 : 0<storageValues v 571 := by rw [out.2.1];exact storageWidth_pos _ _ _ _
  obtain ⟨c1,t,e1,h1,table,bank,z216,f1⟩ := Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.executes (storageValues v)
    (storageNaturalWidth C) H width0
    (fun i hi => storage_values_width v C hC hw i (inputSubset hi)) input tape u
    inputBank scratch0 (blank_of_eq (keep0 7 (by decide)) h7)
    (blank_of_eq (keep0 37 (by decide)) h37)
    (blank_of_eq (keep0 216 (by decide)) h216) headers0
  have table' : (Profile.Runtime.memoryTable (2*(v 331)^3)
      (storageWidth (v 331) (v 640) (v 345) (v 346)) (v 347)
      (storageWidth_pos _ _ _ _) s.val.memory).OutputReady t := by
    exact memoryTable_output_transport _ _ _ _ _ _ width0 (storageWidth_pos _ _ _ _)
      _ _ out.1 out.2.1 out.2.2.1 f0.memory t table
  have natural : NatAssign.Bank RootFrequency.ids (storageValues v) t.val := by
    intro i hi
    have hh := RootFrequency.ids_bounds i hi
    apply word_of_eq (f1.tapes i (by
      simp only [Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation.changed,Finset.mem_insert,Finset.mem_singleton];omega))
    exact b0 i (Finset.mem_union_left _ hi)
  have frame : BinaryPrecision.Frame allocatedChanged s.val t.val :=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have scratch : ∀i,i<5 → Blank t.val i := by
    intro i hi
    interval_cases i
    · exact table'.scratch.1
    · exact table'.scratch.2.1
    · exact table'.scratch.2.2.1
    · exact table'.scratch.2.2.2.1
    · exact blank_of_eq (frame.tapes 4 (by rw [allocatedChanged_eq];decide)) h4
  exact ⟨c0+c1,t,e0.seq e1,by unfold allocatedCost;rw [out.2.1] at h1;omega,
    table',natural,bank,scratch,z216,frame⟩

#print axioms allocated_executes
end Maxwell.Continuum.RationalDataflow.RootTable
