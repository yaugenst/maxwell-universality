import Maxwell.Continuum.RationalDataflowArrayNormalizeAllocation

/-! Allocation and normalization are one fixed executed program. No prepared
destination table or externally chosen storage width is required. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Normalize
open Maxwell.Cost Maxwell.Cost.Structured Calibration
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] Allocation.table Allocation.capacity Allocation.budget Allocation.heap

def allocatedCode : Code := .seq Allocation.code code
def allocatedCost (n : ℕ→ℕ) (B H : ℕ) : ℕ := Allocation.costBound n B H+
  costBound (n 788) (n 700) (Allocation.budget n) (n 788).bits.length

theorem allocated_executes {T : ℕ} (n : ℕ→ℕ) (a : Table T) (v : ℕ→Parts)
    (B H : ℕ) (hB : 10≤B) (width : ∀k∈Allocation.allIds,(n k).bits.length≤B)
    (count : n 788=T)
    (good : Good slots v) (entryValid : ∀i,(a.get i).Valid)
    (positive : 0<sqrtRationalCenter (∑i,(a.get i).value^2) (n 700))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Allocation.allIds n s.val) (array : a.Ready s) (raw : Ready slots v s)
    (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,∃result : Table T,Executes input tape allocatedCode cost s t ∧
      cost≤allocatedCost n B H ∧ result.OutputReady t ∧
      result.MetadataWidth (Allocation.capacity n) ∧
      (∀i,(result.get i).Valid) ∧ (∀i,(result.get i).Width (Allocation.capacity n)) ∧
      (∀i,(result.get i).value=(sqrtRationalCenter (∑j,(a.get j).value^2) (n 700))⁻¹*(a.get i).value) ∧
      (result.width=(Allocation.capacity n).bits ∧ result.basePositive=(Allocation.heap n).bits ∧
        result.baseNegative=(Allocation.heap n+n 788*Allocation.capacity n).bits ∧
        result.baseDenominator=(Allocation.heap n+2*n 788*Allocation.capacity n).bits ∧
        result.clock=List.replicate (Allocation.capacity n) false) ∧
      RationalAccumulator.Word t.val 574 (Allocation.heapEnd n) ∧
      (∀j,j<Allocation.heap n→t.val.memory j=s.val.memory j) := by
  obtain ⟨c0,u,e0,h0,au,ru,bu,nu,_,counter,saved,heapWord,_,frame⟩ :=
    Allocation.executes a n v B H hB width input tape s bank array raw h37 h216 headers
  have hW : 1≤Allocation.budget n := (by decide : 1≤1000).trans (Allocation.budget_ge n)
  have naturalWidth := fun i hi=>Allocation.budget_bound n i
    ((by decide : RationalRoot.Stored.ids 24⊆Allocation.sourceIds) hi)
  have rawWidth := raw_width_of_bank slots Allocation.sourceIds n v (Allocation.budget n)
    (by decide) (Allocation.budget_bound n) u nu ru
  have metadata := a.metadata_of_bank Allocation.sourceIds n (Allocation.budget n) (by decide)
    (Allocation.budget_bound n) (Allocation.budget_table n) u nu au
  have entryWidth:=a.get_width _ metadata u au
  have countWidth:=Allocation.budget_bound n 788 (by decide)
  let b:=Profile.Runtime.memoryTable T (Allocation.capacity n) (Allocation.heap n)
    (Allocation.capacity_pos n) s.val.memory
  have transport (m : ℕ) (hm : m=T)
      (h : (Profile.Runtime.memoryTable m (Allocation.capacity n) (Allocation.heap n)
        (Allocation.capacity_pos n) s.val.memory).OutputReady u ∧
        (Profile.Runtime.memoryTable m (Allocation.capacity n) (Allocation.heap n)
          (Allocation.capacity_pos n) s.val.memory).MetadataWidth (Allocation.capacity n) ∧
        a.SeparatedFrom (Profile.Runtime.memoryTable m (Allocation.capacity n) (Allocation.heap n)
          (Allocation.capacity_pos n) s.val.memory)) :
      b.OutputReady u ∧ b.MetadataWidth (Allocation.capacity n) ∧ a.SeparatedFrom b := by
    subst m
    exact h
  obtain ⟨output,outputWidth,disjoint⟩ := transport (n 788) count (by
    simpa only [Allocation.table] using And.intro bu (And.intro (Allocation.table_metadata n s.val.memory)
      (Allocation.table_disjoint a n u nu au count.symm s.val.memory)))
  have outputMetadata : b.MetadataWidth (2*Normalize.width T (n 700) (Allocation.budget n)+1) := by
    simpa only [Allocation.capacity,count] using outputWidth
  have capacity : 2*Normalize.width T (n 700) (Allocation.budget n)+1≤addressValue b.width := by
    simp only [b,Profile.Runtime.memoryTable,addressValue_bits,Allocation.capacity,count,le_refl]
  have separated : b.Separated := by
    exact Profile.Runtime.memoryTable_separated _ _ _ _ _
  obtain ⟨origin,word⟩:=counter
  obtain ⟨c1,t,result,e1,h1,out,description,valid,fit,values,metadataEq,memory,kept⟩ :=
    executes a b n v (Allocation.budget n) hW naturalWidth rawWidth good entryWidth entryValid
      (by simpa only [count] using countWidth) metadata outputMetadata capacity separated disjoint positive
      input tape (n 788).bits origin countWidth u (by rw [addressValue_bits,count]) word
      (by simpa only [count] using saved)
      (fun i hi=>nu i ((by decide : RationalRoot.Stored.ids 24⊆Allocation.sourceIds) hi)) ru au output
  rw [←count] at h1
  refine ⟨c0+c1,t,result,e0.seq e1,Nat.add_le_add h0 h1,out,?_,valid,?_,values,
    ?_,RationalAccumulator.word_of_eq (kept 574 (by simp [retainedWords])) heapWord,?_⟩
  · simpa only [Allocation.capacity,count] using description
  · simpa only [Allocation.capacity,count] using fit
  · simpa only [b,Profile.Runtime.memoryTable,count] using metadataEq
  intro j hj
  have leP : Allocation.heap n≤addressValue b.basePositive := by
    simp only [b,Profile.Runtime.memoryTable,addressValue_bits,le_refl]
  have leM : Allocation.heap n≤addressValue b.baseNegative := by
    simp only [b,Profile.Runtime.memoryTable,addressValue_bits];omega
  have leD : Allocation.heap n≤addressValue b.baseDenominator := by
    simp only [b,Profile.Runtime.memoryTable,addressValue_bits];omega
  rw [memory (Allocation.heap n) leP leM leD j hj,frame.memory]

#print axioms allocated_executes
end Maxwell.Continuum.RationalDataflow.PartArray.Normalize
