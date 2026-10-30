import Maxwell.Continuum.CalibrationMatrixEntryMachine
import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! An actual computed cached matrix entry is written into the allocated
three-channel raw table. Output metadata and the runtime countdown survive
the arithmetic stage. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def emissionIds : Finset ℕ := ids RawFree.neighborRegisters ∪ Finset.Icc 310 332 ∪ NaturalQuotient.workPorts
def emissionChanged : Finset ℕ := {0,1,2,3,4} ∪ emissionIds

/-- Disjoint ports carried from coefficient generation into inverse setup. -/
def continuationPorts : Finset ℕ := Finset.Icc 107 140 ∪ Finset.Icc 300 309 ∪
  ({206,216} ∪ Finset.Icc 530 534)
def ContinuationFrame (s t : BitRAMState) : Prop :=
  ∀ k∈continuationPorts, t.tapes k=s.tapes k

theorem ContinuationFrame.refl (s : BitRAMState) : ContinuationFrame s s := fun _ _ => rfl
theorem ContinuationFrame.trans {s t u : BitRAMState}
    (h : ContinuationFrame s t) (g : ContinuationFrame t u) : ContinuationFrame s u :=
  fun k hk => (g k hk).trans (h k hk)
theorem continuation_external : ∀ k∈continuationPorts,
    10≤k ∧ k∉emissionChanged ∧ k≠37 ∧ k≠201 ∧ k∉NaturalQuotient.workPorts := by decide

theorem continuation_of_frame {s t : BitRAMState}
    (h : BinaryPrecision.Frame emissionChanged s t) : ContinuationFrame s t :=
  fun k hk => h.tapes k (continuation_external k hk).2.1

def matrixStoreCode : Code := .seq matrixEntryCode (PartArray.writeAtCode 332 12)

theorem emissionIds_parts : ids RawFree.neighborRegisters ⊆ emissionIds := by
  intro k hk; exact Finset.mem_union_left _ (Finset.mem_union_left _ hk)
theorem emissionIds_decode : ports ⊆ emissionIds := by
  intro k hk
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  simp only [ports,Finset.mem_Icc] at hk
  simp only [Finset.mem_Icc]
  omega
theorem emissionIds_work : NaturalQuotient.workPorts ⊆ emissionIds := Finset.subset_union_right
theorem emissionIds_ge (k : ℕ) (hk : k∈emissionIds) : 10≤k := by
  rcases Finset.mem_union.mp hk with hk | hk
  · rcases Finset.mem_union.mp hk with hk | hk
    · exact ids_ge_ten _ k hk
    · simp only [Finset.mem_Icc] at hk; omega
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk; omega

theorem emission_protected : ∀ k∈([5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]:List ℕ),
    k∉emissionChanged := by decide

theorem coordinateLoad_small (n : ℕ → ℕ) (k : ℕ) (hk : k<1000) :
    NatAssign.values coordinateLoad n k=n k := by
  rw [coordinateLoad_values]
  simp (disch := omega) only [writeParts,positivePort,negativePort,denominatorPort,Function.update_of_ne]

theorem matrixNaturals_external (n : ℕ → ℕ) (k : ℕ) (hk : k<1000) (ho : k∉ports) :
    matrixNaturals n k=n k := by
  have hne : k≠310 := fun h => ho (h ▸ (by decide : 310∈ports))
  rw [matrixNaturals,coordinateLoad_small _ k hk,output_outside _ k ho,rowStart,
    Function.update_of_ne hne,columnNaturals_small n k hk,output_outside n k ho]

theorem matrixEntry_output_index (v : ℕ → Parts) (n : ℕ → ℕ) : matrixEntryNaturals v n 332=n 332 := by
  rw [matrixEntryNaturals,ite_eq_right (by decide : 332∉ids RawFree.neighborRegisters)]
  exact matrixNaturals_external n 332 (by decide) (by decide)

theorem outputReady_emission_frame {n : ℕ} (a : PartArray.Table n) (s t : Store)
    (ha : a.OutputReady s) (v : ℕ → Parts) (hr : RationalDataflow.Ready RawFree.neighborRegisters v t)
    (hf : BinaryPrecision.Frame emissionChanged s.val t.val) : a.OutputReady t := by
  have keep (k : ℕ) (hk : k∈([5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215]:List ℕ)) :=
    hf.tapes k (emission_protected k hk)
  apply ha.transfer hf.memory ?_ ?_ (RationalAccumulator.blank_of_eq (keep 7 (by simp)) ha.seven)
  · intro k hk
    apply keep k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    tauto
  · exact ⟨hr.2 0 (by decide),hr.2 1 (by decide),hr.2 2 (by decide),hr.2 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by simp)) ha.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by simp)) ha.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by simp)) ha.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by simp)) ha.scratch.2.2.2.2.2.2.2⟩

theorem matrixStore_executes {T : ℕ} (a : PartArray.Table T) (target : Fin T)
    (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.neighborRegisters, n k=dataValues v k)
    (hzwork : ∀ k ∈ NaturalQuotient.workPorts, n k=0)
    (hg : Good RawFree.neighborRegisters v) (B W : ℕ) (hB : 101≤B)
    (hw : ∀ k ∈ emissionIds, (n k).bits.length≤B)
    (hmeta : a.MetadataWidth W) (htarget : n 332=target.val)
    (hfit : matrixEntryWordBound B≤addressValue a.width) (hsep : a.Separated)
    (R : ℕ) (i j : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 321=i.val) (hj : n 310=j.val)
    (htbox : (3 : ℝ) ≤ (v 0).value)
    (hEbox : (7 : ℝ) ≤ (v 1).value ∧ ((v 1).value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((RawFree.quasiParts v k).value : ℝ)| ≤ 1/16)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) (ha : a.OutputReady s) :
    ∃ cost t, Executes input tape matrixStoreCode cost s t ∧
      cost≤2^510*(B+10)^2+2^20*(max B W+5)^2 ∧
      RationalDataflow.Ready RawFree.neighborRegisters (matrixEntryOutput v n) t ∧
      (a.set target (matrixEntryOutput v n 12)).OutputReady t ∧
      (matrixEntryOutput v n 12).Valid ∧
      (matrixEntryOutput v n 12).value=cachedTransitionMatrix (v 0).value (v 1).value
        (fun k => (RawFree.quasiParts v k).value) R i j ∧
      t.val.memory=a.writeMemory target (matrixEntryOutput v n 12) s.val.memory ∧
      NatAssign.Bank emissionIds (matrixEntryNaturals v n) t.val ∧
      Good RawFree.neighborRegisters (matrixEntryOutput v n) ∧
      WidthBank RawFree.neighborRegisters (matrixEntryWordBound B) (matrixEntryOutput v n) ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      t.val.tapes 201=s.val.tapes 201 ∧
      (∀ k∈([200,202,203,204,205]:List ℕ), t.val.tapes k=s.val.tapes k) ∧
      ContinuationFrame s.val t.val := by
  obtain ⟨c0,u,e0,hc0,bank,ready,good,width,value,frame,z04⟩ := matrixEntry_executes emissionIds
    emissionIds_ge emissionIds_decode emissionIds_work emissionIds_parts (by decide) n v hn hzwork hg
    B hB hw R i j hR hi hj htbox hEbox hrbox input tape s hs hz
  have au := outputReady_emission_frame a s u ha _ ready frame
  have word : RationalAccumulator.Word u.val 332 target.val := by
    have h := bank 332 (by decide)
    simpa only [matrixEntry_output_index,htarget] using h
  have positive : 0<addressValue a.width := by
    have hp : 0<matrixEntryWordBound B := by unfold matrixEntryWordBound RawFree.matrixEntryWidth; positivity
    omega
  obtain ⟨c1,t,e1,hc1,ready1,outReady,mem,writeFrame⟩ := PartArray.writeAt_executes a RawFree.neighborRegisters
    332 (by decide) 12 (by decide) (matrixEntryOutput v n) target positive
    ((width 12 (by decide)).mono hfit) hsep input tape target.val.bits (by simp) u ready au word
  have bank1 : NatAssign.Bank emissionIds (matrixEntryNaturals v n) t.val := by
    intro k hk
    have hge := emissionIds_ge k hk
    have h37 : k≠37 := by intro he; subst k; exact (by decide : 37∉emissionIds) hk
    exact RationalAccumulator.word_of_eq (writeFrame.2.2.2.1 k (Or.inr hge) h37) (bank k hk)
  have blank : ∀ k, k<5 → RationalAccumulator.Blank t.val k := by
    intro k hk
    by_cases h4 : k<4
    · exact ready1.2 k h4
    · have he : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq (writeFrame.2.2.2.1 4 (Or.inl rfl) (by decide)) z04
  refine ⟨c0+c1,t,e0.seq e1,?_,ready1,outReady,good 12 (by decide),value,?_,bank1,good,width,blank,?_,?_,?_⟩
  · have hm : a.MetadataWidth (max B W) := hmeta.mono (le_max_right B W)
    have hx : target.val.bits.length≤max B W := by
      rw [← htarget]
      exact (hw 332 (by decide)).trans (le_max_left B W)
    have cb := a.writeCost_bound (max B W) hm target.val.bits hx (matrixEntryOutput v n 12)
    change c1≤a.writeCost target.val.bits (matrixEntryOutput v n 12) at hc1
    omega
  · rw [mem,frame.memory]
  · exact (writeFrame.2.2.2.1 201 (Or.inr (by decide)) (by decide)).trans
      (frame.tapes 201 (by decide))

  · intro k hk
    have hge : 10≤k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      omega
    have h37 : k≠37 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      omega
    exact (writeFrame.2.2.2.1 k (Or.inr hge) h37).trans
      (frame.tapes k (emission_protected k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        tauto)))

  · intro k hk
    have h := continuation_external k hk
    exact (writeFrame.2.2.2.1 k (Or.inr h.1) h.2.2.1).trans (frame.tapes k h.2.1)

#print axioms matrixStore_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
