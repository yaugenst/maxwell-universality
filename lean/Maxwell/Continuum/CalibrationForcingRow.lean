import Maxwell.Continuum.CalibrationForcingIndex
import Maxwell.Continuum.CalibrationForcingVectorExecution
import Maxwell.Continuum.RationalDataflowRowWriteValues
import Maxwell.Continuum.RationalDataflowArrayMap

/-! One actual alias row: three source reads, all three forcing outputs,
and three raw writes. The source table survives the complete operation. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def forcingWritePlan : List (ℕ×ℕ) := [(0,37),(1,38),(2,39)]
def forcingRowCode : Code := .seq sourceReadCode (.seq RawFree.forcingVectorControl.code
  (PartArray.rowWritePlanCode 3 forcingWritePlan))
def forcingRowParts (R : ℕ) (a : PartArray.Table (aliasArraySize R)) (row : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  RawFree.forcingVectorControl.evaluate (sourceLoaded a row v)
def forcingRowTable {T : ℕ} (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table T) (row : ℕ) (v : ℕ→Parts) : PartArray.Table T :=
  PartArray.rowWriteTable 3 row forcingWritePlan (forcingRowParts R a row v) b

theorem forcing_read_protects_four : sourceReadCode.protectsTape 4=true := by decide
theorem forcing_write_protects_four : (PartArray.rowWritePlanCode 3 forcingWritePlan).protectsTape 4=true := by decide

theorem forcingRow_executes {T : ℕ} (R : ℕ) (a : PartArray.Table (aliasArraySize R)) (b : PartArray.Table T)
    (row : Fin (aliasRowCount R)) (hT : aliasArraySize R≤T) (v : ℕ→Parts) (B W : ℕ) (hB : 2≤B)
    (hv : WidthBank RawFree.neighborRegisters B v) (hg : Good RawFree.neighborRegisters v)
    (haValid : ∀ i, (a.get i).Valid) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (hfit : RawFree.forcingVectorWidth B≤addressValue b.width) (hsep : b.Separated)
    (hdisjoint : a.SeparatedFrom b)
    (hcoord : ∀ k, (RawFree.coordinates v k).value=(arrayAliasAt R (polarizationRow R row 0) k:ℚ))
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤B)
    (hvalue : addressValue word=row.val) (s : Store)
    (hs : RationalDataflow.Ready RawFree.neighborRegisters v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hcounter : BankArray.Word s.val 201 word)
    (hblank : ∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape forcingRowCode cost s t ∧ cost≤2^1110*(B+W+10)^2 ∧
      RationalDataflow.Ready RawFree.neighborRegisters (forcingRowParts R a row.val v) t ∧
      Good RawFree.neighborRegisters (forcingRowParts R a row.val v) ∧
      WidthBank RawFree.neighborRegisters (RawFree.forcingVectorWidth B) (forcingRowParts R a row.val v) ∧
      a.Ready t ∧ (forcingRowTable R a b row.val v).OutputReady t ∧
      (∀ i : Fin 3, (forcingRowParts R a row.val v (37+i.val)).value=
        cachedForcing (v 0).value (v 1).value (fun k => (RawFree.quasiParts v k).value)
          R (tableSource R a) (polarizationRow R row i)) ∧
      (∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank t.val k) ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.tapes 4=s.val.tapes 4 ∧
      (∀ k, 10≤k → k∉ids RawFree.neighborRegisters → k∉PartArray.RowIndex.ids → k≠37 →
        t.val.tapes k=s.val.tapes k) := by
  have hrow : 3*row.val+2<aliasArraySize R := (polarizationRow R row 2).isLt
  have validSource (j : Fin 3) : (a.getD (3*row.val+j.val)).Valid := by
    have hj : 3*row.val+j.val<aliasArraySize R := (polarizationRow R row j).isLt
    rw [PartArray.Table.getD,dite_eq_left hj]
    exact haValid _
  obtain ⟨c0,u0,e0,hc0,ready0,width0,good0,a0,z0,f0⟩ := sourceRead_executes a row.val B hrow v hv hg
    haMeta validSource input tape word hlen hvalue s hs ha hcounter hblank
  have b0 := hb.rowPlan_frame f0 a0.scratch a0.seven
  have p0 := sourceLoaded_other a row.val v 0 (by decide)
  have p1 := sourceLoaded_other a row.val v 1 (by decide)
  obtain ⟨c1,u1,e1,hc1,ready1,good1,width1,value,f1⟩ := RawFree.forcingVector_executes
    RawFree.neighborRegisters (fun _ h => h) (sourceLoaded a row.val v) B hB width0 good0
    (arrayAliasAt R (polarizationRow R row 0))
    (by simpa only [sourceLoaded_coordinates] using hcoord)
    (by simpa only [p0] using ht) (by simpa only [p1] using hE)
    (by simpa only [sourceLoaded_quasi] using hr) input tape u0 ready0
  have a1 := a0.arithmetic_frame RawFree.neighborRegisters f1 ready1.2
  have b1 := b0.shared_frame RawFree.neighborRegisters (f1.mono (PartArray.workspace_subset_shared _))
    a1.scratch a1.seven
  have z1 : ∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank u1.val k := by
    intro k hk
    apply RationalAccumulator.blank_of_eq (f1.tapes k _) (z0 k hk)
    apply outside_workspace _ k
    simp only [PartArray.RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  have count1 : u1.val.tapes 201=s.val.tapes 201 :=
    (f1.tapes 201 (outside_workspace _ _ (by decide))).trans f0.counter
  have positive : 0<addressValue b.width := by
    have hp : 0<RawFree.forcingVectorWidth B := by unfold RawFree.forcingVectorWidth; positivity
    omega
  have writeValid : ∀ x∈forcingWritePlan, x.2∈RawFree.neighborRegisters := by
    simp [forcingWritePlan,RawFree.neighborRegisters]
  have writeOffset : ∀ x∈forcingWritePlan, x.1.bits.length≤2 := by
    simp [forcingWritePlan]
    decide
  have writeFit : ∀ x∈forcingWritePlan, (forcingRowParts R a row.val v x.2).Width (addressValue b.width) := by
    intro x hx
    exact (width1 x.2 (writeValid x hx)).mono hfit
  have writeIndex : ∀ x∈forcingWritePlan, 3*addressValue word+x.1<T := by
    rw [hvalue]
    simp [forcingWritePlan]
    omega
  obtain ⟨c2,t,e2,hc2,ready2,a2,b2,z2,f2⟩ := PartArray.rowWritePlan_executes a b RawFree.neighborRegisters
    3 2 (max B W) forcingWritePlan writeValid writeOffset (hbMeta.mono (le_max_right B W))
    (forcingRowParts R a row.val v) writeFit positive hsep hdisjoint input tape word
    (hlen.trans (le_max_left B W)) writeIndex u1 ready1 a1 b1
    (BankArray.word_of_eq count1 hcounter) z1
  rw [hvalue] at b2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,ready2,good1,width1,a2,b2,?_,z2,
    f2.counter.trans count1,?_,?_⟩
  · have hcost1 := hc1.trans (RawFree.forcingVectorCost_bound B)
    simp only [PartArray.rowPlanCost,forcingWritePlan,List.length_cons,List.length_nil,
      show (3:ℕ).bits.length=2 by decide] at hc2
    have hs0 : (B+9)^2≤(B+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs1 : (B+3)^2≤(B+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs2 : (max B W+2+2+5)^2≤(B+W+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hs3 : 1≤(B+W+10)^2 := one_le_pow₀ (by omega)
    nlinarith only [hc0,hcost1,hc2,hs0,hs1,hs2,hs3]
  · intro i
    exact (value i).trans (loaded_forcing_row R a row v i)
  · exact (e2.protectsTape 4 forcing_write_protects_four).trans
      ((f1.tapes 4 (by decide)).trans (e0.protectsTape 4 forcing_read_protects_four))
  · intro k hge hraw hrow h37
    have hports : k∉RationalDataflow.ports RawFree.neighborRegisters :=
      fun h => hraw (Finset.mem_union_left _ h)
    have hworkspace : k∉workspace RawFree.neighborRegisters := by
      simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨by omega,hraw⟩
    exact (f2.tapes k hge h37 hrow).trans ((f1.tapes k hworkspace).trans (f0.tapes k hge hports hrow))

#print axioms forcingRow_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
