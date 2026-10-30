import Maxwell.Continuum.CalibrationForcingExecution
import Maxwell.Continuum.RationalDataflowRowPlan

/-! Three actual indexed reads load one alias's source components. The
outer counter is the alias row; the program uses the fixed stride three. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def sourceReadPlan : List (ℕ×ℕ) := [(0,28),(1,29),(2,30)]
def sourceReadCode : Code := PartArray.rowPlanCode 3 sourceReadPlan
def sourceLoaded {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  PartArray.rowPlanValues a 3 row sourceReadPlan v

theorem sourceLoaded_values {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts) :
    sourceLoaded a row v=Function.update (Function.update (Function.update v 28 (a.getD (3*row)))
      29 (a.getD (3*row+1))) 30 (a.getD (3*row+2)) := by
  simp [sourceLoaded,sourceReadPlan,PartArray.rowPlanValues]

theorem sourceLoaded_source {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts) (j : Fin 3) :
    RawFree.forcingSource (sourceLoaded a row v) j=a.getD (3*row+j.val) := by
  fin_cases j <;> simp [RawFree.forcingSource,sourceLoaded_values]

theorem sourceLoaded_other {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts)
    (k : ℕ) (hk : k≠28 ∧ k≠29 ∧ k≠30) : sourceLoaded a row v k=v k := by
  rw [sourceLoaded_values,Function.update_of_ne hk.2.2,Function.update_of_ne hk.2.1,
    Function.update_of_ne hk.1]

theorem sourceLoaded_good {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts)
    (hg : Good RawFree.neighborRegisters v) (ha : ∀ j : Fin 3, (a.getD (3*row+j.val)).Valid) :
    Good RawFree.neighborRegisters (sourceLoaded a row v) := by
  rw [sourceLoaded_values]
  exact ((hg.update 28 (by simpa only [Fin.val_zero,Nat.add_zero] using ha 0)).update
    29 (ha 1)).update 30 (ha 2)

theorem sourceLoaded_coordinates {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts) :
    RawFree.coordinates (sourceLoaded a row v)=RawFree.coordinates v := by
  funext j
  fin_cases j
  · exact sourceLoaded_other a row v 13 (by decide)
  · exact sourceLoaded_other a row v 14 (by decide)
  · exact sourceLoaded_other a row v 15 (by decide)

theorem sourceLoaded_quasi {T : ℕ} (a : PartArray.Table T) (row : ℕ) (v : ℕ→Parts) :
    RawFree.quasiParts (sourceLoaded a row v)=RawFree.quasiParts v := by
  funext j
  fin_cases j
  · exact sourceLoaded_other a row v 16 (by decide)
  · exact sourceLoaded_other a row v 17 (by decide)
  · exact sourceLoaded_other a row v 18 (by decide)

theorem sourceRead_executes {T : ℕ} (a : PartArray.Table T) (row B : ℕ) (hrow : 3*row+2<T)
    (v : ℕ→Parts) (hv : WidthBank RawFree.neighborRegisters B v)
    (hg : Good RawFree.neighborRegisters v) (hmeta : a.MetadataWidth B)
    (hvalid : ∀ j : Fin 3, (a.getD (3*row+j.val)).Valid)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤B)
    (hvalue : addressValue word=row) (s : Store)
    (hs : RationalDataflow.Ready RawFree.neighborRegisters v s) (ha : a.Ready s)
    (hcount : BankArray.Word s.val 201 word)
    (hblank : ∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape sourceReadCode cost s t ∧ cost≤2^33*(B+9)^2 ∧
      RationalDataflow.Ready RawFree.neighborRegisters (sourceLoaded a row v) t ∧
      WidthBank RawFree.neighborRegisters B (sourceLoaded a row v) ∧
      Good RawFree.neighborRegisters (sourceLoaded a row v) ∧ a.Ready t ∧
      (∀ k∈PartArray.RowIndex.ids, RationalAccumulator.Blank t.val k) ∧
      PartArray.RowPlanFrame RawFree.neighborRegisters s.val t.val := by
  have valid : ∀ x∈sourceReadPlan, x.2∈RawFree.neighborRegisters := by
    simp [sourceReadPlan,RawFree.neighborRegisters]
  have offset : ∀ x∈sourceReadPlan, x.1.bits.length≤2 := by
    simp [sourceReadPlan]
    decide
  have indices : ∀ x∈sourceReadPlan, 3*addressValue word+x.1<T := by
    rw [hvalue]
    simp [sourceReadPlan]
    omega
  obtain ⟨cost,t,he,hcost,ready,width,outReady,blank,frame⟩ := PartArray.rowPlan_executes a
    RawFree.neighborRegisters 3 2 B sourceReadPlan valid offset hmeta v hv input tape word hlen
    indices s hs ha hcount hblank
  rw [hvalue] at ready width
  refine ⟨cost,t,he,?_,ready,width,sourceLoaded_good a row v hg hvalid,outReady,blank,frame⟩
  have hsq : 1≤(B+9)^2 := one_le_pow₀ (by omega)
  simp only [PartArray.rowPlanCost,sourceReadPlan,List.length_cons,List.length_nil,
    show (3:ℕ).bits.length=2 by decide] at hcost
  nlinarith only [hcost,hsq]

#print axioms sourceRead_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
