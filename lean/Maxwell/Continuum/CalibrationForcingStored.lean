import Maxwell.Continuum.CalibrationForcingRow
import Maxwell.Continuum.CalibrationMatrixTableLoop

/-! The three raw writes contain the exact forcing outputs, and writing one
alias preserves every other row and the allocated table metadata. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem table_setD_width {T : ℕ} (b : PartArray.Table T) (index : ℕ) (v : Parts) :
    (b.setD index v).width=b.width := by unfold PartArray.Table.setD; split_ifs <;> rfl

theorem table_setD_get {T : ℕ} (b : PartArray.Table T) (j : Fin T) (index : ℕ) (v : Parts)
    (hi : index=j.val) (hv : v.Width (addressValue b.width)) : (b.setD index v).get j=v := by
  subst index
  rw [PartArray.Table.setD,dite_eq_left j.isLt]
  exact b.set_get j v hv

theorem forcingWrite_get {T : ℕ} (b : PartArray.Table T) (row : ℕ) (v : ℕ→Parts)
    (j : Fin 3) (slot : Fin T) (hslot : slot.val=3*row+j.val)
    (hfit : ∀ k : Fin 3, (v (37+k.val)).Width (addressValue b.width)) :
    (PartArray.rowWriteTable 3 row forcingWritePlan v b).get slot=v (37+j.val) := by
  fin_cases j <;> norm_num at hslot
  · simp only [forcingWritePlan,PartArray.rowWriteTable]
    rw [PartArray.Table.setD_get_ne _ (3*row+2) slot _ (by omega),
      PartArray.Table.setD_get_ne _ (3*row+1) slot _ (by omega)]
    exact table_setD_get b slot _ _ (by simpa using hslot.symm) (hfit 0)
  · simp only [forcingWritePlan,PartArray.rowWriteTable]
    have hne : 3*row+2≠slot.val := by
      rw [hslot]
      exact Nat.add_left_cancel_iff.not.mpr (by decide : (2:ℕ)≠1)
    rw [PartArray.Table.setD_get_ne _ (3*row+2) slot _ hne]
    apply table_setD_get _ slot _ _ (by simpa using hslot.symm)
    simpa only [table_setD_width] using (show (v 38).Width (addressValue b.width) from hfit 1)
  · simp only [forcingWritePlan,PartArray.rowWriteTable]
    apply table_setD_get _ slot _ _ (by simpa using hslot.symm)
    simpa only [table_setD_width] using (show (v 39).Width (addressValue b.width) from hfit 2)

theorem forcingWrite_unchanged {T : ℕ} (b : PartArray.Table T) (row : ℕ) (v : ℕ→Parts)
    (slot : Fin T) (hslot : slot.val<3*row ∨ 3*row+3≤slot.val) :
    (PartArray.rowWriteTable 3 row forcingWritePlan v b).get slot=b.get slot := by
  apply PartArray.rowWriteTable_get_unchanged
  simp only [forcingWritePlan,List.mem_cons,List.not_mem_nil,or_false]
  rintro x (rfl | rfl | rfl) <;> omega

theorem forcingWrite_metadata {T : ℕ} (a b : PartArray.Table T) (row : ℕ) (v : ℕ→Parts)
    (h : sameMetadata a b) : sameMetadata a (PartArray.rowWriteTable 3 row forcingWritePlan v b) := by
  obtain ⟨hw,hp,hn,hd,hc⟩ := PartArray.rowWriteTable_metadata b 3 row forcingWritePlan v
  exact ⟨hw.trans h.1,hp.trans h.2.1,hn.trans h.2.2.1,hd.trans h.2.2.2.1,hc.trans h.2.2.2.2⟩

theorem forcingVector_parameter (v : ℕ→Parts) (k : ℕ) (hk : k∈matrixParameters) :
    RawFree.forcingVectorControl.evaluate v k=v k := by
  have cases : k=0 ∨ k=1 ∨ k=16 ∨ k=17 ∨ k=18 := by
    simpa only [matrixParameters,Finset.mem_insert,Finset.mem_singleton] using hk
  rw [RawFree.forcingVectorControl,Control.evaluate,
    RawFree.forcingVectorLoop_keep _ _ k (by unfold RawFree.forcingStable; omega)
      (by intro j _; have := j.isLt; omega)]
  exact Function.update_of_ne (by omega) _ _

theorem forcingRow_parameter (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (row : ℕ) (v : ℕ→Parts) (k : ℕ) (hk : k∈matrixParameters) :
    forcingRowParts R a row v k=v k := by
  have cases : k=0 ∨ k=1 ∨ k=16 ∨ k=17 ∨ k=18 := by
    simpa only [matrixParameters,Finset.mem_insert,Finset.mem_singleton] using hk
  rw [forcingRowParts,forcingVector_parameter _ k hk,sourceLoaded_other a row v k (by omega)]

#print axioms forcingWrite_get
#print axioms forcingRow_parameter

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
