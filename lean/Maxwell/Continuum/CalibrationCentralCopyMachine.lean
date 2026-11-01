import Maxwell.Continuum.CalibrationCentralCopyValues

/-! Charged word copies load the isolated central matrix from the stored
Schur entries. The rest of the initialized arithmetic bank is preserved. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes inputPorts relocation gap inputRegisters inputSources

def inputCost (B : ℕ) : ℕ := 3000*8^inputSources.length*(B+2)^2

theorem input_changes : NatAssign.changes inputPlan⊆work := by
  intro i hi
  rcases Finset.mem_union.mp hi with scratch | target
  · have low : i<4 := by simp only [Finset.mem_insert,Finset.mem_singleton] at scratch;omega
    exact Finset.mem_image.mpr ⟨i,Finset.mem_union_left _ scratch,scratch_fixed i low⟩
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp target)
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
    have source : j∈inputPorts:=by simpa only [inputSources,Finset.mem_sort] using hj
    obtain ⟨k,hk,eq⟩:=Finset.mem_image.mp (inputTarget_member j source)
    exact Finset.mem_image.mpr ⟨k,Finset.mem_union_right _ hk,eq⟩

theorem input_executes (v : ℕ→Parts) (B : ℕ) (hB : 1≤ B)
    (width : WidthBank inputRegisters B v) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells inputRegisters v s.val) (ready : Ready bank Initialize.parts (s.renameTapes relocation)) :
    ∃steps t,Executes input tape inputCode steps s t ∧ steps≤ inputCost B ∧
      Ready bank (matrixParts v) (t.renameTapes relocation) ∧
      BinaryPrecision.Frame work s.val t.val := by
  have clear : NatAssign.Scratch s.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq
      ((state_tape s i).trans (congrArg s.val.tapes (scratch_fixed i hi))).symm (ready.2 i hi)
  have source_mem : ∀i∈inputSources,i∈inputIds := by
    intro i hi
    exact Finset.mem_union_left _ (by simpa only [inputSources,Finset.mem_sort] using hi)
  have target_mem : ∀i∈inputSources,inputTarget i∈inputIds := by
    intro i hi
    exact Finset.mem_union_right _ (inputTarget_member i (by simpa only [inputSources,Finset.mem_sort] using hi))
  obtain ⟨steps,t,execution,charge,output,_,_,scratch,frame⟩:=
    NatAssign.copies_executes inputSources inputTarget inputIds source_mem target_mem
      inputTarget_separate inputTarget_injective inputIds_ge (inputWords v) B
      (inputWords_width v B hB width) input tape s (inputWords_bank v s cells ready) clear
  refine ⟨steps,t,execution,charge,⟨?_,?_⟩,frame.mono input_changes⟩
  · intro i hi
    have h:=output (relocation i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    have value:=input_values v i hi
    dsimp only [inputPlan] at value
    rw [value] at h
    obtain ⟨origin,word⟩:=h
    exact ⟨origin,(state_tape t i).trans word⟩
  · intro i hi
    exact RationalAccumulator.blank_of_eq ((state_tape t i).trans (congrArg t.val.tapes (scratch_fixed i hi)))
      (scratch i hi)

#print axioms input_executes
end Maxwell.Continuum.Calibration.CentralRelocation
