import Maxwell.Continuum.CalibrationCentralOutputData

/-! Actual charged copies expose every central inverse output cell while
preserving the isolated internal bank for the next invocation. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes relocation gap outputSources outputNative outputPorts outputRegisters

theorem outputWords_bank (v old : ℕ→Parts) (s : Store)
    (ready : Ready bank v (s.renameTapes relocation)) (cells : Cells outputRegisters old s.val) :
    NatAssign.Bank outputIds (outputWords v old) s.val := by
  intro i hi
  rcases Finset.mem_union.mp hi with source|target
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp source
    rw [outputWords_source v old j hj]
    obtain ⟨origin,word⟩:=ready.1 j (outputNative_member j hj)
    exact ⟨origin,(state_tape s j).symm.trans word⟩
  · rw [outputWords_target v old i target]
    exact cells.bank i (outputPorts_eq ▸ target)

theorem outputWords_width (v old : ℕ→Parts) (B : ℕ)
    (width : WidthBank bank B v) (oldWidth : WidthBank outputRegisters B old) :
    ∀i∈outputIds,(outputWords v old i).bits.length≤ B := by
  intro i hi
  rcases Finset.mem_union.mp hi with source|target
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp source
    rw [outputWords_source v old j hj]
    exact dataValues_width bank v B width j (outputNative_member j hj)
  · rw [outputWords_target v old i target]
    exact dataValues_width outputRegisters old B oldWidth i (Finset.mem_union_left _ (outputPorts_eq ▸ target))

theorem output_changes : NatAssign.changes outputPlan⊆{0,1,2,3}∪outputPorts := by
  intro i hi
  rcases Finset.mem_union.mp hi with scratch|target
  · exact Finset.mem_union_left _ scratch
  · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp target)
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
    exact Finset.mem_union_right _ (outputTarget_member j hj)

theorem output_executes (v old : ℕ→Parts) (B : ℕ)
    (width : WidthBank bank B v) (oldWidth : WidthBank outputRegisters B old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : Ready bank v (s.renameTapes relocation)) (cells : Cells outputRegisters old s.val) :
    ∃steps t,Executes input tape outputCode steps s t ∧ steps≤ outputCost B ∧
      Cells outputRegisters (outputParts v) t.val ∧ Ready bank v (t.renameTapes relocation) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪outputPorts) s.val t.val := by
  have clear : NatAssign.Scratch s.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq
      ((state_tape s i).trans (congrArg s.val.tapes (scratch_fixed i hi))).symm (ready.2 i hi)
  obtain ⟨steps,t,execution,charge,_,copied,_,scratch,frame⟩:=
    NatAssign.copies_executes outputSources outputTarget outputIds
      (fun i hi=>Finset.mem_union_left _ ((outputSources_member i).mp hi))
      (fun i hi=>Finset.mem_union_right _ (outputTarget_member i hi))
      outputTarget_separate outputTarget_injective outputIds_ge (outputWords v old) B
      (outputWords_width v old B width oldWidth) input tape s (outputWords_bank v old s ready cells) clear
  have frame':=frame.mono output_changes
  have word (j : ℕ) (hj : j∈outputNative) :
      RationalAccumulator.Word t.val (j+3372) (dataValues v j) := by
    have mem : relocation j∈outputSources:=
      (outputSources_member _).mpr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    have value:=copied _ mem
    simpa only [outputTarget,relocation_involutive,outputWords_source v old j hj] using value
  refine ⟨steps,t,execution,charge,?_,⟨?_,?_⟩,frame'⟩
  · intro i hi
    have bounds : 1700≤ i ∧ i<2276 := by simpa only [outputRegisters,Finset.mem_Ico] using hi
    have parts (k : ℕ) (hk : k∈cellPorts (i-1124)) : k∈outputNative := by
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,positivePort,negativePort,denominatorPort] at hk
      simp only [outputNative,Finset.mem_Ico]
      omega
    refine ⟨?_,?_,?_⟩
    · have h:=word (positivePort (i-1124)) (parts _ (by simp [cellPorts]))
      rw [dataValues_positive] at h
      convert h using 1 <;> simp only [outputParts,positivePort]; omega
    · have h:=word (negativePort (i-1124)) (parts _ (by simp [cellPorts]))
      rw [dataValues_negative] at h
      convert h using 1 <;> simp only [outputParts,positivePort,negativePort]; omega
    · have h:=word (denominatorPort (i-1124)) (parts _ (by simp [cellPorts]))
      rw [dataValues_denominator] at h
      convert h using 1 <;> simp only [outputParts,positivePort,denominatorPort]; omega
  · intro i hi
    have moved:=moved i (ids_ge bank i hi) (bank_bound i hi)
    have external : relocation i∉{0,1,2,3}∪outputPorts := by
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,outputPorts,Finset.mem_Ico,moved]
      have lower : 20000≤gap := by unfold gap;have :=count_lower;omega
      omega
    obtain ⟨origin,h⟩:=ready.1 i hi
    exact ⟨origin,(state_tape t i).trans ((frame'.tapes _ external).trans ((state_tape s i).symm.trans h))⟩
  · intro i hi
    exact RationalAccumulator.blank_of_eq
      ((state_tape t i).trans (congrArg t.val.tapes (scratch_fixed i hi))) (scratch i hi)

#print axioms output_executes
end Maxwell.Continuum.Calibration.CentralRelocation
