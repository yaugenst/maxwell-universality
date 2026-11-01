import Maxwell.Continuum.CalibrationCentralCopyData

/-! Merge retained Schur words with the initialized isolated arithmetic bank.
Both sides are actual machine words, and their tape intervals are disjoint. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word)
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes inputPorts relocation gap inputRegisters inputSources

theorem relocated_ge (i : ℕ) (hi : i∈ids bank) : gap≤ relocation i := by
  rw [moved i (ids_ge bank i hi) (bank_bound i hi)]
  omega

theorem relocated_outside_input (i : ℕ) (hi : i∈ids bank) : relocation i∉inputPorts := by
  intro member
  have lo:=relocated_ge i hi
  have upper:=inputPorts_bounds _ member
  unfold gap count at lo
  omega

theorem inputIds_ge : ∀i∈inputIds,4≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with original | isolated
  · have h:=inputPorts_bounds i original
    omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp isolated
    have h:=relocated_ge j hj
    unfold gap count at h
    omega

theorem inputWords_bank (v : ℕ→Parts) (s : Store)
    (cells : Cells inputRegisters v s.val) (ready : Ready bank Initialize.parts (s.renameTapes relocation)) :
    NatAssign.Bank inputIds (inputWords v) s.val := by
  intro i hi
  simp only [inputIds,Finset.mem_union] at hi
  by_cases original : i∈inputPorts
  · simpa only [inputWords,ite_eq_left (inputPorts_bounds i original)] using inputPorts_bank v s.val cells i original
  · have isolated : i∈(ids bank).image relocation := hi.resolve_left original
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp isolated
    have outside : ¬(2500≤relocation j ∧ relocation j<4228) := fun h=>original (mem_inputPorts _ h.1 h.2)
    rw [inputWords,ite_eq_right outside,relocation_involutive]
    obtain ⟨origin,word⟩:=ready.1 j hj
    exact ⟨origin,(state_tape s j).symm.trans word⟩

theorem inputWords_width (v : ℕ→Parts) (B : ℕ) (hB : 1≤ B)
    (width : WidthBank inputRegisters B v) : ∀i∈inputIds,(inputWords v i).bits.length≤ B := by
  intro i hi
  simp only [inputIds,Finset.mem_union] at hi
  by_cases original : i∈inputPorts
  · rw [inputWords,ite_eq_left (inputPorts_bounds i original)]
    exact dataValues_width inputRegisters v B width i
      (Finset.mem_union_left _ (by simpa only [inputPorts] using original))
  · have isolated : i∈(ids bank).image relocation := hi.resolve_left original
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp isolated
    have outside : ¬(2500≤relocation j ∧ relocation j<4228) := fun h=>original (mem_inputPorts _ h.1 h.2)
    rw [inputWords,ite_eq_right outside,relocation_involutive]
    exact (Initialize.words_width bank j hj).trans hB

theorem inputWords_original (v : ℕ→Parts) (i : ℕ) (hi : i∈inputPorts) :
    inputWords v i=dataValues v i := ite_eq_left (inputPorts_bounds i hi)

theorem inputWords_isolated (v : ℕ→Parts) (i : ℕ) (hi : i∈ids bank) :
    inputWords v (relocation i)=dataValues Initialize.parts i := by
  have outside : ¬(2500≤relocation i ∧ relocation i<4228) :=
    fun h=>relocated_outside_input i hi (mem_inputPorts _ h.1 h.2)
  rw [inputWords,ite_eq_right outside,relocation_involutive]

theorem input_copy_values (v : ℕ→Parts) (i : ℕ)
    (core : 1000≤ i ∧ i<2728) :
    NatAssign.values inputPlan (inputWords v) (relocation i)=dataValues v (i+1500) := by
  have source : i+1500∈inputSources := by
    simp only [inputSources,Finset.mem_sort]
    exact mem_inputPorts _ (by omega) (by omega)
  have h:=NatAssign.copies_target inputSources inputTarget inputTarget_separate
    inputTarget_injective (inputWords v) (i+1500) source
  have target : inputTarget (i+1500)=relocation i := by simp [inputTarget]
  rw [target,inputWords_original v _ (mem_inputPorts _ (by omega) (by omega))] at h
  exact h

theorem input_copy_unchanged (v : ℕ→Parts) (i : ℕ) (hi : i∈ids bank)
    (outside : ¬(1000≤ i ∧ i<2728)) :
    NatAssign.values inputPlan (inputWords v) (relocation i)=dataValues Initialize.parts i := by
  rw [NatAssign.values_preserves,inputWords_isolated v i hi]
  intro instruction member
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp member
  change relocation i≠inputTarget j
  intro eq
  have eq' : i=j-1500:=relocation.injective eq
  have src : j∈inputPorts:=by simpa only [inputSources,Finset.mem_sort] using hj
  have bounds:=inputPorts_bounds j src
  apply outside
  omega

#print axioms inputWords_bank
end Maxwell.Continuum.Calibration.CentralRelocation
