import Maxwell.Continuum.CalibrationSeedRootPhases
import Maxwell.Cost.BankArray.Unique

/-! The computed alias coordinates fit the retained cube side. This is
the uniform width invariant used when the decoder repeats for every row. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def rowRetained : Finset ℕ := {750,751,780,785,786,787,788}

theorem rowValues_retained (n : ℕ→ℕ) (i : ℕ) (hi : i∈rowRetained) : rowValues n i=n i := by
  simp only [rowRetained,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [NaturalQuotient.workPorts] using rowValues_keep n 750 (Or.inl (by decide))
  · simpa [NaturalQuotient.workPorts] using rowValues_keep n 751 (Or.inl (by decide))
  · simpa [NaturalQuotient.workPorts] using rowValues_keep n 780 (Or.inl (by decide))
  all_goals
    rw [rowValues,NatAssign.values_preserves rowFinish _ _ (by decide),
      ArrayDecodeMachine.output_outside _ _ (by decide)]
    simp [rowHalved,ArrayDecodeMachine.divModValues,rowPrepared,rowPrepare,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem rowValues_fixed_width (M D : ℕ) (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)))
    (n : ℕ→ℕ) (B : ℕ) (hM : n 750=M) (hD : n 751=D) (hrow : n 780=row.val)
    (side : n 786=aliasSide (3*M+D)) (width : ∀i∈rowIds,(n i).bits.length≤B) :
    ∀i∈fixedFields,(rowValues n i).bits.length≤B := by
  have co : coordinates (rowValues n)=decodedCoordinates (3*M+D) (3*row.val) := by
    rw [rowValues_coordinates,hM,hD,hrow]
  have coordWidth (j : Fin 3) : (coordinates (rowValues n) j).bits.length≤B := by
    rw [co]
    have bound := decodedCoordinates_lt (3*M+D) (ArrayDecodeMachine.polarizationRow (3*M+D) row 0) j
    have hb := Nat.size_le_size bound.le
    have hw := width 786 (by decide)
    rw [side] at hw
    have widthBound : (decodedCoordinates (3*M+D) (3*row.val) j).bits.length≤(aliasSide (3*M+D)).bits.length := by
      simpa only [Nat.size_eq_bits_len,ArrayDecodeMachine.polarizationRow,Fin.val_zero,Nat.add_zero] using hb
    exact widthBound.trans hw
  intro i hi
  by_cases retained : i∈rowRetained
  · rw [rowValues_retained n i retained]
    exact width i ((by decide : fixedFields⊆rowIds) hi)
  have cases : i=752 ∨ i=753 ∨ i=754 ∨ i=755 := by
    simp only [fixedFields,rowRetained,Finset.mem_insert,Finset.mem_singleton] at hi retained
    omega
  rcases cases with rfl|rfl|rfl|rfl
  · rw [rowValues_half]
    have hb := Nat.size_le_size (Nat.div_le_self (n 750) 2)
    have widthBound : (n 750/2).bits.length≤(n 750).bits.length := by
      simpa only [Nat.size_eq_bits_len] using hb
    exact widthBound.trans (width 750 (by decide))
  · exact coordWidth 0
  · exact coordWidth 1
  · exact coordWidth 2

theorem rowWidth_ge (B : ℕ) : B≤rowWidth B := by
  change B≤2*(2048*(B+3))+8
  omega

theorem ready_after_row_execution {n : ℕ→ℕ} {v : ℕ→Parts} {s t : Store}
    (old : NatAssign.Bank rowIds n s.val) (ready : Ready slots v s)
    (new : NatAssign.Bank rowIds (rowValues n) t.val) (scratch : NatAssign.Scratch t.val)
    (frame : BinaryPrecision.Frame rowWorkspace s.val t.val) : Ready slots v t := by
  apply rational_ready_after_row ready frame scratch
  intro i hi
  have hm : i∈rowIds := (by decide : RationalMagnitude.ids⊆rowIds) hi
  have lo : i<1000 := by
    simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hw := ready.1 i (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
  rw [dataValues_small v lo] at hw
  have eq : n i=0 := by
    simpa only [RationalAccumulator.address_bits] using congrArg addressValue (BankArray.word_unique (old i hm) hw)
  have unchanged : rowValues n i=n i := by
    have h := rowValues_keep n i (Or.inr (Or.inl hi))
    have no : i∉NaturalQuotient.workPorts := fun hh=>Finset.disjoint_left.mp
      (by decide : Disjoint RationalMagnitude.ids NaturalQuotient.workPorts) hi hh
    simpa only [ite_eq_right no] using h
  simpa only [unchanged,eq] using new i hm

theorem resetParts_idempotent (v : ℕ→Parts) : resetParts (resetParts v)=resetParts v := by
  funext i
  simp only [resetParts,resetList_values]
  split_ifs <;> rfl

#print axioms rowValues_fixed_width
end Maxwell.Continuum.Calibration.SeedRoot
