import Maxwell.Continuum.CalibrationInverseDescriptorStart
import Maxwell.Continuum.CalibrationInverseDescriptorConditions

/-! Assemble the descriptor scanner's bank from the actual coefficient table,
its returned allocation words, and untouched continuation words. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def coldIds : Finset ℕ := Finset.Icc 107 140∪Finset.Icc 300 309∪Finset.Icc 530 534
def inputs (R slot base Q : ℕ) (cold : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k=311 then R else if k=570 then tableSize (aliasArraySize R) else
  if k=571 then slot else if k=572 then base else if k=580 then Q else
  if k=210 then slot else if k=212 then base else
  if k=213 then base+tableSize (aliasArraySize R)*slot else
  if k=214 then base+2*tableSize (aliasArraySize R)*slot else cold k
def inputBound (R slot base Q X M : ℕ) : ℕ :=
  R.bits.length+(tableSize (aliasArraySize R)).bits.length+slot.bits.length+base.bits.length+
    Q.bits.length+X+M+11

theorem cold_continuation : coldIds⊆continuationPorts := by
  intro k hk
  simp only [coldIds,Finset.mem_union,Finset.mem_Icc] at hk
  simp only [continuationPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem input_bank (R slot base Q X M : ℕ) (cold : ℕ→ℕ)
    (a : Table (tableSize (aliasArraySize R))) (layout:SourceLayout a base)
    (width:addressValue a.width=slot) (bounds:a.MetadataWidth M)
    (s : Store) (ready:a.OutputReady s) (bank:NatAssign.Bank coldIds cold s.val)
    (coldWidth:∀k∈coldIds,(cold k).bits.length≤X)
    (radius:RationalAccumulator.Word s.val 311 R)
    (count:RationalAccumulator.Word s.val 570 (tableSize (aliasArraySize R)))
    (slotWord:RationalAccumulator.Word s.val 571 slot)
    (baseWord:RationalAccumulator.Word s.val 572 base)
    (budgetWord:RationalAccumulator.Word s.val 580 Q) :
    NatAssign.Bank ids (inputs R slot base Q cold) s.val ∧
      ∀k∈ids,(inputs R slot base Q cold k).bits.length ≤ inputBound R slot base Q X M := by
  have header:a.width=slot.bits:=layout.canonical.trans (congrArg Nat.bits width)
  have positive:=layout.positive
  have negative:a.baseNegative=(base+tableSize (aliasArraySize R)*slot).bits:=by rw [layout.negative,width]
  have denominator:a.baseDenominator=(base+2*tableSize (aliasArraySize R)*slot).bits:=by rw [layout.denominator,width]
  have each (k : ℕ) (hk:k∈ids) :
      RationalAccumulator.Word s.val k (inputs R slot base Q cold k) ∧
      (inputs R slot base Q cold k).bits.length ≤ inputBound R slot base Q X M := by
    unfold inputs
    split_ifs with h311 h570 h571 h572 h580 h210 h212 h213 h214
    · subst k;exact ⟨radius,by unfold inputBound;omega⟩
    · subst k;exact ⟨count,by unfold inputBound;omega⟩
    · subst k;exact ⟨slotWord,by unfold inputBound;omega⟩
    · subst k;exact ⟨baseWord,by unfold inputBound;omega⟩
    · subst k;exact ⟨budgetWord,by unfold inputBound;omega⟩
    · subst k
      exact ⟨by simpa only [header,BankArray.Word,RationalAccumulator.Word] using ready.width,
        by unfold inputBound;omega⟩
    · subst k
      exact ⟨by simpa only [positive,BankArray.Word,RationalAccumulator.Word] using ready.basePositive,
        by unfold inputBound;omega⟩
    · subst k
      have h:(base+tableSize (aliasArraySize R)*slot).bits.length≤M:=by
        simpa only [negative] using bounds.baseNegative
      exact ⟨by simpa only [negative,BankArray.Word,RationalAccumulator.Word] using ready.baseNegative,
        by unfold inputBound;omega⟩
    · subst k
      have h:(base+2*tableSize (aliasArraySize R)*slot).bits.length≤M:=by
        simpa only [denominator] using bounds.baseDenominator
      exact ⟨by simpa only [denominator,BankArray.Word,RationalAccumulator.Word] using ready.baseDenominator,
        by unfold inputBound;omega⟩
    · have hc:k∈coldIds:=by
        simp only [ids,sourceIds,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
        simp only [coldIds,Finset.mem_union,Finset.mem_Icc]
        omega
      exact ⟨bank k hc,by have h:=coldWidth k hc;unfold inputBound;omega⟩
  exact ⟨fun k hk=>(each k hk).1,fun k hk=>(each k hk).2⟩

theorem input_parameters (R slot base Q : ℕ) (cold : ℕ→ℕ) :
    inputs R slot base Q cold 311=R ∧ inputs R slot base Q cold 570=tableSize (aliasArraySize R) ∧
    inputs R slot base Q cold 571=slot ∧ inputs R slot base Q cold 572=base := by
  simp [inputs]

#print axioms input_bank
end Maxwell.Continuum.Calibration.InverseDescriptor
