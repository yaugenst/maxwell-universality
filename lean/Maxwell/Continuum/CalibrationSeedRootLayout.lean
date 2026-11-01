import Maxwell.Continuum.CalibrationSeedRootRowData
import Maxwell.Continuum.CalibrationForcingIndex
import Maxwell.Continuum.CalibrationGlobalCoordinates

/-! Canonical real/imaginary block addresses for six fixed producers per
alias row. The dimension and the destination address are runtime naturals. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def shapePlan : List NatAssign.Instruction :=
  [.literal 782 2,.literal 783 3,.literal 791 1,
   .copy 750 786,.multiply 783 786,.add 751 786,.multiply 782 786,.add 791 786,
   .copy 786 787,.multiply 786 787,.multiply 786 787,
   .copy 787 785,.multiply 783 785,.copy 785 788,.multiply 782 788]
def shapeValues (v : ℕ→ℕ) := NatAssign.values shapePlan v
def destinationPlan (j : Fin 3) (part : Fin 2) : List NatAssign.Instruction :=
  [.literal 772 j.val,.literal 773 part.val,.literal 783 3,
   .copy 780 789,.multiply 783 789,.add 772 789,
   .copy 785 790,.multiply 773 790,.add 790 789]
def destinationValues (j : Fin 3) (part : Fin 2) (v : ℕ→ℕ) := NatAssign.values (destinationPlan j part) v
def outputCoordinate (M D : ℕ) (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)))
    (j : Fin 3) (part : Fin 2) : Fin (2*aliasArraySize (3*M+D)) :=
  GlobalPower.realIndex (3*M+D) (part,ArrayDecodeMachine.polarizationRow (3*M+D) row j)

theorem shapePlan_valid : ∀a∈shapePlan,a.Valid ids := by
  simp [shapePlan,NatAssign.Instruction.Valid,ids,extra,SelectedParameters.Compare.ids]
theorem destinationPlan_valid (j : Fin 3) (part : Fin 2) : ∀a∈destinationPlan j part,a.Valid ids := by
  simp [destinationPlan,NatAssign.Instruction.Valid,ids,extra,SelectedParameters.Compare.ids]

theorem shapeValues_fields (v : ℕ→ℕ) :
    shapeValues v 785=aliasArraySize (3*v 750+v 751) ∧
    shapeValues v 786=aliasSide (3*v 750+v 751) ∧
    shapeValues v 787=ArrayDecodeMachine.aliasRowCount (3*v 750+v 751) ∧
    shapeValues v 788=2*aliasArraySize (3*v 750+v 751) := by
  simp [shapeValues,shapePlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,aliasArraySize,aliasSide,
    ArrayDecodeMachine.aliasRowCount]
  and_intros <;> first | trivial | ring

theorem destinationValues_index (j : Fin 3) (part : Fin 2) (v : ℕ→ℕ) :
    destinationValues j part v 789=part.val*v 785+(3*v 780+j.val) := by
  simp [destinationValues,destinationPlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  ring

theorem outputCoordinate_value (M D : ℕ) (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)))
    (j : Fin 3) (part : Fin 2) :
    (outputCoordinate M D row j part).val=part.val*aliasArraySize (3*M+D)+(3*row.val+j.val) := by
  simp [outputCoordinate,GlobalPower.realIndex,finProdFinEquiv,ArrayDecodeMachine.polarizationRow,
    Nat.mul_comm,Nat.add_comm]

theorem destinationValues_keep (j : Fin 3) (part : Fin 2) (v : ℕ→ℕ) (i : ℕ)
    (hi : i∉({772,773,783,789,790}:Finset ℕ)) : destinationValues j part v i=v i := by
  apply NatAssign.values_preserves
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp [destinationPlan,NatAssign.Instruction.target,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2]

theorem row_outputAlias (M D : ℕ) (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) :
    outputAlias M D (decodedCoordinates (3*M+D) (3*row.val))=
      arrayAliasAt (3*M+D) (ArrayDecodeMachine.polarizationRow (3*M+D) row 0) := by
  funext k
  rw [arrayAliasAt_decode]
  simp [outputAlias,ArrayDecodeMachine.polarizationRow]

theorem sample_outputCoordinate (M D : ℕ) (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)))
    (j : Fin 3) (part : Fin 2) (f : RationalAliasField) :
    GlobalPower.sample (3*M+D) f (outputCoordinate M D row j part)=
      scalarPart (f (outputAlias M D (decodedCoordinates (3*M+D) (3*row.val))) j) part := by
  rw [row_outputAlias]
  have aliasEq := ArrayDecodeMachine.polarizationRow_alias (3*M+D) row j
  have componentEq := ArrayDecodeMachine.polarizationRow_polarization (3*M+D) row j
  simp only [outputCoordinate,GlobalPower.sample,Equiv.symm_apply_apply]
  change (if part=0 then
    (f (arrayAliasAt (3*M+D) (ArrayDecodeMachine.polarizationRow (3*M+D) row j))
      (arrayPolarizationAt (3*M+D) (ArrayDecodeMachine.polarizationRow (3*M+D) row j))).1 else
    (f (arrayAliasAt (3*M+D) (ArrayDecodeMachine.polarizationRow (3*M+D) row j))
      (arrayPolarizationAt (3*M+D) (ArrayDecodeMachine.polarizationRow (3*M+D) row j))).2)=_
  rw [aliasEq,componentEq]
  fin_cases part <;> rfl

#print axioms sample_outputCoordinate
end Maxwell.Continuum.Calibration.SeedRoot
