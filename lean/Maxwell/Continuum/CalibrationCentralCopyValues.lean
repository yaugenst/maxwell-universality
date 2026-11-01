import Maxwell.Continuum.CalibrationCentralCopyBank

/-! The executed copies load exactly the matrix cells while leaving the
isolated circuit's other rational registers at initialized zero. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes inputPorts relocation gap inputRegisters inputSources inputPlan

theorem input_values (v : ℕ→Parts) (i : ℕ) (hi : i∈ids bank) :
    NatAssign.values inputPlan (inputWords v) (relocation i)=dataValues (matrixParts v) i := by
  rcases Finset.mem_union.mp hi with cell | scratch
  · obtain ⟨j,hj,cell⟩:=Finset.mem_biUnion.mp cell
    have owned :=cell_mem hj cell
    by_cases small : j<576
    · have core : 1000≤ i ∧ i<2728 := by
        simp only [cellPorts,positivePort,negativePort,denominatorPort,
          Finset.mem_insert,Finset.mem_singleton] at cell
        omega
      rw [input_copy_values v i core]
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at cell
      rcases cell with rfl|rfl|rfl
      · rw [show positivePort j+1500=positivePort (500+j) by unfold positivePort;omega]
        simp only [dataValues_positive,matrixParts,ite_eq_left small]
      · rw [show negativePort j+1500=negativePort (500+j) by unfold negativePort;omega]
        simp only [dataValues_negative,matrixParts,ite_eq_left small]
      · rw [show denominatorPort j+1500=denominatorPort (500+j) by unfold denominatorPort;omega]
        simp only [dataValues_denominator,matrixParts,ite_eq_left small]
    · have outside : ¬(1000≤ i ∧ i<2728) := by
        simp only [cellPorts,positivePort,negativePort,denominatorPort,
          Finset.mem_insert,Finset.mem_singleton] at cell
        omega
      rw [input_copy_unchanged v i owned outside]
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at cell
      rcases cell with rfl|rfl|rfl <;>
        simp only [dataValues_positive,dataValues_negative,dataValues_denominator,matrixParts,ite_eq_right small]
  · have low : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at scratch
      omega
    rw [input_copy_unchanged v i (Finset.mem_union_right _ scratch) (by omega),
      dataValues_small _ low,dataValues_small _ low]

#print axioms input_values
end Maxwell.Continuum.Calibration.CentralRelocation
