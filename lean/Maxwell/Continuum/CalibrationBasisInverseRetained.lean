import Maxwell.Continuum.CalibrationBasisInverseTapeBound
import Maxwell.Continuum.RationalDataflowTapeInterval
import Maxwell.Cost.Structured.NatAssign.LengthSumTapeInterval

/-! The fixed basis-inverse programs leave the bisection precision and
Machin workspace untouched. One syntax certificate covers the entire bank. -/
namespace Maxwell.Continuum.Calibration.BasisForcing.Inverse
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
attribute [local irreducible] BasisForcing.code PointSupport.registers support

private theorem forcing_retained (column : Fin 24) :
    (BasisForcing.code column).outsideTapes 850 924=true := by
  unfold BasisForcing.code
  apply Control.outsideTapes (PointSupport.control (support column) 32)
    (PointSupport.registers (support column) 32) 850 924
    (PointSupport.valid _ _ (support_scoped column)) (by decide) _ (by decide +kernel)
  intro i hi
  rcases Finset.mem_union.mp hi with raw|scratch
  · obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp raw
    simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at scratch
    omega

private theorem allocated_retained : AllocatedInverse.code.outsideTapes 850 924=true := by
  have measure : InverseDescriptor.measureCode.outsideTapes 850 924=true := by
    apply NatAssign.LengthSum.initializedCode_outside 530 531 1024 850 924 InverseDescriptor.sources
      (by decide) (by decide) (by decide) (by decide)
    intro i hi
    have member : i∈InverseDescriptor.sourceIds := by
      simpa only [InverseDescriptor.sources,Finset.mem_sort] using hi
    simp only [InverseDescriptor.sourceIds,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton] at member
    omega
  have plan : (NatAssign.code InverseDescriptor.plan).outsideTapes 850 924=true :=
    NatAssign.code_outside _ InverseDescriptor.ids 850 924 InverseDescriptor.plan_valid
      (by decide) (by decide +kernel)
  simp only [AllocatedInverse.code,InverseDescriptor.startCode,InverseDescriptor.code,
    Code.outsideTapes,measure,plan,Bool.and_true]
  decide +kernel

private theorem coefficient_retained : CoefficientAllocation.counterCode.outsideTapes 850 924=true := by
  have outside : ∀i∈CoefficientAllocation.allIds,i<850 ∨924 ≤ i := by decide +kernel
  have measure : CoefficientAllocation.measureCode.outsideTapes 850 924=true := by
    apply NatAssign.LengthSum.initializedCode_outside 580 581 626 850 924 CoefficientAllocation.sources
      (by decide) (by decide) (by decide) (by decide)
    intro i hi
    exact outside i (CoefficientAllocation.sources_valid i hi).1
  have plan : (NatAssign.code CoefficientAllocation.plan).outsideTapes 850 924=true :=
    NatAssign.code_outside _ CoefficientAllocation.allIds 850 924 CoefficientAllocation.plan_valid
      (by decide) outside
  simp only [CoefficientAllocation.counterCode,CoefficientAllocation.code,
    Code.outsideTapes,measure,plan,Bool.true_and]
  decide +kernel

theorem edgeWorkspace_retained (column : Fin 24) :
    (code column).outsideTapes 850 924=true := by
  simp only [code,CoefficientInput.code,inputCode,allocatedCode,tableCode,bodyCode,
    storeCode,prepareCode,countedProgram,CountedShifted.code,Counted.code,Code.outsideTapes,
    forcing_retained column,allocated_retained,coefficient_retained,Bool.and_true]
  decide +kernel

#print axioms edgeWorkspace_retained
end Maxwell.Continuum.Calibration.BasisForcing.Inverse
