import Maxwell.Continuum.CalibrationBasisInverse
import Maxwell.Continuum.CalibrationGeneratedInverseTapeBound

/-! All scalar workspace used to generate a basis inverse stays below the
retained Schur cells. This bound is independent of the chosen column. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem code_tapeBound (column : Fin 24) : (code column).tapeBound ≤ 1696 := by
  apply Control.tapeBound_le (PointSupport.control (support column) 32)
    (PointSupport.registers (support column) 32) 232
    (PointSupport.valid _ _ (support_scoped column))
  intro i hi
  simpa only [registers_eq,Finset.mem_range] using hi

private theorem coefficient_tapeBound : CoefficientAllocation.counterCode.tapeBound ≤ 1696 := by
  have bound : ∀i∈CoefficientAllocation.allIds,i<1696 := by decide
  simp only [CoefficientAllocation.counterCode,CoefficientAllocation.code,Code.tapeBound,max_le_iff]
  refine ⟨⟨?_,?_,by decide⟩,by decide⟩
  · apply NatAssign.LengthSum.initializedCode_tapeBound 580 581 626 1696 CoefficientAllocation.sources
      (by decide) (by decide) (by decide) (by decide)
    intro i hi
    exact bound i ((CoefficientAllocation.sources_valid i hi).1)
  · exact NatAssign.code_tapeBound_le CoefficientAllocation.plan CoefficientAllocation.allIds 1696
      CoefficientAllocation.plan_valid (by decide) bound

namespace Inverse

theorem tapeBound (column : Fin 24) : (code column).tapeBound ≤ 1696 := by
  have allocated : AllocatedInverse.code.tapeBound ≤ 1696 := AllocatedInverse.tapeBound.trans (by decide)
  simp only [code,CoefficientInput.code,inputCode,allocatedCode,tableCode,bodyCode,
    storeCode,prepareCode,countedProgram,CountedShifted.code,Counted.code,Code.tapeBound,max_le_iff,
    code_tapeBound column,coefficient_tapeBound,allocated,and_true]
  decide +kernel

theorem protectsTape (column : Fin 24) (i : ℕ) (hi : 1696 ≤ i) :
    (code column).protectsTape i = true :=
  (code column).protectsTape_of_bound i ((tapeBound column).trans hi)

#print axioms tapeBound

end Inverse
end Maxwell.Continuum.Calibration.BasisForcing
