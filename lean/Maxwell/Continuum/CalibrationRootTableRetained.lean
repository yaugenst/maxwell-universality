import Maxwell.Continuum.CalibrationRootTableComputed
import Maxwell.Cost.Structured.NatAssign.TapeInterval
import Maxwell.Cost.Structured.NatAssignTapeBound

/-! The root cache preserves the later seed operands and all high selector
ports. Literal values remain opaque while their tape footprint is checked. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Calibration
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

theorem parameters_outside (lo hi : ℕ) (low : 700≤lo)
    (simple : (PhysicalMaterial.FixedSubtract.code 338 1).outsideTapes lo hi=true ∧
      (NaturalQuotient.code 338 332 335).outsideTapes lo hi=true ∧
      (WordLength.code 336 340).outsideTapes lo hi=true) :
    RootParameters.code.outsideTapes lo hi=true := by
  have outside : ∀i∈RootParameters.ids,i<lo ∨hi ≤ i := by
    intro i hi'
    simp only [RootParameters.ids,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi'
    left;omega
  have stage (p : List NatAssign.Instruction) (valid : ∀a∈p,a.Valid RootParameters.ids) :
      (NatAssign.code p).outsideTapes lo hi=true :=
    NatAssign.code_outside p RootParameters.ids lo hi valid (by omega) outside
  simp only [RootParameters.code,Code.outsideTapes,Bool.and_eq_true]
  exact ⟨stage _ RootParameters.prepare_valid,simple.1,simple.2.1,
    stage _ RootParameters.gridPlan_valid,simple.2.2,stage _ RootParameters.precisionPlan_valid⟩

theorem computed_seedBank : computedCode.outsideTapes 700 1000=true := by
  have parameters := parameters_outside 700 1000 (by decide) (by decide +kernel)
  simp only [computedCode,parameterCode,Code.outsideTapes,parameters,Bool.true_and]
  decide +kernel

theorem parameters_tapeBound : RootParameters.code.tapeBound≤1040 := by
  have prepare := NatAssign.code_tapeBound_le RootParameters.prepare RootParameters.ids 1040
    RootParameters.prepare_valid (by decide) (by decide)
  simp only [RootParameters.code,Code.tapeBound,max_le_iff]
  exact ⟨prepare,by decide +kernel⟩

theorem computed_tapeBound : computedCode.tapeBound≤1040 := by
  simp only [computedCode,parameterCode,Code.tapeBound,max_le_iff]
  exact ⟨⟨parameters_tapeBound,by decide +kernel⟩,by decide +kernel⟩

#print axioms computed_seedBank
#print axioms computed_tapeBound
end Maxwell.Continuum.RationalDataflow.RootTable
