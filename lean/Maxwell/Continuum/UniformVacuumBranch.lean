import Maxwell.Continuum.UniformVacuumCost
import Maxwell.Continuum.VacuumBranch
import Maxwell.Continuum.LinearCostBudget

/-! The actual shared-parser encoder satisfies the complete vacuum contract,
with its source scan included in the joint encoder and decoder charge. -/
noncomputable section
namespace Maxwell.Continuum.Realization

theorem uniform_vacuum_branch (computed : Cost.Structured.Code) (p : Source.Parameters)
    (C : Constants) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (hbase : S.source=0∨S.nnz≤1)
    (hc : 65000000000≤C.overhead) (hscan : 2*UniformEncoder.vacuumCoefficient p≤C.overhead)
    (hw : 4≤C.wordCoefficient) (hpower : 10≤C.conditionPower) :
    VacuumBranch p C S (UniformEncoder.program computed) CompleteDecoder.program := by
  obtain ⟨_,_,_,_,_,description,remaining⟩:=vacuum_branch p C S hp hbase hc hw hpower
  exact ⟨UniformEncoder.vacuumFuel p S,CompleteDecoder.vacuumCost (vacuumDecoder S)+1,
    UniformEncoder.vacuum_encodes computed p S hp hbase,VacuumDecoder.decodes S C hw,
    linear_cost_budget C S _ _ 3 4096 hscan (by decide) (UniformEncoder.vacuum_cost p S hp),
    description,remaining⟩

#print axioms uniform_vacuum_branch
end Maxwell.Continuum.Realization
