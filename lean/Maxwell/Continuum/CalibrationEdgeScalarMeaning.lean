import Maxwell.Continuum.CalibrationBasisMatrixSign
import Maxwell.Continuum.CalibrationEdgeScalarRestartData
import Maxwell.Continuum.EdgeCertifiedBisection
import Maxwell.Continuum.EdgeBracketMachine

/-! Identify the generated five scalar cells and24-column matrix with the
precise edge decision used by the certified finite bisection. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Maxwell.Certificate

theorem result_admissible (N : ℕ) (mid : Parts) (positive : 0<mid.denominator)
    (inside : edgeInitial.lo≤mid.value ∧ mid.value≤edgeInitial.hi) :
    BasisColumn.admissible (result N mid) := by
  obtain ⟨pi,energy,quasi⟩:=result_value N mid positive
  have bounds:=edgeTrial_totalEnergy_bounds mid.value (edgeInitial_trial_bound mid.value inside)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [pi] using (piCenter_bounds (N+1)).1
  · simpa only [energy,Rat.cast_add,Rat.cast_ofNat] using bounds.1
  · simpa only [energy,Rat.cast_add,Rat.cast_ofNat] using bounds.2
  · intro j
    rw [quasi (234+j.val) (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)]
    norm_num

theorem matrix_eq (N : ℕ) (mid : Parts) (positive : 0<mid.denominator) :
    symmetricRationalMatrix (BasisColumn.matrix (N+5) (result N mid))=edgeMatrix mid.value N := by
  obtain ⟨pi,energy,quasi⟩:=result_value N mid positive
  have zero : (fun j:Fin 3=>(result N mid (234+j.val)).value)=(fun _=>0) := by
    funext j
    exact quasi _ (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)
  rw [BasisColumn.matrix,pi,energy,zero,show N+5-2=N+3 by omega]
  exact cachedEdgeMatrix_eq mid.value N

theorem midpoint_positive (v : ℕ→ℕ) (den : EdgeBracketMachine.Denominators v) :
    0<(EdgeBracketMachine.parts (EdgeBracketMachine.midpointResult v) 2302).denominator := by
  change 0<NatAssign.values (SignedBracket.midpointPlan EdgeBracketMachine.base) v (EdgeBracketMachine.base+8)
  rw [SignedBracket.midpoint_get _ v 8 (by decide)]
  simpa [SignedBracket.midpointValue] using Nat.mul_pos (by decide : 0<2) den.1

theorem bracket_midpoint_inside (k : ℕ) :
    edgeInitial.lo≤(edgeBrackets edgeDecision 182 edgeInitial k).midpoint ∧
      (edgeBrackets edgeDecision 182 edgeInitial k).midpoint≤edgeInitial.hi := by
  have inside:=edgeBrackets_inside edgeDecision 182 edgeInitial k
  have ordered:=(edgeBrackets edgeDecision 182 edgeInitial k).ordered
  simp only [Interval.midpoint]
  constructor <;> linarith

#print axioms matrix_eq
#print axioms result_admissible
end Maxwell.Continuum.Calibration.EdgeScalar
