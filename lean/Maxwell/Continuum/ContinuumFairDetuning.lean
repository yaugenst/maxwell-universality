import Maxwell.Continuum.FairBitsLaw
import Maxwell.Continuum.ContinuumReductionSoundness
import Maxwell.Continuum.ContinuumDetuningWords

/-! The actual finite fair-bit draw induces exactly the midpoint-grid law
used by the continuum resolvent estimate. The bad event is fixed before
the solver field or its report words are chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def randomBitCount : ℕ := Detuning.randomBits S.nnz (count p S hm)

def randomDraw (w : Fin (randomBitCount p S hm) → Bool) : Fin (drawCount p S hm) :=
  FairBits.binaryEquiv (randomBitCount p S hm) w

theorem randomDraw_value (w : Fin (randomBitCount p S hm) → Bool) :
    (randomDraw p S hm w).val=
      ∑i : Fin (randomBitCount p S hm),(finTwoEquiv.symm (w i)).val*2^i.val := rfl

theorem randomDraw_law :
    (FairBits.law (randomBitCount p S hm)).map (fun w => (randomDraw p S hm w).val)=
      DetuningGrid.gridLaw (drawCount p S hm) (by unfold drawCount Detuning.gridSize; positivity) :=
  FairBits.binary_law _

theorem randomDraw_bad_probability (hb : S.source≠0) :
    ((FairBits.law (randomBitCount p S hm)).toOuterMeasure
      {w | (randomDraw p S hm w).val∈computedBadDraws p S hm hb}).toReal≤
        3/(64*(S.nnz : ℝ)) := by
  have h := computed_bad_probability p S hm hb
  unfold DetuningGrid.gridProbability at h
  rw [← randomDraw_law p S hm,PMF.toOuterMeasure_map_apply] at h
  exact h

theorem randomBitCount_linear (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    randomBitCount p S hm≤detuningBitCoefficient p*logSize S := by
  have h := detuningPrecision_linear p S hm hm2 hu
  unfold detuningPrecision at h
  change Detuning.randomBits S.nnz (count p S hm)≤_
  omega

#print axioms randomDraw_law
#print axioms randomDraw_bad_probability
#print axioms randomBitCount_linear

end Maxwell.Continuum.RealizationParameters
