import Maxwell.Continuum.CalibrationEdgeEvaluator
import Maxwell.Continuum.RationalDefinitenessUnitary
import Maxwell.Continuum.EdgeInitialWidths

/-! A total, finite rational algorithm enclosing the actual continuum band edge.
Its decisions are exact finite matrix tests with proved full-fiber error. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate FreeFiber PeriodicBand

def edgeDecision (q : ℚ) (N : ℕ) : Bool := negativeTest (edgeMatrix q N)

theorem rationalOperator_eq_centralMatrix (A : Matrix (Fin 24) (Fin 24) ℚ) :
    rationalOperator A=centralMatrixCLM (A.map (Rat.castHom ℂ)) := by
  ext x i
  rfl

theorem edgeDecision_sound (q : ℚ) (N : ℕ) (hq : edgeInitial.lo≤q ∧ q≤edgeInitial.hi) :
    (edgeDecision q N=true → (dielectricBand 0).re≤(q : ℝ)+(1/2 : ℝ)^N) ∧
      (edgeDecision q N=false → (q : ℝ)-(1/2 : ℝ)^N≤(dielectricBand 0).re) := by
  have he := edgeInitial_trial_bound q hq
  let A := edgeMatrix q N
  let B := unitaryPush centralFinUnitary (rationalOperator A)
  have hA : ∀ i j, A i j=A j i := by
    intro i j
    exact (congrFun (congrFun (edgeMatrix_symmetric q N) i) j).symm
  have herr : ‖B-calibrationFiniteSchur 0 (edgeTrialScaled q)
      edgeParameterBound (edgeEnergyBound he)‖≤(1/2 : ℝ)^N := by
    rw [unitaryPush_error,rationalOperator_eq_centralMatrix]
    exact edgeMatrix_error q N he
  constructor
  · intro h
    exact edge_negative_sign q he B herr (negativeTest_unitary centralFinUnitary A hA h)
  · intro h
    exact edge_nonnegative_sign q he B herr (negativeTest_unitary_false centralFinUnitary A hA h)

def calibratedEdgeInterval (N : ℕ) : Interval := edgeBrackets edgeDecision 182 edgeInitial (2*N)

theorem calibratedEdgeInterval_contains (N : ℕ) :
    (calibratedEdgeInterval N).Contains (dielectricBand 0).re := by
  apply edgeBrackets_contains edgeDecision 182 edgeInitial
    (by rw [edgeInitial_width]) edgeInitial_contains
  intro q P hlo hhi
  exact edgeDecision_sound q P ⟨hlo,hhi⟩

theorem calibratedEdgeInterval_width (N : ℕ) :
    (calibratedEdgeInterval N).width≤(1/2 : ℚ)^N := by
  have hi : edgeInitial.width≤(2 : ℚ)^0 := by
    rw [edgeInitial_width,pow_zero]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  simpa only [calibratedEdgeInterval,add_zero] using
    edgeBrackets_target_width edgeDecision 182 edgeInitial 0 N hi

def calibratedEdge (N : ℕ) : Ball :=
  ⟨(calibratedEdgeInterval N).midpoint,(1/2)^N,by positivity⟩

theorem calibratedEdge_contains (N : ℕ) : (calibratedEdge N).Contains (dielectricBand 0).re := by
  have hw : (calibratedEdgeInterval N).width≤2*(1/2 : ℚ)^N :=
    (calibratedEdgeInterval_width N).trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  have h := (calibratedEdgeInterval N).midpoint_error_of_width (calibratedEdgeInterval_contains N) hw
  change |(dielectricBand 0).re-((calibratedEdgeInterval N).midpoint : ℝ)|≤(((1/2 : ℚ)^N : ℚ) : ℝ)
  simpa only [abs_sub_comm] using h

theorem calibratedEdge_center_width (N : ℕ) :
    RationalWords.Width (calibratedEdge N).center (2^66+24*N+5) := by
  have h := edgeInitialBrackets_midpoint_width edgeDecision (2*N)
  change RationalWords.Width (calibratedEdge N).center (2^66+12*(2*N)+5) at h
  convert h using 1
  ring

#print axioms edgeDecision_sound
#print axioms calibratedEdge_contains
#print axioms calibratedEdge_center_width

end Maxwell.Continuum.Calibration
