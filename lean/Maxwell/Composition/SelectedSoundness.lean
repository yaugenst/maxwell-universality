import Maxwell.Composition.SelectedInstance

/-! Discharge every physical calibration, spacing, source, access, and range
budget with the actual selected platform and executable rational choices. -/
noncomputable section
namespace Maxwell.Composition.SelectedInstance.Input
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

variable (I : Input) (R : SelectedPlatform)

abbrev bad (J : ℕ) : Finset ℕ :=
  PhysicalGram.bad R.physical I.source I.precision (I.distance R)
    (I.zeta R) (I.zeta_pos R) (I.zeta_one R) J

/-- The common event already contains full conditioning and every-message
correctness for the actual target. Only the original source assumptions and
its coefficient precision remain hypotheses. -/
theorem sound_at_minimum (J : ℕ) (j : Fin J) (hj : j.val ∉ I.bad R J)
    (hunit : IsUnit (Source.realMatrix I.source)) (hm : 2 ≤ I.source.nnz)
    (hb : I.source.source ≠ 0) (hp : 1 ≤ I.precision) (haccuracy : I.accuracy ≤ 1)
    (hcondition : (I.source.nnz : ℝ)*condition₂ (Source.realMatrix I.source) ≤ I.sourceBound)
    (hprecision : (I.source.nnz : ℝ)/(2*2^I.precision) ≤ (I.accuracy : ℝ)/(64*I.sourceBound)) :
    IsUnit (I.target R J j).realMatrix ∧
      condition₂ (I.target R J j).realMatrix ≤ 16*(I.fullBudget R : ℝ) ∧
      ∀ y : EuclideanSpace ℂ (I.target R J j).box.Edge, (I.target R J j).Admissible y →
        (I.target R J j).decoder.Fits (fun e => (y e).re) ∧
        (∃ w : (I.target R J j).decoder.Messages,
          (I.target R J j).decoder.Accurate w (fun e => (y e).re)) ∧
        ∀ w : (I.target R J j).decoder.Messages,
          (I.target R J j).decoder.Accurate w (fun e => (y e).re) →
          Source.ResidualTarget I.source ((I.accuracy : ℝ)/4) ((I.target R J j).decoder.decode w) := by
  have h := PhysicalSoundness.sound R.physical I.source I.precision (I.distance R)
    (I.zeta R) (I.zeta_pos R) (I.zeta_one R) (I.distance_minimum R)
    J j I.nnz_pos hj I.epsilon (I.backgroundBudget R) I.epsilon_pos (I.backgroundBudget_pos R)
    (I.coordinates R) (I.increment R) (I.increment_bounds R) (I.increment_ne_zero R)
    (I.residualTolerance R) (I.residualTolerance_pos R) (I.format R)
    hunit hm hb hp (I.sourceBound : ℝ) (I.accuracy : ℝ)
    (by exact_mod_cast I.sourceBound_ge_one) (by exact_mod_cast I.accuracy_pos.le)
    (by exact_mod_cast haccuracy) hcondition hprecision
    (by rw [R.rowBound_eq]) (I.backgroundBudget_ge_one R) I.epsilon_half
    le_rfl (I.distance_floor R) rfl (I.coupling R)
    (I.coupling_lower R) (I.coupling_upper R) (I.coupling_error R)
    (fun i => (I.increment_spec R i).2.2.1) (I.spacing_budget R)
    (I.coordinates_norm R) (I.coordinates_source_budget R)
    (by rw [← I.fullBudget_cast R]; exact I.coordinates_read_budget R)
    (I.residualTolerance_budget R) (I.residualTolerance_half R) (I.format_access R)
    (by rw [← I.fullBudget_cast R]; exact I.format_range R hunit hb)
    (by exact_mod_cast I.logical_budget) (I.read_budget hunit hb)
  rw [← I.fullBudget_cast R] at h
  exact h

/-- Uniformity in the requested accuracy is obtained from the one emitted
minimum-accuracy instance, so no solver output or requested eta changes the
event, parameter choices, source, or decoder. -/
theorem sound (J : ℕ) (j : Fin J) (hj : j.val ∉ I.bad R J)
    (hunit : IsUnit (Source.realMatrix I.source)) (hm : 2 ≤ I.source.nnz)
    (hb : I.source.source ≠ 0) (hp : 1 ≤ I.precision) (haccuracy : I.accuracy ≤ 1)
    (hcondition : (I.source.nnz : ℝ)*condition₂ (Source.realMatrix I.source) ≤ I.sourceBound)
    (hprecision : (I.source.nnz : ℝ)/(2*2^I.precision) ≤ (I.accuracy : ℝ)/(64*I.sourceBound)) :
    IsUnit (I.target R J j).realMatrix ∧
      condition₂ (I.target R J j).realMatrix ≤ 16*(I.fullBudget R : ℝ) ∧
      ∀ y : EuclideanSpace ℂ (I.target R J j).box.Edge, (I.target R J j).Admissible y →
        (I.target R J j).decoder.Fits (fun e => (y e).re) ∧
        (∃ w : (I.target R J j).decoder.Messages,
          (I.target R J j).decoder.Accurate w (fun e => (y e).re)) ∧
        ∀ w : (I.target R J j).decoder.Messages,
          (I.target R J j).decoder.Accurate w (fun e => (y e).re) →
          ∀ eta : ℝ, (I.accuracy : ℝ) ≤ eta →
            Source.ResidualTarget I.source eta ((I.target R J j).decoder.decode w) := by
  obtain ⟨hu,hc,hy⟩ := I.sound_at_minimum R J j hj hunit hm hb hp haccuracy hcondition hprecision
  refine ⟨hu,hc,?_⟩
  intro y hy'
  obtain ⟨hf,he,hw⟩ := hy y hy'
  refine ⟨hf,he,?_⟩
  intro w hw' eta heta
  have hr := hw w hw'
  apply hr.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (Source.rhs I.source))
  have ha : (0 : ℝ) ≤ I.accuracy := by exact_mod_cast I.accuracy_pos.le
  linarith

end Maxwell.Composition.SelectedInstance.Input
