import Maxwell.Continuum.Main

/-! Analytic clauses of the concrete continuum contract. The selected
exceptional event controls the actual PEC inverse and every finite-report
recovery simultaneously. Uniform encoder and complete-description decoder
execution remain separate obligations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.Realization
open RealizationParameters
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent Calibration.FiniteAlgorithm.mode pecCurlCurl computedEnclosures

theorem goodDraw_of_selected (p : Source.Parameters) (C : Constants)
    (S : Source.SparseSystem) (hm : 0 < S.nnz) (hm2 : 2 ≤ S.nnz)
    (hp : Source.Promises p S) (hb : S.source ≠ 0)
    (hpower : analysisBits p ≤ C.conditionPower) (j : Fin (drawCount p S hm))
    (hgood : j.val ∉ computedBadDraws p S hm hb) : GoodDraw p C S hm hb j := by
  obtain ⟨R, hR, hgraph, hcondition⟩ := computed_good_draw_inverse p S hm hm2 hp.1 hb j hgood
  refine ⟨⟨R, hR, hgraph, ?_⟩, ?_⟩
  · rw [S.effectiveSize_of_two_le hm2]
    exact hcondition.trans (pow_le_pow_right₀ (by exact_mod_cast hm) hpower)
  · intro u hu
    have fits := decoder_fits p S hm hm2 hp hb j hgood u hu
    refine ⟨fits, (decoder p S hm).exists_accurate (gridFieldReports p S hm u) fits, ?_⟩
    intro w hw eta heta
    exact decoder_recovery p S hm hm2 hp hb j hgood u hu w hw eta heta

/-- The event is selected solely from the input and finite fair bits.
Its guarantee quantifies over fields and messages only after the draw. -/
theorem selected_good_event (p : Source.Parameters) (C : Constants)
    (S : Source.SparseSystem) (hm : 0 < S.nnz) (hm2 : 2 ≤ S.nnz)
    (hp : Source.Promises p S) (hb : S.source ≠ 0)
    (hpower : analysisBits p ≤ C.conditionPower) :
    (∀ w : Fin (randomBitCount p S hm) → Bool,
      (randomDraw p S hm w).val ∉ computedBadDraws p S hm hb →
        GoodDraw p C S hm hb (randomDraw p S hm w)) ∧
    ((FairBits.law (randomBitCount p S hm)).toOuterMeasure
      {w | (randomDraw p S hm w).val ∈ computedBadDraws p S hm hb}).toReal ≤
        3 / (64 * (S.nnz : ℝ)) :=
  ⟨fun w hgood => goodDraw_of_selected p C S hm hm2 hp hb hpower (randomDraw p S hm w) hgood,
    randomDraw_bad_probability p S hm hb⟩

theorem vacuum_decoder_value (S : Source.SparseSystem) (w : (vacuumDecoder S).Messages) :
    (vacuumDecoder S).decode w = 0 := by
  funext i
  simp [vacuumDecoder, Target.WeightedDecoder.decode]

theorem vacuum_recovery (p : Source.Parameters) (S : Source.SparseSystem)
    (hu : IsUnit (Source.realMatrix S)) (hbase : S.source = 0 ∨ S.nnz ≤ 1)
    (_u : OperatorDomain VacuumBox.domain) (w : (vacuumDecoder S).Messages)
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    Source.ResidualTarget S eta ((vacuumDecoder S).decode w) := by
  rw [vacuum_decoder_value]
  exact (VacuumBox.base_instance p S hu hbase eta heta).2.2.2 _u Fin.elim0

theorem vacuum_condition (C : Constants) (S : Source.SparseSystem)
    (hpower : 10 ≤ C.conditionPower) :
    ‖maxwellGraphMap VacuumBox.domain VacuumBox.material‖ *
      ‖maxwellGraphInverse VacuumBox.domain VacuumBox.material VacuumBox.inverse‖ ≤
      (S.effectiveSize : ℝ) ^ C.conditionPower := by
  have hsize : (2 : ℝ) ≤ S.effectiveSize := by
    exact_mod_cast (le_max_left 2 S.nnz)
  calc
    _ ≤ 702 := VacuumBox.inverse_graph_bounds.2
    _ ≤ (2 : ℝ) ^ 10 := by norm_num
    _ ≤ (S.effectiveSize : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hsize 10
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hsize]) hpower

#print axioms goodDraw_of_selected
#print axioms selected_good_event
#print axioms vacuum_recovery
#print axioms vacuum_condition

end Maxwell.Continuum.Realization
