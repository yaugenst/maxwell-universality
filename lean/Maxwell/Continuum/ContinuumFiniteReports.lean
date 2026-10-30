import Maxwell.Continuum.ContinuumGridTests
import Maxwell.Continuum.FixedPointExistence

/-! The finite-report contract is nonvacuous for every eligible PDE field,
and every accurate word vector has the required original residual. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

namespace Maxwell.Continuum.RealizationParameters

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem finite_reports_and_recovery (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖)
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    (∃w : (decoder p S hm).Messages,(decoder p S hm).Accurate w (gridFieldReports p S hm u)) ∧
    ∀w : (decoder p S hm).Messages,(decoder p S hm).Accurate w (gridFieldReports p S hm u) →
      Source.ResidualTarget S eta ((decoder p S hm).decode w) := by
  exact ⟨(decoder p S hm).exists_accurate (gridFieldReports p S hm u)
      (decoder_fits p S hm hm2 hp hb j hgood u hu),
    fun w hw => decoder_recovery p S hm hm2 hp hb j hgood u hu w hw eta heta⟩

#print axioms finite_reports_and_recovery

end Maxwell.Continuum.RealizationParameters
