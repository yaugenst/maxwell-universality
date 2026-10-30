import Maxwell.Continuum.ContinuumDecoder

/-! All emitted grid tests are real with norm at most two. Every eligible
solver field has observations strictly inside the actual fixed word range. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision messageRangeBits pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem gridTemplate_real (q : Fin (gridCount p S hm)) :
    fieldConjugation (gridTemplate p S hm q)=gridTemplate p S hm q := by
  unfold gridTemplate
  split
  next h => exact selectedTemplates_real p S hm h.choose
  next => exact map_zero _

theorem gridTemplate_norm (q : Fin (gridCount p S hm)) : ‖gridTemplate p S hm q‖≤2 := by
  unfold gridTemplate
  split
  next h => exact selectedTemplates_norm p S hm h.choose
  next => simp

theorem grid_field_range (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖) (q : Fin (gridCount p S hm)) :
    |gridFieldReports p S hm u q|≤6*(inverseBound p S hm : ℝ)*S.nnz := by
  obtain ⟨R,hR,_,_⟩ := computed_good_draw_inverse p S hm hm2 hp.1 hb j hgood
  have hE := approximate_field_norm _ _ R hR (residual_half p S hm) u
    (computedSource p S hm) (computedSource_norm p S hm hm2 hp.1 hb) hu
  exact routed_raw_moment_bound S (precision p S hm) hp.1 hb hm _ _
    (inverseBound_pos p S hm).le hE (gridTemplate_norm p S hm q)

theorem decoder_fits (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm))
    (hgood : j.val∉computedBadDraws p S hm hb)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (computedDielectric p S hm hb j) u-computedSource p S hm‖≤
      (residual p S hm : ℝ)*‖computedSource p S hm‖) :
    (decoder p S hm).Fits (gridFieldReports p S hm u) := by
  intro q
  have hv := grid_field_range p S hm hm2 hp hb j hgood u hu q
  have hR : 8*(inverseBound p S hm : ℝ)*S.nnz≤
      (2 : ℝ)^messageRangeBits (inverseBound p S hm) S.nnz := by
    exact_mod_cast messageRangeBits_spec (inverseBound p S hm) S.nnz
  have hG := inverseBound_pos p S hm
  have hmR : (0 : ℝ)<S.nnz := by exact_mod_cast hm
  have hstrict : 6*(inverseBound p S hm : ℝ)*S.nnz<8*(inverseBound p S hm : ℝ)*S.nnz := by
    nlinarith only [mul_pos hG hmR]
  have hpow : (2 : ℝ)^messageRangeBits (inverseBound p S hm) S.nnz≤
      (2 : ℝ)^(messageRangeBits (inverseBound p S hm) S.nnz+2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h := abs_lt.mp ((hv.trans_lt hstrict).trans_le (hR.trans hpow))
  exact ⟨h.1.le,h.2⟩

#print axioms gridTemplate_real
#print axioms grid_field_range
#print axioms decoder_fits

end Maxwell.Continuum.RealizationParameters
