import Maxwell.Continuum.FiniteAuxiliaryPECRecovery
import Maxwell.Continuum.FiniteAuxiliarySourceLower

/-! Field and observable bounds on the genuine full PEC inverse event,
and nonvanishing of an actual finite approximation to the ideal source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants TopologicalSpace SelfAdjointResolvent

attribute [local irreducible] pecCurlCurl realMode Sh Qh muH

theorem graph_field_norm (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {G η : ℝ} (hR : ‖R.map‖ ≤ G)
    (u : OperatorDomain Ω) (f : testL2Closure Ω)
    (hu : ‖maxwellGraphMap Ω ε u-f‖ ≤ η) :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) u‖ ≤ G*(η+‖f‖) := by
  have he := graph_field_difference Ω ε R hR u 0
  simp only [map_zero, sub_zero] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ ((norm_nonneg R.map).trans hR)
  calc
    _ = ‖(maxwellGraphMap Ω ε u-f)+f‖ := by rw [sub_add_cancel]
    _ ≤ ‖maxwellGraphMap Ω ε u-f‖+‖f‖ := norm_add_le _ _
    _ ≤ η+‖f‖ := add_le_add hu le_rfl

theorem finite_observable_error_actual {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (O Oideal : FieldL2 →L[ℂ] H) {δ V e U : ℝ}
    (hO : ‖O-Oideal‖ ≤ δ) (hV : ‖Oideal‖ ≤ V) (u uref : FieldL2)
    (he : ‖u-uref‖ ≤ e) (hu : ‖u‖ ≤ U) :
    ‖O u-Oideal uref‖ ≤ V*e+δ*U := by
  have hi : O u-Oideal uref = Oideal (u-uref)+(O-Oideal) u := by
    simp only [map_sub, sub_apply]
    abel
  rw [hi]
  exact (norm_add_le _ _).trans (add_le_add
    ((Oideal.le_of_opNorm_le hV _).trans
      (mul_le_mul_of_nonneg_left he ((norm_nonneg _).trans hV)))
    (((O-Oideal).le_of_opNorm_le hO _).trans
      (mul_le_mul_of_nonneg_left hu ((norm_nonneg _).trans hO))))

variable {ι : Type*} [Fintype ι]

theorem finite_source_norm_le {L z α δ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (r : ι → Space) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (g : BrightSpace ι) (f : FieldL2)
    (hf : ‖f-idealSource D (inverse_length_le_1024 hL) r α g‖ ≤ δ) :
    ‖f‖ ≤ δ+‖g‖ := by
  have he := norm_add_le (f-idealSource D (inverse_length_le_1024 hL) r α g)
    (idealSource D (inverse_length_le_1024 hL) r α g)
  rw [sub_add_cancel] at he
  exact he.trans (add_le_add hf (idealSource_norm_le_source hL D r hα hα1 hdisj g))

theorem finite_source_ne_zero {L z α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (r : ι → Space) (hα : 0 < α)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (g : BrightSpace ι) (hg : g ≠ 0) (f : FieldL2)
    (hf : ‖f-idealSource D (inverse_length_le_1024 hL) r α g‖ ≤
      (1/(2 : ℝ)^260)*α*L⁻¹^2*‖g‖) : f ≠ 0 := by
  intro he
  have hs := idealSource_norm_lower D (inverse_length_le_1024 hL) r hα.le
    (by simpa only [inv_inv] using hdisj) g
  rw [he, zero_sub, norm_neg] at hf
  have hp : 0 < α*L⁻¹^2*‖g‖ :=
    mul_pos (mul_pos hα (pow_pos D.h_pos 2)) (norm_pos_iff.mpr hg)
  have hc : (1/(2 : ℝ)^260) < 1/(2 : ℝ)^256 := by norm_num
  have hh := mul_lt_mul_of_pos_right hc hp
  nlinarith only [hs, hf, hh]

#print axioms graph_field_norm
#print axioms finite_observable_error_actual
#print axioms finite_source_ne_zero

end Maxwell.Continuum.FiniteAuxiliary
