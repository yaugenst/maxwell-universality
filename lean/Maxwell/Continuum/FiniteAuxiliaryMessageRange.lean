import Maxwell.Continuum.FiniteAuxiliaryFieldRange
import Maxwell.Continuum.FiniteAuxiliaryMessages
import Maxwell.Continuum.FiniteAuxiliaryMessageFormat
import Maxwell.Continuum.ParameterSpacingSearch

/-! The full PEC inverse controls all raw volume moments, including
moments of approximate solver fields. A rationally selected range then
fits every allowed report in the fixed signed-word message format. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open SelfAdjointResolvent TopologicalSpace Maxwell.Composition

attribute [local irreducible] pecCurlCurl

theorem approximate_field_norm (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {G g e₀ : ℝ}
    (hR : ‖R.map‖ ≤ G) (he : e₀ ≤ 1/2)
    (u : OperatorDomain Ω) (f : testL2Closure Ω)
    (hf : ‖f‖ ≤ 2*g)
    (hu : ‖maxwellGraphMap Ω ε u-f‖ ≤ e₀*‖f‖) :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) u‖ ≤ 3*G*g := by
  have hG : 0 ≤ G := (norm_nonneg R.map).trans hR
  have he' := mul_le_mul_of_nonneg_right he (norm_nonneg f)
  have hb : e₀*‖f‖+‖f‖ ≤ 3*g := by linarith only [he', hf]
  exact (graph_field_norm Ω ε R hR u f hu).trans
    ((mul_le_mul_of_nonneg_left hb hG).trans_eq (by ring))

theorem raw_moment_bound (E a : FieldL2) {G g : ℝ}
    (hE : ‖E‖ ≤ 3*G*g) (ha : ‖a‖ ≤ 2) :
    |(inner ℂ a E).re| ≤ 6*G*g := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm a E).trans
  exact (mul_le_mul ha hE (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem rational_report_range {x G m δ : ℝ} (hG : 1 ≤ G) (hm : 1 ≤ m)
    (hx : |x| ≤ 6*G*m) (hδ : δ ≤ 1) (w : ℚ)
    (hw : |(w : ℝ)-x| ≤ δ) : |(w : ℝ)| < 8*G*m := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hp : 1 ≤ G*m := by nlinarith only [mul_le_mul hG hm zero_le_one hG0]
  have ht := abs_add_le ((w : ℝ)-x) x
  rw [sub_add_cancel] at ht
  linarith only [ht, hw, hx, hδ, hp]

theorem routed_raw_moment_bound (S : Source.SparseSystem) (precision : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) (hb : S.source ≠ 0) (hm : 0 < S.nnz)
    (E a : FieldL2) {G : ℝ} (hG : 0 ≤ G)
    (hE : ‖E‖ ≤ 3*G*‖routedForcing S precision‖) (ha : ‖a‖ ≤ 2) :
    |(inner ℂ a E).re| ≤ 6*G*(S.nnz : ℝ) := by
  apply (raw_moment_bound E a hE ha).trans
  have hg := PhysicalAccuracy.source_norm_le_nnz S precision hunit hb hm
  rw [← routedForcing_norm] at hg
  exact mul_le_mul_of_nonneg_left hg (by positivity)

end Maxwell.Continuum.FiniteAuxiliary
end

namespace Maxwell.Continuum.FiniteAuxiliary

def messageRangeBits (G : ℚ) (m : ℕ) : ℕ :=
  Parameters.rationalUpperBits (8*G*m)

theorem messageRangeBits_spec (G : ℚ) (m : ℕ) :
    8*G*m ≤ (2 : ℚ)^messageRangeBits G m :=
  Parameters.rationalUpperBits_spec _

theorem weighted_report_fits (G : ℚ) (m : ℕ) (v w : ℚ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 8*G*m) :
    |v*w| ≤ (2 : ℚ)^messageRangeBits G m := by
  rw [abs_mul]
  exact ((mul_le_mul_of_nonneg_right hv (abs_nonneg w)).trans
    (by simpa only [one_mul] using hw)).trans (messageRangeBits_spec G m)

def encodedMomentReport (G : ℚ) (m P : ℕ) (v w : ℚ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 8*G*m) :
    Fin (2^(messageRangeBits G m+P+3)) :=
  roundedMomentWord P (messageRangeBits G m) (v*w) (weighted_report_fits G m v w hv hw)

theorem encodedMomentReport_value (G : ℚ) (m P : ℕ) (v w : ℚ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 8*G*m) :
    momentWordDyadic P (messageRangeBits G m+P+2) (encodedMomentReport G m P v w hv hw) =
      roundDyadic P (v*w) := roundedMomentWord_value _ _ _ _

theorem encodedMomentReport_bits (G : ℚ) (m P : ℕ) (v w : ℚ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 8*G*m) :
    Maxwell.unsignedBitLength (encodedMomentReport G m P v w hv hw).val ≤
      messageRangeBits G m+P+3 :=
  momentWord_bits _ _

#print axioms approximate_field_norm
#print axioms routed_raw_moment_bound
#print axioms encodedMomentReport_value
#print axioms encodedMomentReport_bits

end Maxwell.Continuum.FiniteAuxiliary
