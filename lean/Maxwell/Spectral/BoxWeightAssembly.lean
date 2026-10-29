import Maxwell.Spectral.BoxProjectionAssembly
import Maxwell.Spectral.BoxMagnetic

namespace Maxwell.Spectral.BoxWeightAssembly

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxFourierProjection BoxSymbols BoxProjectionAssembly

noncomputable section

def inverseWeight (support : Finset Frequency) (c : Momentum) (ρ t : ℝ) : Frequency → ℝ :=
  fun f => if f ∈ support then 1/Real.sqrt (laplacianSymbol c f/ρ-t) else 0

theorem inverseWeight_nonneg (support : Finset Frequency) (c : Momentum) (ρ t : ℝ)
    (f : Frequency) : 0 ≤ inverseWeight support c ρ t f := by
  unfold inverseWeight
  split_ifs <;> positivity

theorem inverseWeight_norm (support : Finset Frequency) (c : Momentum) (ρ t r : ℝ)
    (hρ : 0 < ρ) (hr : 0 < r) (hbase : 0 < r^2/ρ-t)
    (hf : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖) :
    ‖scalarWeight (inverseWeight support c ρ t)‖ ≤ 1/Real.sqrt (r^2/ρ-t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  apply scalarWeight_norm_bound _ _ (by positivity)
  intro f
  rw [abs_of_nonneg (inverseWeight_nonneg support c ρ t f)]
  by_cases hmem : f ∈ support
  · simp only [inverseWeight, ite_eq_left hmem]
    rw [← longitudinalVector_norm_sq]
    exact BoxWeights.center_inverse_sqrt_weight ρ t r _ hρ hr (hf f hmem) hbase
  · simp only [inverseWeight, ite_eq_right hmem]
    positivity

theorem curl_component_norm (c : Momentum) (f : Frequency) (x : FourierSpace) :
    ‖frequencyComponent f (BoxMagnetic.curlOperator c x)‖ ≤
      ‖longitudinalVector c f‖*‖frequencyComponent f x‖ := by
  rw [show frequencyComponent f (BoxMagnetic.curlOperator c x) =
    (curlSymbolMatrix c f).toEuclideanLin (frequencyComponent f x) from frequencyCurl_component c f x]
  have hnorm : ‖(WithLp.toLp 2 (symbol c f) : Polarization)‖ = ‖longitudinalVector c f‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, longitudinalVector, Complex.norm_conj]
  have hb := BoxCrossNorm.crossMatrix_apply_norm (symbol c f) (frequencyComponent f x)
  rw [hnorm] at hb
  exact hb

/-- The scalar high weight times the actual center curl has norm
`rh/sqrt(rh²/ρ-t)`, preserving the source verifier's sharp remainder. -/
theorem inverseWeight_curl_norm (support : Finset Frequency) (c : Momentum) (ρ t r : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hr : 0 < r) (hbase : 0 < r^2/ρ-t)
    (hf : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖) :
    ‖(scalarWeight (inverseWeight support c ρ t)).comp (BoxMagnetic.curlOperator c)‖ ≤
      r/Real.sqrt (r^2/ρ-t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply norm_le_of_component_bounds _ x _ (by positivity)
  intro f
  change ‖frequencyComponent f (scalarWeight (inverseWeight support c ρ t)
    (BoxMagnetic.curlOperator c x))‖ ≤ _
  rw [scalarWeight_component, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inverseWeight_nonneg support c ρ t f)]
  by_cases hmem : f ∈ support
  · simp only [inverseWeight, ite_eq_left hmem]
    have h := mul_le_mul_of_nonneg_left (curl_component_norm c f x)
      (by positivity : 0 ≤ 1/Real.sqrt (laplacianSymbol c f/ρ-t))
    apply h.trans
    have hc := BoxWeights.curl_weight_sqrt ρ t r _ hρ ht hr (hf f hmem) hbase
    rw [longitudinalVector_norm_sq] at hc
    have hmul := mul_le_mul_of_nonneg_right hc (norm_nonneg (frequencyComponent f x))
    convert hmul using 1; ring
  · simp only [inverseWeight, ite_eq_right hmem, zero_mul]
    positivity

/-- This converts the moving transverse inverse weight to the fixed
center weight used by every stored residual and derivative Gram bound. -/
theorem inverseWeight_shift_comparison
    (support : Finset Frequency) (c q : Momentum) (ρ t σ s r t' : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hq : phaseScale*momentumNorm q ≤ s) (hsr : s < r)
    (hf : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (ht' : t' ≤ t+σ) (hshift : 0 < (r-s)^2/ρ-t-σ) (x : FourierSpace) :
    ‖scalarWeight (inverseWeight support (c+q) ρ t') x‖ ≤
      Real.sqrt ((r^2/ρ-t)/((r-s)^2/ρ-t-σ))*
        ‖scalarWeight (inverseWeight support c ρ t) x‖ := by
  apply scalarWeight_comparison _ _ _ (Real.sqrt_nonneg _)
  intro f
  rw [abs_of_nonneg (inverseWeight_nonneg support (c+q) ρ t' f),
    abs_of_nonneg (inverseWeight_nonneg support c ρ t f)]
  by_cases hmem : f ∈ support
  · simp only [inverseWeight, ite_eq_left hmem]
    have hnorm := BoxProjection.norm_add_lower (longitudinalVector c f)
      (longitudinalVector (c+q) f-longitudinalVector c f) s
      ((longitudinal_increment_bound c q f).trans hq)
    simp only [add_sub_cancel] at hnorm
    have h := BoxWeights.shifted_inverse_sqrt_weight ρ t σ s r
      ‖longitudinalVector c f‖ ‖longitudinalVector (c+q) f‖ t'
      hρ ht hσ hs hsr (hf f hmem) hnorm ht' hshift
    rw [longitudinalVector_norm_sq, longitudinalVector_norm_sq] at h
    simpa only [div_eq_mul_inv, one_mul] using h
  · simp [inverseWeight, hmem]

end
end Maxwell.Spectral.BoxWeightAssembly
