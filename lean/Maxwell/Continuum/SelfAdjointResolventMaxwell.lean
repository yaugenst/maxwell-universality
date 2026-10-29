import Maxwell.Continuum.SelfAdjointResolventGraph
import Maxwell.Continuum.MaterialShift

/-!
# Spectral separation gives the actual Maxwell inverse and conditioning

The operator, material and graph are the literal continuum objects. A real
spectral gap supplies the inverse; it is not an input to these theorems.
-/

noncomputable section

namespace Maxwell.Continuum

open TopologicalSpace SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

/-- A genuine Maxwell inverse, regarded as a map into the curl-curl graph. -/
def maxwellGraphInverse (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) :
    testL2Closure Ω →L[ℂ] OperatorDomain Ω :=
  R.perturbedGraphInverse (pecCurlCurl Ω) (ε.domainMultiplier Ω)

@[simp] theorem maxwellGraphMap_inverse (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) (f : testL2Closure Ω) :
    maxwellGraphMap Ω ε (maxwellGraphInverse Ω ε R f) = f :=
  R.perturbed_apply_inverse (pecCurlCurl Ω) (ε.domainMultiplier Ω) f

@[simp] theorem maxwellGraphInverse_map (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) (u : OperatorDomain Ω) :
    maxwellGraphInverse Ω ε R (maxwellGraphMap Ω ε u) = u :=
  R.perturbed_inverse_apply (pecCurlCurl Ω) (ε.domainMultiplier Ω) u

@[simp] theorem inclusion_maxwellGraphInverse (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) (f : testL2Closure Ω) :
    GraphNorm.inclusion (pecCurlCurl Ω) (maxwellGraphInverse Ω ε R f) = R.map f := rfl

/-- The constants 27 and 702 for a constructed actual L² inverse. -/
theorem maxwell_inverse_graph_bounds (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {L : ℝ}
    (hL : 1 ≤ L) (hR : ‖R.map‖ ≤ L) :
    ‖maxwellGraphInverse Ω ε R‖ ≤ 27 * L ∧
      ‖maxwellGraphMap Ω ε‖ * ‖maxwellGraphInverse Ω ε R‖ ≤ 702 * L :=
  ⟨R.perturbedGraphInverse_opNorm_le (pecCurlCurl Ω) (ε.domainMultiplier Ω)
      (ε.domainMultiplier_norm_le Ω) hL hR,
    R.perturbed_condition_bound (pecCurlCurl Ω) (ε.domainMultiplier Ω)
      (ε.domainMultiplier_norm_le Ω) hL hR⟩

/-- A source residual controls the actual L² field error. -/
theorem maxwell_inverse_residual (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {L : ℝ} (hR : ‖R.map‖ ≤ L)
    (u : OperatorDomain Ω) (f : testL2Closure Ω) :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) u - R.map f‖ ≤
      L * ‖maxwellGraphMap Ω ε u - f‖ :=
  R.perturbed_residual_bound (pecCurlCurl Ω) (ε.domainMultiplier Ω) hR u f

/-- The same residual also controls the full curl-curl graph norm. -/
theorem maxwell_inverse_graph_residual (Ω : Opens Space) (ε : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator Ω ε)) {L : ℝ}
    (hL : 1 ≤ L) (hR : ‖R.map‖ ≤ L) (u : OperatorDomain Ω) (f : testL2Closure Ω) :
    ‖u - maxwellGraphInverse Ω ε R f‖ ≤ 27 * L * ‖maxwellGraphMap Ω ε u - f‖ := by
  have hnorm := (maxwell_inverse_graph_bounds Ω ε R hL hR).1
  calc
    ‖u - maxwellGraphInverse Ω ε R f‖ =
        ‖maxwellGraphInverse Ω ε R (maxwellGraphMap Ω ε u - f)‖ := by
      have he := (maxwellGraphInverse Ω ε R).map_sub (maxwellGraphMap Ω ε u) f
      have hi := congrArg (fun v : OperatorDomain Ω => v - maxwellGraphInverse Ω ε R f)
        (maxwellGraphInverse_map Ω ε R u)
      exact congrArg norm (he.trans hi).symm
    _ ≤ ‖maxwellGraphInverse Ω ε R‖ * ‖maxwellGraphMap Ω ε u - f‖ :=
      (maxwellGraphInverse Ω ε R).le_opNorm _
    _ ≤ 27 * L * ‖maxwellGraphMap Ω ε u - f‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- An actual spectral gap yields a genuine inverse for the literally shifted
dielectric, together with the paper's L² and graph-norm constants. -/
theorem maxwell_spectral_gap_resolvent (Ω : Opens Space) (ε : ScalarDielectric)
    (σ : ℝ) (hσ : 0 ≤ σ) (hupper : ∀ x, ε.coefficient x + σ ≤ 25)
    {δ : ℝ} (hδ : 0 < δ) (hδupper : δ ≤ 1)
    (hgap : ∀ lam ∈ realSpectrum (maxwellOperator Ω ε), δ ≤ |σ - lam|) :
    ∃ R : BoundedInverse (maxwellOperator Ω (ε.shifted σ hσ hupper)),
      ‖R.map‖ ≤ δ⁻¹ ∧
        ‖maxwellGraphInverse Ω (ε.shifted σ hσ hupper) R‖ ≤ 27 * δ⁻¹ ∧
          ‖maxwellGraphMap Ω (ε.shifted σ hσ hupper)‖ *
            ‖maxwellGraphInverse Ω (ε.shifted σ hσ hupper) R‖ ≤ 702 * δ⁻¹ := by
  have hex := exists_boundedInverse_of_gap (maxwellOperator Ω ε)
    (maxwellOperator_selfAdjoint Ω ε) σ hδ hgap
  rw [← maxwellOperator_shifted Ω ε σ hσ hupper] at hex
  obtain ⟨R, hR⟩ := hex
  have hL : 1 ≤ δ⁻¹ := by
    apply (le_inv_comm₀ (by norm_num : (0 : ℝ) < 1) hδ).mpr
    simpa only [inv_one] using hδupper
  exact ⟨R, hR, maxwell_inverse_graph_bounds Ω (ε.shifted σ hσ hupper) R hL hR⟩

end Maxwell.Continuum
