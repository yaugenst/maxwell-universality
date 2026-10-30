import Maxwell.Continuum.PeriodicCenteredFourier
import Maxwell.Continuum.OperatorFourierIntegral
import Maxwell.Continuum.BlochPartition

/-! Exact scaling between a three-dimensional unit-torus coefficient
and the physical angular Fourier integral. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicSampling

open MeasureTheory Bloch OperatorFourier
open scoped InnerProduct

theorem phase_dilated (s : ℝ) (hs : s ≠ 0) (n : Bloch.Alias) (x : Space) :
    Product.phase (-n) x.ofLp = angularPhase (s • x) ((2*Real.pi/s) • integerVector n) := by
  unfold Product.phase PeriodicSampling.phase angularPhase
  rw [← Complex.exp_sum]
  congr 1
  simp only [inner_smul_left, inner_smul_right, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, integerVector_apply, Pi.neg_apply, Int.cast_neg, Fin.sum_univ_three]
  push_cast
  field_simp [hs]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem euclidean_scaled_coefficient (f : Space → E) (s : ℝ) (hs : 0 < s) (n : Bloch.Alias) :
    (∫ x : Fin 3 → ℝ, Product.phase (-n) x • f (s • WithLp.toLp 2 x)) =
      (s^3)⁻¹ • angularFourier f ((2*Real.pi/s) • integerVector n) := by
  let F : Space → E := fun q => angularPhase q ((2*Real.pi/s) • integerVector n) • f q
  have he : (∫ x : Fin 3 → ℝ, Product.phase (-n) x • f (s • WithLp.toLp 2 x)) =
      ∫ x : Space, F (s • x) := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change Product.phase (-n) x • f (s • WithLp.toLp 2 x) = _
      rw [phase_dilated s hs.ne' n (WithLp.toLp 2 x)]
  rw [he, Measure.integral_comp_smul_of_nonneg volume F s (hR := hs.le)]
  rw [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin]
  rw [angularFourier_integral]

#print axioms euclidean_scaled_coefficient

end Maxwell.Continuum.PeriodicSampling
