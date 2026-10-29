import Maxwell.Continuum.AliasOperatorBound
import Maxwell.Continuum.FiniteSupportPairing

/-! The off-alias operator estimate directly from its exact weak kernel
identity, including cutoff factors and Fourier normalization. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

theorem weightedOffAlias_operator_norm_of_pairing {h z : ℝ} (D : Calibration h z)
    (T : ScalarL2 →L[ℂ] ScalarL2)
    (hT : ∀ f g : ScalarL2, inner ℂ g (T f) =
      ∫ p in aliasChart h, star (g p) *
        (∫ p' in aliasChart h, weightedOffAliasKernel h z p p' * f p')) :
    ‖T‖ ≤ (2 : ℝ)^512 * h := by
  have hn := KernelIntegral.finite_support_operator_norm_of_pairing
    (aliasChart_measurable h) (aliasChart_finite h) T (weightedOffAliasKernel h z)
    (by positivity : 0 ≤ (2 : ℝ)^32 * Real.exp (-1 / (512 * Real.sqrt h)))
    (fun p hp p' hp' => weightedOffAliasKernel_bound D p p' hp hp') hT
  exact hn.trans (alias_measure_majorant D.h_pos)

end Maxwell.Continuum.EffectiveMass
