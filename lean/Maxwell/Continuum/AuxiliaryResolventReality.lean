import Maxwell.Continuum.AuxiliaryCutoffReality
import Maxwell.Continuum.AuxiliaryResolventGraph

/-! The actual whole-space cutoff resolvent preserves real physical L²
fields. This follows from literal Plancherel/Bloch conjugation and the
full infinite-fiber inverse, including its exact alias reversal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum

open MeasureTheory

theorem fieldConjugation_eq_iff (f : FieldL2) :
    fieldConjugation f = f ↔ ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      star (f i x) = f i x := by
  constructor
  · intro h i
    have hi := congrArg (fun g : FieldL2 => g i) h
    have ha := scalarConjugation_ae (f i)
    change scalarConjugation (f i) = f i at hi
    rw [hi] at ha
    exact ha.symm
  · intro h
    apply PiLp.ext
    intro i
    apply Lp.ext
    exact (scalarConjugation_ae (f i)).trans (h i)

namespace Auxiliary

open FreeFiber PeriodicBand Bloch CellBandFourier FiberNormalization

attribute [local irreducible] resolvent cutoffFiber fiberResolvent fiberInverse
  FiberAnalytic.fullResolventExtension scaledBand PeriodicPerturbation.perturbation
  PeriodicPerturbation.finiteK CornerBridge.topState RankOneBand.Data.bandRoot

/-- Physical conjugation commutes with the literal whole-space Rσ. -/
theorem resolvent_conjugation {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2) :
    resolvent D hσ0 hσ (fieldConjugation f) =
      fieldConjugation (resolvent D hσ0 hσ f) := by
  apply unitary.injective
  apply Lp.ext
  filter_upwards [resolvent_ae D hσ0 hσ (fieldConjugation f),
    product_ae_all_alias (unitary_conjugation_pair_ae (resolvent D hσ0 hσ f)),
    product_ae_all_alias (negativeFrequency_fst_ae (resolvent_ae D hσ0 hσ f)),
    unitary_conjugation_interior_ae f] with q hR hcR hn hc
  rw [hR]
  by_cases hq : q ∈ cutoffRegion
  · let hi := cutoffRegion_interior q hq
    rw [hc hi, cutoffFiber_reverse_star D hσ0 hσ q hq]
    apply lp.ext
    funext n
    apply PiLp.ext
    intro j
    have hx := hcR n j
    have hy := hn n
    rw [negativeFrequency_interior q hi n] at hx hy
    rw [hy] at hx
    simpa only [reversal_apply, fiber_star_apply, polarization_star_apply] using hx.symm
  · rw [cutoffFiber_zero hq, zero_apply]
    apply lp.ext
    funext n
    apply PiLp.ext
    intro j
    have hx := hcR n j
    have hy := hn n
    have hnot : (negativeFrequency (q,n)).1 ∉ cutoffRegion :=
      mt (negativeFrequency_mem_cutoffRegion (q,n)).mp hq
    rw [cutoffFiber_zero hnot, zero_apply] at hy
    rw [hy] at hx
    simpa only [lp.coeFn_zero, Pi.zero_apply, PiLp.zero_apply, star_zero] using hx.symm

theorem resolvent_preserves_real {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2)
    (hf : fieldConjugation f = f) :
    fieldConjugation (resolvent D hσ0 hσ f) = resolvent D hσ0 hσ f := by
  rw [← resolvent_conjugation, hf]

theorem resolvent_preserves_pointwise_real {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2)
    (hf : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space), star (f i x) = f i x) :
    ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      star (resolvent D hσ0 hσ f i x) = resolvent D hσ0 hσ f i x :=
  (fieldConjugation_eq_iff _).mp
    (resolvent_preserves_real D hσ0 hσ f ((fieldConjugation_eq_iff f).mpr hf))

#print axioms resolvent_conjugation
#print axioms resolvent_preserves_pointwise_real
#print axioms Bloch.unitary_conjugation_pair_ae
#print axioms fourier_scalarConjugation

end Auxiliary
end Maxwell.Continuum
