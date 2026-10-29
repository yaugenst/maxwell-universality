import Maxwell.Continuum.CellBandFourierReferenceFormula
import Maxwell.Continuum.CellBandFourierReferenceL1
import Maxwell.Continuum.BoxModes

/-! The actual reference-field assertions in physical space, with the
paper's full absolute Fourier error and exact calibration normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization PeriodicBand CornerBridge

attribute [local irreducible] normalizedFiberVector topState scaledBand fiberVector
  cellEigenfunction referenceField

theorem antiperiodicField_sub (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) (x : Space) :
    antiperiodicField (u-v) x = antiperiodicField u x - antiperiodicField v x := by
  have huv : Summable (fun ν => ‖(u-v) ν‖) := by
    exact Summable.of_nonneg_of_le (fun ν => norm_nonneg _) (fun ν => norm_sub_le (u ν) (v ν)) (hu.add hv)
  apply (antiperiodicField_hasSum _ huv x).unique
  simpa only [lp.coeFn_sub, Pi.sub_apply, smul_sub] using
    (antiperiodicField_hasSum u hu x).sub (antiperiodicField_hasSum v hv x)

theorem referenceField_real (x : Space) : star (referenceField x) = referenceField x := by
  have ht : star (trigField Corner.normalizedTopVector x) = trigField Corner.normalizedTopVector x := by
    apply PiLp.ext
    intro j
    change star (trigField Corner.normalizedTopVector x j) = trigField Corner.normalizedTopVector x j
    fin_cases j <;> dsimp only [trigField] <;>
      exact Complex.conj_ofReal _
  rw [referenceField, star_smul, ht]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem referenceField_mean_square :
    (1/8 : ℝ) * (∫ x in physicalCell, ‖referenceField x‖ ^ 2) = 1 := by
  simp only [referenceField_eq_fourier, norm_smul, Complex.norm_I, one_mul]
  rw [physical_mean_square _ topState_summable_norm, show ‖topState.val‖ = 1 from topState_norm,
    one_pow]

theorem cellEigenfunction_zero_fourier_reference :
    Summable (fun ν => ‖Complex.I • normalizedFiberVector 0 ν - Complex.I • topState.val ν‖) ∧
      ∑' ν, ‖Complex.I • normalizedFiberVector 0 ν - Complex.I • topState.val ν‖ ≤
        2^16 * backgroundAmplitude := by
  simpa only [← smul_sub, norm_smul, Complex.norm_I, one_mul] using
    normalizedFiberVector_zero_fourier_reference

theorem cellEigenfunction_zero_pointwise_reference (x : Space) :
    ‖cellEigenfunction 0 x - referenceField x‖ ≤ 2^16 * backgroundAmplitude := by
  have hu := (normalizedFiberVector_fourier_l1 chart_zero).1
  have hdiff := normalizedFiberVector_zero_fourier_reference
  have heq : cellEigenfunction 0 x - referenceField x =
      Complex.I • antiperiodicField (normalizedFiberVector 0 - topState.val) x := by
    rw [cellEigenfunction, referenceField_eq_fourier, ← smul_sub,
      antiperiodicField_sub (normalizedFiberVector 0) topState.val hu topState_summable_norm]
  rw [heq, norm_smul, Complex.norm_I, one_mul]
  have hs : Summable (fun ν => ‖(normalizedFiberVector 0 - topState.val) ν‖) := hdiff.1
  exact (antiperiodicField_norm_le (normalizedFiberVector 0 - topState.val) hs x).trans hdiff.2

theorem partial_neg (f : Space → ℝ) (j : Fin 3) (x : Space) :
    BoxModes.partialDeriv (fun y => -f y) j x = -BoxModes.partialDeriv f j x := by
  change (fderiv ℝ (-f) x) (BoxModes.direction j) = _
  rw [fderiv_neg]
  rfl

theorem trigField_divergence (v : Corner.Vec) (hv : ∑ j, v j = 0) (x : Space) :
    ∑ j : Fin 3, BoxModes.partialDeriv (fun y => (trigField v y j).re) j x = 0 := by
  simp only [Fin.sum_univ_three] at hv ⊢
  change BoxModes.partialDeriv (fun y => v 0 * Real.sin (halfAngle y 0) *
      Real.sin (halfAngle y 1) * Real.sin (halfAngle y 2)) 0 x +
    BoxModes.partialDeriv (fun y => -v 1 * Real.cos (halfAngle y 0) *
      Real.cos (halfAngle y 1) * Real.sin (halfAngle y 2)) 1 x +
    BoxModes.partialDeriv (fun y => -v 2 * Real.cos (halfAngle y 0) *
      Real.sin (halfAngle y 1) * Real.cos (halfAngle y 2)) 2 x = 0
  simp (disch := fun_prop) [halfAngle, div_eq_mul_inv,
    BoxModes.partial_mul, BoxModes.partial_sin, BoxModes.partial_cos, partial_neg]
  linear_combination (Real.pi / 2 * Real.cos (Real.pi * x 0 * 2⁻¹) *
    Real.sin (Real.pi * x 1 * 2⁻¹) * Real.sin (Real.pi * x 2 * 2⁻¹)) * hv

#print axioms cellEigenfunction_zero_fourier_reference
#print axioms cellEigenfunction_zero_pointwise_reference
#print axioms referenceField_mean_square
#print axioms trigField_divergence

end Maxwell.Continuum.CellBandFourier
