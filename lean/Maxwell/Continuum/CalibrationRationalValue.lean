import Maxwell.Continuum.CalibrationRationalStencil

/-! Exact vector semantics for rational pairs and elementary linear
operations, shared by the finite central matrix and complex modes. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

theorem represents_zero : Represents (0 : RationalAliasField) 0 := by
  intro ν j
  exact map_zero rationalComplexLinear

theorem represents_sub {f g : RationalAliasField} {u v : FiberSpace}
    (hf : Represents f u) (hg : Represents g v) : Represents (f-g) (u-v) := by
  intro ν j
  change rationalComplexLinear (f ν j-g ν j) = _
  rw [map_sub]
  change rationalComplexValue (f ν j)-rationalComplexValue (g ν j) = _
  rw [hf, hg]
  rfl

theorem represents_smul (c : ℚ) {f : RationalAliasField} {u : FiberSpace}
    (hf : Represents f u) : Represents (c • f) ((c : ℂ) • u) := by
  intro ν j
  change rationalComplexLinear (c • f ν j) = _
  rw [map_smul, ← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul]
  change (c : ℂ)*rationalComplexValue (f ν j) = _
  rw [hf]
  rfl

theorem rationalAmplitude_complex : (rationalAmplitude : ℂ) = (backgroundAmplitude : ℂ) := by
  rw [← Complex.ofReal_ratCast, rationalAmplitude_cast]

end Maxwell.Continuum.Calibration
