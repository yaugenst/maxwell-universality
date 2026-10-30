import Maxwell.Continuum.CalibrationRationalNaturality

/-! Real rational columns are a specialization of the same executable
complex-vector arithmetic, with exact scalar-cast semantics. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalRealEmbedding : ℚ →ₗ[ℚ] RationalComplex := LinearMap.inl ℚ ℚ ℚ

theorem rationalRealEmbedding_value (q : ℚ) :
    rationalComplexValue (rationalRealEmbedding q) = (q : ℂ) := by
  simp only [rationalComplexValue_eq, rationalRealEmbedding, LinearMap.inl_apply,
    Rat.cast_zero, zero_mul, add_zero]

def RealRepresents (f : Alias → Fin 3 → ℚ) (u : FiberSpace) : Prop :=
  ∀ ν j, (f ν j : ℂ) = u ν j

theorem represents_realEmbedding {f : Alias → Fin 3 → ℚ} {u : FiberSpace}
    (hf : RealRepresents f u) : Represents (rationalMap rationalRealEmbedding f) u := by
  intro ν j
  rw [rationalMap, rationalRealEmbedding_value]
  exact hf ν j

theorem realRepresents_schurApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : Alias → Fin 3 → ℚ} {u : FiberSpace} (hf : RealRepresents f u) (K : ℕ) :
    RealRepresents (rationalSchurApply t E r K f)
      (scaledSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K u) := by
  have h := represents_schurApply t E r hr ht hE (represents_realEmbedding hf) K
  rw [rationalSchurApply_map] at h
  intro ν j
  have hv := h ν j
  simpa only [rationalMap, rationalRealEmbedding_value] using hv

end Maxwell.Continuum.Calibration
