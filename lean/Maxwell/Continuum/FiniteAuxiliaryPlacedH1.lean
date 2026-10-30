import Maxwell.Continuum.FiniteAuxiliaryOrthogonal
import Maxwell.Continuum.FiniteAuxiliaryH1Algebra
import Maxwell.Continuum.FiniteAuxiliaryH1Wells

/-! The full H¹ norm of a disjoint family of translated sources has no
factor depending on the number of wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory

theorem H1Data.derivative_supported_ball {a : FieldL2} (Da : H1Data a) (R : ℝ)
    (ha : ∀ k, ∀ᵐ x ∂volume, R ≤ ‖x‖ → a k x = 0) (j k : Fin 3) :
    ∀ᵐ x ∂volume, R ≤ ‖x‖ → Da.derivative j k x = 0 := by
  have he := Da.derivative_supported_balls (fun _ : Unit => (0 : Space)) R (by simpa using ha) j k
  simpa using he

end Maxwell.Continuum.FourierSobolev

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory Bloch FourierSobolev

variable {ι : Type*} [Fintype ι]

def placedH1 (r : ι → Space) {a : FieldL2} (Da : H1Data a) (g : BrightSpace ι) :
    H1Data (placedField r a g) :=
  h1Sum (fun i => g i • fieldTranslation (-r i) a) (fun i => (Da.translate (-r i)).smul (g i))

theorem placedH1_derivative (r : ι → Space) {a : FieldL2} (Da : H1Data a)
    (g : BrightSpace ι) (j : Fin 3) :
    (placedH1 r Da g).derivative j = placedField r (Da.derivative j) g := rfl

theorem placedH1_norm (r : ι → Space) (R : ℝ) {a : FieldL2} (Da : H1Data a)
    (ha : ∀ k, ∀ᵐ x ∂volume, R ≤ ‖x‖ → a k x = 0)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) R) (Metric.ball (r j) R))
    (g : BrightSpace ι) : (placedH1 r Da g).norm = Da.norm*‖g‖ := by
  have hd (j : Fin 3) : ‖(placedH1 r Da g).derivative j‖ = ‖Da.derivative j‖*‖g‖ := by
    rw [placedH1_derivative]
    exact placedField_norm r R (Da.derivative j) (Da.derivative_supported_ball R ha j) hdisj g
  unfold H1Data.norm
  rw [placedField_norm r R a ha hdisj g]
  simp only [hd, mul_pow, ← Finset.sum_mul, ← add_mul]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem H1Data_smul_norm {a : FieldL2} (Da : H1Data a) (c : ℂ) :
    (Da.smul c).norm = ‖c‖*Da.norm := by
  unfold H1Data.norm
  change Real.sqrt (‖c • a‖^2+∑ j, ‖c • Da.derivative j‖^2) = _
  simp only [norm_smul, mul_pow, ← Finset.mul_sum, ← mul_add]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

#print axioms placedH1_norm

end Maxwell.Continuum.FiniteAuxiliary
