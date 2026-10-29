import Maxwell.Spectral.BoxMagnetic
import Maxwell.Spectral.BoxHighCoercivity

/-! Actual signed low-space quadratic bounds for the auxiliary box
operator, with the verifier's separate magnetic, projector and spectral
parameter losses. -/

noncomputable section

namespace Maxwell.Spectral.BoxLowForms

set_option maxRecDepth 4000

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open BoxMagnetic BoxHighCoercivity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem quadratic_abs_le_of_norm (T : V →L[ℂ] V) (b : ℝ) (hT : ‖T‖ ≤ b) (x : V) :
    |(inner ℂ x (T x)).re| ≤ b * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖inner ℂ x (T x)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ ≤ ‖x‖ * (b * ‖x‖) := by gcongr
    _ = _ := by ring

omit [CompleteSpace V] in
theorem norm_image_sq (F : V →L[ℂ] Field) (ν : ℝ) (hF : ‖F‖ ≤ ν) (x : V) :
    ‖F x‖ ^ 2 ≤ ν ^ 2 * ‖x‖ ^ 2 := by
  have h := (F.le_opNorm x).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

theorem diagonal_variation_norm
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ edge, 1 ≤ edgeAverage material edge) (c q : Momentum) (t : ℝ)
    (F : V →L[ℂ] Field) (s ν e dot : ℝ) (hs : displacementSize q ≤ s)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hfirst : ‖firstCompression material c q F F‖ ≤ dot) :
    ‖compression material (c + q) t F F - compression material c t F F‖ ≤
      dot + s ^ 2 * (ν * e + ν ^ 2) := by
  have hν := (norm_nonneg F).trans hF
  have he := (norm_nonneg (appliedCurl c F)).trans hcenter
  have hrem := BoxMagnetic.diagonal_remainder_bound material hm c q t F ν e hν he hF hcenter
  have hrem' : ‖compression material (c + q) t F F - compression material c t F F -
      firstCompression material c q F F‖ ≤ s ^ 2 * (ν * e + ν ^ 2) :=
    hrem.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (displacementSize_nonneg q) hs 2) (by positivity))
  have hid : compression material (c + q) t F F - compression material c t F F =
      (compression material (c + q) t F F - compression material c t F F -
        firstCompression material c q F F) + firstCompression material c q F F := by module
  calc
    _ = ‖(compression material (c + q) t F F - compression material c t F F -
        firstCompression material c q F F) + firstCompression material c q F F‖ := congrArg norm hid
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)

theorem compression_quadratic (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) (F : V →L[ℂ] Field) (x : V) :
    (inner ℂ x (compression material c t F F x)).re =
      (inner ℂ (F x) ((shiftedMagneticFourier material c t).toEuclideanLin (F x))).re := by
  change (inner ℂ x (F.adjoint
    ((Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (shiftedMagneticFourier material c t)) (F x)))).re = _
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right F x _)

theorem auxiliary_compression_quadratic
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (F : V →L[ℂ] Field) (x : V) :
    (inner ℂ (F x) ((auxiliaryMagneticFourier material c t t').toEuclideanLin (F x))).re =
      (inner ℂ x (compression material c t F F x)).re +
      2 * t * ‖BoxProjectionAssembly.projector c (F x)‖ ^ 2 -
      (t' - t) * ‖F x‖ ^ 2 := by
  rw [compression_quadratic]
  have hA := auxiliary_energy material c t t' (F x)
  have hB := auxiliary_energy material c 0 t (F x)
  have hb : auxiliaryMagneticFourier material c 0 t = shiftedMagneticFourier material c t := by
    simp [auxiliaryMagneticFourier]
  rw [hb] at hB
  change _ = _ + 2 * t * ‖longitudinalPart c (F x)‖ ^ 2 - (t' - t) * ‖F x‖ ^ 2
  rw [hA, hB, parts_norm_sq c (F x)]
  ring

theorem auxiliary_center_compression_quadratic
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t : ℝ)
    (F : V →L[ℂ] Field) (x : V) (hx : F x ∈ transverseSubspace c) :
    (inner ℂ (F x) ((auxiliaryMagneticFourier material c t t).toEuclideanLin (F x))).re =
      (inner ℂ x (compression material c t F F x)).re := by
  rw [auxiliary_compression_quadratic]
  have hp : BoxProjectionAssembly.projector c (F x) = 0 :=
    longitudinalProjection_transverse c (F x) hx
  simp only [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero, sub_self, zero_mul, sub_zero]

omit [CompleteSpace V] in
theorem spectral_shift_abs_bound (F : V →L[ℂ] Field) (ν t t' σ : ℝ)
    (hF : ‖F‖ ≤ ν) (hσ : |t' - t| ≤ σ) (x : V) :
    |(t' - t) * ‖F x‖ ^ 2| ≤ σ * ν ^ 2 * ‖x‖ ^ 2 := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖F x‖)]
  calc
    _ ≤ σ * (ν ^ 2 * ‖x‖ ^ 2) :=
      mul_le_mul hσ (norm_image_sq F ν hF x) (sq_nonneg _) ((abs_nonneg _).trans hσ)
    _ = _ := by ring

omit [CompleteSpace V] in
theorem longitudinal_low_bound (c q : Momentum) (F : V →L[ℂ] Field)
    (s r wn : ℝ) (hs : 0 ≤ s) (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f, r ≤ ‖longitudinalVector c f‖)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (hw : ∀ x, ‖BoxProjectionAssembly.scalarWeight
      (fun f => 1 / ‖longitudinalVector c f‖) (F x)‖ ^ 2 ≤ wn * ‖x‖ ^ 2)
    (x : V) : ‖BoxProjectionAssembly.projector (c + q) (F x)‖ ^ 2 ≤
      (s ^ 2 * wn / (1 - s / r) ^ 2) * ‖x‖ ^ 2 := by
  have h := BoxProjectionAssembly.transverse_projection_weighted_norm c q (F x) (htrans x)
    s r hs hq hsr hr
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at hsq
  have hw' := mul_le_mul_of_nonneg_left (hw x) (sq_nonneg (s / (1 - s / r)))
  apply hsq.trans (hw'.trans_eq _)
  simp only [div_pow]
  ring

/-- The actual negative low-space form, with exactly the magnetic,
moving-projector and spectral-shift losses used by the finite verifier. -/
theorem negative_low_form
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ edge, 1 ≤ edgeAverage material edge) (c q : Momentum) (t t' : ℝ)
    (F : V →L[ℂ] Field) (P0 s r ν e dot wn σ : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f, r ≤ ‖longitudinalVector c f‖)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hfirst : ‖firstCompression material c q F F‖ ≤ dot) (hσ : |t' - t| ≤ σ)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (hw : ∀ x, ‖BoxProjectionAssembly.scalarWeight
      (fun f => 1 / ‖longitudinalVector c f‖) (F x)‖ ^ 2 ≤ wn * ‖x‖ ^ 2)
    (hnegative : ∀ x, (inner ℂ x (compression material c t F F x)).re ≤ -P0 * ‖x‖ ^ 2)
    (x : V) :
    (inner ℂ (F x) ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin (F x))).re ≤
      (-P0 + dot + s ^ 2 * (ν * e + ν ^ 2) +
        2 * t * s ^ 2 * wn / (1 - s / r) ^ 2 + σ * ν ^ 2) * ‖x‖ ^ 2 := by
  have hv := quadratic_abs_le_of_norm
    (compression material (c + q) t F F - compression material c t F F)
    (dot + s ^ 2 * (ν * e + ν ^ 2))
    (diagonal_variation_norm material hm c q t F s ν e dot hq hF hcenter hfirst) x
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hv
  have hv' := (abs_le.mp hv).2
  have hshift := (abs_le.mp (spectral_shift_abs_bound F ν t t' σ hF hσ x)).1
  have hp := mul_le_mul_of_nonneg_left
    (longitudinal_low_bound c q F s r wn hs hq hsr hr htrans hw x) (by positivity : 0 ≤ 2 * t)
  rw [auxiliary_compression_quadratic]
  have hn := hnegative x
  calc
    _ ≤ -P0 * ‖x‖ ^ 2 + (dot + s ^ 2 * (ν * e + ν ^ 2)) * ‖x‖ ^ 2 +
        2 * t * (s ^ 2 * wn / (1 - s / r) ^ 2 * ‖x‖ ^ 2) + σ * ν ^ 2 * ‖x‖ ^ 2 := by
      linarith only [hn, hv', hp, hshift]
    _ = _ := by ring

/-- The positive low-space form loses only the magnetic Taylor and
spectral-parameter terms; the moving longitudinal correction is nonnegative. -/
theorem positive_low_form
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ edge, 1 ≤ edgeAverage material edge) (c q : Momentum) (t t' : ℝ)
    (F : V →L[ℂ] Field) (P0 s ν e dot σ : ℝ)
    (ht : 0 ≤ t) (hq : displacementSize q ≤ s)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hfirst : ‖firstCompression material c q F F‖ ≤ dot) (hσ : |t' - t| ≤ σ)
    (hpositive : ∀ x, P0 * ‖x‖ ^ 2 ≤ (inner ℂ x (compression material c t F F x)).re)
    (x : V) :
    (P0 - dot - s ^ 2 * (ν * e + ν ^ 2) - σ * ν ^ 2) * ‖x‖ ^ 2 ≤
      (inner ℂ (F x) ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin (F x))).re := by
  have hv := quadratic_abs_le_of_norm
    (compression material (c + q) t F F - compression material c t F F)
    (dot + s ^ 2 * (ν * e + ν ^ 2))
    (diagonal_variation_norm material hm c q t F s ν e dot hq hF hcenter hfirst) x
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hv
  have hv' := (abs_le.mp hv).1
  have hshift := (abs_le.mp (spectral_shift_abs_bound F ν t t' σ hF hσ x)).2
  have hp : 0 ≤ 2 * t * ‖BoxProjectionAssembly.projector (c + q) (F x)‖ ^ 2 := by positivity
  rw [auxiliary_compression_quadratic]
  have hc := hpositive x
  nlinarith

end Maxwell.Spectral.BoxLowForms
