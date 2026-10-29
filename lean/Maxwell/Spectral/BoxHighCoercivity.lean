import Maxwell.Certificate.FourierAuxiliaryInertia
import Maxwell.Certificate.FourierCompression
import Maxwell.Spectral.BoxFourierProjection
import Maxwell.Spectral.BoxWeights
import Maxwell.Spectral.BoxProjectionAssembly
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Actual auxiliary high-frequency energy and weighted residual coupling. -/

noncomputable section

namespace Maxwell.Spectral.BoxHighCoercivity

set_option maxRecDepth 4000

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum)
open scoped ComplexConjugate ComplexOrder

def longitudinalPart (c : Momentum) : FourierSpace →ₗ[ℂ] FourierSpace :=
  (longitudinalProjectionMatrix c).toEuclideanLin

def transversePart (c : Momentum) : FourierSpace →ₗ[ℂ] FourierSpace :=
  LinearMap.id - longitudinalPart c

theorem transversePart_component (c : Momentum) (f : Frequency) (x : FourierSpace) :
    frequencyComponent f (transversePart c x) = frequencyComponent f x -
      gradientProjection c f (frequencyComponent f x) := by
  change frequencyComponent f (x - longitudinalPart c x) = _
  rw [map_sub, longitudinalPart, longitudinalProjection_component]

/-- This identity also covers a vanishing symbol: its divergence and
longitudinal projection are both zero. -/
theorem transversePart_mem (c : Momentum) (x : FourierSpace) :
    transversePart c x ∈ transverseSubspace c := by
  intro f
  change divergenceSymbol c f (frequencyComponent f (transversePart c x)) = 0
  rw [transversePart_component]
  by_cases hl : laplacianSymbol c f = 0
  · have hn : ‖longitudinalVector c f‖ ^ 2 = 0 := by
      rw [BoxFourierProjection.longitudinalVector_norm_sq, hl]
    have hz : longitudinalVector c f = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    rw [map_sub, gradientProjection_apply, hz, smul_zero, map_zero, sub_zero,
      ← longitudinal_inner, hz, inner_zero_left]
  · exact sub_gradientProjection_mem_transverse c f hl _

theorem parts_inner_eq_zero (c : Momentum) (x y : FourierSpace) :
    inner ℂ (transversePart c x) (longitudinalPart c y) = 0 :=
  ((transverseSubspace c).mem_orthogonal _).mp
    (longitudinalProjection_mem_orthogonal c y) _ (transversePart_mem c x)

theorem parts_norm_sq (c : Momentum) (x : FourierSpace) :
    ‖x‖ ^ 2 = ‖transversePart c x‖ ^ 2 + ‖longitudinalPart c x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (transversePart c x) (longitudinalPart c x) (parts_inner_eq_zero c x x)
  simpa only [transversePart, LinearMap.sub_apply, LinearMap.id_apply, sub_add_cancel,
    pow_two] using h

theorem longitudinalPart_inner (c : Momentum) (x : FourierSpace) :
    (inner ℂ x (longitudinalPart c x)).re = ‖longitudinalPart c x‖ ^ 2 := by
  have hx : x = transversePart c x + longitudinalPart c x := by
    simp only [transversePart, LinearMap.sub_apply, LinearMap.id_apply, sub_add_cancel]
  calc
    _ = (inner ℂ (transversePart c x + longitudinalPart c x) (longitudinalPart c x)).re :=
      congrArg (fun y => (inner ℂ y (longitudinalPart c x)).re) hx
    _ = _ := by
      rw [inner_add_left, parts_inner_eq_zero, zero_add]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (longitudinalPart c x)

theorem norm_sq_frequencyComponents (x : FourierSpace) :
    ‖x‖ ^ 2 = ∑ f, ‖frequencyComponent f x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  change (∑ e : Electric, ‖x e‖ ^ 2) = ∑ f : Frequency, ∑ j : Direction, ‖x (j, f)‖ ^ 2
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem curl_adjoint_norm_sq_parts (c : Momentum) (x : FourierSpace) :
    ‖(frequencyCurl c).conjTranspose.toEuclideanLin x‖ ^ 2 =
      ∑ f, laplacianSymbol c f * ‖frequencyComponent f (transversePart c x)‖ ^ 2 := by
  have hz := frequencyCurl_adjoint_longitudinal c
    ⟨longitudinalPart c x, longitudinalProjection_mem_orthogonal c x⟩
  have he : (frequencyCurl c).conjTranspose.toEuclideanLin (transversePart c x) =
      (frequencyCurl c).conjTranspose.toEuclideanLin x := by
    change (frequencyCurl c).conjTranspose.toEuclideanLin (x - longitudinalPart c x) = _
    rw [map_sub, hz, sub_zero]
  rw [← he, frequencyCurl_adjoint_norm_sq c _ (transversePart_mem c x)]
  simp only [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  change (∑ e : Electric, laplacianSymbol c e.2 * ‖(transversePart c x) e‖ ^ 2) =
    ∑ f : Frequency, ∑ j : Direction, laplacianSymbol c f * ‖(transversePart c x) (j, f)‖ ^ 2
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem matrix_curl_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    inner ℂ x ((C * M * C.conjTranspose).toEuclideanLin x) =
      inner ℂ (C.conjTranspose.toEuclideanLin x)
        (M.toEuclideanLin (C.conjTranspose.toEuclideanLin x)) := by
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_left C.toEuclideanLin _ _).symm

theorem auxiliary_energy (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t t' : ℝ) (x : FourierSpace) :
    (inner ℂ x ((auxiliaryMagneticFourier material c t t').toEuclideanLin x)).re =
      (inner ℂ ((frequencyCurl c).conjTranspose.toEuclideanLin x)
        ((fourierInverseMass material).toEuclideanLin
          ((frequencyCurl c).conjTranspose.toEuclideanLin x))).re -
      t' * ‖transversePart c x‖ ^ 2 + (2 * t - t') * ‖longitudinalPart c x‖ ^ 2 := by
  simp only [auxiliaryMagneticFourier, shiftedMagneticFourier, map_add, map_sub, map_smul,
    Matrix.toLpLin_one, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, inner_add_right, inner_sub_right, Complex.add_re, Complex.sub_re,
    matrix_curl_energy, inner_smul_right, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  change _ - t' * ‖x‖ ^ 2 + ((2 * (t : ℂ)) * inner ℂ x (longitudinalPart c x)).re = _
  rw [Complex.mul_re, show (2 * (t : ℂ)).im = 0 by simp,
    show (2 * (t : ℂ)).re = 2 * t by simp, zero_mul, sub_zero,
    longitudinalPart_inner, parts_norm_sq c x]
  ring

/-- Exact frequency-dependent coercivity of the actual full auxiliary
matrix. No transverse restriction on the test field is required. -/
theorem auxiliary_weighted_lower
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (ρ t t' : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e ∧ edgeAverage material e ≤ ρ)
    (x : FourierSpace) :
    (∑ f, ((laplacianSymbol c f / ρ - t') *
      ‖frequencyComponent f (transversePart c x)‖ ^ 2 +
      (2 * t - t') * ‖frequencyComponent f (longitudinalPart c x)‖ ^ 2)) ≤
      (inner ℂ x ((auxiliaryMagneticFourier material c t t').toEuclideanLin x)).re := by
  have h := fourierInverseMass_quadratic_lower material ρ hm
    ((frequencyCurl c).conjTranspose.toEuclideanLin x)
  rw [curl_adjoint_norm_sq_parts] at h
  rw [auxiliary_energy, norm_sq_frequencyComponents (transversePart c x),
    norm_sq_frequencyComponents (longitudinalPart c x)]
  calc
    _ = ρ⁻¹ * (∑ f, laplacianSymbol c f * ‖frequencyComponent f (transversePart c x)‖ ^ 2) -
        t' * (∑ f, ‖frequencyComponent f (transversePart c x)‖ ^ 2) +
        (2 * t - t') * (∑ f, ‖frequencyComponent f (longitudinalPart c x)‖ ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ ≤ _ := by linarith

theorem longitudinalPart_idempotent (c : Momentum) (x : FourierSpace) :
    longitudinalPart c (longitudinalPart c x) = longitudinalPart c x := by
  have h := longitudinalProjection_transverse c (transversePart c x) (transversePart_mem c x)
  change longitudinalPart c (x - longitudinalPart c x) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- The corrected longitudinal action is exactly scalar, including when
the input trial field is not transverse at the shifted momentum. -/
theorem longitudinalPart_auxiliary
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t t' : ℝ) (x : FourierSpace) :
    longitudinalPart c ((auxiliaryMagneticFourier material c t t').toEuclideanLin x) =
      ((2 * t - t' : ℝ) : ℂ) • longitudinalPart c x := by
  have hc (y : FourierSpace) : longitudinalPart c ((frequencyCurl c).toEuclideanLin y) = 0 :=
    longitudinalProjection_transverse c _ (frequencyCurl_mem_transverse c y)
  simp only [auxiliaryMagneticFourier, shiftedMagneticFourier, map_add, map_sub, map_smul,
    Matrix.toLpLin_mul_same, Matrix.toLpLin_one, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, hc, zero_sub,
    show (longitudinalProjectionMatrix c).toEuclideanLin = longitudinalPart c from rfl,
    longitudinalPart_idempotent, ← neg_smul, ← add_smul]
  congr 1
  push_cast
  ring

abbrev frequencyWeight := BoxProjectionAssembly.scalarWeightLinear

theorem frequencyWeight_norm_sq (w : Frequency → ℝ) (x : FourierSpace) :
    ‖frequencyWeight w x‖ ^ 2 = ∑ f, w f ^ 2 * ‖frequencyComponent f x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ e : Electric, ‖(w e.2 : ℂ) * x e‖ ^ 2) = _
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  change (∑ e : Electric, w e.2 ^ 2 * ‖x e‖ ^ 2) =
    ∑ f : Frequency, ∑ j : Direction, w f ^ 2 * ‖x (j, f)‖ ^ 2
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem frequencyWeight_inverse_inner (w : Frequency → ℝ) (hw : ∀ f, w f ≠ 0)
    (x y : FourierSpace) :
    inner ℂ (frequencyWeight (fun f => (w f)⁻¹) x) (frequencyWeight w y) = inner ℂ x y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro e _
  change (w e.2 : ℂ) * y e * conj (((w e.2)⁻¹ : ℝ) * x e) = y e * conj (x e)
  simp only [map_mul, map_inv₀, Complex.ofReal_inv, Complex.conj_ofReal]
  field_simp [Complex.ofReal_ne_zero.mpr (hw e.2)]

theorem parts_inner (c : Momentum) (x y : FourierSpace) :
    inner ℂ x y = inner ℂ (transversePart c x) (transversePart c y) +
      inner ℂ (longitudinalPart c x) (longitudinalPart c y) := by
  have hadd (z : FourierSpace) : transversePart c z + longitudinalPart c z = z := sub_add_cancel _ _
  calc
    _ = inner ℂ (transversePart c x + longitudinalPart c x)
        (transversePart c y + longitudinalPart c y) := by rw [hadd, hadd]
    _ = _ := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        parts_inner_eq_zero, inner_eq_zero_symm.mpr (parts_inner_eq_zero c y x)]
      simp

abbrev WeightedSpace := WithLp 2 (FourierSpace × FourierSpace)

def weightedParts (c : Momentum) (w : Frequency → ℝ) (a : ℝ) :
    FourierSpace →ₗ[ℂ] WeightedSpace :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (((frequencyWeight (fun f => Real.sqrt (w f))).comp (transversePart c)).prod
      ((Real.sqrt a : ℂ) • longitudinalPart c))

def inverseWeightedParts (c : Momentum) (w : Frequency → ℝ) (a : ℝ) :
    FourierSpace →ₗ[ℂ] WeightedSpace :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (((frequencyWeight (fun f => (Real.sqrt (w f))⁻¹)).comp (transversePart c)).prod
      (((Real.sqrt a)⁻¹ : ℂ) • longitudinalPart c))

theorem weightedParts_norm_sq (c : Momentum) (w : Frequency → ℝ) (a : ℝ)
    (hw : ∀ f, 0 ≤ w f) (ha : 0 ≤ a) (x : FourierSpace) :
    ‖weightedParts c w a x‖ ^ 2 =
      (∑ f, w f * ‖frequencyComponent f (transversePart c x)‖ ^ 2) +
      a * ‖longitudinalPart c x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖frequencyWeight (fun f => Real.sqrt (w f)) (transversePart c x)‖ ^ 2 +
    ‖(Real.sqrt a : ℂ) • longitudinalPart c x‖ ^ 2 = _
  simp only [frequencyWeight_norm_sq, Real.sq_sqrt (hw _), norm_smul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt ha]

theorem weightedParts_duality (c : Momentum) (w : Frequency → ℝ) (a : ℝ)
    (hw : ∀ f, 0 < w f) (ha : 0 < a) (x y : FourierSpace) :
    inner ℂ (inverseWeightedParts c w a x) (weightedParts c w a y) = inner ℂ x y := by
  change inner ℂ (frequencyWeight (fun f => (Real.sqrt (w f))⁻¹) (transversePart c x))
      (frequencyWeight (fun f => Real.sqrt (w f)) (transversePart c y)) +
    inner ℂ (((Real.sqrt a)⁻¹ : ℂ) • longitudinalPart c x)
      ((Real.sqrt a : ℂ) • longitudinalPart c y) = _
  rw [frequencyWeight_inverse_inner _ (fun f => ne_of_gt (Real.sqrt_pos.mpr (hw f))),
    inner_smul_left, inner_smul_right]
  simp only [map_inv₀, Complex.conj_ofReal]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr ha))),
    one_mul, ← parts_inner]

theorem weighted_coupling (c : Momentum) (w : Frequency → ℝ) (a : ℝ)
    (hw : ∀ f, 0 < w f) (ha : 0 < a) (x y : FourierSpace) :
    |(inner ℂ x y).re| ≤ ‖inverseWeightedParts c w a x‖ * ‖weightedParts c w a y‖ := by
  rw [← weightedParts_duality c w a hw ha x y]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

theorem frequencyComponent_restriction (support : Finset Frequency) (f : Frequency)
    (x : FourierSpace) : frequencyComponent f (frequencyRestriction support x) =
      if f ∈ support then frequencyComponent f x else 0 := by
  by_cases hf : f ∈ support
  · simp only [ite_eq_left hf]
    apply WithLp.ofLp_injective 2
    funext j
    change (if f ∈ support then x (j, f) else 0) = x (j, f)
    exact ite_eq_left hf
  · simp only [ite_eq_right hf]
    apply WithLp.ofLp_injective 2
    funext j
    change (if f ∈ support then x (j, f) else 0) = 0
    exact ite_eq_right hf

theorem longitudinalPart_restriction (c : Momentum) (support : Finset Frequency)
    (x : FourierSpace) :
    longitudinalPart c (frequencyRestriction support x) =
      frequencyRestriction support (longitudinalPart c x) := by
  apply WithLp.ofLp_injective 2
  funext e
  have h : frequencyComponent e.2 (longitudinalPart c (frequencyRestriction support x)) =
      frequencyComponent e.2 (frequencyRestriction support (longitudinalPart c x)) := by
    change frequencyComponent e.2
      ((longitudinalProjectionMatrix c).toEuclideanLin (frequencyRestriction support x)) = _
    rw [longitudinalProjection_component, frequencyComponent_restriction,
      frequencyComponent_restriction]
    by_cases hf : e.2 ∈ support
    · simp only [ite_eq_left hf]
      exact (longitudinalProjection_component c e.2 x).symm
    · simp only [ite_eq_right hf, map_zero]
  exact congrArg (fun y : Polarization => y e.1) h

theorem transversePart_restriction (c : Momentum) (support : Finset Frequency)
    (x : FourierSpace) :
    transversePart c (frequencyRestriction support x) =
      frequencyRestriction support (transversePart c x) := by
  change frequencyRestriction support x - longitudinalPart c (frequencyRestriction support x) =
    frequencyRestriction support (x - longitudinalPart c x)
  rw [map_sub, longitudinalPart_restriction]

def highWeight (support : Finset Frequency) (c : Momentum) (ρ t' : ℝ) (f : Frequency) : ℝ :=
  if f ∈ support then laplacianSymbol c f / ρ - t' else 1

theorem highWeight_pos (support : Finset Frequency) (c : Momentum) (ρ t' : ℝ)
    (hw : ∀ f ∈ support, 0 < laplacianSymbol c f / ρ - t') (f : Frequency) :
    0 < highWeight support c ρ t' f := by
  by_cases hf : f ∈ support
  · simpa only [highWeight, ite_eq_left hf] using hw f hf
  · simp only [highWeight, ite_eq_right hf, zero_lt_one]

theorem auxiliary_high_weighted_lower
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum)
    (support : Finset Frequency) (ρ t t' : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e ∧ edgeAverage material e ≤ ρ)
    (hw : ∀ f ∈ support, 0 < laplacianSymbol c f / ρ - t') (ha : 0 < 2 * t - t')
    (x : FourierSpace) :
    ‖weightedParts c (highWeight support c ρ t') (2 * t - t')
      (frequencyRestriction support x)‖ ^ 2 ≤
      (inner ℂ (frequencyRestriction support x)
        ((auxiliaryMagneticFourier material c t t').toEuclideanLin
          (frequencyRestriction support x))).re := by
  rw [weightedParts_norm_sq c _ _ (fun f => (highWeight_pos support c ρ t' hw f).le) ha.le,
    norm_sq_frequencyComponents (longitudinalPart c (frequencyRestriction support x)),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  have he : (∑ f, (highWeight support c ρ t' f *
      ‖frequencyComponent f (transversePart c (frequencyRestriction support x))‖ ^ 2 +
      (2 * t - t') * ‖frequencyComponent f (longitudinalPart c
        (frequencyRestriction support x))‖ ^ 2)) =
      ∑ f, ((laplacianSymbol c f / ρ - t') *
        ‖frequencyComponent f (transversePart c (frequencyRestriction support x))‖ ^ 2 +
        (2 * t - t') * ‖frequencyComponent f (longitudinalPart c
          (frequencyRestriction support x))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : f ∈ support
    · rw [highWeight, ite_eq_left hf]
    · rw [transversePart_restriction, frequencyComponent_restriction, ite_eq_right hf]
      simp
  rw [he]
  exact auxiliary_weighted_lower material c ρ t t' hm _

theorem weightedParts_injective (c : Momentum) (w : Frequency → ℝ) (a : ℝ)
    (hw : ∀ f, 0 < w f) (ha : 0 < a) : Function.Injective (weightedParts c w a) := by
  intro x y hxy
  have h : inner ℂ (x - y) (x - y) = 0 := by
    rw [← weightedParts_duality c w a hw ha]
    simp only [map_sub, hxy, sub_self, inner_zero_right]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

theorem longitudinal_residual_identity
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (support : Finset Frequency) (t t' : ℝ) (x : FourierSpace) :
    longitudinalPart c (frequencyRestriction support
      ((auxiliaryMagneticFourier material c t t').toEuclideanLin x)) =
      ((2 * t - t' : ℝ) : ℂ) • longitudinalPart c (frequencyRestriction support x) := by
  rw [longitudinalPart_restriction, longitudinalPart_auxiliary, map_smul,
    ← longitudinalPart_restriction]

theorem frequencyWeight_mask (support : Finset Frequency) :
    frequencyWeight (fun f => if f ∈ support then (1 : ℝ) else 0) =
      frequencyRestriction support := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  funext e
  change Complex.ofReal (if e.2 ∈ support then (1 : ℝ) else 0) * x e =
    if e.2 ∈ support then x e else 0
  by_cases hf : e.2 ∈ support <;> simp [hf]

theorem high_longitudinal_leakage (c q : Momentum) (support : Finset Frequency)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) (s rh : ℝ)
    (hs : 0 ≤ s) (hq : BoxSymbols.phaseScale * BoxSymbols.momentumNorm q ≤ s)
    (hsr : s < rh) (hr : ∀ f ∈ support, rh ≤ ‖longitudinalVector c f‖) :
    ‖longitudinalPart (c + q) (frequencyRestriction support x)‖ ≤
      (s / (rh - s)) * ‖frequencyRestriction support x‖ := by
  have h := BoxProjectionAssembly.weighted_transverse_projection_bound c q
    (fun f => if f ∈ support then (1 : ℝ) else 0) x hx s rh hs hq hsr (by
      intro f hf
      by_cases hmem : f ∈ support
      · exact hr f hmem
      · simp [hmem] at hf)
  change ‖frequencyWeight (fun f => if f ∈ support then (1 : ℝ) else 0)
    (longitudinalPart (c + q) x)‖ ≤
    (s / (rh - s)) * ‖frequencyWeight (fun f => if f ∈ support then (1 : ℝ) else 0) x‖ at h
  rw [frequencyWeight_mask, ← longitudinalPart_restriction] at h
  exact h

theorem inverseWeightedParts_norm_sq (c : Momentum) (w : Frequency → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (x : FourierSpace) :
    ‖inverseWeightedParts c w a x‖ ^ 2 =
      ‖frequencyWeight (fun f => (Real.sqrt (w f))⁻¹) (transversePart c x)‖ ^ 2 +
      a⁻¹ * ‖longitudinalPart c x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖frequencyWeight (fun f => (Real.sqrt (w f))⁻¹) (transversePart c x)‖ ^ 2 +
    ‖((Real.sqrt a)⁻¹ : ℂ) • longitudinalPart c x‖ ^ 2 = _
  simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    inv_pow, sq_abs, Real.sq_sqrt ha]

theorem inverseWeightedParts_residual_norm_sq
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (support : Finset Frequency) (w : Frequency → ℝ) (t t' : ℝ)
    (ha : 0 < 2 * t - t') (x : FourierSpace) :
    ‖inverseWeightedParts c w (2 * t - t') (frequencyRestriction support
      ((auxiliaryMagneticFourier material c t t').toEuclideanLin x))‖ ^ 2 =
      ‖frequencyWeight (fun f => (Real.sqrt (w f))⁻¹) (transversePart c
        (frequencyRestriction support
          ((auxiliaryMagneticFourier material c t t').toEuclideanLin x)))‖ ^ 2 +
      (2 * t - t') * ‖longitudinalPart c (frequencyRestriction support x)‖ ^ 2 := by
  rw [inverseWeightedParts_norm_sq c w _ ha.le, longitudinal_residual_identity,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  congr 1
  field_simp

/-- The verifier's exact high coupling loss. The transverse residual is
measured in its inverse weight; longitudinal leakage comes from the actual
moving projector, with its exact scalar auxiliary action. -/
theorem inverseWeightedParts_residual_bound
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c q : Momentum) (support : Finset Frequency) (w : Frequency → ℝ)
    (t t' σ s rh rw qfn M : ℝ)
    (ha : 0 < 2 * t - t') (ht' : t - σ ≤ t') (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hq : BoxSymbols.phaseScale * BoxSymbols.momentumNorm q ≤ s) (hsr : s < rh)
    (hr : ∀ f ∈ support, rh ≤ ‖longitudinalVector c f‖)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c)
    (hF : ‖frequencyRestriction support x‖ ≤ qfn * M)
    (hR : ‖frequencyWeight (fun f => (Real.sqrt (w f))⁻¹) (transversePart (c + q)
      (frequencyRestriction support
        ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin x)))‖ ≤ rw * M) :
    ‖inverseWeightedParts (c + q) w (2 * t - t') (frequencyRestriction support
      ((auxiliaryMagneticFourier material (c + q) t t').toEuclideanLin x))‖ ≤
      Real.sqrt (rw ^ 2 + (t + σ) * s ^ 2 * qfn ^ 2 / (rh - s) ^ 2) * M := by
  have hcoef : 0 ≤ s / (rh - s) := div_nonneg hs (sub_pos.mpr hsr).le
  have hP := (high_longitudinal_leakage c q support x hx s rh hs hq hsr hr).trans
    (mul_le_mul_of_nonneg_left hF hcoef)
  have hPsq := pow_le_pow_left₀ (norm_nonneg _) hP 2
  have hRsq := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hts : 0 < t + σ := by linarith
  have hη : 0 ≤ rw ^ 2 + (t + σ) * s ^ 2 * qfn ^ 2 / (rh - s) ^ 2 := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hM)).mp
  rw [mul_pow, Real.sq_sqrt hη, inverseWeightedParts_residual_norm_sq _ _ _ _ _ _ ha]
  have hlong := mul_le_mul_of_nonneg_left hPsq ha.le
  have hlong' := mul_le_mul_of_nonneg_right
    (show 2 * t - t' ≤ t + σ by linarith) (sq_nonneg (s / (rh - s) * (qfn * M)))
  have halgebra : (rw * M) ^ 2 + (t + σ) * (s / (rh - s) * (qfn * M)) ^ 2 =
      (rw ^ 2 + (t + σ) * s ^ 2 * qfn ^ 2 / (rh - s) ^ 2) * M ^ 2 := by
    simp only [mul_pow, div_pow]
    ring
  linarith

/-- The actual high-space coupling in the norm used by the three-block
Schur theorem. The residual hypothesis is the inverse-weighted norm bound,
which the preceding theorem supplies with the exact scalar loss. -/
theorem auxiliary_high_coupling
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum)
    (support : Finset Frequency) (w : Frequency → ℝ) (t t' α M : ℝ)
    (hw : ∀ f, 0 < w f) (ha : 0 < 2 * t - t')
    (x y : FourierSpace) (hy : ∀ f, f ∉ support → ∀ j, y (j, f) = 0)
    (hres : ‖inverseWeightedParts c w (2 * t - t') (frequencyRestriction support
      ((auxiliaryMagneticFourier material c t t').toEuclideanLin x))‖ ≤ α * M) :
    |(inner ℂ x ((auxiliaryMagneticFourier material c t t').toEuclideanLin y)).re| ≤
      α * M * ‖weightedParts c w (2 * t - t') y‖ := by
  rw [← auxiliaryMagneticFourier_symmetric material c t t',
    ← inner_frequencyRestriction support _ y hy]
  exact (weighted_coupling c w _ hw ha _ y).trans
    (mul_le_mul_of_nonneg_right hres (norm_nonneg _))

theorem frequencyWeight_longitudinalPart (c : Momentum) (w : Frequency → ℝ)
    (x : FourierSpace) :
    frequencyWeight w (longitudinalPart c x) = longitudinalPart c (frequencyWeight w x) := by
  apply WithLp.ofLp_injective 2
  funext e
  have h : frequencyComponent e.2 (frequencyWeight w (longitudinalPart c x)) =
      frequencyComponent e.2 (longitudinalPart c (frequencyWeight w x)) := by
    change frequencyComponent e.2 (BoxProjectionAssembly.scalarWeight w (longitudinalPart c x)) =
      frequencyComponent e.2 ((longitudinalProjectionMatrix c).toEuclideanLin
        (BoxProjectionAssembly.scalarWeight w x))
    rw [BoxProjectionAssembly.scalarWeight_component, longitudinalProjection_component,
      BoxProjectionAssembly.scalarWeight_component, map_smul]
    congr 1
    exact longitudinalProjection_component c e.2 x
  exact congrArg (fun y : Polarization => y e.1) h

theorem frequencyWeight_transversePart (c : Momentum) (w : Frequency → ℝ)
    (x : FourierSpace) :
    frequencyWeight w (transversePart c x) = transversePart c (frequencyWeight w x) := by
  change frequencyWeight w (x - longitudinalPart c x) =
    frequencyWeight w x - longitudinalPart c (frequencyWeight w x)
  rw [map_sub, frequencyWeight_longitudinalPart]

/-- Projecting an inverse-weighted residual onto the moved transverse
space cannot increase its norm, since frequency weights commute with the
orthogonal polarization decomposition. -/
theorem weighted_transversePart_norm_le (c : Momentum) (w : Frequency → ℝ)
    (x : FourierSpace) :
    ‖frequencyWeight w (transversePart c x)‖ ≤ ‖frequencyWeight w x‖ := by
  rw [frequencyWeight_transversePart]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [parts_norm_sq c (frequencyWeight w x)]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The material curl energy is nonnegative, so the exact projection term
alone gives the gradient-block lower bound. No Laplacian cutoff is needed. -/
theorem auxiliary_projection_lower
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e) (x : FourierSpace) :
    2 * t * ‖BoxProjectionAssembly.projector c x‖ ^ 2 - t' * ‖x‖ ^ 2 ≤
      (inner ℂ x ((auxiliaryMagneticFourier material c t t').toEuclideanLin x)).re := by
  have hD : (inverseMass material).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro e
    change (0 : ℂ) ≤ (edgeAverage material e : ℂ)⁻¹
    rw [← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr (hm e).le)
  have hM : (fourierInverseMass material).PosSemidef :=
    hD.conjTranspose_mul_mul_same (electricTransform 0)
  have h := (Matrix.isPositive_toEuclideanLin_iff.mpr hM).re_inner_nonneg_right
    ((frequencyCurl c).conjTranspose.toEuclideanLin x)
  change 0 ≤ (inner ℂ ((frequencyCurl c).conjTranspose.toEuclideanLin x)
    ((fourierInverseMass material).toEuclideanLin
      ((frequencyCurl c).conjTranspose.toEuclideanLin x))).re at h
  change 2 * t * ‖longitudinalPart c x‖ ^ 2 - t' * ‖x‖ ^ 2 ≤ _
  rw [auxiliary_energy, parts_norm_sq c x]
  linarith

end Maxwell.Spectral.BoxHighCoercivity
