import Maxwell.Certificate.FourierTransverse
import Maxwell.Spectral.Concrete
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Coercivity of the actual Fourier curl on a supported transverse field. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum)
open scoped ComplexConjugate

def frequencyComponent (f : Frequency) : FourierSpace →ₗ[ℂ] Polarization where
  toFun x := WithLp.toLp 2 fun j => x (j, f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem frequencyCurl_component (c : Momentum) (f : Frequency) (x : FourierSpace) :
    frequencyComponent f ((frequencyCurl c).toEuclideanLin x) =
      (curlSymbolMatrix c f).toEuclideanLin (frequencyComponent f x) := by
  apply WithLp.ofLp_injective 2
  funext i
  change (frequencyCurl c *ᵥ x.ofLp) (i, f) =
    (curlSymbolMatrix c f *ᵥ (fun j => x (j, f))) i
  simp [frequencyCurl, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem frequencyCurl_adjoint_component (c : Momentum) (f : Frequency) (x : FourierSpace) :
    frequencyComponent f ((frequencyCurl c).conjTranspose.toEuclideanLin x) =
      (curlSymbolMatrix c f).conjTranspose.toEuclideanLin (frequencyComponent f x) := by
  apply WithLp.ofLp_injective 2
  funext i
  change ((frequencyCurl c).conjTranspose *ᵥ x.ofLp) (i, f) =
    ((curlSymbolMatrix c f).conjTranspose *ᵥ (fun j => x (j, f))) i
  simp [frequencyCurl, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, apply_ite, ite_mul]

theorem frequencyCurl_mul_adjoint_transverse (c : Momentum)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) (e : Electric) :
    ((frequencyCurl c * (frequencyCurl c).conjTranspose).toEuclideanLin x) e =
      (laplacianSymbol c e.2 : ℂ) * x e := by
  have hc : frequencyComponent e.2 x ∈ transversePolarization c e.2 := hx e.2
  have h := curlSymbolMatrix_mul_adjoint_transverse c e.2 (frequencyComponent e.2 x) hc
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply] at h
  rw [← frequencyCurl_adjoint_component, ← frequencyCurl_component] at h
  have he := congrArg (fun z : Polarization => z e.1) h
  change ((frequencyCurl c).toEuclideanLin
    ((frequencyCurl c).conjTranspose.toEuclideanLin x)) (e.1, e.2) =
      (laplacianSymbol c e.2 : ℂ) * x (e.1, e.2) at he
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using he

private theorem matrix_adjoint_energy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : Matrix ι κ ℂ) (x : EuclideanSpace ℂ ι) :
    inner ℂ x ((C * C.conjTranspose).toEuclideanLin x) =
      inner ℂ (C.conjTranspose.toEuclideanLin x) (C.conjTranspose.toEuclideanLin x) := by
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_left C.toEuclideanLin _ _).symm

/-- Exact spectral energy identity before applying any material bound. -/
theorem frequencyCurl_adjoint_norm_sq (c : Momentum)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) :
    ‖(frequencyCurl c).conjTranspose.toEuclideanLin x‖ ^ 2 =
      ∑ e, laplacianSymbol c e.2 * ‖x e‖ ^ 2 := by
  have hin := matrix_adjoint_energy (frequencyCurl c) x
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← hin]
  change (inner ℂ x
    ((frequencyCurl c * (frequencyCurl c).conjTranspose).toEuclideanLin x)).re = _
  simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [frequencyCurl_mul_adjoint_transverse c x hx]
  rw [mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- A lower bound on the retained Fourier Laplacian gives a lower bound on
the actual curl-adjoint energy of every supported transverse field. -/
theorem frequencyCurl_adjoint_norm_sq_lower (c : Momentum) (support : Finset Frequency)
    (L : ℝ) (hL : ∀ f ∈ support, L ≤ laplacianSymbol c f)
    (x : FourierSpace) (hx : x ∈ supportedTransverseSubspace c support) :
    L * ‖x‖ ^ 2 ≤ ‖(frequencyCurl c).conjTranspose.toEuclideanLin x‖ ^ 2 := by
  rw [frequencyCurl_adjoint_norm_sq c x hx.1]
  have hnorm : ‖x‖ ^ 2 = ∑ e, ‖x e‖ ^ 2 := by
    exact EuclideanSpace.norm_sq_eq x
  rw [hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : e.2 ∈ support
  · exact mul_le_mul_of_nonneg_right (hL e.2 he) (sq_nonneg _)
  · simp [hx.2 e.2 he e.1]

private theorem matrix_quadratic_congruence {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℂ) (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ κ) :
    inner ℂ x ((U.conjTranspose * M * U).toEuclideanLin x) =
      inner ℂ (U.toEuclideanLin x) (M.toEuclideanLin (U.toEuclideanLin x)) := by
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right U.toEuclideanLin _ _

private theorem matrix_unitary_norm_sq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℂ) (hU : U.conjTranspose * U = 1) (x : EuclideanSpace ℂ κ) :
    ‖U.toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := congrArg Complex.re (matrix_quadratic_congruence U 1 x)
  simpa only [Matrix.mul_one, hU, Matrix.toLpLin_one, LinearMap.id_apply,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h.symm

/-- The inverse constitutive matrix is bounded below by the reciprocal of
an upper bound on its actual edge averages. -/
theorem inverseMass_quadratic_lower
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (ρ : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e ∧ edgeAverage material e ≤ ρ)
    (x : FourierSpace) :
    ρ⁻¹ * ‖x‖ ^ 2 ≤ (inner ℂ x ((inverseMass material).toEuclideanLin x)).re := by
  have hquad : (inner ℂ x ((inverseMass material).toEuclideanLin x)).re =
      ∑ e, (edgeAverage material e)⁻¹ * ‖x e‖ ^ 2 := by
    have h := Maxwell.Spectral.diagonal_quadratic_form
      (EuclideanSpace.basisFun Electric ℂ) (fun e => (edgeAverage material e)⁻¹)
      (T := (inverseMass material).toEuclideanLin) ?_ x
    · simpa only [EuclideanSpace.basisFun_repr] using h
    · intro y e
      simp [inverseMass, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec_diagonal, EuclideanSpace.basisFun_repr]
  rw [hquad, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [one_div] using one_div_le_one_div_of_le (hm e).1 (hm e).2

/-- Unitary Fourier conjugation preserves the same material lower bound. -/
theorem fourierInverseMass_quadratic_lower
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (ρ : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e ∧ edgeAverage material e ≤ ρ)
    (x : FourierSpace) :
    ρ⁻¹ * ‖x‖ ^ 2 ≤ (inner ℂ x ((fourierInverseMass material).toEuclideanLin x)).re := by
  have h := inverseMass_quadratic_lower material ρ hm ((electricTransform 0).toEuclideanLin x)
  rw [matrix_unitary_norm_sq _ (electricTransform_conjTranspose_mul 0)] at h
  rw [fourierInverseMass, matrix_quadratic_congruence]
  exact h

/-- The shifted magnetic Fourier operator, allowing the exact threshold
used by either endpoint inertia certificate. -/
def shiftedMagneticFourier (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) : Matrix Electric Electric ℂ :=
  frequencyCurl c * fourierInverseMass material * (frequencyCurl c).conjTranspose -
    (t : ℂ) • 1

/-- The actual high transverse block is coercive with lower margin
`L / ρ - t`; the hypotheses are material and scalar Fourier bounds. -/
theorem shiftedMagneticFourier_high_lower
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (support : Finset Frequency) (ρ L t : ℝ) (hρ : 0 < ρ)
    (hm : ∀ e, 0 < edgeAverage material e ∧ edgeAverage material e ≤ ρ)
    (hL : ∀ f ∈ support, L ≤ laplacianSymbol c f)
    (x : FourierSpace) (hx : x ∈ supportedTransverseSubspace c support) :
    (L / ρ - t) * ‖x‖ ^ 2 ≤
      (inner ℂ x ((shiftedMagneticFourier material c t).toEuclideanLin x)).re := by
  have hC := frequencyCurl_adjoint_norm_sq_lower c support L hL x hx
  have hM := fourierInverseMass_quadratic_lower material ρ hm
    ((frequencyCurl c).conjTranspose.toEuclideanLin x)
  have hCM := mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hρ.le)
  have hq := matrix_quadratic_congruence (frequencyCurl c).conjTranspose
    (fourierInverseMass material) x
  rw [Matrix.conjTranspose_conjTranspose] at hq
  have hshift :
      (inner ℂ x ((shiftedMagneticFourier material c t).toEuclideanLin x)).re =
      (inner ℂ ((frequencyCurl c).conjTranspose.toEuclideanLin x)
        ((fourierInverseMass material).toEuclideanLin
          ((frequencyCurl c).conjTranspose.toEuclideanLin x))).re - t * ‖x‖ ^ 2 := by
    simp only [shiftedMagneticFourier, map_sub, map_smul, Matrix.toLpLin_one,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
      Complex.sub_re, hq, inner_smul_right, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hshift]
  rw [div_eq_mul_inv]
  nlinarith

/-- The source endpoint materials remain below 14 after the exact energy
shift; this uses the frozen material table's proved upper bound. -/
theorem concrete_shifted_edge_bounds (s : ℝ) (hs : 0 ≤ s) (hsmax : s ≤ 5 / 256)
    (e : Electric) :
    0 < edgeAverage (fun r => Maxwell.Spectral.Concrete.material r + 64 * s) e ∧
      edgeAverage (fun r => Maxwell.Spectral.Concrete.material r + 64 * s) e ≤ 14 := by
  have hm (r : Maxwell.Spectral.PeriodicYee.Cell20) :
      1 ≤ Maxwell.Spectral.Concrete.material r + 64 * s ∧
        Maxwell.Spectral.Concrete.material r + 64 * s ≤ 14 := by
    have h₁ := (Maxwell.Spectral.Concrete.material_bounds r).1
    have h₂ := Maxwell.Spectral.Concrete.material_upper r
    constructor <;> norm_num at * <;> linarith
  rw [edgeAverage_binding]
  have he := Maxwell.Spectral.PeriodicYee.edgeAverage_bounds
    (fun r => Maxwell.Spectral.Concrete.material r + 64 * s) 1 14 hm
    (e.1, conventionalCell (representative e.2))
  exact ⟨lt_of_lt_of_le (by norm_num) he.1, he.2⟩

/-- A high-frequency Laplacian lower bound of `(79/100)^2` certifies the
uniform positive margin `1/40` for both actual endpoint shifted materials. -/
theorem concrete_shiftedMagnetic_high_lower (s : ℝ) (hs : 0 ≤ s) (hsmax : s ≤ 5 / 256)
    (c : Momentum) (support : Finset Frequency)
    (hL : ∀ f ∈ support, (79 / 100 : ℝ) ^ 2 ≤ laplacianSymbol c f)
    (x : FourierSpace) (hx : x ∈ supportedTransverseSubspace c support) :
    (1 / 40 : ℝ) * ‖x‖ ^ 2 ≤
      (inner ℂ x ((shiftedMagneticFourier
        (fun r => Maxwell.Spectral.Concrete.material r + 64 * s) c (1 / 64)).toEuclideanLin x)).re := by
  have h := shiftedMagneticFourier_high_lower
    (fun r => Maxwell.Spectral.Concrete.material r + 64 * s) c support
    14 ((79 / 100 : ℝ) ^ 2) (1 / 64) (by norm_num)
    (concrete_shifted_edge_bounds s hs hsmax) hL x hx
  have hc : (1 / 40 : ℝ) ≤ (79 / 100 : ℝ) ^ 2 / 14 - 1 / 64 := by norm_num
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans h

/-- The base-material certificates use the same uniform high-space margin. -/
theorem base_shifted_edge_bounds (s : ℝ) (hs : 0 ≤ s) (hsmax : s ≤ 5 / 256)
    (e : Electric) :
    0 < edgeAverage (fun r => Maxwell.Spectral.Concrete.baseMaterial r + 64 * s) e ∧
      edgeAverage (fun r => Maxwell.Spectral.Concrete.baseMaterial r + 64 * s) e ≤ 14 := by
  have hm (r : Maxwell.Spectral.PeriodicYee.Cell20) :
      1 ≤ Maxwell.Spectral.Concrete.baseMaterial r + 64 * s ∧
        Maxwell.Spectral.Concrete.baseMaterial r + 64 * s ≤ 14 := by
    have hb : 1 ≤ Maxwell.Spectral.Concrete.baseMaterial r ∧
        Maxwell.Spectral.Concrete.baseMaterial r ≤ 12 := by
      dsimp [Maxwell.Spectral.Concrete.baseMaterial, Maxwell.Certificate.Material.baseValue]
      split <;> norm_num
    constructor <;> linarith [hb.1, hb.2]
  rw [edgeAverage_binding]
  have he := Maxwell.Spectral.PeriodicYee.edgeAverage_bounds
    (fun r => Maxwell.Spectral.Concrete.baseMaterial r + 64 * s) 1 14 hm
    (e.1, conventionalCell (representative e.2))
  exact ⟨lt_of_lt_of_le (by norm_num) he.1, he.2⟩

theorem base_shiftedMagnetic_high_lower (s : ℝ) (hs : 0 ≤ s) (hsmax : s ≤ 5 / 256)
    (c : Momentum) (support : Finset Frequency)
    (hL : ∀ f ∈ support, (79 / 100 : ℝ) ^ 2 ≤ laplacianSymbol c f)
    (x : FourierSpace) (hx : x ∈ supportedTransverseSubspace c support) :
    (1 / 40 : ℝ) * ‖x‖ ^ 2 ≤
      (inner ℂ x ((shiftedMagneticFourier
        (fun r => Maxwell.Spectral.Concrete.baseMaterial r + 64 * s) c (1 / 64)).toEuclideanLin x)).re := by
  have h := shiftedMagneticFourier_high_lower
    (fun r => Maxwell.Spectral.Concrete.baseMaterial r + 64 * s) c support
    14 ((79 / 100 : ℝ) ^ 2) (1 / 64) (by norm_num)
    (base_shifted_edge_bounds s hs hsmax) hL x hx
  have hc : (1 / 40 : ℝ) ≤ (79 / 100 : ℝ) ^ 2 / 14 - 1 / 64 := by norm_num
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans h

/-- Restricting one argument to the other argument's frequency support
leaves the inner product unchanged. -/
theorem inner_frequencyRestriction (support : Finset Frequency) (x y : FourierSpace)
    (hy : ∀ f, f ∉ support → ∀ j, y (j, f) = 0) :
    inner ℂ (frequencyRestriction support x) y = inner ℂ x y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.2 ∈ support
  · simp [frequencyRestriction, he]
  · simp [frequencyRestriction, he, hy e.2 he e.1]

/-- An actual projected action residual bounds the mixed low/high form.
The high space has the inherited Hilbert norm, so no coordinate condition
number or unstated norm conversion enters the estimate. -/
theorem low_high_coupling_of_residual
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c : Momentum) (support : Finset Frequency)
    (A : FourierSpace →ₗ[ℂ] FourierSpace) (hA : A.IsSymmetric)
    (F : P →ₗ[ℂ] FourierSpace) (r : ℝ)
    (hR : ∀ p, ‖frequencyRestriction support (A (F p))‖ ≤ r * ‖p‖)
    (p : P) (k : supportedTransverseSubspace c support) :
    |(inner ℂ (F p) (A k)).re| ≤ r * ‖p‖ * ‖k‖ := by
  rw [← hA]
  rw [← inner_frequencyRestriction support (A (F p)) (k : FourierSpace) k.property.2]
  calc
    _ ≤ ‖inner ℂ (frequencyRestriction support (A (F p))) (k : FourierSpace)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖frequencyRestriction support (A (F p))‖ * ‖(k : FourierSpace)‖ :=
      norm_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hR p) (norm_nonneg _)

end Maxwell.Certificate.FourierBinding

