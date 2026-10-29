import Maxwell.Continuum.WellMultiplier
import Maxwell.Continuum.FourierCurl

/-! The actual anisotropic scalar Fourier resolvent and the literal
Birman--Schwinger sandwich. No eigenvalue or inverse is supplied as data. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory FourierTransform

variable (H : Space →L[ℝ] Space) (hH : ∀ ξ, 0 ≤ inner ℝ ξ (H ξ))

def ellipticSymbol (ξ : Space) : ℝ := (2 * Real.pi) ^ 2 * inner ℝ ξ (H ξ)

theorem ellipticSymbol_continuous : Continuous (ellipticSymbol H) := by
  unfold ellipticSymbol
  fun_prop

theorem ellipticSymbol_nonneg (hH : ∀ ξ, 0 ≤ inner ℝ ξ (H ξ)) (ξ : Space) :
    0 ≤ ellipticSymbol H ξ :=
  mul_nonneg (sq_nonneg _) (hH ξ)

def resolventProfile (hH : ∀ ξ, 0 ≤ inner ℝ ξ (H ξ)) : UnitProfile where
  coefficient ξ := (1 + ellipticSymbol H ξ)⁻¹
  measurable := (continuous_const.add (ellipticSymbol_continuous H)).measurable.inv
  nonneg ξ := inv_nonneg.mpr (by linarith [ellipticSymbol_nonneg H hH ξ])
  le_one ξ := inv_le_one_of_one_le₀ (by linarith [ellipticSymbol_nonneg H hH ξ])

def scalarFourier : ScalarL2 ≃ₗᵢ[ℂ] ScalarL2 := Lp.fourierTransformₗᵢ Space ℂ

/-- The literal inverse Fourier multiplier `(1 + pᵀHp)⁻¹`, where `p = 2πξ`. -/
def resolvent : ScalarL2 →L[ℂ] ScalarL2 :=
  scalarFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((resolventProfile H hH).multiplier.comp
      scalarFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem resolvent_fourier (u : ScalarL2) :
    scalarFourier (resolvent H hH u) = (resolventProfile H hH).multiplier (scalarFourier u) :=
  scalarFourier.apply_symm_apply _

theorem resolvent_fourier_ae (u : ScalarL2) :
    scalarFourier (resolvent H hH u) =ᵐ[volume]
      fun ξ => ((1 + ellipticSymbol H ξ)⁻¹ : ℝ) * scalarFourier u ξ := by
  rw [resolvent_fourier]
  exact (resolventProfile H hH).multiplier_ae (scalarFourier u)

theorem resolvent_apply_norm_le (u : ScalarL2) : ‖resolvent H hH u‖ ≤ ‖u‖ := by
  rw [← scalarFourier.norm_map (resolvent H hH u), resolvent_fourier,
    ← scalarFourier.norm_map u]
  exact (resolventProfile H hH).multiplier_apply_norm_le _

theorem resolvent_norm_le : ‖resolvent H hH‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using resolvent_apply_norm_le H hH)

theorem resolvent_symmetric : (resolvent H hH : ScalarL2 →ₗ[ℂ] ScalarL2).IsSymmetric := by
  intro u v
  change inner ℂ (resolvent H hH u) v = inner ℂ u (resolvent H hH v)
  rw [← scalarFourier.inner_map_map (resolvent H hH u) v,
    ← scalarFourier.inner_map_map u (resolvent H hH v), resolvent_fourier, resolvent_fourier]
  exact (resolventProfile H hH).multiplier_symmetric _ _

theorem resolvent_selfAdjoint : IsSelfAdjoint (resolvent H hH) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (resolvent_symmetric H hH)

theorem resolvent_inner_nonneg (u : ScalarL2) :
    0 ≤ RCLike.re (inner ℂ u (resolvent H hH u)) := by
  rw [← scalarFourier.inner_map_map u (resolvent H hH u), resolvent_fourier]
  exact (resolventProfile H hH).inner_nonneg _

/-- The maximal scalar elliptic graph in Fourier coordinates. -/
def EllipticFourierEquation (u f : ScalarL2) : Prop :=
  (fun ξ => ((1 + ellipticSymbol H ξ : ℝ) : ℂ) * scalarFourier u ξ) =ᵐ[volume]
    scalarFourier f

theorem resolvent_solves (f : ScalarL2) :
    EllipticFourierEquation H (resolvent H hH f) f := by
  filter_upwards [resolvent_fourier_ae H hH f] with ξ hξ
  have hpos : 0 < 1 + ellipticSymbol H ξ := by linarith [ellipticSymbol_nonneg H hH ξ]
  rw [hξ, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one,
    one_mul]

theorem resolvent_unique {u f : ScalarL2} (h : EllipticFourierEquation H u f) :
    u = resolvent H hH f := by
  apply scalarFourier.injective
  apply Lp.ext
  filter_upwards [h, resolvent_solves H hH f] with ξ hu hr
  exact mul_left_cancel₀ (by exact_mod_cast (show 1 + ellipticSymbol H ξ ≠ 0 by
    linarith [ellipticSymbol_nonneg H hH ξ])) (hu.trans hr.symm)

theorem ellipticFourierEquation_iff (u f : ScalarL2) :
    EllipticFourierEquation H u f ↔ u = resolvent H hH f :=
  ⟨resolvent_unique H hH, fun h => h ▸ resolvent_solves H hH f⟩

/-- The literal global zero-extension version of `√w (-div H grad + 1)⁻¹ √w`. -/
def birmanSchwinger : ScalarL2 →L[ℂ] ScalarL2 :=
  rootProfile.multiplier.comp ((resolvent H hH).comp rootProfile.multiplier)

theorem birmanSchwinger_apply (u : ScalarL2) :
    birmanSchwinger H hH u = rootProfile.multiplier
      (resolvent H hH (rootProfile.multiplier u)) := rfl

theorem birmanSchwinger_symmetric :
    (birmanSchwinger H hH : ScalarL2 →ₗ[ℂ] ScalarL2).IsSymmetric := by
  intro u v
  change inner ℂ (rootProfile.multiplier (resolvent H hH (rootProfile.multiplier u))) v =
    inner ℂ u (rootProfile.multiplier (resolvent H hH (rootProfile.multiplier v)))
  have hQ (a b : ScalarL2) : inner ℂ (rootProfile.multiplier a) b =
      inner ℂ a (rootProfile.multiplier b) := rootProfile.multiplier_symmetric a b
  have hR (a b : ScalarL2) : inner ℂ (resolvent H hH a) b =
      inner ℂ a (resolvent H hH b) := resolvent_symmetric H hH a b
  rw [hQ, hR, ← hQ]

theorem birmanSchwinger_selfAdjoint : IsSelfAdjoint (birmanSchwinger H hH) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (birmanSchwinger_symmetric H hH)

theorem birmanSchwinger_inner_nonneg (u : ScalarL2) :
    0 ≤ RCLike.re (inner ℂ u (birmanSchwinger H hH u)) := by
  rw [birmanSchwinger_apply]
  have hQ : inner ℂ (rootProfile.multiplier u) (resolvent H hH (rootProfile.multiplier u)) =
      inner ℂ u (rootProfile.multiplier (resolvent H hH (rootProfile.multiplier u))) :=
    rootProfile.multiplier_symmetric _ _
  rw [← hQ]
  exact resolvent_inner_nonneg H hH _

theorem birmanSchwinger_norm_le : ‖birmanSchwinger H hH‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul, birmanSchwinger_apply]
  exact
    (rootProfile.multiplier_apply_norm_le _).trans
      ((resolvent_apply_norm_le H hH _).trans (rootProfile.multiplier_apply_norm_le u))

theorem birmanSchwinger_supported (u : ScalarL2) :
    ∀ᵐ y ∂volume, 1 ≤ ‖y‖ → birmanSchwinger H hH u y = 0 := by
  filter_upwards [rootProfile.multiplier_vanishes_ae
    (resolvent H hH (rootProfile.multiplier u))] with y hy hnorm
  exact hy ((qw_zero_iff y).mpr hnorm)

end Maxwell.Continuum.Well
