import Maxwell.Continuum.CalibrationBumpMultiplier
import Maxwell.Continuum.CellFourierUnitary
import Maxwell.Continuum.CalibrationAliasSupport

/-! Literal multiplication by a finite torus Fourier polynomial is
finite convolution on the complete alias space. The identification
uses the actual L² Fourier unitary, not a sampled-field assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber CellBandFourier UnitAddTorus MeasureTheory PeriodicSampling

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusMultiplier_fourier (n k : Alias) (u : CellFieldL2) (j : Fin 3) :
    mFourierCoeff (torusMultiplier (mFourier n) u j) k =
      mFourierCoeff (u j) (k-n) := by
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [torusMultiplier_ae (mFourier n) u j] with x hx
  rw [hx]
  simp only [smul_eq_mul, ← mul_assoc, ← mFourier_add]
  congr 2
  abel

theorem torusMultiplier_character (n : Alias) (u : FiberSpace) :
    CellFourier.unitary.symm (torusMultiplier (mFourier n) (CellFourier.unitary u)) =
      shift (-n) u := by
  have hu := CellFourier.unitary.symm_apply_apply u
  rw [CellFourier.unitary_symm_apply] at hu
  apply Subtype.ext
  funext k
  apply PiLp.ext
  intro j
  rw [CellFourier.unitary_symm_apply]
  change mFourierBasis.repr (torusMultiplier (mFourier n) (CellFourier.unitary u) j) k = _
  rw [mFourierBasis_repr, torusMultiplier_fourier, ← mFourierBasis_repr]
  have h := congrArg (fun v : FiberSpace => v (k-n) j) hu
  exact h

def torusMultiplierCLM : C(Torus, ℂ) →L[ℂ] (CellFieldL2 →L[ℂ] CellFieldL2) :=
  DiagonalMap.diagonalCLM.comp (CompactCoefficient.coefficientMap (μ := torusMeasure) id measurable_id)

theorem torusMultiplierCLM_apply (f : C(Torus, ℂ)) : torusMultiplierCLM f = torusMultiplier f := rfl

def aliasMultiplier (f : C(Torus, ℂ)) : FiberSpace →L[ℂ] FiberSpace :=
  CellFourier.unitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((torusMultiplier f).comp CellFourier.unitary.toLinearIsometry.toContinuousLinearMap)

theorem aliasMultiplier_norm (f : C(Torus, ℂ)) : ‖aliasMultiplier f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖CellFourier.unitary.symm (torusMultiplier f (CellFourier.unitary u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖torusMultiplier f‖*‖CellFourier.unitary u‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖f‖*‖u‖ := by rw [LinearIsometryEquiv.norm_map]; gcongr; exact torusMultiplier_norm f

def aliasMultiplierLinear : C(Torus, ℂ) →ₗ[ℂ] (FiberSpace →L[ℂ] FiberSpace) where
  toFun := aliasMultiplier
  map_add' f g := by
    have h := torusMultiplierCLM.map_add f g
    change torusMultiplier (f+g) = torusMultiplier f+torusMultiplier g at h
    apply ContinuousLinearMap.ext
    intro u
    simp only [aliasMultiplier, ContinuousLinearMap.comp_apply, h,
      add_apply, map_add]
  map_smul' c f := by
    have h := torusMultiplierCLM.map_smul c f
    change torusMultiplier (c • f) = c • torusMultiplier f at h
    apply ContinuousLinearMap.ext
    intro u
    simp only [aliasMultiplier, ContinuousLinearMap.comp_apply, h,
      smul_apply, map_smul, RingHom.id_apply]

def aliasMultiplierCLM : C(Torus, ℂ) →L[ℂ] (FiberSpace →L[ℂ] FiberSpace) :=
  aliasMultiplierLinear.mkContinuous 1 (fun f => by
    change ‖aliasMultiplier f‖ ≤ 1*‖f‖
    simpa only [one_mul] using aliasMultiplier_norm f)

def finiteAliasConvolution (D : ℕ) (c : Alias → ℂ) : FiberSpace →L[ℂ] FiberSpace :=
  (∑ n ∈ Product.frequencyCube D, c n • shift (-n)).copy
    (fun u => ∑ n ∈ Product.frequencyCube D, c n • shift (-n) u)
    (by funext u; simp only [sum_apply, smul_apply])

def finiteTorusPolynomial (D : ℕ) (c : Alias → ℂ) : C(Torus, ℂ) :=
  ∑ n ∈ Product.frequencyCube D, c n • mFourier n

theorem finiteTorusPolynomial_apply (D : ℕ) (c : Alias → ℂ) (x : Torus) :
    finiteTorusPolynomial D c x = Product.polynomial c D x := by
  simp only [finiteTorusPolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    Product.polynomial, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n _
  exact mul_comm _ _

theorem finiteTorusPolynomial_convolution (D : ℕ) (c : Alias → ℂ) :
    aliasMultiplier (finiteTorusPolynomial D c) = finiteAliasConvolution D c := by
  rw [finiteAliasConvolution, ContinuousLinearMap.copy_eq]
  change aliasMultiplierCLM (∑ n ∈ Product.frequencyCube D, c n • mFourier n) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  apply ContinuousLinearMap.ext
  exact torusMultiplier_character n

theorem AliasSupported.finiteConvolution {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (D : ℕ) (c : Alias → ℂ) : AliasSupported (finiteAliasConvolution D c u) (R+D) := by
  classical
  intro k hk
  obtain ⟨j, hj⟩ := hk
  change (∑ n ∈ Product.frequencyCube D, c n • shift (-n) u) k = 0
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, shift_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := ((Product.mem_frequencyCube D n).mp hn) j
  have hk' : (R : ℤ) < |(k + -n) j| := by
    have habs : |k j| ≤ |k j-n j|+|n j| := by
      have he : k j = (k j-n j)+n j := by ring
      calc
        _ = |(k j-n j)+n j| := congrArg abs he
        _ ≤ _ := abs_add_le _ _
    change (R : ℤ) < |k j + -n j|
    simp only [sub_eq_add_neg] at habs
    push_cast at hj
    omega
  rw [hu _ ⟨j, hk'⟩, smul_zero]

#print axioms finiteTorusPolynomial_convolution
#print axioms AliasSupported.finiteConvolution

end Maxwell.Continuum.Calibration
