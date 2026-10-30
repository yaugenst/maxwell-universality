import Maxwell.Continuum.CalibrationRoundedGrid
import Maxwell.Continuum.CalibrationCutoffPrecision
import Maxwell.Continuum.CalibrationRationalFullSupport

/-! Executable cutoff inverse at every rational grid point, with a
uniform whole-fiber error bound and exact finite rational semantics. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber Auxiliary PeriodicBand

def rationalGridApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (r : Fin 3 → ℚ) (K P : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  if activeGrid r then (gridCutoffApprox r P).center •
    rationalFullApply (piCenter K) (z+σ+7) r K f else 0

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

attribute [local irreducible] fiberResolvent roundedGridFull PeriodicBand.scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

def actualGridInverse (z σ : ℝ) (r : Fin 3 → ℚ) : FiberSpace →L[ℂ] FiberSpace :=
  (cutoff (WithLp.toLp 2 (gridMomentum r)) : ℂ) • fiberResolvent z σ (gridMomentum r)

def roundedGridInverse {L : ℝ} (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (K P : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  if hr : activeGrid r then ((gridCutoffApprox r P).center : ℂ) •
    roundedGridFull z σ D hσ0 hσ r hr K else 0

theorem roundedGridFull_norm {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (hr : activeGrid r) (N ell K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    ‖roundedGridFull z σ D hσ0 hσ r hr K‖ ≤ 5*L^2 := by
  have he := (roundedGridFull_error hL z σ D hσ0 hσ r hr N ell K hlog hK).2
  have hR : ‖fiberResolvent z σ (gridMomentum r)‖ ≤ 4*L^2 := by
    simpa only [inv_pow,inv_inv] using fiberResolvent_norm_le D hσ0 hσ
      (gridMomentum r) (activeGrid_momentum hr)
  have hn := norm_le_norm_sub_add (roundedGridFull z σ D hσ0 hσ r hr K)
    (fiberResolvent z σ (gridMomentum r))
  rw [norm_sub_rev] at hn
  have hp : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [sq_nonneg (L-1)]

theorem roundedGridInverse_error {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (N ell K P : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps (N+2) ell ≤ K)
    (hP : cutoffWorkBits N ell ≤ P) :
    ‖actualGridInverse z σ r-roundedGridInverse z σ D hσ0 hσ r K P‖ ≤ (1/2 : ℝ)^N := by
  by_cases hr : activeGrid r
  · rw [roundedGridInverse,dite_eq_left hr]
    let a : ℝ := cutoff (WithLp.toLp 2 (gridMomentum r))
    let b : ℝ := (gridCutoffApprox r P).center
    let R := fiberResolvent z σ (gridMomentum r)
    let S := roundedGridFull z σ D hσ0 hσ r hr K
    have he := (roundedGridFull_error hL z σ D hσ0 hσ r hr (N+2) ell K hlog hK).2
    have hS := roundedGridFull_norm hL z σ D hσ0 hσ r hr (N+2) ell K hlog hK
    have hc : |a-b| ≤ (1/2 : ℝ)^P :=
      gridCutoffApprox_error r P (fun j => (activeGrid_direction hr j).trans (by norm_num))
    have ha : 0 ≤ a := cutoff_nonneg _
    have ha1 : a ≤ 1 := cutoff_le_one _
    have hid : (a : ℂ) • R-(b : ℂ) • S =
        (a : ℂ) • (R-S)+((a-b : ℝ) : ℂ) • S := by
      rw [Complex.ofReal_sub]
      module
    change ‖(a : ℂ) • R-(b : ℂ) • S‖ ≤ _
    rw [hid]
    calc
      _ ≤ ‖(a : ℂ) • (R-S)‖+‖((a-b : ℝ) : ℂ) • S‖ := norm_add_le _ _
      _ = a*‖R-S‖+|a-b| * ‖S‖ := by
        rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,
          Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
      _ ≤ 1*(1/2 : ℝ)^(N+2)+(1/2 : ℝ)^P*(5*L^2) := by
        gcongr
      _ ≤ _ := by
        convert! cutoff_precision_error hL N ell P hlog hP using 1
        ring
  · rw [roundedGridInverse,dite_eq_right hr,actualGridInverse,cutoff_zero_of_inactive hr,
      Complex.ofReal_zero,zero_smul ℂ (fiberResolvent z σ (gridMomentum r)),sub_zero,norm_zero]
    positivity

theorem rationalGridApply_represents {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (N ell K P : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalGridApply z σ r K P f) (roundedGridInverse z σ D hσ0 hσ r K P u) := by
  by_cases hr : activeGrid r
  · rw [rationalGridApply,ite_eq_left hr,roundedGridInverse,dite_eq_left hr]
    exact represents_smul _ (roundedGridFull_represents hL z σ D hσ0 hσ r hr N ell K hlog hK hf)
  · rw [rationalGridApply,ite_eq_right hr,roundedGridInverse,dite_eq_right hr]
    exact represents_zero

theorem RationalSupported.gridApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    {f : Alias → Fin 3 → V} {R : ℕ} (hf : RationalSupported f R)
    (z σ : ℚ) (r : Fin 3 → ℚ) (K P : ℕ) :
    RationalSupported (rationalGridApply z σ r K P f) (R+K+2) := by
  unfold rationalGridApply
  split_ifs
  · exact (hf.fullApply _ _ _ _).smul _
  · exact RationalSupported.zero _

#print axioms roundedGridInverse_error
#print axioms rationalGridApply_represents

end
end Maxwell.Continuum.Calibration
