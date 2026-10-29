import Maxwell.Continuum.FreeFiberPotential

/-!
# Absolutely summable Fourier polarization fields

The aliases and three-component polarization blocks are exactly those of
the infinite Maxwell fiber. The continuous inclusion into its Hilbert space
preserves every coefficient, and bounded block multipliers intertwine it.
-/

noncomputable section
namespace Maxwell.Continuum.FiberL1

open FreeFiber
open scoped BigOperators

abbrev Space := lp (fun _ : Alias => Polarization) 1

theorem norm_eq_tsum (u : Space) : ‖u‖ = ∑' ν, ‖u ν‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) u

theorem summable_norm (u : Space) : Summable (fun ν => ‖u ν‖) := by
  simpa using (lp.memℓp u).summable (by norm_num : 0 < (1 : ENNReal).toReal)

def inclusionLinear : Space →ₗ[ℂ] FiberSpace :=
  lp.linearMapOfLE ℂ (fun _ : Alias => Polarization) (by norm_num : (1 : ENNReal) ≤ 2)

@[simp] theorem inclusionLinear_apply (u : Space) (ν : Alias) : inclusionLinear u ν = u ν := rfl

theorem inclusionLinear_norm_le (u : Space) : ‖inclusionLinear u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ENNReal).toReal) (norm_nonneg u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, inclusionLinear_apply]
  have hs2 : Summable (fun ν => ‖u ν‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, inclusionLinear_apply] using
      (lp.memℓp (inclusionLinear u)).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  calc
    (∑' ν, ‖u ν‖ ^ 2) ≤ ∑' ν, ‖u‖ * ‖u ν‖ := by
      apply hs2.tsum_le_tsum _ ((summable_norm u).mul_left ‖u‖)
      intro ν
      have h := lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) u ν
      nlinarith [norm_nonneg (u ν)]
    _ = ‖u‖ ^ 2 := by rw [tsum_mul_left, ← norm_eq_tsum]; ring

def inclusion : Space →L[ℂ] FiberSpace :=
  inclusionLinear.mkContinuous 1 (fun u => by simpa only [one_mul] using inclusionLinear_norm_le u)

@[simp] theorem inclusion_apply (u : Space) (ν : Alias) : inclusion u ν = u ν := rfl

theorem inclusion_norm_le : ‖inclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖inclusionLinear u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using inclusionLinear_norm_le u

theorem inclusion_injective : Function.Injective inclusion := by
  intro u v huv
  apply Subtype.ext
  funext ν
  exact congrArg (fun z : FiberSpace => z ν) huv

def blockMultiplier (R : Alias → Polarization →L[ℂ] Polarization) {C : ℝ}
    (hC : 0 ≤ C) (hR : ∀ ν, ‖R ν‖ ≤ C) : Space →L[ℂ] Space :=
  lp.mapCLM 1 R hC hR

@[simp] theorem blockMultiplier_apply (R : Alias → Polarization →L[ℂ] Polarization) {C : ℝ}
    (hC : 0 ≤ C) (hR : ∀ ν, ‖R ν‖ ≤ C) (u : Space) (ν : Alias) :
    blockMultiplier R hC hR u ν = R ν (u ν) := rfl

theorem blockMultiplier_norm_le (R : Alias → Polarization →L[ℂ] Polarization) {C : ℝ}
    (hC : 0 ≤ C) (hR : ∀ ν, ‖R ν‖ ≤ C) : ‖blockMultiplier R hC hR‖ ≤ C :=
  lp.norm_mapCLM_le 1 R hC hR

theorem inclusion_blockMultiplier (R : Alias → Polarization →L[ℂ] Polarization) {C : ℝ}
    (hC : 0 ≤ C) (hR : ∀ ν, ‖R ν‖ ≤ C) (u : Space) :
    inclusion (blockMultiplier R hC hR u) = boundedBlocks R hC hR (inclusion u) := rfl

def reindex (e : Alias ≃ Alias) : Space ≃ₗᵢ[ℂ] Space where
  toFun u := ⟨fun ν => u (e ν), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩
  invFun u := ⟨fun ν => u (e.symm ν), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩
  left_inv u := by apply Subtype.ext; funext ν; simp
  right_inv u := by apply Subtype.ext; funext ν; simp
  map_add' u v := by apply Subtype.ext; funext ν; rfl
  map_smul' c u := by apply Subtype.ext; funext ν; rfl
  norm_map' u := by
    rw [norm_eq_tsum, norm_eq_tsum]
    exact e.tsum_eq (fun ν : Alias => ‖u ν‖)

def shift (a : Alias) : Space →L[ℂ] Space :=
  (reindex (aliasTranslation a)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem shift_apply (a : Alias) (u : Space) (ν : Alias) : shift a u ν = u (ν + a) := rfl

theorem shift_norm_le (a : Alias) : ‖shift a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖(reindex (aliasTranslation a)) u‖ ≤ 1 * ‖u‖
  rw [(reindex (aliasTranslation a)).norm_map, one_mul]

theorem inclusion_shift (a : Alias) (u : Space) :
    inclusion (shift a u) = FreeFiber.shift a (inclusion u) := rfl

/-- The same six-neighbor material convolution, on absolutely summable coefficients. -/
def potential : Space →L[ℂ] Space :=
  ∑ j : Fin 3, (potentialWeight j : ℂ) • (shift (unitAlias j) + shift (-unitAlias j))

theorem potential_norm_le : ‖potential‖ ≤ 7 := by
  calc
    ‖potential‖ ≤ ∑ j : Fin 3,
        ‖(potentialWeight j : ℂ) • (shift (unitAlias j) + shift (-unitAlias j))‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, potentialWeight j * (1 + 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (potentialWeight_nonneg j)]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (shift_norm_le _) (shift_norm_le _)))
        (potentialWeight_nonneg j)
    _ = 7 := by norm_num [Fin.sum_univ_succ, potentialWeight]

theorem inclusion_potential (u : Space) : inclusion (potential u) = FreeFiber.potential (inclusion u) := by
  simp only [potential, FreeFiber.potential, sum_apply, smul_apply, add_apply,
    map_sum, map_smul, map_add, inclusion_shift]

#print axioms inclusionLinear_norm_le
#print axioms potential_norm_le

end Maxwell.Continuum.FiberL1
