import Maxwell.Continuum.FreeFiberNoncentralEstimate
import Maxwell.Continuum.FreeFiberNeumann
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Actual uniform noncentral-alias inverse on the paper's complex box

Every alias outside `{-1,0}³` is included. The total energy is
`3π²/4 + ρe`, including the background dielectric shift by seven.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

def IsCentralAlias (ν : Alias) : Prop := ∀ j, ν j = -1 ∨ ν j = 0

def baseMomentum (ν : Alias) : Fin 3 → ℝ :=
  fun j => Real.pi / 2 + Real.pi * (ν j : ℝ)

theorem aliasMomentum_decomposition (q : Momentum) (ν : Alias) :
    aliasMomentum q ν = realMomentum (baseMomentum ν) + q := by
  funext j
  simp only [aliasMomentum, realMomentum, baseMomentum, Pi.add_apply, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

theorem halfInteger_sq_ge (n : ℤ) : (1 / 4 : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
  by_cases hn : 0 ≤ n
  · have h : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg (n : ℝ)]
  · have h : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    nlinarith [sq_nonneg ((n : ℝ) + 1)]

theorem noncentral_halfInteger_sq_ge (n : ℤ) (hn : n ≠ -1 ∧ n ≠ 0) :
    (9 / 4 : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
  have hcases : n ≤ -2 ∨ 1 ≤ n := by omega
  rcases hcases with h | h
  · have h' : (n : ℝ) ≤ -2 := by exact_mod_cast h
    nlinarith [sq_nonneg ((n : ℝ) + 2)]
  · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem noncentral_base_norm_sq (ν : Alias) (hν : ¬IsCentralAlias ν) :
    24 ≤ ‖momentumVector (realMomentum (baseMomentum ν))‖ ^ 2 := by
  have hex : ∃ j, ν j ≠ -1 ∧ ν j ≠ 0 := by
    simpa only [IsCentralAlias, not_forall, not_or] using hν
  obtain ⟨j, hj⟩ := hex
  have h0 := halfInteger_sq_ge (ν 0)
  have h1 := halfInteger_sq_ge (ν 1)
  have h2 := halfInteger_sq_ge (ν 2)
  have hj' := noncentral_halfInteger_sq_ge (ν j) hj
  have hsum : (11 / 4 : ℝ) ≤ ∑ i : Fin 3, ((ν i : ℝ) + 1 / 2) ^ 2 := by
    fin_cases j <;> simp only [Fin.sum_univ_succ] <;> norm_num at hj' ⊢ <;> linarith
  have hnorm : ‖momentumVector (realMomentum (baseMomentum ν))‖ ^ 2 =
      Real.pi ^ 2 * ∑ i : Fin 3, ((ν i : ℝ) + 1 / 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [momentumVector, realMomentum, baseMomentum,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hnorm]
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg Real.pi)
  nlinarith [Real.pi_gt_three]

def backgroundAmplitude : ℝ := ((2 : ℝ) ^ 100)⁻¹

theorem backgroundAmplitude_pos : 0 < backgroundAmplitude := by
  unfold backgroundAmplitude
  positivity

theorem backgroundAmplitude_le : backgroundAmplitude ≤ 1 / 1024 := by
  norm_num [backgroundAmplitude]

def scaledMomentum (t : Momentum) : Momentum := fun j => (backgroundAmplitude : ℂ) * t j

/-- Total inverse energy, including the background `+7` shift. -/
def totalEnergy (e : ℂ) : ℂ := ((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) +
  (backgroundAmplitude : ℂ) * e

theorem scaledMomentum_norm_le (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖momentumVector (scaledMomentum t)‖ ≤ 1 / 10 := by
  have hcoord (j : Fin 3) : ‖scaledMomentum t j‖ ≤ 1 / 100 := by
    rw [scaledMomentum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos backgroundAmplitude_pos]
    have hprod := mul_le_mul backgroundAmplitude_le (ht j) (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1 / 1024)
    norm_num at hprod
    linarith
  have hsq (j : Fin 3) : ‖scaledMomentum t j‖ ^ 2 ≤ (1 / 10000 : ℝ) := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr (hcoord j)
    norm_num at h
    exact h
  have hnorm := EuclideanSpace.norm_sq_eq (momentumVector (scaledMomentum t))
  change ‖momentumVector (scaledMomentum t)‖ ^ 2 = ∑ j : Fin 3, ‖scaledMomentum t j‖ ^ 2 at hnorm
  norm_num [Fin.sum_univ_succ] at hnorm
  nlinarith [hsq 0, hsq 1, hsq 2, norm_nonneg (momentumVector (scaledMomentum t))]

theorem energy_perturbation_norm_le (e : ℂ) (he : ‖e‖ ≤ 8) :
    ‖(backgroundAmplitude : ℂ) * e‖ ≤ 1 / 100 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  have h := mul_le_mul backgroundAmplitude_le he (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 1024)
  norm_num at h
  linarith

/-- Every noncentral literal complex block is invertible with norm at most
`3/4` on the entire stated box, uniformly over the infinite alias lattice. -/
theorem noncentral_inverse_estimate (t : Momentum) (e : ℂ) (ν : Alias)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (hν : ¬IsCentralAlias ν) :
    totalEnergy e ≠ 0 ∧
      momentumSquare (aliasMomentum (scaledMomentum t) ν) - totalEnergy e ≠ 0 ∧
      ‖inverseBlock (aliasMomentum (scaledMomentum t) ν) (totalEnergy e)‖ ≤ 3 / 4 := by
  rw [aliasMomentum_decomposition]
  apply inverseBlock_coarse_noncentral
  · exact noncentral_base_norm_sq ν hν
  · exact scaledMomentum_norm_le t ht
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_lt_four, Real.pi_pos]
  · exact energy_perturbation_norm_le e he

theorem noncentral_inverse_norm_lt_one (t : Momentum) (e : ℂ) (ν : Alias)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (hν : ¬IsCentralAlias ν) :
    ‖inverseBlock (aliasMomentum (scaledMomentum t) ν) (totalEnergy e)‖ < 1 :=
  ((noncentral_inverse_estimate t e ν ht he hν).2.2).trans_lt (by norm_num)

abbrev NoncentralAlias := {ν : Alias // ¬IsCentralAlias ν}
abbrev NoncentralSpace := HilbertSum NoncentralAlias Polarization

def noncentralOperator (t : Momentum) (e : ℂ) : NoncentralSpace →ₗ.[ℂ] NoncentralSpace :=
  maximalOperator (fun ν => block (aliasMomentum (scaledMomentum t) ν.val) (totalEnergy e))

/-- The actual infinite noncentral inverse, with its maximal-domain range and
both inverse identities, obtained from the proved uniform estimate. -/
def noncentralInverseData (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    SelfAdjointResolvent.BoundedInverse (noncentralOperator t e) := by
  let B : NoncentralAlias → Polarization →L[ℂ] Polarization :=
    fun ν => block (aliasMomentum (scaledMomentum t) ν.val) (totalEnergy e)
  let R : NoncentralAlias → Polarization →L[ℂ] Polarization :=
    fun ν => inverseBlock (aliasMomentum (scaledMomentum t) ν.val) (totalEnergy e)
  have hR : ∀ ν, ‖R ν‖ ≤ (3 / 4 : ℝ) :=
    fun ν => (noncentral_inverse_estimate t e ν.val ht he ν.property).2.2
  have hBR : ∀ ν x, B ν (R ν x) = x := by
    intro ν
    exact block_inverseBlock _ _ (noncentral_inverse_estimate t e ν.val ht he ν.property).1
      (noncentral_inverse_estimate t e ν.val ht he ν.property).2.1
  have hRB : ∀ ν x, R ν (B ν x) = x := by
    intro ν
    exact inverseBlock_block _ _ (noncentral_inverse_estimate t e ν.val ht he ν.property).1
      (noncentral_inverse_estimate t e ν.val ht he ν.property).2.1
  have hC : (0 : ℝ) ≤ 3 / 4 := by norm_num
  change SelfAdjointResolvent.BoundedInverse (maximalOperator B)
  exact
    { map := boundedBlocks R hC hR
      mem_domain := boundedBlocks_mem_maximalDomain B R hC hR hBR
      apply_map := maximalOperator_boundedBlocks B R hC hR hBR
      map_apply := boundedBlocks_maximalOperator B R hC hR hRB }

theorem noncentralInverseData_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖(noncentralInverseData t e ht he).map‖ ≤ 3 / 4 := by
  dsimp only [noncentralInverseData]
  apply boundedBlocks_norm_le
  · norm_num
  · intro ν
    exact (noncentral_inverse_estimate t e ν.val ht he ν.property).2.2

end Maxwell.Continuum.FreeFiber
