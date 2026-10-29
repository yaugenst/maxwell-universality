import Maxwell.Continuum.RankOneBandComparison
import Maxwell.Continuum.RankOneBandInverseBounds

/-! Rescaling an actual isolated top eigenvector to the proved rank-one
Schur construction. The bounded perturbation need not be compact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.TopEigenPerturbation

open Set Metric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Data (A : H →L[ℂ] H) (u : H) (mu d : ℝ) : Prop where
  unit_norm : ‖u‖ = 1
  symmetric : A.IsSymmetric
  eigenvector : A u = (mu : ℂ) • u
  gap_pos : 0 < d
  gap_le_mu : d ≤ mu
  complement : ∀ x : H, inner ℂ u x = 0 → ‖A x‖ ≤ (mu - d) * ‖x‖

def scale (d : ℝ) : ℝ := 20 * d

def base (A : H →L[ℂ] H) (mu d : ℝ) : H →L[ℂ] H :=
  ((scale d)⁻¹ : ℂ) • (A - (mu : ℂ) • 1)

def perturbation (E : H →L[ℂ] H) (d : ℝ) : H →L[ℂ] H := ((scale d)⁻¹ : ℂ) • E

def family (E : H →L[ℂ] H) (d : ℝ) (_ : Unit) (_ : ℂ) : H →L[ℂ] H := perturbation E d

namespace Data

variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

omit [CompleteSpace H] in
theorem scale_pos : 0 < scale d := by unfold scale; linarith [D.gap_pos]

omit [CompleteSpace H] in
theorem complement_energy (x : H) (hx : inner ℂ u x = 0) :
    (inner ℂ x (A x)).re ≤ (mu - d) * ‖x‖ ^ 2 := by
  change RCLike.re (inner ℂ x (A x)) ≤ _
  calc
    _ ≤ ‖x‖ * ‖A x‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖x‖ * ((mu - d) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (D.complement x hx) (norm_nonneg _)
    _ = _ := by ring

omit D [CompleteSpace H] in
theorem base_energy (x : H) :
    (inner ℂ x ((0 : ℂ) • x - base A mu d x)).re =
      (mu * ‖x‖ ^ 2 - (inner ℂ x (A x)).re) / scale d := by
  simp only [base, zero_smul, zero_sub, smul_apply, sub_apply, one_apply_eq_self,
    inner_neg_right, inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow]
  change (-((scale d : ℂ)⁻¹ * (inner ℂ x (A x) - (mu : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ)))).re = _
  simp only [← Complex.ofReal_inv, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
  ring

theorem rankData : RankOneBand.Data (base A mu d) u 0 where
  unit_norm := D.unit_norm
  symmetric := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    unfold base
    exact (show IsSelfAdjoint ((scale d : ℂ)⁻¹) by simp [IsSelfAdjoint]).smul
      (D.symmetric.isSelfAdjoint.sub
        ((show IsSelfAdjoint (mu : ℂ) by simp [IsSelfAdjoint]).smul
          (show IsSelfAdjoint (1 : H →L[ℂ] H) by simp [IsSelfAdjoint])))
  eigenvector := by simp [base, smul_apply, sub_apply, D.eigenvector]
  gap := by
    intro x hx
    simp only [Complex.ofReal_zero]
    rw [base_energy]
    apply (le_div_iff₀ D.scale_pos).mpr
    have h := D.complement_energy x hx
    unfold scale
    nlinarith

omit [CompleteSpace H] in
theorem perturbation_norm (E : H →L[ℂ] H) :
    ‖perturbation E d‖ = ‖E‖ / scale d := by
  rw [perturbation, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg D.scale_pos.le, div_eq_mul_inv, mul_comm]

omit [CompleteSpace H] in
theorem perturbation_small (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖perturbation E d‖ ≤ 1 / 256 := by
  rw [D.perturbation_norm]
  apply (div_le_iff₀ D.scale_pos).mpr
  unfold scale
  linarith [D.gap_pos]

omit [CompleteSpace H] in
theorem perturbationData (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    RankOneBand.PerturbationData (family E d) Set.univ 0 where
  small := fun _ _ _ _ => D.perturbation_small E hE
  energy_lipschitz := by
    intro p _
    apply LipschitzOnWith.of_dist_le_mul
    intro e _ f _
    simp only [family, dist_self]
    positivity

omit [CompleteSpace H] in
theorem zeroData : RankOneBand.PerturbationData (family (0 : H →L[ℂ] H) d) Set.univ 0 :=
  D.perturbationData 0 (by simpa using div_nonneg D.gap_pos.le (by norm_num : (0 : ℝ) ≤ 64))

def root (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) : ℂ :=
  D.rankData.bandRoot (D.perturbationData E hE) ()

def rawVector (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) : H :=
  D.rankData.bandVector (D.perturbationData E hE) ()

def eigenvalue (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) : ℂ :=
  (mu : ℂ) + (scale d : ℂ) * D.root E hE

theorem root_mem (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    D.root E hE ∈ closedBall (0 : ℂ) (1 / 100) :=
  D.rankData.bandRoot_mem (D.perturbationData E hE) () (Set.mem_univ ())

theorem root_norm (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖D.root E hE‖ ≤ 1 / 200 := by
  simpa only [root, Complex.ofReal_zero, sub_zero] using
    D.rankData.bandRoot_center_bound (D.perturbationData E hE) () (Set.mem_univ ())

theorem rawVector_ne_zero (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    D.rawVector E hE ≠ 0 :=
  D.rankData.bandVector_ne_zero (D.perturbationData E hE) ()

theorem rawVector_error (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) :
    ‖D.rawVector E hE - u‖ ≤ 2 * ‖E‖ / d := by
  have hr : ‖D.root E hE - (0 : ℂ)‖ ≤ 1 / 100 := by
    simpa only [mem_closedBall, dist_eq_norm] using D.root_mem E hE
  have h := D.rankData.correctionVector_norm_le (perturbation E d) (D.root E hE)
    (D.perturbation_small E hE) hr
  change ‖RankOneBand.correctionVector (base A mu d) u 0 (perturbation E d) (D.root E hE)‖ ≤ _ at h
  have hv : D.rawVector E hE - u =
      RankOneBand.correctionVector (base A mu d) u 0 (perturbation E d) (D.root E hE) := by
    simp only [rawVector, RankOneBand.Data.bandVector, RankOneBand.eigenvectorLift,
      family, add_sub_cancel_left, root]
  rw [hv]
  apply h.trans_eq
  rw [D.perturbation_norm]
  unfold scale
  field_simp
  ring

end Data
end Maxwell.Continuum.TopEigenPerturbation
