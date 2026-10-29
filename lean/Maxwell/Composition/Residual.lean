import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative residual propagation for finite physical composition

These statements use the genuine norm of continuous linear maps.  They are
dimension-independent and apply in particular to the Euclidean spaces in the
source and target interfaces.  The exact physical Schur identity and the
spectral bounds are explicit modular inputs where they are used; they are not
replaced by a hypothesis asserting the final realization theorem.
-/

namespace Maxwell.Composition

section Residual

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] in
/-- The implemented source is compared to the ideal source before any
solver residual is propagated. -/
theorem emitted_source_norm (fhat fstar : E) (bound error : ℝ)
    (hstar : ‖fstar‖ ≤ bound) (herror : ‖fhat - fstar‖ ≤ error) :
    ‖fhat‖ ≤ bound + error := by
  calc
    ‖fhat‖ = ‖fstar + (fhat - fstar)‖ := by congr 1; abel
    _ ≤ ‖fstar‖ + ‖fhat - fstar‖ := norm_add_le _ _
    _ ≤ bound + error := add_le_add hstar herror

/-- An arbitrary residual for the emitted source gives a residual for the
ideal source, including the full source-vector calibration/rounding error. -/
theorem emitted_to_ideal_residual (A : E →L[ℝ] E) (y fhat fstar : E)
    (solverError sourceError : ℝ)
    (hsolver : ‖A y - fhat‖ ≤ solverError)
    (hsource : ‖fhat - fstar‖ ≤ sourceError) :
    ‖A y - fstar‖ ≤ solverError + sourceError := by
  calc
    ‖A y - fstar‖ = ‖(A y - fhat) + (fhat - fstar)‖ := by congr 1; abel
    _ ≤ ‖A y - fhat‖ + ‖fhat - fstar‖ := norm_add_le _ _
    _ ≤ solverError + sourceError := add_le_add hsolver hsource

/-- Propagate a residual through an actual bounded linear map. -/
theorem residual_map_bound (R : E →L[ℝ] F) (r : E)
    (mapBound residualBound : ℝ) (hmap : ‖R‖ ≤ mapBound)
    (hres : ‖r‖ ≤ residualBound) :
    ‖R r‖ ≤ mapBound * residualBound := by
  have hmap0 : 0 ≤ mapBound := (norm_nonneg R).trans hmap
  exact (R.le_opNorm r).trans
    (mul_le_mul hmap hres (norm_nonneg r) hmap0)

/-- A perturbation of the actual operator acts on the actual recovered
vector; auxiliary components are not assumed to vanish. -/
theorem operator_perturbation_residual (S T : E →L[ℝ] F) (z : E) (g : F)
    (residualBound perturbationBound vectorBound : ℝ)
    (hres : ‖S z - g‖ ≤ residualBound)
    (hpert : ‖S - T‖ ≤ perturbationBound)
    (hvec : ‖z‖ ≤ vectorBound) :
    ‖T z - g‖ ≤ residualBound + perturbationBound * vectorBound := by
  have herror : ‖(S - T) z‖ ≤ perturbationBound * vectorBound :=
    residual_map_bound (S - T) z perturbationBound vectorBound hpert hvec
  calc
    ‖T z - g‖ = ‖(S z - g) - (S - T) z‖ := by
      congr 1
      simp only [sub_apply]
      abel
    _ ≤ ‖S z - g‖ + ‖(S - T) z‖ := norm_sub_le _ _
    _ ≤ residualBound + perturbationBound * vectorBound := add_le_add hres herror

/-- Calibration and finite coordinate arithmetic perturb the readout in
the norm of the full vector, rather than independently per defect. -/
theorem readout_residual (Γ : E →L[ℝ] F) (z zhat : E) (g : F)
    (residualBound mapBound readoutError : ℝ)
    (hres : ‖Γ z - g‖ ≤ residualBound)
    (hmap : ‖Γ‖ ≤ mapBound) (hread : ‖zhat - z‖ ≤ readoutError) :
    ‖Γ zhat - g‖ ≤ residualBound + mapBound * readoutError := by
  have herr : ‖Γ (zhat - z)‖ ≤ mapBound * readoutError :=
    residual_map_bound Γ (zhat - z) mapBound readoutError hmap hread
  calc
    ‖Γ zhat - g‖ = ‖(Γ z - g) + Γ (zhat - z)‖ := by
      congr 1
      rw [map_sub]
      abel
    _ ≤ ‖Γ z - g‖ + ‖Γ (zhat - z)‖ := norm_add_le _ _
    _ ≤ residualBound + mapBound * readoutError := add_le_add hres herr

/-- The difference of two implemented linear readouts is controlled by
the operator norm of their difference and the full physical field norm. -/
theorem calibrated_readout_error (D Dhat : E →L[ℝ] F) (y : E)
    (calibrationError fieldBound : ℝ)
    (hcal : ‖Dhat - D‖ ≤ calibrationError) (hy : ‖y‖ ≤ fieldBound) :
    ‖Dhat y - D y‖ ≤ calibrationError * fieldBound := by
  simpa only [sub_apply] using
    residual_map_bound (Dhat - D) y calibrationError fieldBound hcal hy

/-- Calibration of a source injection is measured before applying the
actual finite background operator. -/
theorem calibrated_source_error (K : E →L[ℝ] F) (I Ihat : G →L[ℝ] E)
    (g : G) (operatorBound calibrationError sourceBound : ℝ)
    (hK : ‖K‖ ≤ operatorBound) (hI : ‖Ihat - I‖ ≤ calibrationError)
    (hg : ‖g‖ ≤ sourceBound) :
    ‖K (Ihat g) - K (I g)‖ ≤
      operatorBound * (calibrationError * sourceBound) := by
  rw [← map_sub]
  exact residual_map_bound K (Ihat g - I g) operatorBound
    (calibrationError * sourceBound) hK
    (calibrated_readout_error I Ihat g calibrationError sourceBound hI hg)

/-- A bound on the inverse controls every residual solution, without
requiring the solver to choose a preferred representative. -/
theorem amplitude_of_residual (S : E ≃L[ℝ] E) (z target : E)
    (inverseBound sourceBound residualBound : ℝ)
    (hInv : ‖(S.symm : E →L[ℝ] E)‖ ≤ inverseBound)
    (hsource : ‖target‖ ≤ sourceBound)
    (hres : ‖S z - target‖ ≤ residualBound) :
    ‖z‖ ≤ inverseBound * (sourceBound + residualBound) := by
  have hSz : ‖S z‖ ≤ sourceBound + residualBound :=
    emitted_source_norm (S z) target sourceBound residualBound hsource hres
  simpa only [ContinuousLinearEquiv.coe_apply, S.symm_apply_apply] using
    residual_map_bound (S.symm : E →L[ℝ] E) (S z) inverseBound
      (sourceBound + residualBound) hInv hSz

end Residual

section PaperConstants

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The paper's actual source and physical tolerance imply its ideal-source
residual bound. Positivity is needed only for the explicitly used scales. -/
theorem physical_residual_budget
    (A : E →L[ℝ] E) (y fhat fstar : E)
    (α ε G J cW L : ℝ) (hε : 0 ≤ ε)
    (hJ : 0 < J) (hcW : 0 < cW) (hL : 0 < L)
    (hsourceNorm : ‖fhat‖ ≤ 2 * α * J * cW * G)
    (hsourceError : ‖fhat - fstar‖ ≤ α * ε * G / (8192 * L))
    (hsolver : ‖A y - fhat‖ ≤ (ε / (8192 * J * cW * L)) * ‖fhat‖) :
    ‖A y - fstar‖ ≤ 3 * α * ε * G / (8192 * L) := by
  have hdelta : 0 ≤ ε / (8192 * J * cW * L) := by positivity
  have hscaled : ‖A y - fhat‖ ≤ 2 * α * ε * G / (8192 * L) := by
    calc
      ‖A y - fhat‖ ≤ (ε / (8192 * J * cW * L)) * ‖fhat‖ := hsolver
      _ ≤ (ε / (8192 * J * cW * L)) * (2 * α * J * cW * G) :=
        mul_le_mul_of_nonneg_left hsourceNorm hdelta
      _ = 2 * α * ε * G / (8192 * L) := by
        field_simp
  calc
    ‖A y - fstar‖ ≤ 2 * α * ε * G / (8192 * L) + α * ε * G / (8192 * L) :=
      emitted_to_ideal_residual A y fhat fstar _ _ hscaled hsourceError
    _ = 3 * α * ε * G / (8192 * L) := by ring

/-- Application of the physical Schur residual multiplier at the paper's
chosen tolerance. The exact residual identity must be supplied separately. -/
theorem bright_residual_budget (R : E →L[ℝ] F) (r : E)
    (α ε G L : ℝ) (hL : 0 < L)
    (hR : ‖R‖ ≤ 2 * L)
    (hr : ‖r‖ ≤ 3 * α * ε * G / (8192 * L)) :
    ‖R r‖ ≤ 3 * α * ε * G / 4096 := by
  calc
    ‖R r‖ ≤ (2 * L) * (3 * α * ε * G / (8192 * L)) :=
      residual_map_bound R r _ _ hR hr
    _ = 3 * α * ε * G / 4096 := by field_simp; ring

/-- The explicit 33 Kbar G bound used for the actual bright amplitudes. -/
theorem bright_amplitude_budget (S : E ≃L[ℝ] E) (z g : E)
    (α ε G K : ℝ) (hα : 0 < α) (hε : ε ≤ 1 / 2)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hg : ‖g‖ ≤ G)
    (hInv : ‖(S.symm : E →L[ℝ] E)‖ ≤ 32 * K / α)
    (hres : ‖S z - α • g‖ ≤ 3 * α * ε * G / 4096) :
    ‖z‖ ≤ 33 * K * G := by
  have htarget : ‖α • g‖ ≤ α * G := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
    exact mul_le_mul_of_nonneg_left hg hα.le
  have hbound := amplitude_of_residual S z (α • g) (32 * K / α)
    (α * G) (3 * α * ε * G / 4096) hInv htarget hres
  have heq : (32 * K / α) * (α * G + 3 * α * ε * G / 4096) =
      32 * K * G + (3 / 128) * ε * (K * G) := by field_simp; ring
  rw [heq] at hbound
  have hscaled := mul_le_mul_of_nonneg_right hε (mul_nonneg hK hG)
  nlinarith [mul_nonneg hK hG]

/-- The actual bright-block perturbation and actual bright-vector bound
produce the target residual, with the manuscript's constants. -/
theorem target_residual_budget (S T : E →L[ℝ] F) (z : E) (g : F)
    (α ε G K : ℝ) (hK : 0 < K)
    (hres : ‖S z - g‖ ≤ 3 * α * ε * G / 4096)
    (hpert : ‖S - T‖ ≤ α * ε / (4096 * K))
    (hz : ‖z‖ ≤ 33 * K * G) :
    ‖T z - g‖ ≤ 36 * α * ε * G / 4096 := by
  calc
    ‖T z - g‖ ≤ 3 * α * ε * G / 4096 +
        (α * ε / (4096 * K)) * (33 * K * G) :=
      operator_perturbation_residual S T z g _ _ _ hres hpert hz
    _ = 36 * α * ε * G / 4096 := by field_simp; ring

/-- Combining ideal logical residual and all calibration/access errors
gives exactly the conservative coefficient 141/1024. -/
theorem computed_logical_residual_budget (Γ : E →L[ℝ] F)
    (z zhat : E) (g : F) (ε G : ℝ)
    (hres : ‖Γ z - g‖ ≤ ε * G / 16)
    (hΓ : ‖Γ‖ ≤ 7) (hread : ‖zhat - z‖ ≤ 11 * ε * G / 1024) :
    ‖Γ zhat - g‖ ≤ 141 * ε * G / 1024 := by
  calc
    ‖Γ zhat - g‖ ≤ ε * G / 16 + 7 * (11 * ε * G / 1024) :=
      readout_residual Γ z zhat g _ _ _ hres hΓ hread
    _ = 141 * ε * G / 1024 := by ring

theorem computed_logical_residual_below_half (Γ : E →L[ℝ] F)
    (z zhat : E) (g : F) (ε G : ℝ) (hεG : 0 < ε * G)
    (hres : ‖Γ z - g‖ ≤ ε * G / 16)
    (hΓ : ‖Γ‖ ≤ 7) (hread : ‖zhat - z‖ ≤ 11 * ε * G / 1024) :
    ‖Γ zhat - g‖ < ε * G / 2 := by
  have h := computed_logical_residual_budget Γ z zhat g ε G hres hΓ hread
  nlinarith

end PaperConstants

end Maxwell.Composition
