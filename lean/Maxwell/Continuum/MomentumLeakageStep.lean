import Maxwell.Continuum.MomentumLeakageCross

/-! One exact nested-cutoff step for the literal auxiliary equation.
Both the high-input contraction and low-input leakage constants are
obtained from the actual finite well and periodic Maxwell inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open Bloch PeriodicBand

attribute [local irreducible] Bloch.unitary highMomentumProjection Auxiliary.resolvent

variable {h z σ : ℝ} (D : Calibration h z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)

theorem resolvent_high_apply_norm {r : ℝ} (hr : smallRadius/4 ≤ r) (f : FieldL2) :
    ‖resolvent D hσ0 hσ (highMomentumProjection r f)‖ ≤
      (2 : ℝ)^192 * ‖highMomentumProjection r f‖ := by
  have hi : highMomentumProjection r (highMomentumProjection r f) = highMomentumProjection r f :=
    congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (highMomentumProjection_idempotent r)
  have hc := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T (highMomentumProjection r f))
    (highMomentumProjection_resolvent D hσ0 hσ r)
  change highMomentumProjection r (resolvent D hσ0 hσ (highMomentumProjection r f)) =
    resolvent D hσ0 hσ (highMomentumProjection r (highMomentumProjection r f)) at hc
  rw [hi] at hc
  rw [← hc]
  exact (highMomentumProjection r * resolvent D hσ0 hσ).le_of_opNorm_le
    (highMomentumProjection_resolvent_norm_le D hσ0 hσ hr) _

theorem equation_projection_step (W : FieldL2 →L[ℂ] FieldL2) (f g : FieldL2)
    (heq : f = g + W (resolvent D hσ0 hσ f)) (s r : ℝ)
    (hr : smallRadius/4 ≤ r) :
    ‖highMomentumProjection s f‖ ≤ ‖highMomentumProjection s g‖ +
      (‖W‖*(2 : ℝ)^192) * ‖highMomentumProjection r f‖ +
      (‖highMomentumProjection s * W * lowMomentumProjection r‖ * (4*(h^2)⁻¹)) * ‖f‖ := by
  have hc := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f)
    (highMomentumProjection_resolvent D hσ0 hσ r)
  change highMomentumProjection r (resolvent D hσ0 hσ f) =
    resolvent D hσ0 hσ (highMomentumProjection r f) at hc
  have he : highMomentumProjection s f = highMomentumProjection s g +
      highMomentumProjection s (W (resolvent D hσ0 hσ (highMomentumProjection r f))) +
      (highMomentumProjection s * W * lowMomentumProjection r) (resolvent D hσ0 hσ f) := by
    have hp := congrArg (fun u => highMomentumProjection s u) heq
    rw [map_add] at hp
    rw [hp]
    change highMomentumProjection s g + highMomentumProjection s (W (resolvent D hσ0 hσ f)) =
      highMomentumProjection s g + highMomentumProjection s (W (resolvent D hσ0 hσ (highMomentumProjection r f))) +
      highMomentumProjection s (W (resolvent D hσ0 hσ f-highMomentumProjection r (resolvent D hσ0 hσ f)))
    rw [map_sub, map_sub, hc]
    abel
  have hh := (highMomentumProjection s).le_of_opNorm_le (highMomentumProjection_norm_le s)
    (W (resolvent D hσ0 hσ (highMomentumProjection r f)))
  rw [one_mul] at hh
  have hhigh : ‖highMomentumProjection s (W (resolvent D hσ0 hσ (highMomentumProjection r f)))‖ ≤
      (‖W‖*(2 : ℝ)^192) * ‖highMomentumProjection r f‖ := by
    calc
      _ ≤ ‖W‖ * ‖resolvent D hσ0 hσ (highMomentumProjection r f)‖ := hh.trans (W.le_opNorm _)
      _ ≤ ‖W‖ * ((2 : ℝ)^192 * ‖highMomentumProjection r f‖) :=
        mul_le_mul_of_nonneg_left (resolvent_high_apply_norm D hσ0 hσ hr f) (norm_nonneg _)
      _ = _ := by ring
  have hlow : ‖(highMomentumProjection s * W * lowMomentumProjection r) (resolvent D hσ0 hσ f)‖ ≤
      (‖highMomentumProjection s * W * lowMomentumProjection r‖ * (4*(h^2)⁻¹)) * ‖f‖ := by
    calc
      _ ≤ ‖highMomentumProjection s * W * lowMomentumProjection r‖ * ‖resolvent D hσ0 hσ f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖highMomentumProjection s * W * lowMomentumProjection r‖ * ((4*(h^2)⁻¹)*‖f‖) :=
        mul_le_mul_of_nonneg_left
          ((resolvent D hσ0 hσ).le_of_opNorm_le (resolvent_norm_le D hσ0 hσ) f) (norm_nonneg _)
      _ = _ := by ring
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl hhigh)) hlow)

variable {ι : Type*} [Fintype ι]

theorem finiteWell_projection_step (hh : h ≤ 1/(2 : ℝ)^1024)
    (x : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*h^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (x i) h⁻¹) (Metric.ball (x j) h⁻¹))
    (f g : FieldL2) (heq : f = g + finiteWellOperator h x v (resolvent D hσ0 hσ f))
    (s r : ℝ) (hr : smallRadius/4 ≤ r) :
    ‖highMomentumProjection s f‖ ≤ ‖highMomentumProjection s g‖ +
      (1/4 : ℝ) * ‖highMomentumProjection r f‖ +
      ((2 : ℝ)^232 * (Fintype.card ι : ℝ) * Real.exp (-Real.sqrt ((s-r)/h)/512)) * ‖f‖ := by
  have hW := finiteWellOperator_norm_le D.h_pos (by positivity : 0 ≤ (2 : ℝ)^130*h^2)
    x v hv0 hv hdisj
  have hsmall : ((2 : ℝ)^130*h^2) * (2 : ℝ)^192 ≤ 1/4 := by
    have hs : h^2 ≤ (1/(2 : ℝ)^1024)^2 :=
      (sq_le_sq₀ D.h_pos.le (by positivity)).mpr hh
    calc
      _ ≤ ((2 : ℝ)^130*(1/(2 : ℝ)^1024)^2) * (2 : ℝ)^192 := by gcongr
      _ ≤ _ := by norm_num
  have hhigh : ‖finiteWellOperator h x v‖*(2 : ℝ)^192 ≤ 1/4 :=
    (mul_le_mul_of_nonneg_right hW (by positivity)).trans hsmall
  have hcross := finiteWell_cross_norm D.h_pos x v hv0 hv s r
  have hlow : ‖highMomentumProjection s * finiteWellOperator h x v * lowMomentumProjection r‖ *
      (4*(h^2)⁻¹) ≤ (2 : ℝ)^232 * (Fintype.card ι : ℝ) * Real.exp (-Real.sqrt ((s-r)/h)/512) := by
    calc
      _ ≤ ((2 : ℝ)^100 * (Fintype.card ι : ℝ) * ((2 : ℝ)^130*h^2) *
          Real.exp (-Real.sqrt ((s-r)/h)/512)) * (4*(h^2)⁻¹) :=
        mul_le_mul_of_nonneg_right hcross (by positivity)
      _ = _ := by field_simp [D.h_pos.ne']; ring
  exact (equation_projection_step D hσ0 hσ (finiteWellOperator h x v) f g heq s r hr).trans
    (add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hhigh (norm_nonneg _)))
      (mul_le_mul_of_nonneg_right hlow (norm_nonneg _)))

#print axioms finiteWell_projection_step

end Maxwell.Continuum.Auxiliary
