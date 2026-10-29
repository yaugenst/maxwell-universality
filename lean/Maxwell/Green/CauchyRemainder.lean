import Maxwell.Green.Residue

/-! # A uniform contour representation of the regular pole remainder

The remainder is represented on a fixed normal circle, whose denominator is
separated from zero. This gives ordinary uniform derivative bounds without
assuming a joint moving-pole division theorem.
-/

noncomputable section

open Complex Metric Set

namespace Maxwell.Green

private theorem cauchy_division_algebra {C x y z J : ℂ} (hC : C ≠ 0) (hx : x ≠ 0)
    (h : C * (x * y) - C * z = x * J) : y = z / x + C⁻¹ * J := by
  field_simp
  linear_combination h

theorem analyticOnNhd_dslope {f : ℂ → ℂ} {s : Set ℂ} {p : ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hp : p ∈ s) : AnalyticOnNhd ℂ (dslope f p) s := by
  intro z hz
  by_cases heq : z = p
  · subst z
    exact analyticAt_dslope (hf p hp)
  · have hquot : AnalyticAt ℂ (fun z => (f z - f p) / (z - p)) z :=
      ((hf z hz).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr heq)
    apply hquot.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne f heq] with w hw
    simpa only [slope_def_field] using hw.symm

/-- On a disk containing only one simple zero, divided differences construct
a nonvanishing analytic denominator factor throughout the entire disk. -/
theorem simple_zero_factor_on_disk {D : ℂ → ℂ} {p center : ℂ} {R : ℝ}
    (hD : AnalyticOnNhd ℂ D (closedBall center R))
    (hp : p ∈ ball center R) (hDp : D p = 0) (hD' : deriv D p ≠ 0)
    (hzero : ∀ z ∈ closedBall center R, D z = 0 → z = p) :
    AnalyticOnNhd ℂ (dslope D p) (closedBall center R) ∧
      (∀ z ∈ closedBall center R, dslope D p z ≠ 0) ∧
      ∀ z, D z = (z - p) * dslope D p z := by
  refine ⟨analyticOnNhd_dslope hD (ball_subset_closedBall hp), ?_, ?_⟩
  · intro z hz
    by_cases heq : z = p
    · simpa only [heq, dslope_same] using hD'
    · rw [dslope_of_ne D heq, slope_def_field, hDp, sub_zero]
      exact div_ne_zero (fun h => heq (hzero z hz h)) (sub_ne_zero.mpr heq)
  · intro z
    simpa only [hDp, sub_zero, smul_eq_mul] using (sub_smul_dslope D p z).symm

/-- The regular remainder at a pole is a Cauchy integral on a fixed outer
circle. This representation is smooth in every parameter for which the
original numerator and denominator are smooth on that circle. -/
def normalCauchyRemainder (A D : ℂ → ℂ) (center : ℂ) (R : ℝ) (u : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    ∮ z in C(center, R), (z - u)⁻¹ * (A z / D z)

theorem simple_pole_cauchy_remainder {A D : ℂ → ℂ} {p center u : ℂ} {R : ℝ}
    (hA : AnalyticOnNhd ℂ A (closedBall center R))
    (hD : AnalyticOnNhd ℂ D (closedBall center R))
    (hp : p ∈ ball center R) (hu : u ∈ ball center R) (hup : u ≠ p)
    (hDp : D p = 0) (hD' : deriv D p ≠ 0)
    (hzero : ∀ z ∈ closedBall center R, D z = 0 → z = p) :
    A u / D u = (A p / deriv D p) / (u - p) + normalCauchyRemainder A D center R u := by
  obtain ⟨hd, hdne, hfactor⟩ := simple_zero_factor_on_disk hD hp hDp hD' hzero
  let B : ℂ → ℂ := fun z => A z / dslope D p z
  have hB : AnalyticOnNhd ℂ B (closedBall center R) := hA.div hd hdne
  have hR : 0 < R := dist_nonneg.trans_lt hp
  have hzp (z : ℂ) (hz : z ∈ sphere center R) : z ≠ p := by
    intro h
    subst z
    exact (ne_of_lt hp) hz
  have hzu (z : ℂ) (hz : z ∈ sphere center R) : z ≠ u := by
    intro h
    subst z
    exact (ne_of_lt hu) hz
  have hcu : CircleIntegrable (fun z => (z - u)⁻¹ * B z) center R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => sub_ne_zero.mpr (hzu z hz))).mul (hB.continuousOn.mono sphere_subset_closedBall)
  have hcp : CircleIntegrable (fun z => (z - p)⁻¹ * B z) center R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => sub_ne_zero.mpr (hzp z hz))).mul (hB.continuousOn.mono sphere_subset_closedBall)
  have heq : (∮ z in C(center, R), (z - u)⁻¹ * B z - (z - p)⁻¹ * B z) =
      (u - p) * ∮ z in C(center, R), (z - u)⁻¹ * (A z / D z) := by
    change _ = (u - p) • ∮ z in C(center, R), (z - u)⁻¹ * (A z / D z)
    rw [← circleIntegral.integral_smul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    change _ = (u - p) * ((z - u)⁻¹ * (A z / D z))
    rw [hfactor z]
    dsimp [B]
    field_simp [sub_ne_zero.mpr (hzu z hz), sub_ne_zero.mpr (hzp z hz),
      hdne z (sphere_subset_closedBall hz)]
    ring
  rw [circleIntegral.integral_sub hcu hcp] at heq
  have huB := hB.differentiableOn.circleIntegral_sub_inv_smul hu
  have hpB := hB.differentiableOn.circleIntegral_sub_inv_smul hp
  simp only [smul_eq_mul] at huB hpB
  rw [huB, hpB] at heq
  have hfacu := hfactor u
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hBp : B p = A p / deriv D p := by simp only [B, dslope_same]
  have hBu : B u = (u - p) * (A u / D u) := by
    rw [hfacu]
    dsimp [B]
    field_simp
  rw [hBp, hBu] at heq
  exact cauchy_division_algebra hC (sub_ne_zero.mpr hup) heq

/-- The normalized Cauchy kernels used to differentiate the regular part. -/
def cauchyTerm (f : ℂ → ℂ) (n : ℕ) (center : ℂ) (R : ℝ) (u : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    ∮ z in C(center, R), (z - u) ^ (-(n + 1 : ℕ) : ℤ) * f z

theorem cauchyTerm_zero (A D : ℂ → ℂ) (center : ℂ) (R : ℝ) :
    cauchyTerm (fun z => A z / D z) 0 center R = normalCauchyRemainder A D center R := by
  ext u
  simp only [cauchyTerm, normalCauchyRemainder, Nat.zero_add, Nat.cast_one, zpow_neg_one]

/-- All normal derivatives of the regular part follow from differentiation
of the nonsingular outer-circle kernel. -/
theorem hasDerivAt_cauchyTerm (f : ℂ → ℂ) (n : ℕ) {center u : ℂ} {R : ℝ}
    (hf : CircleIntegrable f center R) (hu : u ∉ sphere center |R|) :
    HasDerivAt (cauchyTerm f n center R)
      ((n + 1 : ℕ) * cauchyTerm f (n + 1) center R u) u := by
  have h := (hasDerivAt_circleIntegral_sub_zpow_smul (n := -(n + 1 : ℕ)) hf hu).const_mul
    (2 * Real.pi * I : ℂ)⁻¹
  convert h using 1
  · rfl
  · simp only [cauchyTerm, smul_eq_mul]
    have he : (-(n + 1 : ℕ) : ℤ) - 1 = -(n + 1 + 1 : ℕ) := by omega
    rw [he]
    push_cast
    ring

/-- The Cauchy regular part is analytic in the full disk, including the
moving pole itself. -/
theorem analyticAt_cauchyTerm (f : ℂ → ℂ) (n : ℕ) {center u : ℂ} {R : ℝ}
    (hf : CircleIntegrable f center R) (hu : u ∉ sphere center |R|) :
    AnalyticAt ℂ (cauchyTerm f n center R) u := by
  apply DifferentiableOn.analyticAt (s := (sphere center |R|)ᶜ)
    (fun z hz => (hasDerivAt_cauchyTerm f n hf hz).differentiableAt.differentiableWithinAt)
  exact isClosed_sphere.isOpen_compl.mem_nhds hu

theorem circle_sub_norm_lower {center u z : ℂ} {R : ℝ}
    (hu : ‖u - center‖ ≤ R / 2) (hz : z ∈ sphere center R) :
    R / 2 ≤ ‖z - u‖ := by
  have h := norm_sub_norm_le (z - center) (u - center)
  have hzc : ‖z - center‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  rw [hzc] at h
  have he : z - center - (u - center) = z - u := by ring
  rw [he] at h
  linarith

/-- A uniform boundary bound gives explicit uniform bounds for every normal
Cauchy derivative kernel throughout the half-radius disk. -/
theorem norm_cauchyTerm_le (f : ℂ → ℂ) (n : ℕ) {center u : ℂ} {R M : ℝ}
    (hR : 0 < R) (hu : ‖u - center‖ ≤ R / 2)
    (hf : ∀ z ∈ sphere center R, ‖f z‖ ≤ M) :
    ‖cauchyTerm f n center R u‖ ≤ R * ((2 / R) ^ (n + 1) * M) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
  intro z hz
  rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
  have hlow := circle_sub_norm_lower hu hz
  have hinv : ‖z - u‖⁻¹ ≤ 2 / R := by
    calc
      ‖z - u‖⁻¹ ≤ (R / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 / R := by ring
  rw [← inv_pow]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv _)
    (hf z hz) (norm_nonneg _) (by positivity)

end Maxwell.Green
