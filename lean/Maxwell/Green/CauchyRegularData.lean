import Maxwell.Green.CauchyCutoff
import Maxwell.Green.ScalarAsymptotic

/-! Construction of regular normal data from the actual outer-circle
Cauchy remainder. Parameter measurability and joint integrability are
conclusions, obtained from the original boundary function and cutoffs. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Complex Metric Set
open scoped Topology ContDiff

/-- Joint measurability of the outer-circle Cauchy kernels follows directly
from joint measurability of their boundary data. -/
theorem measurable_cauchyTerm_joint (f : ℂ → ℂ → ℂ)
    (hf : Measurable (Function.uncurry f)) (n : ℕ) (center : ℂ) (R : ℝ) :
    Measurable (fun x : ℂ × ℂ => cauchyTerm (f x.1) n center R x.2) := by
  have hm : Measurable (fun x : (ℂ × ℂ) × ℝ =>
      (circleMap 0 R x.2 * I) *
        ((circleMap center R x.2 - x.1.2) ^ (-(n + 1 : ℕ) : ℤ) *
          f x.1.1 (circleMap center R x.2))) := by
    have hf' : Measurable (fun x : (ℂ × ℂ) × ℝ => f x.1.1 (circleMap center R x.2)) := hf.comp
      (measurable_fst.fst.prodMk ((measurable_circleMap center R).comp measurable_snd))
    have hc := measurable_circleMap center R
    have hc₀ := measurable_circleMap 0 R
    fun_prop
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc 0 (2 * Real.pi)))
  have he (x : ℂ × ℂ) : cauchyTerm (f x.1) n center R x.2 =
      (2 * Real.pi * I : ℂ)⁻¹ * ∫ θ in Icc 0 (2 * Real.pi),
        (circleMap 0 R θ * I) * ((circleMap center R θ - x.2) ^ (-(n + 1 : ℕ) : ℤ) *
          f x.1 (circleMap center R θ)) := by
    rw [cauchyTerm, circleIntegral_def_Icc]
    simp only [deriv_circleMap, smul_eq_mul]
  simpa only [he] using hi.measurable.const_mul (2 * Real.pi * I : ℂ)⁻¹

theorem measurable_cauchyTerm_real_joint (f : ℂ → ℂ → ℂ)
    (hf : Measurable (Function.uncurry f)) (n : ℕ) (center : ℂ) (R : ℝ) :
    Measurable (fun x : ℂ × ℝ => cauchyTerm (f x.1) n center R x.2) := by
  have hm : Measurable (fun x : ℂ × ℝ => (x.1, (x.2 : ℂ))) :=
    measurable_fst.prodMk measurable_snd.complex_ofReal
  simpa only [Function.comp_def] using
    (measurable_cauchyTerm_joint f hf n center R).comp hm

theorem cauchyTerm_const_mul (a : ℂ) (f : ℂ → ℂ) (n : ℕ)
    (center : ℂ) (R : ℝ) (u : ℂ) :
    cauchyTerm (fun z => a * f z) n center R u = a * cauchyTerm f n center R u := by
  unfold cauchyTerm
  simp_rw [show ∀ z : ℂ, (z - u) ^ (-(n + 1 : ℕ) : ℤ) * (a * f z) =
    a * ((z - u) ^ (-(n + 1 : ℕ) : ℤ) * f z) by intro z; ring]
  rw [circleIntegral.integral_const_mul]
  ring

/-- Measurability and an ordinary boundary bound imply circle integrability;
it need not be supplied as a separate analytic-remainder assumption. -/
theorem circleIntegrable_of_measurable_bound (f : ℂ → ℂ) (hf : Measurable f)
    {center : ℂ} {R M : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z ∈ sphere center R, ‖f z‖ ≤ M) : CircleIntegrable f center R := by
  apply (intervalIntegrable_const (a := (0 : ℝ)) (b := 2 * Real.pi) (c := M)).mono_fun'
    (hf.comp (measurable_circleMap center R)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  exact hb _ (circleMap_mem_sphere center hR θ)

/-- A compactly supported, bounded, jointly measurable function is jointly
integrable; this is applied to the explicit second Cauchy derivative. -/
theorem integrable_joint_of_compact_bound (g : ℂ × ℝ → ℂ)
    (s : Set (ℂ × ℝ)) (hs : IsCompact s) (hm : Measurable g) (C : ℝ)
    (hzero : ∀ x ∉ s, g x = 0) (hb : ∀ x ∈ s, ‖g x‖ ≤ C) : Integrable g := by
  have hsupport : Function.support g ⊆ s := by
    intro x hx
    by_contra h
    exact hx (hzero x h)
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply (integrableOn_const (μ := volume) (s := s) (C := C) hs.measure_ne_top).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
  exact hb x hx

theorem scaledPoleCutoff_complex_contDiff (ρ : ℝ) :
    ContDiff ℝ ∞ (fun u : ℝ => (scaledPoleCutoff ρ u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (unitPoleCutoff_contDiff.comp (contDiff_id.div_const ρ))

theorem scaledPoleCutoff_complex_tsupport {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (fun u : ℝ => (scaledPoleCutoff ρ u : ℂ)) ⊆ closedBall 0 (2 * ρ) := by
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  by_contra h
  have he : scaledPoleCutoff ρ u = 0 := scaledPoleCutoff_eq_zero hρ (le_of_not_ge h)
  exact hu (by simp only [he, Complex.ofReal_zero])

theorem scaledPoleCutoff_complex_hasCompactSupport {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (fun u : ℝ => (scaledPoleCutoff ρ u : ℂ)) :=
  (isCompact_closedBall (0 : ℝ) (2 * ρ)).of_isClosed_subset
    (isClosed_tsupport _) (scaledPoleCutoff_complex_tsupport hρ)

theorem scaledPoleCutoff_complex_half_disk {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 4 * ρ ≤ R)
    (u : ℝ) (hu : u ∈ tsupport (fun u : ℝ => (scaledPoleCutoff ρ u : ℂ))) :
    ‖(u : ℂ) - 0‖ ≤ R / 2 := by
  have h := scaledPoleCutoff_complex_tsupport hρ hu
  simp only [mem_closedBall, Real.dist_eq, sub_zero] at h
  rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- The actual fixed-circle Cauchy regular remainder defines the regular
data consumed by the scalar Green asymptotic. No measurability or
integrability assumption is made on the remainder itself. Bounds on the
original boundary function are needed only where the transverse cutoff is
nonzero. -/
theorem exists_cauchyRegularData (ψ : ℂ → ℂ) (χ : ℝ → ℂ) (f : ℂ → ℂ → ℂ)
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hf : Measurable (Function.uncurry f))
    {center : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hchart : ∀ u ∈ tsupport χ, ‖(u : ℂ) - center‖ ≤ R / 2)
    (hb : ∀ w, ψ w ≠ 0 → ∀ z ∈ sphere center R, ‖f w z‖ ≤ M) :
    ∃ D : RegularNormalData, ∀ w u,
      D.amplitude w u = ψ w * cutoffCauchy χ (f w) center R u := by
  let F : ℂ → ℂ → ℂ := fun w z => ψ w * f w z
  have hmF : Measurable (Function.uncurry F) :=
    (hψ.measurable.comp measurable_fst).mul hf
  obtain ⟨Kψ, hKψ⟩ := hψs.exists_bound_of_continuous hψ
  have hKψ₀ : 0 ≤ Kψ := (norm_nonneg (ψ 0)).trans (hKψ 0)
  have hFb (w : ℂ) (z : ℂ) (hz : z ∈ sphere center R) : ‖F w z‖ ≤ Kψ * M := by
    by_cases hw : ψ w = 0
    · simp only [F, hw, zero_mul, norm_zero]
      exact mul_nonneg hKψ₀ hM
    · exact (norm_mul _ _).le.trans (mul_le_mul (hKψ w) (hb w hw z hz)
        (norm_nonneg _) hKψ₀)
  have hFi (w : ℂ) : CircleIntegrable (F w) center R :=
    circleIntegrable_of_measurable_bound (F w)
      (hmF.comp (measurable_const.prodMk measurable_id)) hR.le (hFb w)
  have havoid (u : ℝ) (hu : u ∈ tsupport χ) : (u : ℂ) ∉ sphere center |R| := by
    rw [abs_of_pos hR]
    have he := hchart u hu
    have hlt : dist (u : ℂ) center < R := by rw [dist_eq_norm]; linarith
    exact ne_of_lt hlt
  let g : ℂ → ℝ → ℂ := fun w => cutoffCauchy χ (F w) center R
  have hg (w : ℂ) : ContDiff ℝ ∞ (g w) := contDiff_cutoffCauchy hχ (hFi w) havoid
  have hg₁ (w : ℂ) : ContDiff ℝ ∞ (deriv (g w)) := (contDiff_infty_iff_deriv.mp (hg w)).2
  have hg₂ (w : ℂ) : ContDiff ℝ ∞ (deriv (deriv (g w))) :=
    (contDiff_infty_iff_deriv.mp (hg₁ w)).2
  have hχ₁ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hχ₂ : ContDiff ℝ ∞ (deriv (deriv χ)) := (contDiff_infty_iff_deriv.mp hχ₁).2
  obtain ⟨K₀, h₀⟩ := hχs.exists_bound_of_continuous hχ.continuous
  obtain ⟨K₁, h₁⟩ := hχs.deriv.exists_bound_of_continuous hχ₁.continuous
  obtain ⟨K₂, h₂⟩ := hχs.deriv.deriv.exists_bound_of_continuous hχ₂.continuous
  have hK₀ : 0 ≤ K₀ := (norm_nonneg (χ 0)).trans (h₀ 0)
  have hK₁ : 0 ≤ K₁ := (norm_nonneg (deriv χ 0)).trans (h₁ 0)
  have hK₂ : 0 ≤ K₂ := (norm_nonneg (deriv (deriv χ) 0)).trans (h₂ 0)
  have hm₀ := measurable_cauchyTerm_real_joint F hmF 0 center R
  have hm₁ := measurable_cauchyTerm_real_joint F hmF 1 center R
  have hm₂ := measurable_cauchyTerm_real_joint F hmF 2 center R
  have hmg : Measurable (Function.uncurry g) :=
    (hχ.continuous.measurable.comp measurable_snd).mul hm₀
  have hsecond (w : ℂ) (u : ℝ) : deriv (deriv (g w)) u =
      deriv (deriv χ) u * cauchyTerm (F w) 0 center R u +
        2 * deriv χ u * cauchyTerm (F w) 1 center R u +
        2 * χ u * cauchyTerm (F w) 2 center R u :=
    second_deriv_cutoffCauchy hχ (hFi w) havoid u
  have hmg₂ : Measurable (fun x : ℂ × ℝ => deriv (deriv (g x.1)) x.2) := by
    simp_rw [hsecond]
    have := hχ.continuous.measurable
    have := hχ₁.continuous.measurable
    have := hχ₂.continuous.measurable
    fun_prop
  let L := K₂ * (R * ((2 / R) ^ 1 * (Kψ * M))) +
    2 * K₁ * (R * ((2 / R) ^ 2 * (Kψ * M))) +
    2 * K₀ * (R * ((2 / R) ^ 3 * (Kψ * M)))
  have hgb (w : ℂ) (u : ℝ) : ‖deriv (deriv (g w)) u‖ ≤ L :=
    norm_second_deriv_cutoffCauchy_le hχ (hFi w) hR (mul_nonneg hKψ₀ hM)
      hK₀ hK₁ hK₂ hchart (hFb w) h₀ h₁ h₂ u
  have hzero (x : ℂ × ℝ) (hx : x ∉ tsupport ψ ×ˢ tsupport χ) :
      deriv (deriv (g x.1)) x.2 = 0 := by
    by_cases hw : x.1 ∈ tsupport ψ
    · have hu : x.2 ∉ tsupport χ := fun hu => hx ⟨hw, hu⟩
      have hu₁ : x.2 ∉ tsupport (deriv χ) := fun hu' => hu (tsupport_deriv_subset hu')
      rw [hsecond, image_eq_zero_of_notMem_tsupport hu, deriv_of_notMem_tsupport hu,
        deriv_of_notMem_tsupport hu₁]
      simp
    · have hw₀ : ψ x.1 = 0 := image_eq_zero_of_notMem_tsupport hw
      have he : g x.1 = 0 := by
        funext u
        simp [g, F, hw₀, cutoffCauchy, cauchyTerm, circleIntegral]
      rw [he]
      simp
  have hig₂ : Integrable (fun x : ℂ × ℝ => deriv (deriv (g x.1)) x.2) :=
    integrable_joint_of_compact_bound _ (tsupport ψ ×ˢ tsupport χ) (hψs.prod hχs)
      hmg₂ L hzero (fun x _ => hgb x.1 x.2)
  refine ⟨{
    amplitude := g
    first := fun w => deriv (g w)
    second := fun w => deriv (deriv (g w))
    measurable := hmg
    derivative := fun w u => (contDiff_infty_iff_deriv.mp (hg w)).1 u |>.hasDerivAt
    derivative_first := fun w u => (contDiff_infty_iff_deriv.mp (hg₁ w)).1 u |>.hasDerivAt
    continuous_second := fun w => (hg₂ w).continuous
    compact := fun w => cutoffCauchy_hasCompactSupport (F w) center R hχs
    integrable_second := hig₂
  }, ?_⟩
  intro w u
  change χ u * cauchyTerm (fun z => ψ w * f w z) 0 center R u =
    ψ w * (χ u * cauchyTerm (f w) 0 center R u)
  rw [cauchyTerm_const_mul]
  ring

/-- Direct decay of the actual outer-circle regular integral. The constant
is independent of normal frequency and every transverse pole location. -/
theorem exists_uniform_cauchyRegular_fourier_bound
    (ψ : ℂ → ℂ) (χ : ℝ → ℂ) (f : ℂ → ℂ → ℂ)
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hf : Measurable (Function.uncurry f))
    {center : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hchart : ∀ u ∈ tsupport χ, ‖(u : ℂ) - center‖ ≤ R / 2)
    (hb : ∀ w, ψ w ≠ 0 → ∀ z ∈ sphere center R, ‖f w z‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      Integrable (fun w : ℂ => ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) *
        (ψ w * cutoffCauchy χ (f w) center R u)) ∧
      ‖∫ w : ℂ, ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) *
        (ψ w * cutoffCauchy χ (f w) center R u)‖ ≤ C / T ^ 2 := by
  obtain ⟨D, hD⟩ := exists_cauchyRegularData ψ χ f hψ hψs hχ hχs hf hR hM hchart hb
  refine ⟨D.derivativeMass, D.derivativeMass_nonneg, ?_⟩
  intro T hT
  have h := D.integral_bound hT
  have he : D.normalIntegral T = fun w : ℂ => ∫ u : ℝ,
      Complex.exp (I * (T : ℂ) * u) * (ψ w * cutoffCauchy χ (f w) center R u) := by
    funext w
    simp only [RegularNormalData.normalIntegral, hD]
  rwa [he] at h

/-- The explicit smooth normal cutoff instantiates all local normal-cutoff
conditions once its support fits inside half of the analytic disk. -/
theorem exists_scaled_cauchyRegularData (ψ : ℂ → ℂ) (f : ℂ → ℂ → ℂ)
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hf : Measurable (Function.uncurry f))
    {ρ R M : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hρR : 4 * ρ ≤ R) (hM : 0 ≤ M)
    (hb : ∀ w, ψ w ≠ 0 → ∀ z ∈ sphere (0 : ℂ) R, ‖f w z‖ ≤ M) :
    ∃ D : RegularNormalData, ∀ w u,
      D.amplitude w u = ψ w *
        cutoffCauchy (fun u : ℝ => (scaledPoleCutoff ρ u : ℂ)) (f w) 0 R u :=
  exists_cauchyRegularData ψ _ f hψ hψs (scaledPoleCutoff_complex_contDiff ρ)
    (scaledPoleCutoff_complex_hasCompactSupport hρ) hf hR hM
    (scaledPoleCutoff_complex_half_disk hρ hρR) hb

/-- Specialization to the original analytic numerator/denominator quotient;
the returned amplitude contains exactly `normalCauchyRemainder`. -/
theorem exists_quotient_cauchyRegularData (ψ : ℂ → ℂ) (A B : ℂ → ℂ → ℂ)
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hA : Measurable (Function.uncurry A)) (hB : Measurable (Function.uncurry B))
    {ρ R M : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hρR : 4 * ρ ≤ R) (hM : 0 ≤ M)
    (hb : ∀ w, ψ w ≠ 0 → ∀ z ∈ sphere (0 : ℂ) R, ‖A w z / B w z‖ ≤ M) :
    ∃ D : RegularNormalData, ∀ w u,
      D.amplitude w u = ψ w * (scaledPoleCutoff ρ u : ℂ) *
        normalCauchyRemainder (A w) (B w) 0 R u := by
  obtain ⟨D, hD⟩ := exists_scaled_cauchyRegularData ψ (fun w z => A w z / B w z)
    hψ hψs (hA.div hB) hρ hR hρR hM hb
  refine ⟨D, ?_⟩
  intro w u
  rw [hD, cutoffCauchy, cauchyTerm_zero]
  ring

end Maxwell.Green
