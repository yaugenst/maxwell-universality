import Maxwell.Green.PeriodicRemainder

/-! Smooth removal of a local torus singularity and decay of the remainder. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Maxwell.Green

/-- Fill the removable value with the smooth local residual. -/
def localizedRemainder (H L R : RealTorusCoordinates → ℂ) (q : RealTorusCoordinates) : ℂ :=
  if q = 0 then R 0 else H q - L q

@[simp] theorem localizedRemainder_zero (H L R : RealTorusCoordinates → ℂ) :
    localizedRemainder H L R 0 = R 0 := by simp [localizedRemainder]

theorem localizedRemainder_eq_sub_of_ne
    (H L R : RealTorusCoordinates → ℂ) {q : RealTorusCoordinates} (hq : q ≠ 0) :
    localizedRemainder H L R q = H q - L q := by simp only [localizedRemainder, ite_eq_right hq]

theorem localizedRemainder_germ_away_zero
    (H L R : RealTorusCoordinates → ℂ) {q : RealTorusCoordinates} (hq : q ≠ 0) :
    localizedRemainder H L R =ᶠ[𝓝 q] fun x => H x - L x := by
  filter_upwards [eventually_ne_nhds hq] with x hx
  exact localizedRemainder_eq_sub_of_ne H L R hx

/-- Equality on the punctured neighborhood becomes full germ equality
once the removable value is filled. -/
theorem localizedRemainder_germ_at_zero
    (H L R : RealTorusCoordinates → ℂ)
    (hres : (fun q => H q - L q) =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] R) :
    localizedRemainder H L R =ᶠ[𝓝 (0 : RealTorusCoordinates)] R := by
  have he := eventually_nhdsWithin_iff.mp hres
  filter_upwards [he] with q hq
  by_cases hzero : q = 0
  · subst q
    exact localizedRemainder_zero H L R
  · rw [localizedRemainder_eq_sub_of_ne H L R hzero]
    exact hq hzero

/-- The globally defined remainder is smooth near every point of the
fundamental cube, including the removed singularity. -/
theorem localizedRemainder_smoothOnTorusCube
    (H L R : RealTorusCoordinates → ℂ)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q)
    (hL : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ L q)
    (hR : ContDiffAt ℝ ∞ R 0)
    (hres : (fun q => H q - L q) =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] R) :
    SmoothOnTorusCube (localizedRemainder H L R) := by
  intro q hq
  by_cases hzero : q = 0
  · subst q
    exact hR.congr_of_eventuallyEq (localizedRemainder_germ_at_zero H L R hres)
  · exact ((hH q hq hzero).sub (hL q hq hzero)).congr_of_eventuallyEq
      (localizedRemainder_germ_away_zero H L R hzero)

theorem interior_torusCube (a p : ℝ) :
    interior (torusCube a p) = {q : RealTorusCoordinates | ∀ i, q i ∈ Ioo a (a + p)} := by
  have heq : torusCube a p = Set.univ.pi (fun _ : Fin 3 => Icc a (a + p)) := by
    ext q
    simp only [torusCube, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const]
  rw [heq, interior_pi_set (Set.toFinite Set.univ)]
  ext q
  simp only [Set.mem_pi, mem_univ, forall_const, mem_ofPred_eq, interior_Icc]

theorem torusCube_face_not_mem_interior
    (a p : ℝ) (i : Fin 3) (q : RealTorusCoordinates) (hq : q i = a ∨ q i = a + p) :
    q ∉ interior (torusCube a p) := by
  rw [interior_torusCube]
  intro h
  have hi := h i
  rcases hq with hq | hq
  · rw [hq] at hi
    exact (lt_irrefl a) hi.1
  · rw [hq] at hi
    exact (lt_irrefl (a + p)) hi.2

theorem insertNth_ne_zero_of_coordinate
    (i : Fin 3) (q : Fin 2 → ℝ) {a : ℝ} (ha : a ≠ 0) : (i.insertNth a q : RealTorusCoordinates) ≠ 0 := by
  intro h
  have h' := congrArg (fun z : RealTorusCoordinates => z i) h
  exact ha (by simpa only [Fin.insertNth_apply_same, Pi.zero_apply] using h')

/-- Outside the localized term's support, the filled remainder agrees
locally with the original periodic function. -/
theorem localizedRemainder_germ_outside_support
    (H L R : RealTorusCoordinates → ℂ) {q : RealTorusCoordinates}
    (hq : q ≠ 0) (hL : q ∉ tsupport L) :
    localizedRemainder H L R =ᶠ[𝓝 q] H := by
  filter_upwards [localizedRemainder_germ_away_zero H L R hq,
    notMem_tsupport_iff_eventuallyEq.mp hL] with x hx hzero
  simpa only [hzero, Pi.zero_apply, sub_zero] using hx

/-- A subtraction supported strictly inside the cube preserves the germ
of the original function at every point of each pair of opposite faces. -/
theorem localizedRemainder_face_germs
    (H L R : RealTorusCoordinates → ℂ)
    (hsupport : tsupport L ⊆ interior (torusCube (-Real.pi) (2 * Real.pi)))
    (i : Fin 3) (q : Fin 2 → ℝ) :
    localizedRemainder H L R =ᶠ[𝓝 (i.insertNth (-Real.pi) q)] H ∧
    localizedRemainder H L R =ᶠ[𝓝 (i.insertNth (-Real.pi + 2 * Real.pi) q)] H := by
  constructor
  · apply localizedRemainder_germ_outside_support H L R
    · exact insertNth_ne_zero_of_coordinate i q (neg_ne_zero.mpr Real.pi_ne_zero)
    · intro h
      exact torusCube_face_not_mem_interior (-Real.pi) (2 * Real.pi) i _
        (Or.inl (Fin.insertNth_apply_same i _ q)) (hsupport h)
  · apply localizedRemainder_germ_outside_support H L R
    · apply insertNth_ne_zero_of_coordinate i q
      linarith [Real.pi_pos]
    · intro h
      exact torusCube_face_not_mem_interior (-Real.pi) (2 * Real.pi) i _
        (Or.inr (Fin.insertNth_apply_same i _ q)) (hsupport h)

/-- The smooth part left by an actual local singular subtraction has
quadratic Fourier decay along every nonzero integer direction. -/
theorem localizedRemainder_fourier_bound
    (H L R : RealTorusCoordinates → ℂ)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q)
    (hL : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ L q)
    (hR : ContDiffAt ℝ ∞ R 0)
    (hres : (fun q => H q - L q) =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] R)
    (hsupport : tsupport L ⊆ interior (torusCube (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (q : RealTorusCoordinates),
      H (q + (2 * Real.pi) • Pi.single i 1) = H q)
    (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 0 < d →
      ‖∫ q, torusFourierFactor d v q * localizedRemainder H L R q
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤ C / (d : ℝ) ^ 2 := by
  have hex : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hfaces := torusFaceMatches_of_periodic_face_germs i (hperiod i)
    (fun q _ => localizedRemainder_face_germs H L R hsupport i q)
  exact smooth_torus_fourier_bound_of_matching_faces
    (localizedRemainder_smoothOnTorusCube H L R hH hL hR hres) v i hi hfaces.1 hfaces.2

/-- The original amplitude splits into localized singular and smooth parts
almost everywhere; the arbitrary value at the removed point is immaterial. -/
theorem localizedRemainder_reconstruct_ae
    (H L R : RealTorusCoordinates → ℂ) (a p : ℝ) :
    H =ᵐ[torusCubeMeasure a p] fun q => L q + localizedRemainder H L R q := by
  have hnull : NullSingletonClass (torusCubeMeasure a p) := by
    unfold torusCubeMeasure
    infer_instance
  filter_upwards [(torusCubeMeasure a p).ae_ne 0] with q hq
  rw [localizedRemainder_eq_sub_of_ne H L R hq]
  ring

theorem integrable_torusFourier_mul
    {F : RealTorusCoordinates → ℂ} {a p : ℝ}
    (hF : Integrable F (torusCubeMeasure a p)) (d : ℕ) (v : Fin 3 → ℤ) :
    Integrable (fun q => torusFourierFactor d v q * F q) (torusCubeMeasure a p) :=
  hF.bdd_mul (continuous_torusFourierFactor d v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => (torusFourierFactor_norm d v q).le)

/-- The actual Fourier integral splits once the local pole term is
integrable and the filled remainder is smooth on the cube. -/
theorem localizedRemainder_fourier_decomposition
    (H L R : RealTorusCoordinates → ℂ)
    (hL : Integrable L (torusCubeMeasure (-Real.pi) (2 * Real.pi)))
    (hrem : SmoothOnTorusCube (localizedRemainder H L R)) (d : ℕ) (v : Fin 3 → ℤ) :
    (∫ q, torusFourierFactor d v q * H q ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      (∫ q, torusFourierFactor d v q * L q ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) +
      (∫ q, torusFourierFactor d v q * localizedRemainder H L R q
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
  have hI := continuousOn_integrable_torusCube hrem.continuousOn
  rw [← integral_add (integrable_torusFourier_mul hL d v) (integrable_torusFourier_mul hI d v)]
  apply integral_congr_ae
  filter_upwards [localizedRemainder_reconstruct_ae H L R (-Real.pi) (2 * Real.pi)] with q hq
  rw [hq, mul_add]

/-- Cutoff form of the localization theorem. The cutoff is real-valued,
smooth, one near zero, and supported inside the cube. The local identity
`H=P+R` then constructs the smooth remainder and its Fourier estimate. -/
theorem cutoff_localizedRemainder_fourier_bound
    (H P R : RealTorusCoordinates → ℂ) (χ : RealTorusCoordinates → ℝ)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q)
    (hP : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ P q)
    (hR : ContDiffAt ℝ ∞ R 0) (hχ : ContDiff ℝ ∞ χ)
    (hχone : χ =ᶠ[𝓝 (0 : RealTorusCoordinates)] fun _ => 1)
    (hres : H =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] fun q => P q + R q)
    (hsupport : tsupport χ ⊆ interior (torusCube (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (q : RealTorusCoordinates),
      H (q + (2 * Real.pi) • Pi.single i 1) = H q)
    (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 0 < d →
      ‖∫ q, torusFourierFactor d v q *
          localizedRemainder H (fun q => (χ q : ℂ) * P q) R q
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤ C / (d : ℝ) ^ 2 := by
  apply localizedRemainder_fourier_bound H (fun q => (χ q : ℂ) * P q) R hH
  · intro q hq hzero
    exact ((Complex.ofRealCLM.contDiff.comp hχ).contDiffAt).mul (hP q hq hzero)
  · exact hR
  · filter_upwards [hres, hχone.filter_mono nhdsWithin_le_nhds] with q hq hχq
    simp only [hq, hχq, Complex.ofReal_one, one_mul]
    ring
  · exact tsupport_mul_subset_left.trans ((tsupport_comp_subset (show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero) χ).trans hsupport)
  · exact hperiod
  · exact hv

end Maxwell.Green
