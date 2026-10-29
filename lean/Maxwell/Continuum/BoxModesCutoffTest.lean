import Maxwell.Continuum.BoxModesCutoffTensor
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual compact smooth test fields approximating the box modes. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators

def innerClosedBox (N : Fin 3 → ℝ) (δ : ℝ) : Set Point :=
  WithLp.ofLp ⁻¹' (Set.univ.pi fun j => Set.Icc δ (N j - δ))

theorem isCompact_innerClosedBox (N : Fin 3 → ℝ) (δ : ℝ) :
    IsCompact (innerClosedBox N δ) :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem innerClosedBox_subset_openBox (N : Fin 3 → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    innerClosedBox N δ ⊆ openBox N := by
  intro x hx
  rw [mem_openBox]
  intro j
  have hj : δ ≤ x j ∧ x j ≤ N j - δ := hx j (Set.mem_univ j)
  constructor <;> linarith

theorem tsupport_cutoffScalarMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3)
    {δ : ℝ} (hδ : 0 < δ) : tsupport (cutoffScalarMode N ν c δ) ⊆ innerClosedBox N δ := by
  apply closure_minimal ?_ (isCompact_innerClosedBox N δ).isClosed
  intro x hx j _
  have hj : cutoffCoordinateMode N ν c δ j (x j) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) j (Finset.mem_univ j)
  constructor
  · by_contra hn
    apply hj
    rw [cutoffCoordinateMode, intervalCutoff_eq_zero_of_le hδ (le_of_not_ge hn), zero_mul]
  · by_contra hn
    apply hj
    rw [cutoffCoordinateMode, intervalCutoff_eq_zero_of_ge hδ (le_of_not_ge hn), zero_mul]

theorem hasCompactSupport_cutoffScalarMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3)
    {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (cutoffScalarMode N ν c δ) :=
  (isCompact_innerClosedBox N δ).of_isClosed_subset isClosed_closure
    (tsupport_cutoffScalarMode N ν c hδ)

def cutoffTestScalar (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3)
    (δ : ℝ) (hδ : 0 < δ) : TestFunction (boxDomain N) ℂ ⊤ :=
  ⟨fun x => (cutoffScalarMode N ν c δ x : ℂ),
    Complex.ofRealCLM.contDiff.comp (contDiff_cutoffScalarMode N ν c δ),
    (hasCompactSupport_cutoffScalarMode N ν c hδ).comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero (cutoffScalarMode N ν c δ)).trans
      ((tsupport_cutoffScalarMode N ν c hδ).trans (innerClosedBox_subset_openBox N hδ))⟩

def cutoffTestField (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3)
    (δ : ℝ) (hδ : 0 < δ) : TestField (boxDomain N) :=
  Pi.single c (cutoffTestScalar N ν c δ hδ)

theorem partialSchwartz_cutoffTestScalar (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c j : Fin 3) (δ : ℝ) (hδ : 0 < δ) (x : Space) :
    partialSchwartz j (testSchwartz (boxDomain N) (cutoffTestScalar N ν c δ hδ)) x =
      (partialDeriv (cutoffScalarMode N ν c δ) j x : ℂ) := by
  change fderiv ℝ (fun x : Point => (cutoffScalarMode N ν c δ x : ℂ)) x
    (direction j) = _
  have hd := (contDiff_cutoffScalarMode N ν c δ).differentiable (by simp)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hd.differentiableAt.hasFDerivAt
  change HasFDerivAt (fun x : Point => (cutoffScalarMode N ν c δ x : ℂ)) _ x at hc
  rw [hc.fderiv]
  rfl

theorem intervalCutoff_locally_one {N δ x : ℝ} (hδ : 0 < δ)
    (hl : 2 * δ < x) (hr : x < N - 2 * δ) :
    intervalCutoff N δ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [eventually_gt_nhds hl, eventually_lt_nhds hr] with y hy₁ hy₂
  exact intervalCutoff_eq_one hδ hy₁.le hy₂.le

theorem intervalCutoff_eventually_locally_one (N x : ℝ) (hx : x ∈ Set.Ioo 0 N) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), intervalCutoff N δ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  have hsmall : 0 < min x (N - x) / 2 :=
    div_pos (lt_min hx.1 (sub_pos.mpr hx.2)) (by norm_num)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hsmall).filter_mono nhdsWithin_le_nhds] with δ hδ hs
  apply intervalCutoff_locally_one hδ
  · have := min_le_left x (N - x)
    linarith
  · have := min_le_right x (N - x)
    linarith

theorem cutoffScalarMode_eventually_locally_eq (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (x : Point) (hx : x ∈ openBox N) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), cutoffScalarMode N ν c δ =ᶠ[𝓝 x] scalarBoxMode N ν c := by
  have hcoord (j : Fin 3) := intervalCutoff_eventually_locally_one (N j) (x j)
    ((mem_openBox N x).mp hx j)
  filter_upwards [eventually_all.mpr hcoord] with δ hδ
  have he (j : Fin 3) :
      (fun y : Point => intervalCutoff (N j) δ (y j)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    (hδ j).comp_tendsto (differentiable_coordinate j).continuous.continuousAt
  filter_upwards [eventually_all.mpr he] with y hy
  unfold cutoffScalarMode scalarBoxMode
  apply Finset.prod_congr rfl
  intro j _
  rw [cutoffCoordinateMode, hy j, one_mul]

theorem cutoffScalarMode_eq_zero_outside (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) {δ : ℝ} (hδ : 0 < δ) {x : Point} (hx : x ∉ openBox N) :
    cutoffScalarMode N ν c δ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hs => hx ((innerClosedBox_subset_openBox N hδ)
    ((tsupport_cutoffScalarMode N ν c hδ) hs))

theorem partial_cutoffScalarMode_eq_zero_outside (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c j : Fin 3) {δ : ℝ} (hδ : 0 < δ) {x : Point} (hx : x ∉ openBox N) :
    partialDeriv (cutoffScalarMode N ν c δ) j x = 0 := by
  have hs : x ∉ tsupport (cutoffScalarMode N ν c δ) := fun hs =>
    hx ((innerClosedBox_subset_openBox N hδ) ((tsupport_cutoffScalarMode N ν c hδ) hs))
  rw [partialDeriv, fderiv_of_notMem_tsupport ℝ hs, zero_apply]

def cutoffWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem cutoffWidth_pos (n : ℕ) : 0 < cutoffWidth n := by
  unfold cutoffWidth
  positivity

theorem cutoffWidth_tendsto : Tendsto cutoffWidth atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Filter.Eventually.of_forall cutoffWidth_pos⟩

theorem cutoffScalarMode_eventually_eq (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (x : Point) :
    ∀ᶠ n : ℕ in atTop, cutoffScalarMode N ν c (cutoffWidth n) x =
      (openBox N).indicator (scalarBoxMode N ν c) x := by
  by_cases hx : x ∈ openBox N
  · filter_upwards [cutoffWidth_tendsto.eventually
      (cutoffScalarMode_eventually_locally_eq N ν c x hx)] with n hn
    rw [Set.indicator_of_mem hx]
    exact hn.eq_of_nhds
  · exact Filter.Eventually.of_forall fun n => by
      rw [Set.indicator_of_notMem hx]
      exact cutoffScalarMode_eq_zero_outside N ν c (cutoffWidth_pos n) hx

theorem partial_cutoffScalarMode_eventually_eq (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c j : Fin 3) (x : Point) :
    ∀ᶠ n : ℕ in atTop, partialDeriv (cutoffScalarMode N ν c (cutoffWidth n)) j x =
      (openBox N).indicator (fun x => partialDeriv (scalarBoxMode N ν c) j x) x := by
  by_cases hx : x ∈ openBox N
  · filter_upwards [cutoffWidth_tendsto.eventually
      (cutoffScalarMode_eventually_locally_eq N ν c x hx)] with n hn
    rw [Set.indicator_of_mem hx, partialDeriv, hn.fderiv_eq]
    rfl
  · exact Filter.Eventually.of_forall fun n => by
      rw [Set.indicator_of_notMem hx]
      exact partial_cutoffScalarMode_eq_zero_outside N ν c j (cutoffWidth_pos n) hx

#print axioms partialSchwartz_cutoffTestScalar
#print axioms partial_cutoffScalarMode_eventually_eq

end Maxwell.Continuum.BoxModes
