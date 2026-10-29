import Maxwell.Continuum.BoxModesSpan
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Completeness of the literal mixed sine/cosine modes in box L²

The measure is the product of the usual restricted Lebesgue measures on the
closed coordinate intervals. Endpoint sets have measure zero. The proof uses
the concrete dense cosine algebra and the explicit sine weight, which is
nonzero almost everywhere, rather than assuming a Fourier basis.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory
open scoped InnerProductSpace ENNReal

/-- Unnormalized Lebesgue measure on a closed coordinate interval. -/
def intervalMeasure (N : ℝ) : Measure (Set.Icc (0 : ℝ) N) :=
  (volume : Measure ℝ).comap Subtype.val

instance intervalMeasure_finite (N : ℝ) : IsFiniteMeasure (intervalMeasure N) where
  measure_univ_lt_top := by
    rw [intervalMeasure, comap_subtype_coe_apply measurableSet_Icc,
      Set.image_univ, Subtype.range_coe]
    exact isCompact_Icc.measure_lt_top

instance intervalMeasure_nullSingleton (N : ℝ) : NullSingletonClass (intervalMeasure N) where
  measure_singleton x := by
    rw [intervalMeasure, comap_subtype_coe_apply measurableSet_Icc, Set.image_singleton]
    exact measure_singleton _

/-- Product Lebesgue measure, without normalizing the box volume. -/
def cubeMeasure (N : Fin 3 → ℝ) : Measure (ClosedCube N) :=
  Measure.pi (fun j => intervalMeasure (N j))

instance cubeMeasure_finite (N : Fin 3 → ℝ) : IsFiniteMeasure (cubeMeasure N) := by
  unfold cubeMeasure
  infer_instance

instance cubeMeasure_weaklyRegular (N : Fin 3 → ℝ) : (cubeMeasure N).WeaklyRegular :=
  inferInstance

/-- Boundary coordinates carry zero product Lebesgue measure. -/
theorem cubePoint_mem_openBox_ae (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    ∀ᵐ x : ClosedCube N ∂cubeMeasure N, cubePoint N x ∈ openBox N := by
  have hlow (j : Fin 3) : ∀ᵐ x : ClosedCube N ∂cubeMeasure N, (x j : ℝ) ≠ 0 := by
    have h := Measure.ae_eval_ne (μ := fun j : Fin 3 =>
      (intervalMeasure (N j))) j ⟨0, le_rfl, (hN j).le⟩
    filter_upwards [h] with x hx
    intro heq
    apply hx
    exact Subtype.ext heq
  have hupp (j : Fin 3) : ∀ᵐ x : ClosedCube N ∂cubeMeasure N, (x j : ℝ) ≠ N j := by
    have h := Measure.ae_eval_ne (μ := fun j : Fin 3 =>
      (intervalMeasure (N j))) j ⟨N j, (hN j).le, le_rfl⟩
    filter_upwards [h] with x hx
    intro heq
    apply hx
    exact Subtype.ext heq
  filter_upwards [ae_all_iff.mpr hlow, ae_all_iff.mpr hupp] with x hl hu
  rw [mem_openBox]
  intro j
  exact ⟨lt_of_le_of_ne (x j).property.1 (hl j).symm,
    lt_of_le_of_ne (x j).property.2 (hu j)⟩

theorem baseWeight_ne_zero_ae (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) (c : Fin 3) :
    ∀ᵐ x : ClosedCube N ∂cubeMeasure N, baseWeight N c x ≠ 0 := by
  filter_upwards [cubePoint_mem_openBox_ae N hN] with x hx
  exact (baseWeight_pos_on_openBox N hN c x hx).ne'

abbrev CubeL2 (N : Fin 3 → ℝ) := Lp ℝ 2 (cubeMeasure N)

def cubeModeL2 (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) : CubeL2 N :=
  ContinuousMap.toLp 2 (cubeMeasure N) ℝ (cubeMode N c ν)

def cubeModeL2Span (N : Fin 3 → ℝ) (c : Fin 3) : Submodule ℝ (CubeL2 N) :=
  Submodule.span ℝ (Set.range (cubeModeL2 N c))

/-- Continuous weighted functions lie in the actual L² mode closure. -/
theorem weighted_toLp_mem_cubeModeL2_closure (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (f : C(ClosedCube N, ℝ)) :
    ContinuousMap.toLp 2 (cubeMeasure N) ℝ (f * baseWeight N c) ∈
      (cubeModeL2Span N c).topologicalClosure := by
  let L : C(ClosedCube N, ℝ) →L[ℝ] CubeL2 N := ContinuousMap.toLp 2 (cubeMeasure N) ℝ
  have h : (mixedModeSpan N c).topologicalClosure ≤
      ((cubeModeL2Span N c).topologicalClosure).comap L.toLinearMap := by
    apply (mixedModeSpan N c).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨ν, rfl⟩
      exact (cubeModeL2Span N c).le_topologicalClosure (Submodule.subset_span ⟨ν, rfl⟩)
    · exact (cubeModeL2Span N c).isClosed_topologicalClosure.preimage L.continuous
  exact h (continuous_mul_baseWeight_mem_closure N hN c f)

/-- A mode-orthogonal L² function is zero: multiplication by the interior
sine weight reduces this to density of ordinary continuous functions. -/
theorem orthogonal_cubeModeL2_closure_eq_zero (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (u : CubeL2 N)
    (hu : u ∈ ((cubeModeL2Span N c).topologicalClosure)ᗮ) : u = 0 := by
  have hwm : MemLp (baseWeight N c) ∞ (cubeMeasure N) :=
    ContinuousMap.memLp (p := ∞) (cubeMeasure N) ℝ (baseWeight N c)
  have hmul : MemLp (fun x => baseWeight N c x * u x) 2
      (cubeMeasure N) := hwm.fun_mul (Lp.memLp u)
  let v : CubeL2 N := hmul.toLp (fun x => baseWeight N c x * u x)
  have hvcoe : (v : ClosedCube N → ℝ) =ᵐ[cubeMeasure N] fun x => baseWeight N c x * u x :=
    hmul.coeFn_toLp
  have hvinner (f : C(ClosedCube N, ℝ)) :
      inner ℝ (ContinuousMap.toLp 2 (cubeMeasure N) ℝ f) v = 0 := by
    have hh := hu _ (weighted_toLp_mem_cubeModeL2_closure N hN c f)
    convert hh using 1
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (cubeMeasure N) f,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (cubeMeasure N) (f * baseWeight N c), hvcoe]
      with x hf hfw hv
    rw [hf, hfw, hv]
    simp only [ContinuousMap.mul_apply, RCLike.inner_apply, conj_trivial]
    ring
  have hvzero : v = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hclosed : IsClosed {g : CubeL2 N | inner ℝ g v = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hsubset : Set.range (ContinuousMap.toLp 2 (cubeMeasure N) ℝ :
        C(ClosedCube N, ℝ) →L[ℝ] CubeL2 N) ⊆ {g | inner ℝ g v = 0} := by
      rintro _ ⟨f, rfl⟩
      exact hvinner f
    exact (closure_minimal hsubset hclosed)
      (ContinuousMap.toLp_denseRange ℝ (cubeMeasure N) ℝ (by norm_num) v)
  apply Lp.ext
  filter_upwards [hvcoe, baseWeight_ne_zero_ae N hN c,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (cubeMeasure N))]
    with x hv hw hz
  rw [hvzero, hz] at hv
  exact (mul_eq_zero.mp hv.symm).resolve_left hw |>.trans hz.symm

/-- Completeness for the actual mixed trigonometric family in box L². -/
theorem cubeModeL2_complete (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) (c : Fin 3) :
    (cubeModeL2Span N c).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro u hu
  simpa only [Submodule.mem_bot] using orthogonal_cubeModeL2_closure_eq_zero N hN c u hu

#print axioms cubeModeL2_complete

end Maxwell.Continuum.BoxModes
