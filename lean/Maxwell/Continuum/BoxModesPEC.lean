import Maxwell.Continuum.BoxModesComplex
import Maxwell.Continuum.PECSupport

/-!
# Complete component modes in the actual PEC ambient L² space

This module uses the same global complex L² fields and supported-domain
subspace as the distributional PEC construction. Modes are literal zero
extensions of the mixed trigonometric functions on the physical box.
Their closed span equals `testL2Closure`; curl graph membership is separate.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ENNReal

theorem isOpen_openBox (N : Fin 3 → ℝ) : IsOpen (openBox N) :=
  (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

def boxDomain (N : Fin 3 → ℝ) : Opens Space := ⟨openBox N, isOpen_openBox N⟩

theorem boxComplexModeL2_coe_ae (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    (boxComplexModeL2 N c ν : Point → ℂ) =ᵐ[volume.restrict (openBox N)]
      fun x => (scalarBoxMode N ν c x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (boxModeL2 N c ν),
    (memLp_scalarBoxMode N ν c).coeFn_toLp] with x hc hr
  exact hc.trans (congrArg Complex.ofRealCLM hr)

theorem memLp_complex_scalarBoxMode (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    MemLp (fun x => (scalarBoxMode N ν c x : ℂ)) 2
      (volume.restrict (openBox N)) :=
  (Lp.memLp (boxComplexModeL2 N c ν)).ae_eq (boxComplexModeL2_coe_ae N c ν)

def zeroExtendedBoxMode (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) : ScalarL2 :=
  MemLp.toLp ((openBox N).indicator (fun x => (scalarBoxMode N ν c x : ℂ)))
    ((memLp_indicator_iff_restrict (isOpen_openBox N).measurableSet).mpr
      (memLp_complex_scalarBoxMode N c ν))

theorem zeroExtendedBoxMode_coe_ae (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    (zeroExtendedBoxMode N c ν : Space → ℂ) =ᵐ[volume]
      (openBox N).indicator (fun x => (scalarBoxMode N ν c x : ℂ)) :=
  MemLp.coeFn_toLp _

def componentBoxMode (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) : FieldL2 :=
  PiLp.single 2 c (zeroExtendedBoxMode N c ν)

theorem componentBoxMode_supported (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    FieldSupported (boxDomain N) (componentBoxMode N c ν) := by
  intro j
  by_cases hj : j = c
  · subst j
    filter_upwards [zeroExtendedBoxMode_coe_ae N c ν] with x hx hΩ
    change (PiLp.single 2 c (zeroExtendedBoxMode N c ν) : FieldL2) c x = 0
    change x ∉ openBox N at hΩ
    rw [PiLp.single_eq_same, hx, Set.indicator_of_notMem hΩ]
  · filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure Space))]
      with x hx _
    change (PiLp.single 2 c (zeroExtendedBoxMode N c ν) : FieldL2) j x = 0
    rw [PiLp.single_eq_of_ne 2 hj]
    exact hx

theorem componentBoxMode_mem_testL2Closure (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) : componentBoxMode N c ν ∈ testL2Closure (boxDomain N) :=
  mem_testL2Closure_of_supported _ _ (componentBoxMode_supported N c ν)

def restrictBoxL2 (N : Fin 3 → ℝ) (u : ScalarL2) : BoxComplexL2 N :=
  ((Lp.memLp u).mono_measure Measure.restrict_le_self).toLp (u : Space → ℂ)

theorem restrictBoxL2_coe_ae (N : Fin 3 → ℝ) (u : ScalarL2) :
    (restrictBoxL2 N u : Space → ℂ) =ᵐ[volume.restrict (openBox N)] u :=
  MemLp.coeFn_toLp _

theorem zeroExtendedBoxMode_inner (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) (u : ScalarL2) :
    inner ℂ (zeroExtendedBoxMode N c ν) u =
      inner ℂ (boxComplexModeL2 N c ν) (restrictBoxL2 N u) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (zeroExtendedBoxMode N c ν x) (u x)) =
        ∫ x, (openBox N).indicator
          (fun x => inner ℂ (scalarBoxMode N ν c x : ℂ) (u x)) x := by
      apply integral_congr_ae
      filter_upwards [zeroExtendedBoxMode_coe_ae N c ν] with x hx
      rw [hx]
      by_cases hΩ : x ∈ openBox N
      · rw [Set.indicator_of_mem hΩ, Set.indicator_of_mem hΩ]
      · rw [Set.indicator_of_notMem hΩ, Set.indicator_of_notMem hΩ, inner_zero_left]
    _ = ∫ x in openBox N, inner ℂ (scalarBoxMode N ν c x : ℂ) (u x) :=
      integral_indicator (isOpen_openBox N).measurableSet
    _ = ∫ x in openBox N,
        inner ℂ (boxComplexModeL2 N c ν x) (restrictBoxL2 N u x) := by
      apply integral_congr_ae
      filter_upwards [boxComplexModeL2_coe_ae N c ν, restrictBoxL2_coe_ae N u]
        with x hm hu
      rw [hm, hu]

abbrev ComponentModeIndex := Σ c : Fin 3, {ν : Fin 3 → ℤ // AdmissibleIndex c ν}

def componentBoxModeSpan (N : Fin 3 → ℝ) : Submodule ℂ FieldL2 :=
  Submodule.span ℂ (Set.range fun q : ComponentModeIndex => componentBoxMode N q.1 q.2.val)

theorem orthogonal_componentBoxMode_vanishes (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (u : FieldL2) (hu : u ∈ (componentBoxModeSpan N)ᗮ) :
    ∀ c, ∀ᵐ x ∂volume, x ∈ openBox N → u c x = 0 := by
  intro c
  have horth : restrictBoxL2 N (u c) ∈
      ((admissibleBoxComplexModeSpan N c).topologicalClosure)ᗮ := by
    rw [Submodule.orthogonal_closure]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨ν, rfl⟩ := hv
      change inner ℂ (boxComplexModeL2 N c ν.val) (restrictBoxL2 N (u c)) = 0
      rw [← zeroExtendedBoxMode_inner, ← field_inner_single_left c]
      exact hu _ (Submodule.subset_span ⟨⟨c, ν⟩, rfl⟩)
    | zero => exact inner_zero_left _
    | add v w _ _ hv hw => rw [inner_add_left, hv, hw, add_zero]
    | smul a v _ hv => rw [inner_smul_left, hv, mul_zero]
  have hz : restrictBoxL2 N (u c) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    exact horth _ (by rw [admissibleBoxComplexMode_complete N hN c]; trivial)
  apply (ae_restrict_iff' (isOpen_openBox N).measurableSet).mp
  filter_upwards [restrictBoxL2_coe_ae N (u c),
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict (openBox N))] with x hx hzero
  rw [hz, hzero] at hx
  exact hx.symm

/-- The actual zero-extended component modes span exactly the same complex
L² domain as compactly supported smooth PEC test fields. -/
theorem componentBoxMode_complete (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    (componentBoxModeSpan N).topologicalClosure = testL2Closure (boxDomain N) := by
  apply le_antisymm
  · apply (componentBoxModeSpan N).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      exact componentBoxMode_mem_testL2Closure N q.1 q.2.val
    · exact (testFieldL2 (boxDomain N)).range.isClosed_topologicalClosure
  · intro u hu
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    intro v hv
    have hvzero := orthogonal_componentBoxMode_vanishes N hN v hv
    have husupp := supported_of_mem_testL2Closure _ u hu
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro c _
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hvzero c, husupp c] with x hvx hux
    simp only [Pi.zero_apply]
    by_cases hΩ : x ∈ openBox N
    · rw [hvx hΩ, inner_zero_left]
    · rw [hux hΩ, inner_zero_right]

#print axioms componentBoxMode_complete

end Maxwell.Continuum.BoxModes
