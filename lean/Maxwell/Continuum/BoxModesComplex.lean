import Maxwell.Continuum.BoxModesAdmissible
import Maxwell.Continuum.BoxModesMeasure

/-!
# Complete complex modes on the physical box

Real scalar completeness is complexified by the actual real/imaginary-part
maps on L², then transported through the volume-preserving box embedding.
The resulting family has exactly the admissible PEC component frequencies.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory
open scoped InnerProductSpace ENNReal

abbrev CubeComplexL2 (N : Fin 3 → ℝ) := Lp ℂ 2 (cubeMeasure N)
abbrev BoxComplexL2 (N : Fin 3 → ℝ) := Lp ℂ 2 (volume.restrict (openBox N))

def cubeRealToComplex (N : Fin 3 → ℝ) : CubeL2 N →L[ℝ] CubeComplexL2 N :=
  Complex.ofRealCLM.compLpL 2 (cubeMeasure N)

def cubeComplexModeL2 (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    CubeComplexL2 N := cubeRealToComplex N (cubeModeL2 N c ν)

def admissibleCubeComplexModeSpan (N : Fin 3 → ℝ) (c : Fin 3) :
    Submodule ℂ (CubeComplexL2 N) :=
  Submodule.span ℂ (Set.range fun ν : {ν : Fin 3 → ℤ // AdmissibleIndex c ν} =>
    cubeComplexModeL2 N c ν.val)

theorem cubeRealToComplex_mem_closure (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (u : CubeL2 N) :
    cubeRealToComplex N u ∈ (admissibleCubeComplexModeSpan N c).topologicalClosure := by
  let P := (admissibleCubeComplexModeSpan N c).topologicalClosure
  have h : (admissibleCubeModeL2Span N c).topologicalClosure ≤
      (P.restrictScalars ℝ).comap (cubeRealToComplex N).toLinearMap := by
    apply (admissibleCubeModeL2Span N c).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨ν, rfl⟩
      exact (admissibleCubeComplexModeSpan N c).le_topologicalClosure
        (Submodule.subset_span ⟨ν, rfl⟩)
    · exact (admissibleCubeComplexModeSpan N c).isClosed_topologicalClosure.preimage
        (cubeRealToComplex N).continuous
  exact h (by rw [admissibleCubeModeL2_complete N hN c]; trivial)

theorem cubeComplex_real_imag_decomposition (N : Fin 3 → ℝ) (u : CubeComplexL2 N) :
    u = cubeRealToComplex N (Complex.reCLM.compLp u) +
      Complex.I • cubeRealToComplex N (Complex.imCLM.compLp u) := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp u, Complex.imCLM.coeFn_compLp u,
    Complex.ofRealCLM.coeFn_compLp (Complex.reCLM.compLp u),
    Complex.ofRealCLM.coeFn_compLp (Complex.imCLM.compLp u),
    Lp.coeFn_add (cubeRealToComplex N (Complex.reCLM.compLp u))
      (Complex.I • cubeRealToComplex N (Complex.imCLM.compLp u)),
    Lp.coeFn_smul Complex.I (cubeRealToComplex N (Complex.imCLM.compLp u))]
    with x hr hi her hei ha hs
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  change u x = Complex.ofRealCLM.compLp (Complex.reCLM.compLp u) x +
    Complex.I * Complex.ofRealCLM.compLp (Complex.imCLM.compLp u) x
  rw [her, hei, hr, hi]
  simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  exact (Complex.re_add_im (u x)).symm.trans (by ring)

theorem admissibleCubeComplexMode_complete (N : Fin 3 → ℝ)
    (hN : ∀ j, 0 < N j) (c : Fin 3) :
    (admissibleCubeComplexModeSpan N c).topologicalClosure = ⊤ := by
  apply top_unique
  intro u _
  rw [cubeComplex_real_imag_decomposition N u]
  exact Submodule.add_mem _ (cubeRealToComplex_mem_closure N hN c _)
    (Submodule.smul_mem _ Complex.I (cubeRealToComplex_mem_closure N hN c _))

def boxComplexPullback (N : Fin 3 → ℝ) : BoxComplexL2 N →ₗᵢ[ℂ] CubeComplexL2 N :=
  Lp.compMeasurePreservingₗᵢ ℂ (cubePoint N) (cubePoint_measurePreserving N)

def boxComplexModeL2 (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    BoxComplexL2 N := Complex.ofRealCLM.compLp (boxModeL2 N c ν)

theorem boxComplexModeL2_pullback (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    boxComplexPullback N (boxComplexModeL2 N c ν) = cubeComplexModeL2 N c ν := by
  apply Lp.ext
  have hp := Lp.coeFn_compMeasurePreserving (boxComplexModeL2 N c ν)
    (cubePoint_measurePreserving N)
  have hs := (cubePoint_measurePreserving N).quasiMeasurePreserving.ae
    (Complex.ofRealCLM.coeFn_compLp (boxModeL2 N c ν))
  have hr := Lp.coeFn_compMeasurePreserving (boxModeL2 N c ν)
    (cubePoint_measurePreserving N)
  have hc := Complex.ofRealCLM.coeFn_compLp (cubeModeL2 N c ν)
  change (boxL2Pullback N (boxModeL2 N c ν) : ClosedCube N → ℝ) =ᵐ[cubeMeasure N]
    (boxModeL2 N c ν : Point → ℝ) ∘ cubePoint N at hr
  rw [boxModeL2_pullback] at hr
  filter_upwards [hp, hs, hr, hc] with x hp hs hr hc
  exact hp.trans (hs.trans (congrArg Complex.ofRealCLM hr.symm)) |>.trans hc.symm

def admissibleBoxComplexModeSpan (N : Fin 3 → ℝ) (c : Fin 3) :
    Submodule ℂ (BoxComplexL2 N) :=
  Submodule.span ℂ (Set.range fun ν : {ν : Fin 3 → ℤ // AdmissibleIndex c ν} =>
    boxComplexModeL2 N c ν.val)

/-- Completeness on the actual complex physical L² space, with the genuine
admissible mixed sine/cosine frequencies and ordinary Euclidean volume. -/
theorem admissibleBoxComplexMode_complete (N : Fin 3 → ℝ)
    (hN : ∀ j, 0 < N j) (c : Fin 3) :
    (admissibleBoxComplexModeSpan N c).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro u hu
  have hu' : boxComplexPullback N u ∈
      ((admissibleCubeComplexModeSpan N c).topologicalClosure)ᗮ := by
    rw [Submodule.orthogonal_closure]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨ν, rfl⟩ := hv
      change inner ℂ (cubeComplexModeL2 N c ν.val) (boxComplexPullback N u) = 0
      rw [← boxComplexModeL2_pullback, (boxComplexPullback N).inner_map_map]
      exact hu _ ((admissibleBoxComplexModeSpan N c).le_topologicalClosure
        (Submodule.subset_span ⟨ν, rfl⟩))
    | zero => exact inner_zero_left _
    | add v w _ _ hv hw => rw [inner_add_left, hv, hw, add_zero]
    | smul a v _ hv => rw [inner_smul_left, hv, mul_zero]
  have hp : boxComplexPullback N u = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    exact hu' _ (by rw [admissibleCubeComplexMode_complete N hN c]; trivial)
  have hz : u = 0 := (boxComplexPullback N).injective (hp.trans (map_zero _).symm)
  exact hz ▸ Submodule.zero_mem _

#print axioms admissibleCubeComplexMode_complete
#print axioms admissibleBoxComplexMode_complete

end Maxwell.Continuum.BoxModes
