import Maxwell.Continuum.BoxModesL2

/-!
# Removing redundant signed frequencies

Only nonnegative cosine frequencies and strictly positive sine frequencies
are needed. Negative frequencies change a mode by a scalar sign, and a zero
sine frequency makes the mode identically zero.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory
open scoped BigOperators

def frequencySign (c j : Fin 3) (n : ℤ) : ℝ :=
  if j = c ∨ 0 ≤ n then 1 else -1

theorem cubeFactor_abs (N : Fin 3 → ℝ) (c j : Fin 3) (n : ℤ) :
    cubeFactor N c n j = frequencySign c j n • cubeFactor N c |n| j := by
  ext x
  by_cases hj : j = c
  · subst j
    by_cases hn : 0 ≤ n
    · simp [cubeFactor, frequencySign, abs_of_nonneg hn]
    · have hn' : n < 0 := lt_of_not_ge hn
      simp [cubeFactor, frequencySign, cubeCos, intervalCos, abs_of_neg hn', neg_div, neg_mul]
  · by_cases hn : 0 ≤ n
    · simp [cubeFactor, frequencySign, hj, hn, abs_of_nonneg hn]
    · have hn' : n < 0 := lt_of_not_ge hn
      simp [cubeFactor, frequencySign, hj, hn, cubeSin, intervalSin, abs_of_neg hn', neg_div, neg_mul]

theorem cubeMode_abs (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    cubeMode N c ν = (∏ j, frequencySign c j (ν j)) •
      cubeMode N c (fun j => |ν j|) := by
  ext x
  simp only [cubeMode, ContinuousMap.prod_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact congrArg (fun f : C(ClosedCube N, ℝ) => f x) (cubeFactor_abs N c j (ν j))

theorem cubeMode_eq_zero_of_sine_zero (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) (j : Fin 3) (hj : j ≠ c) (hν : ν j = 0) :
    cubeMode N c ν = 0 := by
  ext x
  change (∏ k, cubeFactor N c (ν k) k x) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [cubeFactor, hj, hν, cubeSin, intervalSin]

def admissibleCubeModeL2Span (N : Fin 3 → ℝ) (c : Fin 3) : Submodule ℝ (CubeL2 N) :=
  Submodule.span ℝ (Set.range fun ν : {ν : Fin 3 → ℤ // AdmissibleIndex c ν} =>
    cubeModeL2 N c ν.val)

theorem cubeModeL2_mem_admissible_span (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    cubeModeL2 N c ν ∈ admissibleCubeModeL2Span N c := by
  classical
  by_cases hz : ∃ j, j ≠ c ∧ ν j = 0
  · obtain ⟨j, hj, hν⟩ := hz
    have he := cubeMode_eq_zero_of_sine_zero N c ν j hj hν
    unfold cubeModeL2
    rw [he, map_zero]
    exact Submodule.zero_mem _
  · have hν : AdmissibleIndex c (fun j => |ν j|) := by
      refine ⟨abs_nonneg _, fun j hj => abs_pos.mpr ?_⟩
      intro hn
      exact hz ⟨j, hj, hn⟩
    have he := cubeMode_abs N c ν
    unfold cubeModeL2
    rw [he, map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨_, hν⟩, rfl⟩

theorem admissibleCubeModeL2Span_eq (N : Fin 3 → ℝ) (c : Fin 3) :
    admissibleCubeModeL2Span N c = cubeModeL2Span N c := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨ν, rfl⟩
    exact Submodule.subset_span ⟨ν.val, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨ν, rfl⟩
    exact cubeModeL2_mem_admissible_span N c ν

/-- Completeness uses precisely the frequencies with nonzero sine factors. -/
theorem admissibleCubeModeL2_complete (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) (c : Fin 3) :
    (admissibleCubeModeL2Span N c).topologicalClosure = ⊤ := by
  rw [admissibleCubeModeL2Span_eq]
  exact cubeModeL2_complete N hN c

#print axioms admissibleCubeModeL2_complete

end Maxwell.Continuum.BoxModes
