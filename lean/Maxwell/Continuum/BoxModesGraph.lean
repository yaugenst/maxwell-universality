import Maxwell.Continuum.BoxModesGraphTraces

/-!
# Box modes belong to the actual closed PEC curl graph

Each mode is approximated by the explicit compactly supported smooth test
fields. The field and every tangential derivative converge in L², so the
pair consisting of the mode and its literal curl belongs to the graph
closure defining `pecGraph`.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Filter MeasureTheory
open scoped Topology

def componentCurlL2 (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) : FieldL2 :=
  WithLp.toLp 2 (fun i =>
    (if i + 2 = c then zeroExtendedBoxPartial N ν c (i + 1) else 0) -
    (if i + 1 = c then zeroExtendedBoxPartial N ν c (i + 2) else 0))

theorem testSchwartzField_single (Ω : TopologicalSpace.Opens Space) (c : Fin 3)
    (f : TestFunction Ω ℂ ⊤) :
    testSchwartzField Ω (Pi.single c f) = Pi.single c (testSchwartz Ω f) := by
  funext i
  by_cases hi : i = c
  · subst i
    simp [testSchwartzField]
  · simp [testSchwartzField, hi]

theorem cutoffTestField_curl_component (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c i : Fin 3) (n : ℕ) :
    schwartzFieldL2 (curlSchwartz (testSchwartzField (boxDomain N)
      (cutoffTestField N ν c (cutoffWidth n) (cutoffWidth_pos n)))) i =
    (if i + 2 = c then cutoffPartialL2 N ν c (i + 1) n else 0) -
    (if i + 1 = c then cutoffPartialL2 N ν c (i + 2) n else 0) := by
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (curlSchwartz (testSchwartzField (boxDomain N)
      (Pi.single c (cutoffTestScalar N ν c (cutoffWidth n) (cutoffWidth_pos n)))) i) = _
  rw [testSchwartzField_single, curlSchwartz_apply]
  simp only [Pi.single_apply]
  rw [map_sub]
  split_ifs
  · rfl
  · simp only [map_zero]
    rfl
  · simp only [map_zero]
    rfl
  · simp only [map_zero]

theorem tendsto_fieldL2_of_components (F : ℕ → FieldL2) (f : FieldL2)
    (h : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (f i))) : Tendsto F atTop (𝓝 f) := by
  have hp := tendsto_pi_nhds.mpr h
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ScalarL2)).continuousAt.tendsto.comp hp

theorem cutoffTestField_L2_tendsto (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    Tendsto (fun n => testFieldL2 (boxDomain N)
      (cutoffTestField N ν c (cutoffWidth n) (cutoffWidth_pos n)))
      atTop (𝓝 (componentBoxMode N c ν)) := by
  apply tendsto_fieldL2_of_components
  intro i
  simp only [cutoffTestField, testFieldL2_single]
  by_cases hi : i = c
  · subst i
    simp only [componentBoxMode, PiLp.single_eq_same]
    change Tendsto (cutoffScalarL2 N ν c) atTop (𝓝 (zeroExtendedBoxMode N c ν))
    exact cutoffScalarL2_tendsto N ν c
  · simpa only [componentBoxMode, PiLp.single_eq_of_ne 2 hi] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ScalarL2)) atTop (𝓝 0))

theorem cutoffTestField_curl_tendsto (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    Tendsto (fun n => schwartzFieldL2 (curlSchwartz (testSchwartzField (boxDomain N)
      (cutoffTestField N ν c (cutoffWidth n) (cutoffWidth_pos n)))))
      atTop (𝓝 (componentCurlL2 N ν c)) := by
  apply tendsto_fieldL2_of_components
  intro i
  have hneq : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  have hleft : Tendsto (fun n => if i + 2 = c then cutoffPartialL2 N ν c (i + 1) n else 0)
      atTop (𝓝 (if i + 2 = c then zeroExtendedBoxPartial N ν c (i + 1) else 0)) := by
    split_ifs with hi
    · exact cutoffPartialL2_tendsto N hN ν c (i + 1)
        (fun he => hneq (he.trans hi.symm))
    · exact tendsto_const_nhds
  have hright : Tendsto (fun n => if i + 1 = c then cutoffPartialL2 N ν c (i + 2) n else 0)
      atTop (𝓝 (if i + 1 = c then zeroExtendedBoxPartial N ν c (i + 2) else 0)) := by
    split_ifs with hi
    · exact cutoffPartialL2_tendsto N hN ν c (i + 2)
        (fun he => hneq (hi.trans he.symm))
    · exact tendsto_const_nhds
  simpa only [cutoffTestField_curl_component, componentCurlL2] using hleft.sub hright

def componentCurlGraph (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) : CurlGraphAmbient :=
  WithLp.toLp 2 (componentBoxMode N c ν, componentCurlL2 N ν c)

/-- A sequence in the defining smooth PEC graph converges to the actual
box-mode/curl pair in the graph norm. -/
theorem cutoffTestField_graph_tendsto (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    Tendsto (fun n => testCurlGraph (boxDomain N)
      (cutoffTestField N ν c (cutoffWidth n) (cutoffWidth_pos n)))
      atTop (𝓝 (componentCurlGraph N ν c)) :=
  (WithLp.prod_continuous_toLp 2 FieldL2 FieldL2).continuousAt.tendsto.comp
    ((cutoffTestField_L2_tendsto N ν c).prodMk_nhds
      (cutoffTestField_curl_tendsto N hN ν c))

/-- Genuine graph-domain membership, proved by explicit smooth approximation. -/
theorem componentCurlGraph_mem_pecGraph (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    componentCurlGraph N ν c ∈ pecGraph (boxDomain N) := by
  apply (testCurlGraph (boxDomain N)).range.isClosed_topologicalClosure.mem_of_tendsto
    (cutoffTestField_graph_tendsto N hN ν c)
  exact Filter.Eventually.of_forall fun n =>
    (testCurlGraph (boxDomain N)).range.le_topologicalClosure
      ⟨cutoffTestField N ν c (cutoffWidth n) (cutoffWidth_pos n), rfl⟩

def pecComponentMode (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) (ν : Fin 3 → ℤ) (c : Fin 3) :
    pecGraph (boxDomain N) :=
  ⟨componentCurlGraph N ν c, componentCurlGraph_mem_pecGraph N hN ν c⟩

@[simp] theorem pecComponentMode_field (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    pecInclusion (boxDomain N) (pecComponentMode N hN ν c) = componentBoxMode N c ν := rfl

@[simp] theorem pecComponentMode_curl (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    pecCurl (boxDomain N) (pecComponentMode N hN ν c) = componentCurlL2 N ν c := rfl

#print axioms componentCurlGraph_mem_pecGraph

end Maxwell.Continuum.BoxModes
