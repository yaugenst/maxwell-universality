import Maxwell.Continuum.PEC
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Identification of the physical L² space on an open PEC domain

The closure of compactly supported smooth fields is exactly the global L²
fields vanishing almost everywhere outside the open set. Test-function
separation is proved from the fundamental lemma for distributions, rather
than being assumed as a density hypothesis.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace Distributions SchwartzMap

theorem testFieldL2_coe_ae (Ω : Opens Space) (u : TestField Ω) (i : Fin 3) :
    (testFieldL2 Ω u i : Space → ℂ) =ᵐ[volume] u i :=
  (testSchwartz Ω (u i)).coeFn_toLp 2 volume

theorem testFieldL2_single (Ω : Opens Space) (i : Fin 3)
    (f : TestFunction Ω ℂ ⊤) :
    testFieldL2 Ω (Pi.single i f) =
      PiLp.single 2 i ((testSchwartz Ω f).toLp 2 volume) := by
  classical
  apply PiLp.ext
  intro j
  change ((testSchwartz Ω ((Pi.single i f : TestField Ω) j)).toLp 2 volume) = _
  by_cases hji : j = i
  · subst j
    simp
  · rw [Pi.single_eq_of_ne hji, (testSchwartz Ω).map_zero, PiLp.single_eq_of_ne 2 hji]
    exact (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_zero

theorem field_inner_single_left (i : Fin 3) (f : ScalarL2) (u : FieldL2) :
    inner ℂ (PiLp.single 2 i f) u = inner ℂ f (u i) := by
  classical
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [PiLp.single_eq_same]
  · intro j _ hji
    rw [PiLp.single_eq_of_ne 2 hji, inner_zero_left]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem testFieldL2_inner_eq_integral (Ω : Opens Space)
    (f : TestFunction Ω ℂ ⊤) (u : ScalarL2) :
    inner ℂ ((testSchwartz Ω f).toLp 2 volume) u =
      ∫ x, inner ℂ (f x) (u x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(testSchwartz Ω f).coeFn_toLp 2 volume] with x hx
  rw [hx]
  rfl

theorem orthogonal_testFieldL2_vanishes (Ω : Opens Space) (u : FieldL2)
    (hu : u ∈ (testFieldL2 Ω).rangeᗮ) :
    ∀ i, ∀ᵐ x ∂volume, x ∈ Ω → u i x = 0 := by
  intro i
  apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp (u i)).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω)
  intro g hg hgc hgs
  let f : TestFunction Ω ℂ ⊤ :=
    ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp hg,
      hgc.comp_left (show Complex.ofReal 0 = 0 from Complex.ofReal_zero),
      (tsupport_comp_subset (show Complex.ofReal 0 = 0 from Complex.ofReal_zero) g).trans hgs⟩
  have h := hu (testFieldL2 Ω (Pi.single i f)) ⟨Pi.single i f, rfl⟩
  rw [testFieldL2_single, field_inner_single_left, testFieldL2_inner_eq_integral] at h
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change g x • u i x = inner ℂ (g x : ℂ) (u i x)
    simp [RCLike.inner_apply, Complex.real_smul, mul_comm]

theorem orthogonal_testFieldL2_of_vanishes (Ω : Opens Space) (u : FieldL2)
    (hu : ∀ i, ∀ᵐ x ∂volume, x ∈ Ω → u i x = 0) :
    u ∈ (testFieldL2 Ω).rangeᗮ := by
  rintro _ ⟨v, rfl⟩
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [testFieldL2_coe_ae Ω v i, hu i] with x hx hux
  simp only [Pi.zero_apply]
  by_cases hΩ : x ∈ Ω
  · rw [hux hΩ, inner_zero_right]
  · rw [hx, (v i).zero_on_compl hΩ]
    simp only [Pi.zero_apply, inner_zero_left]

/-- Test-function separation identifies the full orthogonal complement. -/
theorem mem_orthogonal_testFieldL2_iff (Ω : Opens Space) (u : FieldL2) :
    u ∈ (testFieldL2 Ω).rangeᗮ ↔
      ∀ i, ∀ᵐ x ∂volume, x ∈ Ω → u i x = 0 :=
  ⟨orthogonal_testFieldL2_vanishes Ω u, orthogonal_testFieldL2_of_vanishes Ω u⟩

/-- A global L² field represents a physical field on Ω if its zero extension
vanishes almost everywhere outside Ω. -/
def FieldSupported (Ω : Opens Space) (u : FieldL2) : Prop :=
  ∀ i, ∀ᵐ x ∂volume, x ∉ Ω → u i x = 0

theorem mem_testL2Closure_of_supported (Ω : Opens Space) (u : FieldL2)
    (hu : FieldSupported Ω u) : u ∈ testL2Closure Ω := by
  rw [testL2Closure, ← Submodule.orthogonal_orthogonal_eq_closure]
  intro v hv
  have hvzero := orthogonal_testFieldL2_vanishes Ω v hv
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hvzero i, hu i] with x hvx hux
  simp only [Pi.zero_apply]
  by_cases hΩ : x ∈ Ω
  · rw [hvx hΩ, inner_zero_left]
  · rw [hux hΩ, inner_zero_right]

/-- The L² part of a scalar field outside the open domain. -/
def outsideL2 (Ω : Opens Space) (u : ScalarL2) : ScalarL2 :=
  MemLp.toLp ((Ω : Set Space)ᶜ.indicator (u : Space → ℂ))
    (MemLp.indicator Ω.isOpen.measurableSet.compl (Lp.memLp u))

theorem outsideL2_coe_ae (Ω : Opens Space) (u : ScalarL2) :
    (outsideL2 Ω u : Space → ℂ) =ᵐ[volume]
      (Ω : Set Space)ᶜ.indicator (u : Space → ℂ) :=
  MemLp.coeFn_toLp _

theorem outsideL2_vanishes_on (Ω : Opens Space) (u : ScalarL2) :
    ∀ᵐ x ∂volume, x ∈ Ω → outsideL2 Ω u x = 0 := by
  filter_upwards [outsideL2_coe_ae Ω u] with x hx hΩ
  rw [hx, Set.indicator_of_notMem (by simpa using hΩ)]

theorem outsideL2_inner (Ω : Opens Space) (u : ScalarL2) :
    inner ℂ (outsideL2 Ω u) (outsideL2 Ω u) = inner ℂ (outsideL2 Ω u) u := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [outsideL2_coe_ae Ω u] with x hx
  by_cases hΩ : x ∈ Ω
  · rw [hx, Set.indicator_of_notMem (by simpa using hΩ)]
    simp only [inner_zero_left]
  · rw [hx, Set.indicator_of_mem hΩ]

theorem supported_of_mem_testL2Closure (Ω : Opens Space) (u : FieldL2)
    (hu : u ∈ testL2Closure Ω) : FieldSupported Ω u := by
  classical
  intro i
  let v : FieldL2 := PiLp.single 2 i (outsideL2 Ω (u i))
  have hv : v ∈ (testFieldL2 Ω).rangeᗮ := by
    apply orthogonal_testFieldL2_of_vanishes
    intro j
    by_cases hji : j = i
    · subst j
      simpa [v] using outsideL2_vanishes_on Ω (u i)
    · exact Filter.Eventually.of_forall fun x _ => by
        simp [v, hji]
  have hvclosure : v ∈ (testL2Closure Ω)ᗮ := by
    simpa only [testL2Closure, Submodule.orthogonal_closure] using hv
  have hinner : inner ℂ v u = 0 :=
    (testL2Closure Ω).inner_left_of_mem_orthogonal hu hvclosure
  have houtzero : outsideL2 Ω (u i) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [outsideL2_inner]
    exact (field_inner_single_left i _ u).symm.trans hinner
  filter_upwards [outsideL2_coe_ae Ω (u i), Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := (volume : Measure Space))] with x hx hz hΩ
  rw [houtzero, hz, Set.indicator_of_mem hΩ] at hx
  exact hx.symm

/-- The PEC ambient space is the actual L² space on Ω, represented by zero
extension in global L². No smooth-test density assumption remains. -/
theorem mem_testL2Closure_iff_supported (Ω : Opens Space) (u : FieldL2) :
    u ∈ testL2Closure Ω ↔ FieldSupported Ω u :=
  ⟨supported_of_mem_testL2Closure Ω u, mem_testL2Closure_of_supported Ω u⟩

theorem test_curl_supported (Ω : Opens Space) (u : TestField Ω) :
    FieldSupported Ω (schwartzFieldL2 (curlSchwartz (testSchwartzField Ω u))) := by
  intro i
  filter_upwards [(curlSchwartz (testSchwartzField Ω u) i).coeFn_toLp 2 volume]
    with x hx hΩ
  change (curlSchwartz (testSchwartzField Ω u) i).toLp 2 volume x = 0
  rw [hx]
  have hz (j k : Fin 3) : partialSchwartz j (testSchwartz Ω (u k)) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hΩ
    apply (u k).tsupport_subset
    exact (SchwartzMap.tsupport_lineDerivOp_subset (coordinateDirection j)
      (testSchwartz Ω (u k))) hs
  change (partialSchwartz (i + 1) (testSchwartz Ω (u (i + 2))) -
    partialSchwartz (i + 2) (testSchwartz Ω (u (i + 1)))) x = 0
  rw [sub_apply, hz, hz, sub_self]

/-- The weak curl of a PEC field is also an L² field on Ω. This follows from
support preservation of derivatives on the test core and graph closure. -/
theorem pecCurl_mem_testL2Closure (Ω : Opens Space) (u : pecGraph Ω) :
    pecCurl Ω u ∈ testL2Closure Ω := by
  have h : pecGraph Ω ≤ (testL2Closure Ω).comap graphCurl.toLinearMap := by
    apply (testCurlGraph Ω).range.topologicalClosure_minimal
    · rintro _ ⟨v, rfl⟩
      exact mem_testL2Closure_of_supported Ω _ (test_curl_supported Ω v)
    · exact (testFieldL2 Ω).range.isClosed_topologicalClosure.preimage graphCurl.continuous
  exact h u.property

theorem pecCurl_supported (Ω : Opens Space) (u : pecGraph Ω) :
    FieldSupported Ω (pecCurl Ω u) :=
  supported_of_mem_testL2Closure Ω _ (pecCurl_mem_testL2Closure Ω u)

theorem pecInclusion_supported (Ω : Opens Space) (u : pecGraph Ω) :
    FieldSupported Ω (pecInclusion Ω u) :=
  supported_of_mem_testL2Closure Ω _ (pecInclusion_mem_testL2Closure Ω u)

end Maxwell.Continuum
