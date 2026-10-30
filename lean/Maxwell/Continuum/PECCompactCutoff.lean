import Maxwell.Continuum.SchwartzH1Density
import Maxwell.Continuum.H1Curl

/-! A smooth cutoff supported in the interior of an open domain takes
every actual H¹ field into the defining PEC curl-graph closure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory FourierSobolev TopologicalSpace Filter
open scoped SchwartzMap Topology

theorem scalar_schwartz_derivative (θ φ : SchwartzMap Space ℂ) (j : Fin 3) :
    (partialSchwartz j (SchwartzMap.smulLeftCLM ℂ θ φ)).toLp 2 volume =
      scalar (partialSchwartz j θ) (φ.toLp 2 volume)+
        scalar θ ((partialSchwartz j φ).toLp 2 volume) := by
  change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
    (partialSchwartz j (SchwartzMap.smulLeftCLM ℂ θ φ)) = _
  rw [partialSchwartz_product, map_add]
  exact congrArg₂ (fun a b : ScalarL2 => a+b)
    (scalar_schwartz (partialSchwartz j θ) φ).symm
    (scalar_schwartz θ (partialSchwartz j φ)).symm

def compactCutoffTest (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hc : HasCompactSupport θ) (hΩ : tsupport θ ⊆ Ω) (φ : SchwartzField) : TestField Ω :=
  fun j =>
    ⟨SchwartzMap.smulLeftCLM ℂ θ (φ j),
      (SchwartzMap.smulLeftCLM ℂ θ (φ j)).smooth',
      hc.of_isClosed_subset isClosed_closure
        ((SchwartzMap.tsupport_smulLeftCLM_subset θ (φ j)).trans Set.inter_subset_right),
      ((SchwartzMap.tsupport_smulLeftCLM_subset θ (φ j)).trans Set.inter_subset_right).trans hΩ⟩

theorem compactCutoffTest_schwartz (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hc : HasCompactSupport θ) (hΩ : tsupport θ ⊆ Ω) (φ : SchwartzField) :
    testSchwartzField Ω (compactCutoffTest Ω θ hc hΩ φ) =
      fun j => SchwartzMap.smulLeftCLM ℂ θ (φ j) := by
  funext j
  ext x
  rfl

theorem compactCutoffTest_field (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hc : HasCompactSupport θ) (hΩ : tsupport θ ⊆ Ω) (φ : SchwartzField) :
    testFieldL2 Ω (compactCutoffTest Ω θ hc hΩ φ) = field θ (schwartzFieldL2 φ) := by
  change schwartzFieldL2 (testSchwartzField Ω (compactCutoffTest Ω θ hc hΩ φ)) = _
  rw [compactCutoffTest_schwartz]
  apply PiLp.ext
  intro j
  exact (scalar_schwartz θ (φ j)).symm

theorem field_tendsto_of_components {I : Type*} {l : Filter I}
    (F : I → FieldL2) (f : FieldL2)
    (h : ∀ j, Tendsto (fun t => F t j) l (𝓝 (f j))) : Tendsto F l (𝓝 f) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ScalarL2)).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr h)

theorem cutoff_curlGraph_mem_pecGraph (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hc : HasCompactSupport θ) (hΩ : tsupport θ ⊆ Ω) {f : FieldL2} (Df : H1Data f) :
    (h1Product θ Df).curlGraph ∈ pecGraph Ω := by
  have ha (k : Fin 3) := scalar_schwartz_H1_approximation (f k)
    (fun j => Df.derivative j k) (fun j => Df.weak_derivative j k)
  choose φ hf hd using ha
  let u (n : ℕ) : SchwartzField := fun k => φ k n
  let t (n : ℕ) : TestField Ω := compactCutoffTest Ω θ hc hΩ (u n)
  have hfield : Tendsto (fun n => testFieldL2 Ω (t n)) atTop (𝓝 (field θ f)) := by
    simp only [t, compactCutoffTest_field]
    apply (field θ).continuous.continuousAt.tendsto.comp
    exact field_tendsto_of_components _ f hf
  have hpartial (j k : Fin 3) : Tendsto
      (fun n => (partialSchwartz j (testSchwartzField Ω (t n) k)).toLp 2 volume)
      atTop (𝓝 ((h1Product θ Df).derivative j k)) := by
    have ht := ((scalar (partialSchwartz j θ)).continuous.continuousAt.tendsto.comp (hf k)).add
      ((scalar θ).continuous.continuousAt.tendsto.comp (hd k j))
    simpa only [Function.comp_def, t, compactCutoffTest_schwartz, u,
      scalar_schwartz_derivative, h1Product, PiLp.add_apply, field_apply] using ht
  have hcurl : Tendsto (fun n => schwartzFieldL2 (curlSchwartz (testSchwartzField Ω (t n))))
      atTop (𝓝 (h1Product θ Df).curl) := by
    apply field_tendsto_of_components
    intro i
    have ht := (hpartial (i+1) (i+2)).sub (hpartial (i+2) (i+1))
    convert ht using 1
    · funext n
      change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
        (partialSchwartz (i+1) (testSchwartzField Ω (t n) (i+2))-
          partialSchwartz (i+2) (testSchwartzField Ω (t n) (i+1))) = _
      exact map_sub _ _ _
    · rfl
  have hgraph : Tendsto (fun n => testCurlGraph Ω (t n)) atTop (𝓝 (h1Product θ Df).curlGraph) :=
    (WithLp.prod_continuous_toLp 2 FieldL2 FieldL2).continuousAt.tendsto.comp
      (hfield.prodMk_nhds hcurl)
  apply (testCurlGraph Ω).range.isClosed_topologicalClosure.mem_of_tendsto hgraph
  exact Filter.Eventually.of_forall fun n =>
    (testCurlGraph Ω).range.le_topologicalClosure ⟨t n, rfl⟩

#print axioms cutoff_curlGraph_mem_pecGraph

end Maxwell.Continuum.SchwartzMultiplier
