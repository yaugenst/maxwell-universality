import Maxwell.Continuum.WeakCurl
import Mathlib.Analysis.Distribution.TestFunction

/-!
# PEC fields as the closure of compactly supported smooth curl graphs

This is the defining H₀(curl) closure on an open set.  Every graph element
has an actual distributional curl; no boundary regularity or identification
with a trigonometric expansion is assumed.  Those identifications are
separate theorems, not fields in an input structure.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory TopologicalSpace
open scoped SchwartzMap Distributions

abbrev SchwartzField := Fin 3 → SchwartzMap Space ℂ
abbrev TestField (Ω : Opens Space) := Fin 3 → TestFunction Ω ℂ ⊤

def schwartzFieldL2 : SchwartzField →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)).comp
        (ContinuousLinearMap.proj i))

@[simp] theorem schwartzFieldL2_apply (u : SchwartzField) (i : Fin 3) :
    schwartzFieldL2 u i = (u i).toLp 2 volume := rfl

def partialSchwartz (i : Fin 3) : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap Space ℂ) (coordinateDirection i)

def curlSchwartz : SchwartzField →L[ℂ] SchwartzField :=
  ContinuousLinearMap.pi fun i =>
    (partialSchwartz (i + 1)).comp (ContinuousLinearMap.proj (i + 2)) -
      (partialSchwartz (i + 2)).comp (ContinuousLinearMap.proj (i + 1))

@[simp] theorem curlSchwartz_apply (u : SchwartzField) (i : Fin 3) :
    curlSchwartz u i = partialSchwartz (i + 1) (u (i + 2)) -
      partialSchwartz (i + 2) (u (i + 1)) := rfl

theorem schwartz_curl_distribution (u : SchwartzField) :
    curlDistribution (fieldDistribution (schwartzFieldL2 u)) =
      fieldDistribution (schwartzFieldL2 (curlSchwartz u)) := by
  ext i
  simp only [curlDistribution_apply, fieldDistribution_apply, schwartzFieldL2_apply,
    curlSchwartz_apply, Lp.toTemperedDistribution_toLp_eq]
  simp only [partialDistribution, partialSchwartz,
    LineDeriv.lineDerivOpCLM_apply, TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq,
    map_sub]

def schwartzCurlGraph : SchwartzField →L[ℂ] CurlGraphAmbient :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ FieldL2 FieldL2).symm.toContinuousLinearMap.comp
    (schwartzFieldL2.prod (schwartzFieldL2.comp curlSchwartz))

theorem schwartzCurlGraph_mem (u : SchwartzField) :
    schwartzCurlGraph u ∈ weakCurlGraph :=
  (mem_weakCurlGraph _).mpr (schwartz_curl_distribution u)

/-- A smooth compactly supported test function is a Schwartz function. -/
def testSchwartz (Ω : Opens Space) : TestFunction Ω ℂ ⊤ →ₗ[ℂ] SchwartzMap Space ℂ where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl

def testSchwartzField (Ω : Opens Space) : TestField Ω →ₗ[ℂ] SchwartzField :=
  LinearMap.pi fun i => (testSchwartz Ω).comp (LinearMap.proj i)

def testFieldL2 (Ω : Opens Space) : TestField Ω →ₗ[ℂ] FieldL2 :=
  schwartzFieldL2.toLinearMap.comp (testSchwartzField Ω)

def testCurlGraph (Ω : Opens Space) : TestField Ω →ₗ[ℂ] CurlGraphAmbient :=
  schwartzCurlGraph.toLinearMap.comp (testSchwartzField Ω)

/-- H₀(curl;Ω), realized as a closed graph subspace of L²×L². -/
def pecGraph (Ω : Opens Space) : Submodule ℂ CurlGraphAmbient :=
  (testCurlGraph Ω).range.topologicalClosure

instance (Ω : Opens Space) : CompleteSpace (pecGraph Ω) :=
  Submodule.topologicalClosure.completeSpace _

theorem pecGraph_le_weakCurlGraph (Ω : Opens Space) : pecGraph Ω ≤ weakCurlGraph := by
  apply (testCurlGraph Ω).range.topologicalClosure_minimal _ weakCurlGraph_isClosed
  rintro _ ⟨u, rfl⟩
  exact schwartzCurlGraph_mem _

def pecInclusion (Ω : Opens Space) : pecGraph Ω →L[ℂ] FieldL2 :=
  graphField.comp (pecGraph Ω).subtypeL

def pecCurl (Ω : Opens Space) : pecGraph Ω →L[ℂ] FieldL2 :=
  graphCurl.comp (pecGraph Ω).subtypeL

theorem pecInclusion_injective (Ω : Opens Space) : Function.Injective (pecInclusion Ω) := by
  intro u v huv
  apply Subtype.ext
  apply (WithLp.equiv 2 (FieldL2 × FieldL2)).injective
  apply Prod.ext
  · exact huv
  · exact weakCurl_unique (pecGraph_le_weakCurlGraph Ω u.property)
      (pecGraph_le_weakCurlGraph Ω v.property) huv

theorem pecInclusion_norm_le (Ω : Opens Space) (u : pecGraph Ω) :
    ‖pecInclusion Ω u‖ ≤ ‖u‖ := WithLp.norm_fst_le (α := FieldL2) u.val

theorem pecCurl_norm_le (Ω : Opens Space) (u : pecGraph Ω) :
    ‖pecCurl Ω u‖ ≤ ‖u‖ := WithLp.norm_snd_le (α := FieldL2) u.val

theorem pec_curl_distribution (Ω : Opens Space) (u : pecGraph Ω) :
    curlDistribution (fieldDistribution (pecInclusion Ω u)) =
      fieldDistribution (pecCurl Ω u) :=
  (mem_weakCurlGraph _).mp (pecGraph_le_weakCurlGraph Ω u.property)

theorem pec_graph_inner (Ω : Opens Space) (u v : pecGraph Ω) :
    inner ℂ u v = inner ℂ (pecInclusion Ω u) (pecInclusion Ω v) +
      inner ℂ (pecCurl Ω u) (pecCurl Ω v) :=
  WithLp.prod_inner_apply u.val v.val

/-- The L² closure of compactly supported smooth fields in the open domain.
The support characterization is proved separately in `PECSupport`. -/
def testL2Closure (Ω : Opens Space) : Submodule ℂ FieldL2 :=
  (testFieldL2 Ω).range.topologicalClosure

instance (Ω : Opens Space) : CompleteSpace (testL2Closure Ω) :=
  Submodule.topologicalClosure.completeSpace _

theorem pecInclusion_mem_testL2Closure (Ω : Opens Space) (u : pecGraph Ω) :
    pecInclusion Ω u ∈ testL2Closure Ω := by
  have h : pecGraph Ω ≤ (testL2Closure Ω).comap graphField.toLinearMap := by
    apply (testCurlGraph Ω).range.topologicalClosure_minimal
    · rintro _ ⟨v, rfl⟩
      exact (testFieldL2 Ω).range.le_topologicalClosure ⟨v, rfl⟩
    · exact (testFieldL2 Ω).range.isClosed_topologicalClosure.preimage graphField.continuous
  exact h u.property

def pecDomainInclusion (Ω : Opens Space) : pecGraph Ω →L[ℂ] testL2Closure Ω :=
  (pecInclusion Ω).codRestrict (testL2Closure Ω) (pecInclusion_mem_testL2Closure Ω)

theorem pecDomainInclusion_injective (Ω : Opens Space) :
    Function.Injective (pecDomainInclusion Ω) := by
  intro u v h
  exact pecInclusion_injective Ω (congrArg Subtype.val h)

theorem pecDomainInclusion_norm_le (Ω : Opens Space) (u : pecGraph Ω) :
    ‖pecDomainInclusion Ω u‖ ≤ ‖u‖ := pecInclusion_norm_le Ω u

theorem pecDomainInclusion_dense (Ω : Opens Space) :
    DenseRange (pecDomainInclusion Ω) := by
  rw [DenseRange, Subtype.dense_iff]
  intro u hu
  apply closure_mono (s := (testFieldL2 Ω).range) _ hu
  rintro _ ⟨v, rfl⟩
  let w : pecGraph Ω := ⟨testCurlGraph Ω v,
    (testCurlGraph Ω).range.le_topologicalClosure ⟨v, rfl⟩⟩
  exact ⟨pecDomainInclusion Ω w, ⟨w, rfl⟩, rfl⟩

end Maxwell.Continuum
