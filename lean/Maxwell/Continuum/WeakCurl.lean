import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The distributional curl on actual continuum fields

Fields are three complex L² functions on Euclidean three-space.  The curl
graph is defined by equality of tempered distributions, rather than by a
finite stencil or an assumed operator.  Injectivity of the L²-to-distribution
map proves uniqueness of the weak curl.  Closedness gives a Hilbert graph
space, also used for the closure imposing the PEC boundary condition.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory
open scoped SchwartzMap

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev ScalarL2 := Lp ℂ 2 (volume : Measure Space)
abbrev FieldL2 := PiLp 2 (fun _ : Fin 3 => ScalarL2)
abbrev ScalarDistribution := TemperedDistribution Space ℂ
abbrev FieldDistribution := Fin 3 → ScalarDistribution
abbrev CurlGraphAmbient := WithLp 2 (FieldL2 × FieldL2)

/-- The literal Cartesian unit vector, in the spatial (real) Hilbert space. -/
def coordinateDirection (i : Fin 3) : Space := PiLp.single 2 i 1

def fieldDistribution : FieldL2 →L[ℂ] FieldDistribution :=
  ContinuousLinearMap.pi fun i =>
    (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2).comp
      (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) i)

@[simp] theorem fieldDistribution_apply (u : FieldL2) (i : Fin 3) :
    fieldDistribution u i = Lp.toTemperedDistribution (u i) := rfl

theorem fieldDistribution_injective : Function.Injective fieldDistribution := by
  have hi : Function.Injective
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  intro u v huv
  apply PiLp.ext
  intro i
  exact hi (congrFun huv i)

/-- Distributional differentiation in a Cartesian direction. -/
def partialDistribution (i : Fin 3) : ScalarDistribution →L[ℂ] ScalarDistribution :=
  LineDeriv.lineDerivOpCLM ℂ ScalarDistribution (coordinateDirection i)

/-- All three components of ∇×u, with cyclic Cartesian indexing. -/
def curlDistribution : FieldDistribution →L[ℂ] FieldDistribution :=
  ContinuousLinearMap.pi fun i =>
    (partialDistribution (i + 1)).comp (ContinuousLinearMap.proj (i + 2)) -
      (partialDistribution (i + 2)).comp (ContinuousLinearMap.proj (i + 1))

@[simp] theorem curlDistribution_apply (u : FieldDistribution) (i : Fin 3) :
    curlDistribution u i = partialDistribution (i + 1) (u (i + 2)) -
      partialDistribution (i + 2) (u (i + 1)) := rfl

def graphField : CurlGraphAmbient →L[ℂ] FieldL2 := WithLp.fstL 2 ℂ FieldL2 FieldL2
def graphCurl : CurlGraphAmbient →L[ℂ] FieldL2 := WithLp.sndL 2 ℂ FieldL2 FieldL2

/-- The graph of the weak curl in the full physical L² space. -/
def weakCurlGraph : Submodule ℂ CurlGraphAmbient :=
  ((curlDistribution.comp fieldDistribution).comp graphField -
    fieldDistribution.comp graphCurl).ker

theorem mem_weakCurlGraph (u : CurlGraphAmbient) :
    u ∈ weakCurlGraph ↔ curlDistribution (fieldDistribution (graphField u)) =
      fieldDistribution (graphCurl u) := by
  simp only [weakCurlGraph, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.comp_apply, sub_eq_zero]

theorem weakCurlGraph_isClosed : IsClosed (weakCurlGraph : Set CurlGraphAmbient) :=
  ContinuousLinearMap.isClosed_ker _

instance : CompleteSpace weakCurlGraph := weakCurlGraph_isClosed.completeSpace_coe

/-- Weak curls are unique: the graph has no nonzero vertical vector. -/
theorem weakCurl_unique {u v : CurlGraphAmbient}
    (hu : u ∈ weakCurlGraph) (hv : v ∈ weakCurlGraph)
    (hfield : graphField u = graphField v) : graphCurl u = graphCurl v := by
  apply fieldDistribution_injective
  rw [← (mem_weakCurlGraph u).mp hu, ← (mem_weakCurlGraph v).mp hv, hfield]

def weakCurlInclusion : weakCurlGraph →L[ℂ] FieldL2 :=
  graphField.comp weakCurlGraph.subtypeL

theorem weakCurlInclusion_injective : Function.Injective weakCurlInclusion := by
  intro u v huv
  apply Subtype.ext
  apply (WithLp.equiv 2 (FieldL2 × FieldL2)).injective
  apply Prod.ext
  · exact huv
  · exact weakCurl_unique u.property v.property huv

theorem weakCurlInclusion_norm_le (u : weakCurlGraph) :
    ‖weakCurlInclusion u‖ ≤ ‖u‖ := WithLp.norm_fst_le (α := FieldL2) u.val

end Maxwell.Continuum
