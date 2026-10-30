import Maxwell.Continuum.PECCompactCutoff
import Maxwell.Continuum.SchwartzCurlCommutator
import Maxwell.Continuum.PECDistribution

/-! Actual compact cutoff fields belong to the self-adjoint PEC
curl-curl operator domain, with the explicit commutator as their image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory FourierSobolev TopologicalSpace

def ScalarSupported (Ω : Opens Space) (f : ScalarL2) : Prop :=
  ∀ᵐ x ∂volume, x ∉ Ω → f x = 0

theorem ScalarSupported.add {Ω : Opens Space} {f g : ScalarL2}
    (hf : ScalarSupported Ω f) (hg : ScalarSupported Ω g) : ScalarSupported Ω (f+g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hz hΩ
  rw [hz]
  change f x+g x = 0
  rw [hx hΩ, hy hΩ, add_zero]

theorem ScalarSupported.sub {Ω : Opens Space} {f g : ScalarL2}
    (hf : ScalarSupported Ω f) (hg : ScalarSupported Ω g) : ScalarSupported Ω (f-g) := by
  filter_upwards [hf, hg, Lp.coeFn_sub f g] with x hx hy hz hΩ
  rw [hz]
  change f x-g x = 0
  rw [hx hΩ, hy hΩ, sub_self]

theorem scalar_supported (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) (f : ScalarL2) : ScalarSupported Ω (scalar θ f) := by
  filter_upwards [scalar_ae θ f] with x hx hnot
  rw [hx, image_eq_zero_of_notMem_tsupport (fun hm => hnot (hΩ hm)), zero_mul]

theorem field_supported (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) (f : FieldL2) : FieldSupported Ω (field θ f) :=
  fun j => scalar_supported Ω θ hΩ (f j)

theorem partialSchwartz_tsupport (θ : SchwartzMap Space ℂ) (j : Fin 3) :
    tsupport (partialSchwartz j θ) ⊆ tsupport θ :=
  SchwartzMap.tsupport_lineDerivOp_subset (coordinateDirection j) θ

theorem secondProductRemainder_supported (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) {f : FieldL2} (Df : H1Data f) (a b c : Fin 3) :
    ScalarSupported Ω (secondProductRemainder θ Df a b c) :=
  ((scalar_supported Ω _ ((partialSchwartz_tsupport _ a).trans
      ((partialSchwartz_tsupport θ b).trans hΩ)) _).add
    (scalar_supported Ω _ ((partialSchwartz_tsupport θ b).trans hΩ) _)).add
    (scalar_supported Ω _ ((partialSchwartz_tsupport θ a).trans hΩ) _)

theorem curlCurlCommutator_supported (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) {f : FieldL2} (Df : H1Data f) :
    FieldSupported Ω (curlCurlCommutator θ Df) := by
  intro i
  exact ((secondProductRemainder_supported Ω θ hΩ Df _ _ _).sub
      (secondProductRemainder_supported Ω θ hΩ Df _ _ _)).sub
    ((secondProductRemainder_supported Ω θ hΩ Df _ _ _).sub
      (secondProductRemainder_supported Ω θ hΩ Df _ _ _))

theorem cutoff_image_supported (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) {f : FieldL2} (Df : H1Data f) (A : FieldL2) :
    FieldSupported Ω (field θ A+curlCurlCommutator θ Df) := by
  intro i
  exact (scalar_supported Ω θ hΩ (A i)).add (curlCurlCommutator_supported Ω θ hΩ Df i)

def cutoffPhysicalField (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) (f : FieldL2) : testL2Closure Ω :=
  ⟨field θ f, mem_testL2Closure_of_supported Ω _ (field_supported Ω θ hΩ f)⟩

def cutoffPhysicalImage (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hΩ : tsupport θ ⊆ Ω) {f : FieldL2} (Df : H1Data f) (A : FieldL2) : testL2Closure Ω :=
  ⟨field θ A+curlCurlCommutator θ Df,
    mem_testL2Closure_of_supported Ω _ (cutoff_image_supported Ω θ hΩ Df A)⟩

theorem cutoff_pecCurlCurl (Ω : Opens Space) (θ : SchwartzMap Space ℂ)
    (hc : HasCompactSupport θ) (hΩ : tsupport θ ⊆ Ω) {f A : FieldL2} (Df : H1Data f)
    (hA : curlDistribution (curlDistribution (fieldDistribution f)) = fieldDistribution A) :
    ∃ hu : cutoffPhysicalField Ω θ hΩ f ∈ (pecCurlCurl Ω).domain,
      pecCurlCurl Ω ⟨cutoffPhysicalField Ω θ hΩ f, hu⟩ = cutoffPhysicalImage Ω θ hΩ Df A := by
  apply (pecCurlCurl_graph_iff_distributional Ω _ _).mpr
  refine ⟨⟨(h1Product θ Df).curlGraph, cutoff_curlGraph_mem_pecGraph Ω θ hc hΩ Df⟩, ?_, ?_⟩
  · rfl
  · intro φ
    change distributionPairing (curlDistribution (curlDistribution (fieldDistribution (field θ f)))) _ = _
    rw [curlCurl_product_L2 θ Df hA]
    rfl

#print axioms cutoff_pecCurlCurl

end Maxwell.Continuum.SchwartzMultiplier
