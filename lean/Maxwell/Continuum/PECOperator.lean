import Maxwell.Continuum.PEC
import Maxwell.Continuum.FormPerturbation

/-!
# The represented continuum PEC curl-curl operator

The form is the L² inner product of the actual weak curls.  Applying the
proved representation theorem constructs its operator domain, proves
self-adjointness, and identifies weak solutions with that domain.

The ambient Hilbert space is the L² closure of smooth fields supported in Ω;
`PECSupport` identifies this closure with all L² fields zero outside Ω.
-/

noncomputable section

namespace Maxwell.Continuum

open TopologicalSpace

def pecFormEmbedding (Ω : Opens Space) :
    FormEmbedding ℂ (pecGraph Ω) (testL2Closure Ω) where
  inclusion := pecDomainInclusion Ω
  injective := pecDomainInclusion_injective Ω
  dense := pecDomainInclusion_dense Ω
  contractive := pecDomainInclusion_norm_le Ω

@[simp] theorem pecFormEmbedding_inclusion (Ω : Opens Space) :
    (pecFormEmbedding Ω).inclusion = pecDomainInclusion Ω := rfl

theorem pecForm_eq_curl_inner (Ω : Opens Space) (u v : pecGraph Ω) :
    (pecFormEmbedding Ω).form u v = inner ℂ (pecCurl Ω u) (pecCurl Ω v) := by
  change inner ℂ u v - inner ℂ (pecInclusion Ω u) (pecInclusion Ω v) = _
  rw [pec_graph_inner, add_sub_cancel_left]

/-- Curl-curl with its PEC weak operator domain. -/
def pecCurlCurl (Ω : Opens Space) : testL2Closure Ω →ₗ.[ℂ] testL2Closure Ω :=
  (pecFormEmbedding Ω).operator

theorem pecCurlCurl_selfAdjoint (Ω : Opens Space) : IsSelfAdjoint (pecCurlCurl Ω) :=
  (pecFormEmbedding Ω).operator_selfAdjoint

theorem pecCurlCurl_closed (Ω : Opens Space) : (pecCurlCurl Ω).IsClosed :=
  (pecFormEmbedding Ω).operator_closed

theorem pecCurlCurl_dense (Ω : Opens Space) :
    Dense ((pecCurlCurl Ω).domain : Set (testL2Closure Ω)) :=
  (pecFormEmbedding Ω).operator_dense

theorem pecCurlCurl_nonnegative (Ω : Opens Space) (u : (pecCurlCurl Ω).domain) :
    0 ≤ (inner ℂ (pecCurlCurl Ω u) (u : testL2Closure Ω)).re :=
  (pecFormEmbedding Ω).operator_nonnegative u

/-- Exact weak-domain characterization, with no eigenbasis or finite truncation premise. -/
theorem pecCurlCurl_graph_iff (Ω : Opens Space) (u g : testL2Closure Ω) :
    (∃ hu : u ∈ (pecCurlCurl Ω).domain, pecCurlCurl Ω ⟨u, hu⟩ = g) ↔
      ∃ v : pecGraph Ω, pecDomainInclusion Ω v = u ∧
        ∀ w : pecGraph Ω, inner ℂ (pecCurl Ω v) (pecCurl Ω w) =
          inner ℂ g (pecDomainInclusion Ω w) := by
  simpa only [pecCurlCurl, pecForm_eq_curl_inner, pecFormEmbedding_inclusion] using
    (pecFormEmbedding Ω).operator_graph_iff u g

end Maxwell.Continuum
