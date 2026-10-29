import Maxwell.Continuum.PECOperator
import Maxwell.Continuum.PECSupport
import Maxwell.Continuum.MaterialForm
import Maxwell.Continuum.GraphNorm

/-!
# The actual scalar-dielectric continuum Maxwell operator

All fields live in the full supported complex L² space. The PEC condition
is imposed by the closure of compactly supported smooth curl graphs. The
dielectric acts by actual pointwise scalar multiplication. No discretization,
spectral certificate, or assumed self-adjoint realization is used here.
-/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space)

theorem multiplier_mem_testL2Closure (u : testL2Closure Ω) :
    ε.multiplier u ∈ testL2Closure Ω :=
  mem_testL2Closure_of_supported Ω _
    (ε.multiplier_vanishes_ae Ω u (supported_of_mem_testL2Closure Ω u u.property))

/-- Restriction of the literal scalar multiplier to the physical domain. -/
def domainMultiplier : testL2Closure Ω →L[ℂ] testL2Closure Ω :=
  (ε.multiplier.comp (testL2Closure Ω).subtypeL).codRestrict (testL2Closure Ω)
    (ε.multiplier_mem_testL2Closure Ω)

@[simp] theorem domainMultiplier_coe (u : testL2Closure Ω) :
    (ε.domainMultiplier Ω u : FieldL2) = ε.multiplier u := rfl

theorem domainMultiplier_symmetric : (ε.domainMultiplier Ω).IsSymmetric := by
  intro u v
  exact ε.multiplier_symmetric u.val v.val

theorem domainMultiplier_selfAdjoint : IsSelfAdjoint (ε.domainMultiplier Ω) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (ε.domainMultiplier_symmetric Ω)

theorem domainMultiplier_norm_le : ‖ε.domainMultiplier Ω‖ ≤ 25 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  exact ε.multiplier_apply_norm_le u.val

theorem domainMultiplier_inner_lower (u : testL2Closure Ω) :
    ‖u‖ ^ 2 ≤ (inner ℂ u (ε.domainMultiplier Ω u)).re := ε.inner_lower u.val

theorem domainMultiplier_inner_upper (u : testL2Closure Ω) :
    (inner ℂ u (ε.domainMultiplier Ω u)).re ≤ 25 * ‖u‖ ^ 2 := ε.inner_upper u.val

end ScalarDielectric

/-- The frequency-one Maxwell operator C−ε on precisely D(C). -/
def maxwellOperator (Ω : Opens Space) (ε : ScalarDielectric) :
    testL2Closure Ω →ₗ.[ℂ] testL2Closure Ω :=
  FormPerturbation.addBounded (pecCurlCurl Ω) (-ε.domainMultiplier Ω)

@[simp] theorem maxwellOperator_domain (Ω : Opens Space) (ε : ScalarDielectric) :
    (maxwellOperator Ω ε).domain = (pecCurlCurl Ω).domain := rfl

@[simp] theorem maxwellOperator_apply (Ω : Opens Space) (ε : ScalarDielectric)
    (u : (maxwellOperator Ω ε).domain) :
    maxwellOperator Ω ε u = pecCurlCurl Ω u - ε.domainMultiplier Ω u := by
  simp only [maxwellOperator, FormPerturbation.addBounded_apply, neg_apply, sub_eq_add_neg]

theorem maxwellOperator_selfAdjoint (Ω : Opens Space) (ε : ScalarDielectric) :
    IsSelfAdjoint (maxwellOperator Ω ε) := by
  apply FormPerturbation.addBounded_selfAdjoint _ _ (pecCurlCurl_selfAdjoint Ω)
  intro u v
  change inner ℂ (-ε.domainMultiplier Ω u) v = inner ℂ u (-ε.domainMultiplier Ω v)
  rw [inner_neg_left, inner_neg_right]
  exact congrArg Neg.neg (ε.domainMultiplier_symmetric Ω u v)

theorem maxwellOperator_closed (Ω : Opens Space) (ε : ScalarDielectric) :
    (maxwellOperator Ω ε).IsClosed := (maxwellOperator_selfAdjoint Ω ε).isClosed

/-- A weak solution with an L² source belongs to the actual operator domain. -/
theorem maxwellOperator_graph_iff (Ω : Opens Space) (ε : ScalarDielectric)
    (u f : testL2Closure Ω) :
    (∃ hu : u ∈ (maxwellOperator Ω ε).domain, maxwellOperator Ω ε ⟨u, hu⟩ = f) ↔
      ∃ v : pecGraph Ω, pecDomainInclusion Ω v = u ∧
        ∀ w : pecGraph Ω, inner ℂ (pecCurl Ω v) (pecCurl Ω w) -
          inner ℂ (ε.domainMultiplier Ω u) (pecDomainInclusion Ω w) =
            inner ℂ f (pecDomainInclusion Ω w) := by
  simpa only [maxwellOperator, pecCurlCurl, pecForm_eq_curl_inner,
    pecFormEmbedding_inclusion, neg_apply, inner_neg_left, sub_eq_add_neg] using
    FormPerturbation.addBounded_graph_iff (pecFormEmbedding Ω) (-ε.domainMultiplier Ω) u f

/-- D(C) with the genuine Hilbert graph norm. -/
abbrev OperatorDomain (Ω : Opens Space) := GraphNorm.space (pecCurlCurl Ω)

instance (Ω : Opens Space) : CompleteSpace (OperatorDomain Ω) :=
  (GraphNorm.space_isClosed (pecCurlCurl_closed Ω)).completeSpace_coe

def maxwellGraphMap (Ω : Opens Space) (ε : ScalarDielectric) :
    OperatorDomain Ω →L[ℂ] testL2Closure Ω :=
  GraphNorm.perturbed (pecCurlCurl Ω) (ε.domainMultiplier Ω)

theorem maxwellGraphMap_norm_le (Ω : Opens Space) (ε : ScalarDielectric) :
    ‖maxwellGraphMap Ω ε‖ ≤ 26 :=
  GraphNorm.perturbed_norm_le _ _ (ε.domainMultiplier_norm_le Ω)

/-- The paper's 702 factor follows from an L² resolvent estimate on the
actual Maxwell equation. Existence and the L² bound are supplied by the
spectral-count/detuning theorem, not assumed in the operator construction. -/
theorem maxwell_graph_condition (Ω : Opens Space) (ε : ScalarDielectric)
    {L : ℝ} (hL : 1 ≤ L) (R : testL2Closure Ω →L[ℂ] OperatorDomain Ω)
    (heq : ∀ f, maxwellGraphMap Ω ε (R f) = f)
    (hfield : ∀ f, ‖GraphNorm.inclusion (pecCurlCurl Ω) (R f)‖ ≤ L * ‖f‖) :
    ‖maxwellGraphMap Ω ε‖ * ‖R‖ ≤ 702 * L :=
  GraphNorm.condition_bound _ _ (ε.domainMultiplier_norm_le Ω) hL R heq hfield

end Maxwell.Continuum
