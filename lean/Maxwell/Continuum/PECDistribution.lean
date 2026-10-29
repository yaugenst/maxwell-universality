import Maxwell.Continuum.PECOperator
import Maxwell.Continuum.PECSupport
import Mathlib.Tactic.Ring

/-!
# The represented PEC operator is distributional curl-curl in the interior

Equality is tested only on smooth fields compactly supported in Ω. No global
distributional equality for zero extensions across the boundary is claimed.
Complex conjugation connects the Hermitian energy form to the complex-linear
test-function pairing used by tempered distributions.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace SchwartzMap Distributions

/-- Complex conjugation as a real continuous linear map on Schwartz space. -/
def conjugateSchwartz : SchwartzMap Space ℂ →L[ℝ] SchwartzMap Space ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

@[simp] theorem conjugateSchwartz_apply (f : SchwartzMap Space ℂ) (x : Space) :
    conjugateSchwartz f x = star (f x) := rfl

@[simp] theorem conjugateSchwartz_involutive (f : SchwartzMap Space ℂ) :
    conjugateSchwartz (conjugateSchwartz f) = f := by
  ext x
  simp

theorem partialSchwartz_conjugate (i : Fin 3) (f : SchwartzMap Space ℂ) :
    partialSchwartz i (conjugateSchwartz f) = conjugateSchwartz (partialSchwartz i f) := by
  ext x
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp x (f.hasFDerivAt x)
  have heq := congrArg (fun L : Space →L[ℝ] ℂ => L (coordinateDirection i)) h.fderiv
  exact heq

def conjugateSchwartzField (f : SchwartzField) : SchwartzField :=
  fun i => conjugateSchwartz (f i)

@[simp] theorem conjugateSchwartzField_involutive (f : SchwartzField) :
    conjugateSchwartzField (conjugateSchwartzField f) = f := by
  funext i
  exact conjugateSchwartz_involutive (f i)

theorem curlSchwartz_conjugate (f : SchwartzField) :
    curlSchwartz (conjugateSchwartzField f) = conjugateSchwartzField (curlSchwartz f) := by
  funext i
  change partialSchwartz (i + 1) (conjugateSchwartz (f (i + 2))) -
      partialSchwartz (i + 2) (conjugateSchwartz (f (i + 1))) =
    conjugateSchwartz (partialSchwartz (i + 1) (f (i + 2)) -
      partialSchwartz (i + 2) (f (i + 1)))
  rw [partialSchwartz_conjugate, partialSchwartz_conjugate, map_sub]

def conjugateTestField (Ω : Opens Space) (f : TestField Ω) : TestField Ω :=
  fun i => TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap (f i)

theorem testSchwartzField_conjugate (Ω : Opens Space) (f : TestField Ω) :
    testSchwartzField Ω (conjugateTestField Ω f) =
      conjugateSchwartzField (testSchwartzField Ω f) := by
  funext i
  ext x
  rfl

/-- Componentwise complex-linear distribution pairing. -/
def distributionPairing (T : FieldDistribution) (f : SchwartzField) : ℂ :=
  ∑ i, T i (f i)

/-- Curl is formally symmetric for the distribution/test pairing. -/
theorem curlDistribution_pairing (T : FieldDistribution) (f : SchwartzField) :
    distributionPairing (curlDistribution T) f =
      distributionPairing T (curlSchwartz f) := by
  simp only [distributionPairing, Fin.sum_univ_three, curlDistribution_apply,
    curlSchwartz_apply, partialDistribution, partialSchwartz,
    sub_apply, LineDeriv.lineDerivOpCLM_apply,
    TemperedDistribution.lineDerivOp_apply_apply, map_neg, map_sub]
  norm_num
  ring

/-- Distribution pairing with conjugated tests is the ordinary L² inner
product, in the order test first and field second. -/
theorem fieldDistribution_pairing_conjugate (u : FieldL2) (f : SchwartzField) :
    distributionPairing (fieldDistribution u) (conjugateSchwartzField f) =
      inner ℂ (schwartzFieldL2 f) u := by
  rw [distributionPairing, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fieldDistribution_apply, Lp.toTemperedDistribution_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(f i).coeFn_toLp 2 volume] with x hx
  change star (f i x) * u i x = inner ℂ ((f i).toLp 2 volume x) (u i x)
  rw [hx, RCLike.inner_apply']
  rfl

theorem fieldDistribution_pairing_eq_inner (u : FieldL2) (f : SchwartzField) :
    distributionPairing (fieldDistribution u) f =
      inner ℂ (schwartzFieldL2 (conjugateSchwartzField f)) u := by
  simpa only [conjugateSchwartzField_involutive] using
    fieldDistribution_pairing_conjugate u (conjugateSchwartzField f)

/-- A field satisfying the represented weak equation has the literal
distributional curl-curl right-hand side on tests supported inside Ω. -/
theorem pec_weak_curlCurl_distribution (Ω : Opens Space) (v : pecGraph Ω)
    (g : testL2Closure Ω)
    (hweak : ∀ w : pecGraph Ω,
      inner ℂ (pecCurl Ω v) (pecCurl Ω w) = inner ℂ g (pecDomainInclusion Ω w))
    (φ : TestField Ω) :
    distributionPairing (curlDistribution (fieldDistribution (pecCurl Ω v)))
        (testSchwartzField Ω φ) =
      distributionPairing (fieldDistribution (g : FieldL2)) (testSchwartzField Ω φ) := by
  let w : pecGraph Ω := ⟨testCurlGraph Ω (conjugateTestField Ω φ),
    (testCurlGraph Ω).range.le_topologicalClosure ⟨conjugateTestField Ω φ, rfl⟩⟩
  have hw : inner ℂ (pecCurl Ω w) (pecCurl Ω v) =
      inner ℂ (pecInclusion Ω w) (g : FieldL2) := by
    change inner ℂ (pecCurl Ω w) (pecCurl Ω v) = inner ℂ (pecDomainInclusion Ω w) g
    have h := congrArg (starRingEnd ℂ) (hweak w)
    simpa only [inner_conj_symm] using h
  calc
    distributionPairing (curlDistribution (fieldDistribution (pecCurl Ω v)))
        (testSchwartzField Ω φ) =
        inner ℂ (schwartzFieldL2
          (curlSchwartz (conjugateSchwartzField (testSchwartzField Ω φ))))
          (pecCurl Ω v) := by
      rw [curlDistribution_pairing, fieldDistribution_pairing_eq_inner,
        curlSchwartz_conjugate]
    _ = inner ℂ (pecCurl Ω w) (pecCurl Ω v) := by
      rw [← testSchwartzField_conjugate]
      rfl
    _ = inner ℂ (pecInclusion Ω w) (g : FieldL2) := hw
    _ = distributionPairing (fieldDistribution (g : FieldL2))
        (testSchwartzField Ω φ) := by
      rw [fieldDistribution_pairing_eq_inner, ← testSchwartzField_conjugate]
      rfl

/-- Every vector in the self-adjoint PEC curl-curl operator domain has the
stated distributional equation in the interior. -/
theorem pecCurlCurl_distribution (Ω : Opens Space) (u : (pecCurlCurl Ω).domain) :
    ∃ v : pecGraph Ω, pecDomainInclusion Ω v = (u : testL2Closure Ω) ∧
      ∀ φ : TestField Ω,
        distributionPairing (curlDistribution (fieldDistribution (pecCurl Ω v)))
            (testSchwartzField Ω φ) =
          distributionPairing (fieldDistribution (pecCurlCurl Ω u : FieldL2))
            (testSchwartzField Ω φ) := by
  obtain ⟨v, hv, hweak⟩ := (pecCurlCurl_graph_iff Ω (u : testL2Closure Ω)
    (pecCurlCurl Ω u)).mp ⟨u.property, rfl⟩
  exact ⟨v, hv, pec_weak_curlCurl_distribution Ω v _ hweak⟩

/-- The represented operator is literally ∇×∇× on the original continuum
field when tested inside Ω; boundary surface distributions are excluded by
the support restriction on the tests. -/
theorem pecCurlCurl_eq_distributional_curlCurl (Ω : Opens Space)
    (u : (pecCurlCurl Ω).domain) (φ : TestField Ω) :
    distributionPairing
        (curlDistribution (curlDistribution
          (fieldDistribution ((u : testL2Closure Ω) : FieldL2))))
        (testSchwartzField Ω φ) =
      distributionPairing (fieldDistribution (pecCurlCurl Ω u : FieldL2))
        (testSchwartzField Ω φ) := by
  obtain ⟨v, hv, hdistribution⟩ := pecCurlCurl_distribution Ω u
  have hfield : pecInclusion Ω v = ((u : testL2Closure Ω) : FieldL2) :=
    congrArg Subtype.val hv
  rw [← hfield, pec_curl_distribution]
  exact hdistribution φ

/-- The interior distributional equation extends from compact smooth tests
to the entire PEC form domain by its defining graph closure. -/
theorem pec_weak_of_curlCurl_distribution (Ω : Opens Space) (v : pecGraph Ω)
    (g : testL2Closure Ω)
    (hdistribution : ∀ φ : TestField Ω,
      distributionPairing (curlDistribution (fieldDistribution (pecCurl Ω v)))
          (testSchwartzField Ω φ) =
        distributionPairing (fieldDistribution (g : FieldL2)) (testSchwartzField Ω φ)) :
    ∀ w : pecGraph Ω,
      inner ℂ (pecCurl Ω v) (pecCurl Ω w) = inner ℂ g (pecDomainInclusion Ω w) := by
  have hcore (φ : TestField Ω) :
      inner ℂ (pecCurl Ω v) (graphCurl (testCurlGraph Ω φ)) =
        inner ℂ (g : FieldL2) (graphField (testCurlGraph Ω φ)) := by
    have h := hdistribution (conjugateTestField Ω φ)
    rw [testSchwartzField_conjugate, curlDistribution_pairing, curlSchwartz_conjugate,
      fieldDistribution_pairing_conjugate, fieldDistribution_pairing_conjugate] at h
    have hc := congrArg (starRingEnd ℂ) h
    simp only [inner_conj_symm] at hc
    exact hc
  intro w
  have hclosed : IsClosed {z : CurlGraphAmbient |
      inner ℂ (pecCurl Ω v) (graphCurl z) = inner ℂ (g : FieldL2) (graphField z)} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact closure_minimal (by
    rintro _ ⟨φ, rfl⟩
    exact hcore φ) hclosed w.property

/-- Exact distributional characterization of the self-adjoint PEC operator
domain, including the converse from an L² right-hand side. -/
theorem pecCurlCurl_graph_iff_distributional (Ω : Opens Space)
    (u g : testL2Closure Ω) :
    (∃ hu : u ∈ (pecCurlCurl Ω).domain, pecCurlCurl Ω ⟨u, hu⟩ = g) ↔
      ∃ v : pecGraph Ω, pecDomainInclusion Ω v = u ∧
        ∀ φ : TestField Ω,
          distributionPairing
              (curlDistribution (curlDistribution (fieldDistribution (u : FieldL2))))
              (testSchwartzField Ω φ) =
            distributionPairing (fieldDistribution (g : FieldL2)) (testSchwartzField Ω φ) := by
  rw [pecCurlCurl_graph_iff]
  constructor
  · rintro ⟨v, hv, hweak⟩
    refine ⟨v, hv, fun φ => ?_⟩
    have hfield : pecInclusion Ω v = (u : FieldL2) := congrArg Subtype.val hv
    rw [← hfield, pec_curl_distribution]
    exact pec_weak_curlCurl_distribution Ω v g hweak φ
  · rintro ⟨v, hv, hdistribution⟩
    refine ⟨v, hv, pec_weak_of_curlCurl_distribution Ω v g ?_⟩
    intro φ
    have hfield : pecInclusion Ω v = (u : FieldL2) := congrArg Subtype.val hv
    have h := hdistribution φ
    rw [← hfield, pec_curl_distribution] at h
    exact h

end Maxwell.Continuum
