import Maxwell.Continuum.BoxModesDistribution
import Maxwell.Continuum.BoxModesSmooth

/-!
# The actual PEC curl-curl operator on box Fourier modes

The smooth-cutoff construction puts each mode in the PEC form domain.
Compact-test integration by parts then identifies the represented operator
with the classical, explicitly computed Fourier symbol.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open MeasureTheory
open scoped ContDiff BigOperators Matrix

def integerWaveNumber (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) : Vector :=
  fun j => (ν j : ℝ) * Real.pi / N j

theorem electric_eq_scalarBoxMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (a : Vector) (x : Point) (j : Fin 3) :
    electric (integerWaveNumber N ν) a x j = a j * scalarBoxMode N ν j x := by
  fin_cases j <;>
    simp [electric, scalarBoxMode, coordinateMode, integerWaveNumber,
      intervalSin, intervalCos, Fin.prod_univ_three] <;> ring

def componentField (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) : Field :=
  fun x => Pi.single c (scalarBoxMode N ν c x)

theorem componentField_eq_electric (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    componentField N ν c = electric (integerWaveNumber N ν) (Pi.single c 1) := by
  funext x j
  rw [electric_eq_scalarBoxMode]
  by_cases hj : j = c
  · subst j
    simp [componentField]
  · simp [componentField, hj]

theorem curl_apply_cyclic (F : Field) (x : Point) (i : Fin 3) :
    curl F x i = partialDeriv (fun y => F y (i + 2)) (i + 1) x -
      partialDeriv (fun y => F y (i + 1)) (i + 2) x := by
  fin_cases i <;> rfl

theorem partial_componentField (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j k : Fin 3)
    (x : Point) :
    partialDeriv (fun y => componentField N ν c y k) j x =
      if k = c then partialDeriv (scalarBoxMode N ν c) j x else 0 := by
  by_cases hk : k = c
  · subst k
    simp [componentField]
  · simp [componentField, hk]

theorem componentCurlL2_coe_ae (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c i : Fin 3) :
    (componentCurlL2 N ν c i : Space → ℂ) =ᵐ[volume]
      (openBox N).indicator (fun x => (curl (componentField N ν c) x i : ℂ)) := by
  have hs := Lp.coeFn_sub
    (if i + 2 = c then zeroExtendedBoxPartial N ν c (i + 1) else 0)
    (if i + 1 = c then zeroExtendedBoxPartial N ν c (i + 2) else 0)
  filter_upwards [hs, zeroExtendedBoxPartial_coe_ae N ν c (i + 1),
    zeroExtendedBoxPartial_coe_ae N ν c (i + 2)] with x hx h1 h2
  change ((if i + 2 = c then zeroExtendedBoxPartial N ν c (i + 1) else 0) -
    (if i + 1 = c then zeroExtendedBoxPartial N ν c (i + 2) else 0) : ScalarL2) x = _
  rw [hx]
  simp only [Pi.sub_apply, curl_apply_cyclic, partial_componentField]
  by_cases hΩ : x ∈ openBox N <;>
    by_cases hleft : i + 2 = c <;> by_cases hright : i + 1 = c <;>
    simp [hleft, hright, h1, h2, Set.indicator, hΩ]

theorem complexPartial_ofReal (f : Point → ℝ) (hf : Differentiable ℝ f)
    (j : Fin 3) (x : Point) :
    complexPartial (fun y => (f y : ℂ)) j x = (partialDeriv f j x : ℂ) := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  change HasFDerivAt (fun y => (f y : ℂ)) _ x at hc
  unfold complexPartial partialDeriv
  rw [hc.fderiv]
  rfl

theorem complexCurl_ofReal (F : Field) (hF : ∀ i, Differentiable ℝ (fun x => F x i)) :
    complexCurl (fun x i => (F x i : ℂ)) = fun x i => (curl F x i : ℂ) := by
  funext x i
  simp only [complexCurl, complexPartial_ofReal _ (hF _) _, curl_apply_cyclic,
    Complex.ofReal_sub]

def boxAmplitudeL2 (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) : FieldL2 :=
  WithLp.toLp 2 (fun j => a j • zeroExtendedBoxMode N j ν)

theorem boxAmplitudeL2_coe_ae (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (a : Fin 3 → ℂ) (j : Fin 3) :
    (boxAmplitudeL2 N ν a j : Space → ℂ) =ᵐ[volume]
      (openBox N).indicator (fun x => a j * (scalarBoxMode N ν j x : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (a j) (zeroExtendedBoxMode N j ν),
    zeroExtendedBoxMode_coe_ae N j ν] with x hs hx
  change (a j • zeroExtendedBoxMode N j ν : ScalarL2) x = _
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hx]
  by_cases hΩ : x ∈ openBox N <;> simp [Set.indicator, hΩ]

theorem boxAmplitudeL2_supported (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    FieldSupported (boxDomain N) (boxAmplitudeL2 N ν a) := by
  intro j
  filter_upwards [boxAmplitudeL2_coe_ae N ν a j] with x hx hΩ
  change x ∉ openBox N at hΩ
  rw [hx, Set.indicator_of_notMem hΩ]

def boxAmplitude (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    testL2Closure (boxDomain N) :=
  ⟨boxAmplitudeL2 N ν a, mem_testL2Closure_of_supported _ _ (boxAmplitudeL2_supported N ν a)⟩

def componentMode (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    testL2Closure (boxDomain N) :=
  ⟨componentBoxMode N c ν, componentBoxMode_mem_testL2Closure N c ν⟩

theorem contDiff_curl_componentField (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c i : Fin 3) : ContDiff ℝ ∞ (fun x => curl (componentField N ν c) x i) := by
  rw [componentField_eq_electric, curl_electric]
  exact contDiff_pi.mp (contDiff_magnetic _ _) i

/-- Each physical component mode belongs to the represented PEC operator
 domain, and its action is exactly the continuum curl-curl symbol. -/
theorem componentMode_operator_graph (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    ∃ hu : componentMode N c ν ∈ (pecCurlCurl (boxDomain N)).domain,
      pecCurlCurl (boxDomain N) ⟨componentMode N c ν, hu⟩ =
        boxAmplitude N ν (fun j => (curlCurlSymbol (integerWaveNumber N ν) (Pi.single c 1) j : ℂ)) := by
  apply (pecCurlCurl_graph_iff (boxDomain N) _ _).mpr
  refine ⟨pecComponentMode N hN ν c, rfl, ?_⟩
  apply pec_weak_of_curlCurl_distribution
  intro φ
  rw [pecComponentMode_curl]
  rw [distributionPairing_curl_zeroExtension (boxDomain N) (componentCurlL2 N ν c)
    (fun x i => (curl (componentField N ν c) x i : ℂ))
    (fun i => Complex.ofRealCLM.contDiff.comp (contDiff_curl_componentField N ν c i))
    (componentCurlL2_coe_ae N ν c)]
  change _ = distributionPairing (fieldDistribution (boxAmplitudeL2 N ν
    (fun j => (curlCurlSymbol (integerWaveNumber N ν) (Pi.single c 1) j : ℂ))))
      (testSchwartzField (boxDomain N) φ)
  rw [distributionPairing_zeroExtension (boxDomain N) _ _
    (boxAmplitudeL2_coe_ae N ν (fun j =>
      (curlCurlSymbol (integerWaveNumber N ν) (Pi.single c 1) j : ℂ)))]
  rw [complexCurl_ofReal _ (fun i =>
    (contDiff_curl_componentField N ν c i).differentiable (by simp))]
  simp only [componentField_eq_electric, curl_curl_electric, electric_eq_scalarBoxMode,
    Complex.ofReal_mul]

theorem componentMode_mem_operatorDomain (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    componentMode N c ν ∈ (pecCurlCurl (boxDomain N)).domain :=
  (componentMode_operator_graph N hN ν c).choose

theorem componentMode_operator (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3)
    (hu : componentMode N c ν ∈ (pecCurlCurl (boxDomain N)).domain) :
    pecCurlCurl (boxDomain N) ⟨componentMode N c ν, hu⟩ =
      boxAmplitude N ν (fun j => (curlCurlSymbol (integerWaveNumber N ν) (Pi.single c 1) j : ℂ)) :=
  (componentMode_operator_graph N hN ν c).choose_spec

#print axioms componentMode_operator_graph

end Maxwell.Continuum.BoxModes
