import Maxwell.Continuum.BoxModesBasis
import Maxwell.Continuum.PECTransverse

/-!
# Actual transverse Fourier coefficient equation

The rank-one part of the concrete curl-curl symbol is an actual longitudinal
kernel mode. Orthogonality to the full PEC kernel therefore removes it,
yielding the scalar free eigenvalue on every Fourier coefficient.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

set_option backward.isDefEq.respectTransparency false

open scoped InnerProductSpace BigOperators

def boxAmplitudeMap (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) :
    (Fin 3 → ℂ) →ₗ[ℂ] testL2Closure (boxDomain N) where
  toFun := boxAmplitude N ν
  map_add' a b := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change (a j + b j) • zeroExtendedBoxMode N j ν =
      a j • zeroExtendedBoxMode N j ν + b j • zeroExtendedBoxMode N j ν
    exact add_smul _ _ _
  map_smul' a b := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change (a * b j) • zeroExtendedBoxMode N j ν =
      a • b j • zeroExtendedBoxMode N j ν
    exact mul_smul _ _ _

@[simp] theorem boxAmplitudeMap_apply (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    boxAmplitudeMap N ν a = boxAmplitude N ν a := rfl

theorem boxAmplitude_single (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3) :
    boxAmplitude N ν (Pi.single c 1) = componentMode N c ν := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  by_cases hj : j = c
  · subst j
    simp [boxAmplitude, boxAmplitudeL2, componentMode, componentBoxMode]
  · simp [boxAmplitude, boxAmplitudeL2, componentMode, componentBoxMode,
      hj]

theorem boxAmplitude_eq_sum (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    boxAmplitude N ν a = ∑ c : Fin 3, a c • componentMode N c ν := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  fin_cases j <;>
    simp [boxAmplitude, boxAmplitudeL2, componentMode, componentBoxMode,
      Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply]

def operatorComponentMode (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) : (pecCurlCurl (boxDomain N)).domain :=
  ⟨componentMode N c ν, componentMode_mem_operatorDomain N hN ν c⟩

def operatorAmplitude (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) : (pecCurlCurl (boxDomain N)).domain :=
  ∑ c : Fin 3, a c • operatorComponentMode N hN ν c

theorem operatorAmplitude_coe (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    (operatorAmplitude N hN ν a : testL2Closure (boxDomain N)) = boxAmplitude N ν a := by
  rw [boxAmplitude_eq_sum]
  rfl

theorem operatorAmplitude_apply (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    pecCurlCurl (boxDomain N) (operatorAmplitude N hN ν a) =
      boxAmplitudeMap N ν (∑ c : Fin 3, a c •
        (fun j => (curlCurlSymbol (integerWaveNumber N ν) (Pi.single c 1) j : ℂ))) := by
  change (pecCurlCurl (boxDomain N)).toFun
    (∑ c : Fin 3, a c • operatorComponentMode N hN ν c) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul, map_smul]
  exact congrArg (fun v => a c • v) (componentMode_operator N hN ν c _)

def longitudinalMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) : testL2Closure (boxDomain N) :=
  boxAmplitude N ν (fun j => (integerWaveNumber N ν j : ℂ))

theorem longitudinalMode_mem_kernel (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) : longitudinalMode N ν ∈ gradientSpace (boxDomain N) := by
  let a : Fin 3 → ℂ := fun j => (integerWaveNumber N ν j : ℂ)
  apply (pecCurlCurl (boxDomain N)).mem_ker_iff.mpr
  refine ⟨operatorAmplitude N hN ν a, (operatorAmplitude_coe N hN ν a).symm, ?_⟩
  rw [operatorAmplitude_apply]
  have hzero : (∑ c : Fin 3, a c •
      (fun j => (curlCurlSymbol (integerWaveNumber N ν) (Pi.single c 1) j : ℂ))) = 0 := by
    funext j
    fin_cases j <;>
      simp [a, curlCurlSymbol, Fin.sum_univ_three, Pi.single_apply] <;> ring
  rw [hzero, map_zero]

def modeEigenvalue (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) : ℝ :=
  ∑ j : Fin 3, integerWaveNumber N ν j ^ 2

theorem componentMode_operator_decompose (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) :
    pecCurlCurl (boxDomain N) (operatorComponentMode N hN ν c) =
      (modeEigenvalue N ν : ℂ) • componentMode N c ν -
        (integerWaveNumber N ν c : ℂ) • longitudinalMode N ν := by
  change pecCurlCurl (boxDomain N)
    ⟨componentMode N c ν, componentMode_mem_operatorDomain N hN ν c⟩ = _
  rw [componentMode_operator N hN ν c]
  rw [← boxAmplitude_single N ν c]
  change boxAmplitudeMap N ν _ =
    (modeEigenvalue N ν : ℂ) • boxAmplitudeMap N ν (Pi.single c 1) -
      (integerWaveNumber N ν c : ℂ) • boxAmplitudeMap N ν _
  rw [← map_smul, ← map_smul, ← map_sub]
  congr 1
  funext j
  simp only [curlCurlSymbol, modeEigenvalue, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Complex.ofReal_sub, Complex.ofReal_mul]
  split_ifs <;> simp <;> ring

theorem componentMode_transverse_coefficient (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c : Fin 3) (u : (pecCurlCurl (boxDomain N)).domain)
    (hu : (u : testL2Closure (boxDomain N)) ∈ transverseSpace (boxDomain N)) :
    inner ℂ (componentMode N c ν) (pecCurlCurl (boxDomain N) u) =
      (modeEigenvalue N ν : ℂ) * inner ℂ (componentMode N c ν) (u : testL2Closure (boxDomain N)) := by
  have hs := (pecFormEmbedding (boxDomain N)).operator_symmetric
    (operatorComponentMode N hN ν c) u
  change inner ℂ (pecCurlCurl (boxDomain N) (operatorComponentMode N hN ν c))
      (u : testL2Closure (boxDomain N)) =
    inner ℂ (componentMode N c ν) (pecCurlCurl (boxDomain N) u) at hs
  rw [componentMode_operator_decompose, inner_sub_left, inner_smul_left, inner_smul_left,
    hu _ (longitudinalMode_mem_kernel N hN ν), mul_zero, sub_zero,
    Complex.conj_ofReal] at hs
  exact hs.symm

/-- The concrete Fourier coefficient equation on the actual PEC transverse
operator domain. -/
theorem componentHilbertBasis_transverse_coefficient (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (u : (pecCurlCurl (boxDomain N)).domain)
    (hu : (u : testL2Closure (boxDomain N)) ∈ transverseSpace (boxDomain N))
    (q : ComponentModeIndex) :
    (componentHilbertBasis N hN).repr (pecCurlCurl (boxDomain N) u) q =
      (modeEigenvalue N q.2.val : ℂ) •
        (componentHilbertBasis N hN).repr (u : testL2Closure (boxDomain N)) q := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    componentHilbertBasis_apply, normalizedComponentMode, inner_smul_left, inner_smul_left]
  change star ((‖indexedComponentMode N q‖ : ℂ)⁻¹) *
      inner ℂ (componentMode N q.1 q.2.val) (pecCurlCurl (boxDomain N) u) = _
  rw [componentMode_transverse_coefficient N hN q.2.val q.1 u hu]
  change _ = (modeEigenvalue N q.2.val : ℂ) *
    (star ((‖indexedComponentMode N q‖ : ℂ)⁻¹) *
      inner ℂ (componentMode N q.1 q.2.val) (u : testL2Closure (boxDomain N)))
  ring

theorem transverseCurlCurl_coefficient (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (u : (transverseCurlCurl (boxDomain N)).domain) (q : ComponentModeIndex) :
    (componentHilbertBasis N hN).repr
      (transverseCurlCurl (boxDomain N) u : testL2Closure (boxDomain N)) q =
      (modeEigenvalue N q.2.val : ℂ) • (componentHilbertBasis N hN).repr
        ((u : transverseSpace (boxDomain N)) : testL2Closure (boxDomain N)) q :=
  componentHilbertBasis_transverse_coefficient N hN
    (transverseDomainInclusion (boxDomain N) u) (u : transverseSpace (boxDomain N)).property q

#print axioms longitudinalMode_mem_kernel
#print axioms transverseCurlCurl_coefficient

end Maxwell.Continuum.BoxModes
