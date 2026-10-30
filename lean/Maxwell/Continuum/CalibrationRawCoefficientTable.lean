import Maxwell.Continuum.CalibrationRawCoordinates
import Maxwell.Continuum.CalibrationNeumannRawTable

/-! An explicit raw numerator-pair/denominator table for the actual
cached Neumann matrix and forcing, without rational normalization. -/

namespace Maxwell.Continuum.Calibration.RawFree

open RationalDataflow FreeFiber NeumannMachine
set_option maxHeartbeats 2500000

def sumThree (x : Fin 3 → Parts) : Parts := ((x 0).add (x 1)).add (x 2)

theorem sumThree_valid (x : Fin 3 → Parts) (hx : ∀ j, (x j).Valid) :
    (sumThree x).Valid := Parts.add_valid (Parts.add_valid (hx 0) (hx 1)) (hx 2)

theorem sumThree_value (x : Fin 3 → Parts) (hx : ∀ j, (x j).Valid) :
    (sumThree x).value = ∑ j, (x j).value := by
  rw [sumThree,Parts.add_value _ _ (Parts.add_valid (hx 0) (hx 1)) (hx 2),
    Parts.add_value _ _ (hx 0) (hx 1),Fin.sum_univ_three]

theorem sumThree_width (x : Fin 3 → Parts) (B : ℕ) (hx : ∀ j, (x j).Width B) :
    (sumThree x).Width (3*B+2) := by
  have h := ((hx 0).add (hx 1)).add (hx 2)
  convert h using 1 <;> first | rfl | omega

def basisPart (μ : Alias) (j : Fin 3) (ν : Alias) (k : Fin 3) : Parts :=
  Parts.literal (rationalNoncentral (pointBasis μ j) ν k)

theorem basisPart_width (μ : Alias) (j : Fin 3) (ν : Alias) (k : Fin 3) :
    (basisPart μ j ν k).Width 1 := by
  unfold basisPart rationalNoncentral pointBasis
  split_ifs <;> norm_num [Parts.Width,Parts.literal]

def perturbationPart (μ : Alias) (j : Fin 3) (ν : Alias) (k : Fin 3) : Parts :=
  if rationalCentralCheck ν then Parts.literal 0 else
    (Parts.literal (-rationalAmplitude)).mul (sumThree (fun d =>
      (Parts.literal (rationalWeight d)).mul
        ((basisPart μ j (ν+unitAlias d) k).add (basisPart μ j (ν-unitAlias d) k))))

theorem perturbationPart_valid (μ : Alias) (j : Fin 3) (ν : Alias) (k : Fin 3) :
    (perturbationPart μ j ν k).Valid := by
  unfold perturbationPart
  split_ifs
  · exact Parts.literal_valid _
  · exact Parts.mul_valid (Parts.literal_valid _) (sumThree_valid _ (fun d =>
      Parts.mul_valid (Parts.literal_valid _) (Parts.add_valid (Parts.literal_valid _)
        (Parts.literal_valid _))))

theorem perturbationPart_value (μ : Alias) (j : Fin 3) (ν : Alias) (k : Fin 3) :
    (perturbationPart μ j ν k).value = rationalPerturbation (pointBasis μ j) ν k := by
  unfold perturbationPart
  split_ifs with hc
  · simp only [Parts.literal_value,rationalPerturbation,rationalNoncentral,hc,ite_true,
      smul_eq_mul,mul_zero]
  · simp only [basisPart]
    rw [Parts.mul_value,sumThree_value _ (fun d => Parts.mul_valid (Parts.literal_valid _)
      (Parts.add_valid (Parts.literal_valid _) (Parts.literal_valid _)))]
    simp only [Parts.literal_value,Parts.mul_value,
      Parts.add_value _ _ (Parts.literal_valid _) (Parts.literal_valid _),rationalPerturbation,
      rationalNoncentral,hc,Bool.false_eq_true,ite_false,rationalPotential,smul_eq_mul]

theorem perturbationPart_width (μ : Alias) (j : Fin 3) (ν : Alias) (k : Fin 3) :
    (perturbationPart μ j ν k).Width 256 := by
  unfold perturbationPart
  split_ifs
  · norm_num [Parts.Width,Parts.literal]
  · have hamp : (Parts.literal (-rationalAmplitude)).Width 101 := by
      norm_num [Parts.Width,Parts.literal,rationalAmplitude]
      decide
    have hw (d : Fin 3) : (Parts.literal (rationalWeight d)).Width 2 := by
      fin_cases d <;> norm_num [Parts.Width,Parts.literal,rationalWeight] <;> decide
    have hsum := sumThree_width _ 6 (fun d =>
      (hw d).mul ((basisPart_width μ j (ν+unitAlias d) k).add
        (basisPart_width μ j (ν-unitAlias d) k)))
    exact (hamp.mul hsum).mono (by norm_num)

def stencilPart (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i : Fin 3) (μ : Alias) (j : Fin 3) : Parts :=
  (Parts.literal 0).sub (sumThree (fun k =>
    (freeEntry t E r c ν i k).mul (perturbationPart μ j ν k)))

theorem stencilPart_sound (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i : Fin 3) (μ : Alias) (j : Fin 3)
    (ht : t.Valid) (hE : E.Valid) (hr : ∀ k, (r k).Valid) (hc : ∀ k, (c k).Valid)
    (hcoord : ∀ k, (c k).value = (ν k : ℚ))
    (htbox : (3 : ℝ) ≤ t.value) (hEbox : (7 : ℝ) ≤ E.value ∧ (E.value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((r k).value : ℝ)| ≤ 1/16) :
    (stencilPart t E r c ν i μ j).Valid ∧
    (stencilPart t E r c ν i μ j).value =
      stencilEntry t.value E.value (fun k => (r k).value) ν i μ j := by
  have hfree (k) := freeEntry_sound t E r c ν ht hE hr hc hcoord htbox hEbox hrbox i k
  have hv (k) := Parts.mul_valid (hfree k).1 (perturbationPart_valid μ j ν k)
  refine ⟨Parts.sub_valid (Parts.literal_valid _) (sumThree_valid _ hv),?_⟩
  rw [stencilPart,Parts.sub_value _ _ (Parts.literal_valid _) (sumThree_valid _ hv),
    Parts.literal_value,zero_sub,sumThree_value _ hv]
  simp_rw [Parts.mul_value,(hfree _).2,perturbationPart_value]
  rfl

theorem stencilPart_width (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i : Fin 3) (μ : Alias) (j : Fin 3)
    (B : ℕ) (ht : t.Width B) (hE : E.Width B)
    (hr : ∀ k, (r k).Width B) (hc : ∀ k, (c k).Width B) :
    (stencilPart t E r c ν i μ j).Width (1024*(B+3)) := by
  have hzero : (Parts.literal 0).Width 1 := by norm_num [Parts.Width,Parts.literal]
  have hsum := sumThree_width _ (128*(B+3)+256+1) (fun k =>
    (freeEntry_width t E r c ν i k B ht hE hr hc).mul (perturbationPart_width μ j ν k))
  exact (hzero.sub hsum).mono (by omega)

def forcingPart (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i : Fin 3) (f : Fin 3 → Parts) : Parts :=
  sumThree (fun k => (freeEntry t E r c ν i k).mul (f k))

theorem forcingPart_sound (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i : Fin 3) (f : Fin 3 → Parts)
    (ht : t.Valid) (hE : E.Valid) (hr : ∀ k, (r k).Valid) (hc : ∀ k, (c k).Valid)
    (hf : ∀ k, (f k).Valid) (hcoord : ∀ k, (c k).value = (ν k : ℚ))
    (htbox : (3 : ℝ) ≤ t.value) (hEbox : (7 : ℝ) ≤ E.value ∧ (E.value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((r k).value : ℝ)| ≤ 1/16) :
    (forcingPart t E r c ν i f).Valid ∧
    (forcingPart t E r c ν i f).value =
      ∑ k, rationalFreeInverseMatrix t.value E.value (fun k => (r k).value) ν i k*(f k).value := by
  have hfree (k) := freeEntry_sound t E r c ν ht hE hr hc hcoord htbox hEbox hrbox i k
  have hv (k) := Parts.mul_valid (hfree k).1 (hf k)
  refine ⟨sumThree_valid _ hv,?_⟩
  rw [forcingPart,sumThree_value _ hv]
  simp_rw [Parts.mul_value,(hfree _).2]

theorem forcingPart_width (t E : Parts) (r c : Fin 3 → Parts) (ν : Alias) (i : Fin 3) (f : Fin 3 → Parts)
    (B : ℕ) (ht : t.Width B) (hE : E.Width B)
    (hr : ∀ k, (r k).Width B) (hc : ∀ k, (c k).Width B) (hf : ∀ k, (f k).Width B) :
    (forcingPart t E r c ν i f).Width (1024*(B+3)) :=
  (sumThree_width _ (128*(B+3)+B+1) (fun k =>
    (freeEntry_width t E r c ν i k B ht hE hr hc).mul (hf k))).mono (by omega)

def coefficientTable (t E : Parts) (r : Fin 3 → Parts) (R : ℕ)
    (f : Alias → Fin 3 → Parts) : CoefficientIndex (aliasArraySize R) → Parts :=
  Sum.elim
    (fun i => forcingPart t E r (coordinatePart R i) (arrayAliasAt R i) (arrayPolarizationAt R i)
      (f (arrayAliasAt R i)))
    (fun ij => stencilPart t E r (coordinatePart R ij.1) (arrayAliasAt R ij.1)
      (arrayPolarizationAt R ij.1) (arrayAliasAt R ij.2) (arrayPolarizationAt R ij.2))

theorem coefficientTable_sound (t E : Parts) (r : Fin 3 → Parts) (R : ℕ)
    (f : Alias → Fin 3 → Parts) (ht : t.Valid) (hE : E.Valid) (hr : ∀ k, (r k).Valid)
    (hf : ∀ ν, aliasInCube R ν → ∀ k, (f ν k).Valid)
    (htbox : (3 : ℝ) ≤ t.value) (hEbox : (7 : ℝ) ≤ E.value ∧ (E.value : ℝ) ≤ 8)
    (hrbox : ∀ k, |((r k).value : ℝ)| ≤ 1/16)
    (i : CoefficientIndex (aliasArraySize R)) :
    (coefficientTable t E r R f i).Valid ∧
    (coefficientTable t E r R f i).value =
      cachedCoefficientTable t.value E.value (fun k => (r k).value) R (fun ν k => (f ν k).value) i := by
  rcases i with i | ⟨i,j⟩
  · have h := forcingPart_sound t E r (coordinatePart R i) (arrayAliasAt R i)
      (arrayPolarizationAt R i) (f (arrayAliasAt R i)) ht hE hr (coordinatePart_valid R i)
      (hf _ (arrayAlias_mem R _)) (coordinatePart_value R i) htbox hEbox hrbox
    exact ⟨h.1,h.2⟩
  · have h := stencilPart_sound t E r (coordinatePart R i) (arrayAliasAt R i)
      (arrayPolarizationAt R i) (arrayAliasAt R j) (arrayPolarizationAt R j) ht hE hr
      (coordinatePart_valid R i) (coordinatePart_value R i) htbox hEbox hrbox
    exact ⟨h.1,h.2.trans (cachedTransitionMatrix_entry _ _ _ _ _ _).symm⟩

theorem coefficientTable_width (t E : Parts) (r : Fin 3 → Parts) (R : ℕ)
    (f : Alias → Fin 3 → Parts) (B : ℕ) (hR : R.bits.length+2 ≤ B)
    (ht : t.Width B) (hE : E.Width B) (hr : ∀ k, (r k).Width B)
    (hf : ∀ ν, aliasInCube R ν → ∀ k, (f ν k).Width B)
    (i : CoefficientIndex (aliasArraySize R)) :
    (coefficientTable t E r R f i).Width (1024*(B+3)) := by
  rcases i with i | ⟨i,j⟩
  · exact forcingPart_width t E r (coordinatePart R i) (arrayAliasAt R i) (arrayPolarizationAt R i)
      (f (arrayAliasAt R i)) B ht hE hr (fun k => (coordinatePart_width R i k).mono hR)
      (hf _ (arrayAlias_mem R _))
  · exact stencilPart_width t E r (coordinatePart R i) (arrayAliasAt R i) (arrayPolarizationAt R i)
      (arrayAliasAt R j) (arrayPolarizationAt R j) B ht hE hr
      (fun k => (coordinatePart_width R i k).mono hR)

#print axioms coefficientTable_sound
#print axioms coefficientTable_width

end Maxwell.Continuum.Calibration.RawFree
