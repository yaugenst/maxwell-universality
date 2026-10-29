import Maxwell.Certificate.GlobalCenter
import Maxwell.Spectral.BoxResidual
import Maxwell.Spectral.BoxMixedForm

/-! Exact coordinate meanings of the axis and gradient arrays in the global
box verifier.  The fields below use the same fixed center Fourier gauge as
`GlobalCenter`; no numerical bound is assumed in their operator identities. -/

noncomputable section
namespace Maxwell.Certificate.GlobalDerivative

set_option maxRecDepth 4000

open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum Direction Cell20)
open Maxwell.Spectral BoxSymbols BoxCrossNorm BoxMagnetic BoxResidual
open BoxFourierProjection BoxProjectionAssembly BoxGradient BoxMixedForm BoxLinear

def axisSymbol (c : Momentum) (a : Direction) (f : Frequency) (j : Direction) : ℂ :=
  if j = a then (symbol c f j+1)*(Complex.I*(phaseScale : ℂ)) else 0

theorem axisSymbol_eq (c : Momentum) (a : Direction) (f : Frequency) :
    axisSymbol c a f = linearSymbol c (axis a) f := by
  funext j
  by_cases h : j = a
  · subst j
    simp [axisSymbol, linearSymbol, axis, symbol]
  · simp [axisSymbol, linearSymbol, axis, h]

def curlPrimeField (c : Momentum) (a : Direction) (u : FourierSpace) : FourierSpace :=
  (linearFrequencyCurl c (axis a)).conjTranspose.toEuclideanLin u

theorem curlPrimeField_apply (c : Momentum) (a : Direction) (u : FourierSpace)
    (e : Electric) :
    curlPrimeField c a u e =
      ((crossMatrix (axisSymbol c a e.2)).conjTranspose *ᵥ fun j => u (j,e.2)) e.1 := by
  rw [axisSymbol_eq]
  change ((linearFrequencyCurl c (axis a)).conjTranspose *ᵥ u) e = _
  simp [linearFrequencyCurl, blockMatrix, directSumMatrix, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Matrix.conjTranspose_apply, apply_ite, ite_mul]

def materialField (material : Cell20 → ℝ) (u : FourierSpace) : FourierSpace :=
  inverseMaterial material u

theorem materialField_apply (material : Cell20 → ℝ) (u : FourierSpace) (e : Electric) :
    materialField material u e =
      ((transform 0).conjTranspose *ᵥ fun r =>
        (transform 0 *ᵥ fun f => u (e.1,f)) r / (edgeAverage material (e.1,r) : ℂ)) e.2 := by
  change (fourierInverseMass material *ᵥ u) e = _
  simp only [fourierInverseMass, ← Matrix.mulVec_mulVec]
  rw [GlobalCenter.electricTransform_adjoint_mulVec]
  congr 2
  funext r
  simp only [inverseMass, Matrix.mulVec_diagonal, electricTransform_mulVec, div_eq_mul_inv]
  ring

theorem materialField_eq (material : Cell20 → ℝ) (u : FourierSpace) :
    materialField material u = inverseMaterial material u := rfl

theorem weightedField_eq (material : Cell20 → ℝ) (c : Momentum) (u : FourierSpace) :
    GlobalCenter.weightedField material c u = materialField material (GlobalCenter.curlField c u) := by
  change _ = (fourierInverseMass material).toEuclideanLin _
  simp only [GlobalCenter.weightedField, GlobalCenter.spatialWeightedField,
    GlobalCenter.inverseCurlField, fourierInverseMass, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply]

theorem curlField_eq (c : Momentum) (u : FourierSpace) :
    GlobalCenter.curlField c u = (curlOperator c).adjoint u := by
  change (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (star (frequencyCurl c))) u = _
  rw [map_star]
  rfl

theorem curlPrimeField_eq (c : Momentum) (a : Direction) (u : FourierSpace) :
    curlPrimeField c a u = (linearCurlOperator c (axis a)).adjoint u := by
  change (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (star (linearFrequencyCurl c (axis a)))) u = _
  rw [map_star]
  rfl

def weightedPrimeField (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (u : FourierSpace) : FourierSpace := materialField material (curlPrimeField c a u)

def magneticPrimeField (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (u : FourierSpace) : FourierSpace :=
  (linearFrequencyCurl c (axis a)).toEuclideanLin (GlobalCenter.weightedField material c u) +
    (frequencyCurl c).toEuclideanLin (weightedPrimeField material c a u)

theorem magneticPrimeField_apply (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (u : FourierSpace) (e : Electric) :
    magneticPrimeField material c a u e =
      (crossMatrix (axisSymbol c a e.2) *ᵥ fun j =>
        GlobalCenter.weightedField material c u (j,e.2)) e.1 +
      (curlSymbolMatrix c e.2 *ᵥ fun j => weightedPrimeField material c a u (j,e.2)) e.1 := by
  rw [axisSymbol_eq]
  change ((linearFrequencyCurl c (axis a) *ᵥ _) e) + ((frequencyCurl c *ᵥ _) e) = _
  rw [frequencyCurl_mulVec]
  congr 1
  simp [linearFrequencyCurl, blockMatrix, directSumMatrix, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, ite_mul]

def projectionPrimeField (c : Momentum) (a : Direction) (u : FourierSpace) : FourierSpace :=
  WithLp.toLp 2 fun e => star (symbol c e.2 e.1) *
    ((∑ j, axisSymbol c a e.2 j*u (j,e.2))/(laplacianSymbol c e.2 : ℂ))

theorem projectionPrimeField_eq (c : Momentum) (a : Direction) (u : FourierSpace) :
    projectionPrimeField c a u = linearProjector c (axis a) u := by
  ext e
  change star (symbol c e.2 e.1) *
    ((∑ j, axisSymbol c a e.2 j*u (j,e.2))/(laplacianSymbol c e.2 : ℂ)) =
      (BoxProjection.transverseLinearTerm (longitudinalVector c e.2)
        (longitudinalLinear c (axis a) e.2) (frequencyComponent e.2 u)) e.1
  have hi : inner ℂ (longitudinalLinear c (axis a) e.2) (frequencyComponent e.2 u) =
      ∑ j, linearSymbol c (axis a) e.2 j*u (j,e.2) := by
    change (∑ j, u (j,e.2)*star (star (linearSymbol c (axis a) e.2 j))) = _
    simp only [star_star, mul_comm]
  rw [axisSymbol_eq, BoxProjection.transverseLinearTerm_apply, hi]
  simp only [BoxProjection.inverseVector, PiLp.smul_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  change star (symbol c e.2 e.1) *
    ((∑ j, linearSymbol c (axis a) e.2 j*u (j,e.2))/(laplacianSymbol c e.2 : ℂ)) =
    (∑ j, linearSymbol c (axis a) e.2 j*u (j,e.2)) *
      ((((1/‖longitudinalVector c e.2‖)^2 : ℝ) : ℂ)*star (symbol c e.2 e.1))
  rw [← longitudinalVector_norm_sq]
  push_cast
  simp only [div_eq_mul_inv, inv_pow, one_mul]
  ring

def auxiliaryPrimeField (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (u : FourierSpace) : FourierSpace :=
  magneticPrimeField material c a u + (1/32 : ℂ) • projectionPrimeField c a u

def gradientPrimeField (c : Momentum) (a : Direction) (low : Finset Frequency)
    (g : Coefficients) : FourierSpace :=
  WithLp.toLp 2 fun e => if e.2 ∈ low then
    g e.2 * (8*star (axisSymbol c a e.2 e.1)/(Real.sqrt (laplacianSymbol c e.2) : ℂ)) else 0

theorem normalizedGradient_coordinate (c : Momentum) (f : Frequency) (j : Direction) :
    normalizedGradient c f j = 8*star (symbol c f j)/(Real.sqrt (laplacianSymbol c f) : ℂ) := by
  simp only [normalizedGradient, longitudinalVector, PiLp.smul_apply, smul_eq_mul]
  rw [← longitudinalVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  change (8/(‖longitudinalVector c f‖ : ℂ))*star (symbol c f j) = _
  ring

theorem normalizedGradientLinear_coordinate (c : Momentum) (a : Direction)
    (f : Frequency) (j : Direction) :
    normalizedGradientLinear c (axis a) f j =
      8*star (axisSymbol c a f j)/(Real.sqrt (laplacianSymbol c f) : ℂ) := by
  simp only [axisSymbol_eq, normalizedGradientLinear, longitudinalLinear,
    PiLp.smul_apply, smul_eq_mul]
  rw [← longitudinalVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  change (8/(‖longitudinalVector c f‖ : ℂ))*star (linearSymbol c (axis a) f j) = _
  ring

theorem gradientOperator_coordinate (c : Momentum) (low : Finset Frequency)
    (g : Coefficients) (e : Electric) :
    gradientOperator c low g e = if e.2 ∈ low then
      g e.2*(8*star (symbol c e.2 e.1)/(Real.sqrt (laplacianSymbol c e.2) : ℂ)) else 0 := by
  change (if e.2 ∈ low then g e.2*normalizedGradient c e.2 e.1 else 0) = _
  rw [normalizedGradient_coordinate]

theorem gradientPrimeField_eq (c : Momentum) (a : Direction) (low : Finset Frequency)
    (g : Coefficients) : gradientPrimeField c a low g = gradientLinearOperator c (axis a) low g := by
  ext e
  change (if e.2 ∈ low then _ else 0) =
    (if e.2 ∈ low then g e.2*normalizedGradientLinear c (axis a) e.2 e.1 else 0)
  by_cases he : e.2 ∈ low
  · simp only [he, ite_true, axisSymbol_eq, normalizedGradientLinear, longitudinalLinear,
      PiLp.smul_apply, smul_eq_mul]
    rw [← longitudinalVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    simp only [Complex.star_def]
    ring
  · simp only [he, ite_false]

def gradientMagneticPrimeField (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (low : Finset Frequency) (g : Coefficients) : FourierSpace :=
  (frequencyCurl c).toEuclideanLin
    (weightedPrimeField material c a (gradientOperator c low g))

def mixedPrimeField (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (low : Finset Frequency) (g : Coefficients) : FourierSpace :=
  gradientMagneticPrimeField material c a low g + (1/32 : ℂ) • gradientPrimeField c a low g

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem firstMagneticAction_apply (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (F : V →L[ℂ] Field) (x : V) :
    firstMagneticAction material c (axis a) F x = magneticPrimeField material c a (F x) := by
  simp only [firstMagneticAction, magneticPrimeField, weightedPrimeField, weightedField_eq,
    materialField_eq, curlField_eq, curlPrimeField_eq, appliedCurl, appliedLinear,
    _root_.add_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem firstAuxiliaryAction_apply (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (F : V →L[ℂ] Field) (x : V) :
    firstAuxiliaryAction material c (axis a) (1/64) F x =
      auxiliaryPrimeField material c a (F x) := by
  simp only [firstAuxiliaryAction, auxiliaryPrimeField, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply,
    firstMagneticAction_apply, projectionPrimeField_eq]
  norm_num

theorem gradient_firstMagneticAction_apply (material : Cell20 → ℝ) (c : Momentum)
    (a : Direction) (low : Finset Frequency) (g : Coefficients) :
    firstMagneticAction material c (axis a) (gradientOperator c low) g =
      gradientMagneticPrimeField material c a low g := by
  simp only [firstMagneticAction, gradient_center_curl_zero, ContinuousLinearMap.comp_zero,
    zero_add, gradientMagneticPrimeField, weightedPrimeField, materialField_eq,
    curlPrimeField_eq, appliedLinear, ContinuousLinearMap.comp_apply]
  rfl

variable [CompleteSpace V]

private theorem first_sandwich {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B M : H →L[ℂ] H) (F : V →L[ℂ] H) (G : W →L[ℂ] H) :
    BoxCompression.sandwich M (A.adjoint.comp F) (B.adjoint.comp G) +
      BoxCompression.sandwich M (B.adjoint.comp F) (A.adjoint.comp G) =
    F.adjoint.comp (A.comp (M.comp (B.adjoint.comp G)) +
      B.comp (M.comp (A.adjoint.comp G))) := by
  simp only [BoxCompression.sandwich, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc]

theorem firstCompression_eq (material : Cell20 → ℝ) (c q : Momentum)
    (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) :
    firstCompression material c q F G = F.adjoint.comp (firstMagneticAction material c q G) := by
  exact first_sandwich (linearCurlOperator c q) (curlOperator c) (inverseMaterial material) F G

theorem firstCompression_apply (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) (x : W) :
    firstCompression material c (axis a) F G x =
      F.adjoint (magneticPrimeField material c a (G x)) := by
  rw [firstCompression_eq, ContinuousLinearMap.comp_apply, firstMagneticAction_apply]

theorem mixedFirstCompression_apply (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (low : Finset Frequency) (F : V →L[ℂ] Field) (g : Coefficients) :
    mixedFirstCompression material c (axis a) (1/64) low F g =
      F.adjoint (mixedPrimeField material c a low g) := by
  simp only [mixedFirstCompression, firstCompression_eq, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply,
    gradient_firstMagneticAction_apply, mixedPrimeField, map_add, map_smul,
    gradientPrimeField_eq]
  norm_num

theorem firstCompression_inner (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) (x : V) (y : W) :
    inner ℂ x (firstCompression material c (axis a) F G y) =
      inner ℂ (F x) (magneticPrimeField material c a (G y)) := by
  rw [firstCompression_apply, ContinuousLinearMap.adjoint_inner_right]

theorem mixedFirstCompression_inner (material : Cell20 → ℝ) (c : Momentum) (a : Direction)
    (low : Finset Frequency) (F : V →L[ℂ] Field) (x : V) (g : Coefficients) :
    inner ℂ x (mixedFirstCompression material c (axis a) (1/64) low F g) =
      inner ℂ (F x) (mixedPrimeField material c a low g) := by
  rw [mixedFirstCompression_apply, ContinuousLinearMap.adjoint_inner_right]

end Maxwell.Certificate.GlobalDerivative
