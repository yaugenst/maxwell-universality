import Maxwell.Certificate.DyadicProjection
import Maxwell.Certificate.DyadicMagnetic
import Maxwell.Certificate.DyadicFFT
import Maxwell.Certificate.FourierGauge
import Maxwell.Certificate.FourierTransverse

noncomputable section
namespace Maxwell.Certificate.GlobalCenter
open Matrix FourierBinding DyadicRectangle
open Maxwell.Spectral.PrimitiveYee Maxwell.Spectral.PeriodicYee

abbrev RectField := Frequency → Fin 3 → DyadicRectangle

def inputPolarization (p : ℕ) (raw : RectField) (f : Frequency) : Polarization :=
  WithLp.toLp 2 fun j => value p (raw f j)

def projectedPolarization (p : ℕ) (c : Momentum) (raw : RectField) (f : Frequency) : Polarization :=
  inputPolarization p raw f - gradientProjection c f (inputPolarization p raw f)

def projectedField (p : ℕ) (c : Momentum) (raw : RectField) : FourierSpace :=
  WithLp.toLp 2 fun e => projectedPolarization p c raw e.2 e.1

theorem projectedField_transverse (p : ℕ) (c : Momentum) (raw : RectField)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) : projectedField p c raw ∈ transverseSubspace c := by
  intro f
  exact sub_gradientProjection_mem_transverse c f (hlap f) _

theorem projection_contains (p : ℕ) (c : Momentum) (raw d : RectField)
    (lap : Frequency → DyadicRectangle) (w : Frequency → ProjectionProposal)
    (hd : ∀ f j, (d f j).Contains p (symbol c f j))
    (hl : ∀ f, (lap f).Contains p (laplacianSymbol c f : ℂ))
    (hw : ∀ f, projectionCheck p (d f) (raw f) (lap f) (w f) = true)
    (f : Frequency) (j : Fin 3) :
    ((w f).result j).Contains p ((projectedField p c raw) (j,f)) := by
  have h := projectionCheck_sound (hw f) (hd f)
    (fun i => value_contains p (raw f i)) (hl f) j
  simpa only [projectedField, projectedPolarization,
    gradientProjection_apply, PiLp.sub_apply, PiLp.smul_apply, inputPolarization,
    longitudinalVector, Complex.star_def, divergenceSymbol, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul, mul_comm] using h

def curlField (c : Momentum) (u : FourierSpace) : FourierSpace :=
  (frequencyCurl c).conjTranspose.toEuclideanLin u

def inverseCurlField (c : Momentum) (u : FourierSpace) : FourierSpace :=
  (electricTransform 0).toEuclideanLin (curlField c u)

def spatialWeightedField (material : Cell20 → ℝ) (c : Momentum) (u : FourierSpace) : FourierSpace :=
  (inverseMass material).toEuclideanLin (inverseCurlField c u)

def weightedField (material : Cell20 → ℝ) (c : Momentum) (u : FourierSpace) : FourierSpace :=
  (electricTransform 0).conjTranspose.toEuclideanLin (spatialWeightedField material c u)

theorem electricTransform_adjoint_mulVec (c : Momentum) (u : Electric → ℂ) (e : Electric) :
    ((electricTransform c).conjTranspose *ᵥ u) e =
      ((transform c).conjTranspose *ᵥ fun f => u (e.1,f)) e.2 := by
  simp only [electricTransform, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp [apply_ite, ite_mul, transform]

theorem spatialWeightedField_apply (material : Cell20 → ℝ) (c : Momentum)
    (u : FourierSpace) (e : Electric) :
    spatialWeightedField material c u e = inverseCurlField c u e / (edgeAverage material e : ℂ) := by
  simp [spatialWeightedField, inverseMass, Matrix.toEuclideanLin, Matrix.mulVec_diagonal,
    div_eq_mul_inv, mul_comm]

theorem weightedField_apply (material : Cell20 → ℝ) (c : Momentum) (u : FourierSpace) (e : Electric) :
    weightedField material c u e =
      ((transform 0).conjTranspose *ᵥ fun f => spatialWeightedField material c u (e.1,f)) e.2 :=
  electricTransform_adjoint_mulVec _ _ _

theorem magnetic_action_apply (material : Cell20 → ℝ) (c : Momentum)
    (u : FourierSpace) (e : Electric) :
    ((shiftedMagneticFourier material c (1/64)).toEuclideanLin u) e =
      (curlSymbolMatrix c e.2 *ᵥ fun j => weightedField material c u (j,e.2)) e.1 - u e/64 := by
  change ((shiftedMagneticFourier material c (1/64)) *ᵥ u) e = _
  simp only [shiftedMagneticFourier, fourierInverseMass, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [frequencyCurl_mulVec]
  push_cast
  change _ - (1/64:ℂ)*u e = _
  congr 1
  ring

theorem weightedField_contains (material : Cell20 → ℝ) (c : Momentum) (u : FourierSpace)
    (curl inverse spatial weighted : RectField)
    (hc : ∀ f j, (curl f j).Contains 52 (curlField c u (j,f)))
    (hi : ∀ j (v : Cell → ℂ), DyadicFFT.Contains 52 (fun f => curl f j) v →
      DyadicFFT.Contains 52 (fun f => inverse f j) (transform 0 *ᵥ v))
    (hm : ∀ j (v : Cell → ℂ), DyadicFFT.Contains 52 (fun f => inverse f j) v →
      DyadicFFT.Contains 52 (fun f => spatial f j)
        (fun r => v r / (edgeAverage material (j,r) : ℂ)))
    (hf : ∀ j (v : Cell → ℂ), DyadicFFT.Contains 52 (fun f => spatial f j) v →
      DyadicFFT.Contains 52 (fun f => weighted f j) ((transform 0).conjTranspose *ᵥ v))
    (f : Frequency) (j : Fin 3) :
    (weighted f j).Contains 52 (weightedField material c u (j,f)) := by
  have hinv := hi j _ (fun f => hc f j)
  have hinv' : DyadicFFT.Contains 52 (fun f => inverse f j)
      (fun r => inverseCurlField c u (j,r)) := by
    intro r
    change (inverse r j).Contains 52 ((electricTransform 0 *ᵥ curlField c u) (j,r))
    rw [electricTransform_mulVec]
    exact hinv r
  have hmat := hm j _ hinv'
  have hmat' : DyadicFFT.Contains 52 (fun f => spatial f j)
      (fun r => spatialWeightedField material c u (j,r)) := by
    intro r
    change (spatial r j).Contains 52 (spatialWeightedField material c u (j,r))
    rw [spatialWeightedField_apply]
    exact hmat r
  rw [weightedField_apply]
  exact hf j _ hmat' f

theorem magnetic_result_contains (material : Cell20 → ℝ) (c : Momentum) (u : FourierSpace)
    (d field weighted result : RectField)
    (hd : ∀ f j, (d f j).Contains 52 (symbol c f j))
    (hu : ∀ f j, (field f j).Contains 52 (u (j,f)))
    (hw : ∀ f j, (weighted f j).Contains 52 (weightedField material c u (j,f)))
    (h : ∀ f, magneticCheck (d f) (weighted f) (field f) (result f) = true)
    (f : Frequency) (j : Fin 3) :
    (result f j).Contains 52
      (((shiftedMagneticFourier material c (1/64)).toEuclideanLin u) (j,f)) := by
  rw [magnetic_action_apply]
  exact magneticCheck_sound (h f) (hd f) (hw f) (hu f) j

end Maxwell.Certificate.GlobalCenter
