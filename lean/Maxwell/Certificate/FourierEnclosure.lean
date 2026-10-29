import Maxwell.Certificate.FourierGauge

/-! Verified rational enclosures of actual Fourier basis and field entries.
The square-root endpoints are proposals checked by exact rational squares. -/

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction)
open Trigonometric IntervalMatrix

def sqrtCellCountInterval : Interval :=
  ⟨824963474247118971758 / (2 : ℚ)^64,
   824963474247118971759 / (2 : ℚ)^64, by norm_num⟩

theorem sqrtCellCount_checked :
    Interval.sqrtCheck (Interval.point 2000) sqrtCellCountInterval = true := by
  decide +kernel

theorem sqrtCellCount_positive : 0 < sqrtCellCountInterval.lo := by
  norm_num [sqrtCellCountInterval]

def normalizationBall : Ball :=
  intervalToBall (Interval.reciprocal sqrtCellCountInterval sqrtCellCount_positive)

theorem normalizationBall_contains : normalizationBall.Contains (1 / Real.sqrt 2000) :=
  intervalToBall_contains (Interval.reciprocal_contains sqrtCellCount_positive
    (Interval.sqrtCheck_sound sqrtCellCount_checked (Interval.contains_point 2000)))

def normalizationRectangle : ComplexRectangle := realRectangle normalizationBall

theorem normalizationRectangle_contains : normalizationRectangle.Contains normalization := by
  have h := realRectangle_contains normalizationBall_contains
  simpa only [normalizationRectangle, normalization, Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, one_mul] using h

def entryPhase (c : Direction → ℚ) (p : Cell) (f : Frequency) : ℚ :=
  (∑ j : Direction, ((reciprocalIndex f j : ℚ) + c j) * (representative p j : ℚ)) / 20

theorem planeWave_eq_cis_entry (c : Direction → ℚ) (p : Cell) (f : Frequency) :
    planeWave (fun j => (c j : ℝ)) f (representative p) = Trigonometric.cis (entryPhase c p f) := by
  unfold planeWave phase Trigonometric.cis entryPhase
  congr 1
  push_cast
  ring

def transformRectangle (c : Direction → ℚ) (p : Cell) (f : Frequency) : ComplexRectangle :=
  normalizationRectangle.mul (Trigonometric.cisRectangle (entryPhase c p f))

theorem transformRectangle_contains (c : Direction → ℚ) (p : Cell) (f : Frequency) :
    (transformRectangle c p f).Contains (transform (fun j => (c j : ℝ)) p f) := by
  unfold transform basis
  rw [planeWave_eq_cis_entry]
  exact ComplexRectangle.contains_mul normalizationRectangle_contains (cisRectangle_contains _)

def sumRectangle {ι : Type*} [Fintype ι] (a : ι → ComplexRectangle) : ComplexRectangle where
  re := ⟨∑ i, (a i).re.center, ∑ i, (a i).re.radius,
    Finset.sum_nonneg fun i _ => (a i).re.radius_nonneg⟩
  im := ⟨∑ i, (a i).im.center, ∑ i, (a i).im.radius,
    Finset.sum_nonneg fun i _ => (a i).im.radius_nonneg⟩

theorem sumBall_bound {ι : Type*} [Fintype ι] (a : ι → Ball) (x : ι → ℝ)
    (h : ∀ i, (a i).Contains (x i)) :
    |(∑ i, x i) - ((∑ i, (a i).center : ℚ) : ℝ)| ≤ ((∑ i, (a i).radius : ℚ) : ℝ) := by
  simp only [Rat.cast_sum, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

theorem sumRectangle_contains {ι : Type*} [Fintype ι]
    {a : ι → ComplexRectangle} {z : ι → ℂ} (h : ∀ i, (a i).Contains (z i)) :
    (sumRectangle a).Contains (∑ i, z i) := by
  constructor
  · simpa only [Ball.Contains, sumRectangle, Complex.re_sum] using
      sumBall_bound (fun i => (a i).re) (fun i => (z i).re) (fun i => (h i).1)
  · simpa only [Ball.Contains, sumRectangle, Complex.im_sum] using
      sumBall_bound (fun i => (a i).im) (fun i => (z i).im) (fun i => (h i).2)

def pointRectangle (q : ℚ × ℚ) : ComplexRectangle :=
  ⟨⟨q.1, 0, le_rfl⟩, ⟨q.2, 0, le_rfl⟩⟩

theorem pointRectangle_contains (q : ℚ × ℚ) : (pointRectangle q).Contains (toComplex q) := by
  constructor <;> simp [pointRectangle, Ball.Contains, toComplex]

def fieldRectangle (c : Direction → ℚ) (coefficients : Frequency → ComplexRectangle)
    (p : Cell) : ComplexRectangle :=
  sumRectangle fun f => (transformRectangle c p f).mul (coefficients f)

theorem fieldRectangle_contains (c : Direction → ℚ) (coefficients : Frequency → ComplexRectangle)
    (v : Frequency → ℂ) (hv : ∀ f, (coefficients f).Contains (v f)) (p : Cell) :
    (fieldRectangle c coefficients p).Contains ((transform (fun j => (c j : ℝ)) *ᵥ v) p) := by
  exact sumRectangle_contains fun f =>
    ComplexRectangle.contains_mul (transformRectangle_contains c p f) (hv f)

/-- Rational complex coefficients, including the frozen dyadic witnesses,
need no input-containment assumption. -/
theorem rational_fieldRectangle_contains (c : Direction → ℚ) (v : Frequency → ℚ × ℚ) (p : Cell) :
    (fieldRectangle c (fun f => pointRectangle (v f)) p).Contains
      ((transform (fun j => (c j : ℝ)) *ᵥ fun f => toComplex (v f)) p) :=
  fieldRectangle_contains c _ _ (fun f => pointRectangle_contains (v f)) p

theorem electricTransform_mulVec (c : Maxwell.Spectral.PeriodicYee.Momentum)
    (v : Electric → ℂ) (e : Electric) :
    (electricTransform c *ᵥ v) e = (transform c *ᵥ fun f => v (e.1, f)) e.2 := by
  simp [electricTransform, transform, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    ite_mul]

def electricFieldRectangle (c : Direction → ℚ) (coefficients : Electric → ComplexRectangle)
    (e : Electric) : ComplexRectangle :=
  fieldRectangle c (fun f => coefficients (e.1, f)) e.2

theorem electricFieldRectangle_contains (c : Direction → ℚ)
    (coefficients : Electric → ComplexRectangle) (v : Electric → ℂ)
    (hv : ∀ f, (coefficients f).Contains (v f)) (e : Electric) :
    (electricFieldRectangle c coefficients e).Contains
      ((electricTransform (fun j => (c j : ℝ)) *ᵥ v) e) := by
  rw [electricTransform_mulVec]
  exact fieldRectangle_contains c _ _ (fun f => hv (e.1, f)) e.2

theorem rational_electricFieldRectangle_contains (c : Direction → ℚ)
    (v : Electric → ℚ × ℚ) (e : Electric) :
    (electricFieldRectangle c (fun f => pointRectangle (v f)) e).Contains
      ((electricTransform (fun j => (c j : ℝ)) *ᵥ fun f => toComplex (v f)) e) :=
  electricFieldRectangle_contains c _ _ (fun f => pointRectangle_contains (v f)) e

end Maxwell.Certificate.FourierBinding
