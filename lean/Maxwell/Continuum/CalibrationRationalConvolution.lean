import Maxwell.Continuum.CalibrationBumpConvolution
import Maxwell.Continuum.CalibrationRationalFullSupport

/-! Executable multiplication of rational complex coefficients and the
literal finite convolution for the computed well-root polynomial. -/

namespace Maxwell.Continuum.Calibration

set_option backward.isDefEq.respectTransparency false

open FreeFiber PeriodicSampling Maxwell.Certificate

def rationalComplexMul (a b : RationalComplex) : RationalComplex :=
  (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)

theorem rationalComplexMul_value (a b : RationalComplex) :
    rationalComplexValue (rationalComplexMul a b) = rationalComplexValue a*rationalComplexValue b := by
  simp only [rationalComplexValue_eq,rationalComplexMul,Rat.cast_sub,Rat.cast_mul,Rat.cast_add]
  linear_combination -((a.2 : ℂ)*(b.2 : ℂ))*Complex.I_sq

theorem rationalComplexMul_zero (a : RationalComplex) : rationalComplexMul a 0 = 0 := by
  ext <;> simp [rationalComplexMul]

def rectangleRational (a : ComplexRectangle) : RationalComplex := (a.re.center,a.im.center)

theorem rectangleRational_value (a : ComplexRectangle) :
    rationalComplexValue (rectangleRational a) = rectangleCenter a := by
  rw [rationalComplexValue_eq]
  rfl

def rationalConvolution (D : ℕ) (c : Alias → RationalComplex) (f : RationalAliasField) : RationalAliasField :=
  fun ν j => ∑ n ∈ Product.frequencyCube D, rationalComplexMul (c n) (f (ν-n) j)

theorem rationalConvolution_represents (D : ℕ) (c : Alias → RationalComplex)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalConvolution D c f) (finiteAliasConvolution D (fun n => rationalComplexValue (c n)) u) := by
  intro ν j
  change rationalComplexLinear (∑ n ∈ Product.frequencyCube D,
    rationalComplexMul (c n) (f (ν-n) j)) = _
  simp only [map_sum]
  change _ = (∑ n ∈ Product.frequencyCube D, rationalComplexValue (c n) • shift (-n) u) ν j
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,PiLp.smul_apply,
    WithLp.ofLp_sum,smul_eq_mul,shift_apply]
  apply Finset.sum_congr rfl
  intro n _
  change rationalComplexValue (rationalComplexMul (c n) (f (ν-n) j)) =
    rationalComplexValue (c n)*u (ν+ -n) j
  rw [rationalComplexMul_value,hf]
  rw [sub_eq_add_neg]

theorem RationalSupported.convolution {f : RationalAliasField} {R : ℕ}
    (hf : RationalSupported f R) (D : ℕ) (c : Alias → RationalComplex) :
    RationalSupported (rationalConvolution D c f) (R+D) := by
  intro ν hν j
  obtain ⟨k,hk⟩ := hν
  unfold rationalConvolution
  apply Finset.sum_eq_zero
  intro n hn
  have hnk := (Product.mem_frequencyCube D n).mp hn k
  have hb : (R : ℤ) < |(ν-n) k| := by
    have h := abs_add_le (ν k-n k) (n k)
    rw [sub_add_cancel] at h
    change (R : ℤ) < |ν k-n k|
    push_cast at hk
    omega
  rw [hf _ ⟨k,hb⟩ j,rationalComplexMul_zero]

def rationalRootApply (s : ℚ) (N ell : ℕ) (f : RationalAliasField) : RationalAliasField :=
  rationalConvolution (rootDegree s N ell) (fun n => rectangleRational (computedRootCoefficient s N ell n)) f

theorem rationalRootApply_represents (s : ℚ) (N ell : ℕ)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalRootApply s N ell f) (computedRootConvolution s N ell u) := by
  have h := rationalConvolution_represents (rootDegree s N ell)
    (fun n => rectangleRational (computedRootCoefficient s N ell n)) hf
  simpa only [rectangleRational_value,rationalRootApply,computedRootConvolution] using h

theorem RationalSupported.rootApply {f : RationalAliasField} {R : ℕ}
    (hf : RationalSupported f R) (s : ℚ) (N ell : ℕ) :
    RationalSupported (rationalRootApply s N ell f) (R+rootDegree s N ell) :=
  hf.convolution _ _

#print axioms rationalRootApply_represents

end Maxwell.Continuum.Calibration
